import NautyVerified.Proofs.Search.Processnode.Ring

/-!
# Recording a pair in the workspace

`pushAuto_eq`: with `wsCap = 500`, `pushAuto` replaces the last pair when the
workspace is full and appends otherwise (`pushA`). `AutosAt.push`: after the
pair's words are written at slot `slotOf size` and `fmptr` points past it, the
workspace holds `pushA`.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

variable {n : Nat}

/-- `pushAuto` with `wsCap = 500`. -/
def pushA (autos : Array (VSet n × VSet n)) (pair : VSet n × VSet n) : Array (VSet n × VSet n) :=
  if autos.size = wsPairs then autos.set! (wsPairs - 1) pair else autos.push pair

theorem pushAuto_eq {κ : Type} (st : SearchState n κ) (pair : VSet n × VSet n)
    (h : st.wsCap = wsPairs) : pushAuto st pair = { st with autos := pushA st.autos pair } := by
  unfold pushAuto pushA
  rw [h]
  by_cases hs : st.autos.size = wsPairs
  · simp [hs]
  · simp [hs]

theorem pushA_size {autos : Array (VSet n × VSet n)} (pair : VSet n × VSet n)
    (h : autos.size ≤ wsPairs) : (pushA autos pair).size = slotOf autos.size + 1 := by
  unfold pushA slotOf
  by_cases hs : autos.size = wsPairs
  · simp [hs]
  · simp [hs]

theorem pushA_get {autos : Array (VSet n × VSet n)} (pair : VSet n × VSet n)
    (h : autos.size ≤ wsPairs) {i : Nat} (hi : i < slotOf autos.size + 1) :
    (pushA autos pair)[i]! = if i = slotOf autos.size then pair else autos[i]! := by
  unfold pushA slotOf at *
  by_cases hs : autos.size = wsPairs
  · simp only [hs, ite_true] at hi ⊢
    by_cases hk : i = wsPairs - 1
    · subst hk; rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; decide)]; simp
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hk), ite_eq_right hk]
  · simp only [hs, ite_false] at hi ⊢
    by_cases hk : i = autos.size
    · subst hk; simp
    · rw [ite_eq_right hk]
      simp only [getElem!_def, Array.getElem?_push]
      rw [if_neg hk]

theorem AutosAtG.push {ge : genv} [E : NautyEnv ge] {m m' : mem} {S : SLoc} {autos : Array (VSet n × VSet n)}
    (ha : AutosAtG m S autos) (hM : 0 < S.M) {pair : VSet n × VSet n}
    {wf wm : Nat → Lib.Integers.int64}
    (hf : ArrayAt m' .Mint64 S.bws (S.wb + 8 * (2 * S.M * slotOf autos.size)) (longs wf) S.M)
    (hm : ArrayAt m' .Mint64 S.bws (S.wb + 8 * (2 * S.M * slotOf autos.size + S.M)) (longs wm) S.M)
    (hrf : SetRep (fun w => bv64 (wf w)) S.M pair.1) (hrm : SetRep (fun w => bv64 (wm w)) S.M pair.2)
    (hr : Rest m m' S.bws (S.wb + 8 * (2 * S.M * slotOf autos.size)) S.bws
      (S.wb + 8 * (2 * S.M * slotOf autos.size + S.M)) S.M)
    (hk : Alloc.Keep m m' S.bws)
    (hp : PtrAt m' E.fmptr (.Vptr S.bws (ptrTo S.wb 8 (2 * S.M * (slotOf autos.size + 1))))) :
    AutosAtG m' S (pushA autos pair) := by
  have hsz := ha.size
  obtain ⟨ww, hws, hrep⟩ := ha.arr
  have hk1 : slotOf autos.size + 1 ≤ wsPairs := by
    unfold slotOf; by_cases h : autos.size = wsPairs
    · rw [if_pos h]; decide
    · rw [if_neg h]; omega
  have hks : slotOf autos.size ≤ autos.size := by
    unfold slotOf; by_cases h : autos.size = wsPairs
    · rw [if_pos h, h]; decide
    · rw [if_neg h]; exact Nat.le_refl _
  have hle : 2 * S.M * slotOf autos.size + S.M + S.M ≤ 2 * wsPairs * S.M := by
    have h1 := Nat.mul_le_mul_left (2 * S.M) hk1
    rw [Nat.mul_succ] at h1; rw [wsT]; omega
  have hws' := Processnode.ArrayAt.slot hws hf (by push_cast at hm ⊢; exact hm) hle
    (by push_cast at hr ⊢; exact hr) hk
  refine ⟨by rw [pushA_size _ hsz]; exact hk1, ⟨_, hws', fun i hi => ?_⟩, ?_⟩
  · rw [pushA_size _ hsz] at hi
    rw [pushA_get _ hsz hi]
    by_cases hik : i = slotOf autos.size
    · subst hik
      rw [ite_eq_left rfl]
      refine ⟨Graph.setRep_congr hrf fun w hw => ?_, Graph.setRep_congr hrm fun w hw => ?_⟩
      · simp only [slotSet]
        generalize 2 * S.M * slotOf autos.size = K
        rw [ite_eq_left ⟨by omega, by omega⟩, show K + w - K = w by omega]
      · simp only [slotSet]
        generalize 2 * S.M * slotOf autos.size = K
        rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
          show K + S.M + w - (K + S.M) = w by omega]
    · rw [ite_eq_right hik]
      have hil : i < slotOf autos.size := by omega
      have hi2 : 2 * S.M * i + 2 * S.M ≤ 2 * S.M * slotOf autos.size := by
        have := Nat.mul_le_mul_left (2 * S.M) hil; rw [Nat.mul_succ] at this; omega
      obtain ⟨r1, r2⟩ := hrep i (by omega)
      refine ⟨Graph.setRep_congr r1 fun w hw => ?_, Graph.setRep_congr r2 fun w hw => ?_⟩
      · simp only [slotSet]
        generalize 2 * S.M * slotOf autos.size = K at hi2
        generalize 2 * S.M * i = I at hi2 ⊢
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      · simp only [slotSet]
        generalize 2 * S.M * slotOf autos.size = K at hi2
        generalize 2 * S.M * i = I at hi2 ⊢
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [pushA_size _ hsz, fmptr_ptrTo]; exact hp

end NautyVerified.Proofs.Search.Processnode
