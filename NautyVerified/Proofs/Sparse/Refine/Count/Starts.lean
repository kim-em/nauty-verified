import NautyVerified.Proofs.Sparse.Refine.Count.Min

/-!
# The second fragment's cell starts

`wp_starts`: `for (k = v2; k < v3; ++k) CELLSTART[lab[k]] = v2;` writes
`startsLit`.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem foldl_starts (lab : Array Nat) (v2 : Nat) (a : Array Nat) (k V3 : Nat) (hk : k < V3) :
    (List.range' k (V3 - k)).foldl (fun a k => a.set! lab[k]! v2) a =
      (List.range' (k + 1) (V3 - (k + 1))).foldl (fun a k => a.set! lab[k]! v2) (a.set! lab[k]! v2) := by
  rw [show V3 - k = (V3 - (k + 1)) + 1 by omega, List.range'_succ, List.foldl_cons]

theorem wp_starts {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    (hr : Rep L t S) (ht : Tmp le L t) {V2 V3 : Nat} (h23 : V2 ≤ V3) (h3 : V3 ≤ n)
    (hlab : ∀ q < n, t.lab[q]! < n) (hsz : t.cellstart.size = n)
    (hk : PTree.get id.«k» le = some (.Vint (ir V2)))
    (hv2 : PTree.get id.«v2» le = some (.Vint (ir V2)))
    (hv3 : PTree.get id.«v3» le = some (.Vint (ir V3)))
    (hQ : ∀ le' m' (w : Nat → val),
      Mem m' L G { t with cellstart := Count.startsLit t.lab t.cellstart V2 V3 } { S with w1 := w } →
      Rep L { t with cellstart := Count.startsLit t.lab t.cellstart V2 V3 } { S with w1 := w } →
      Frame L m m' → PTree.get id.«k» le' = some (.Vint (ir V3)) →
      (∀ x, x ≠ id.«k» → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F startsD Q empty_env le m := by
  have hnl := hok.nlt
  let fin := Count.startsLit t.lab t.cellstart V2 V3
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ k a w, v = V3 - k ∧ V2 ≤ k ∧ k ≤ V3 ∧ a.size = n ∧
      fin = (List.range' k (V3 - k)).foldl (fun a k => a.set! t.lab[k]! V2) a ∧
      Mem m' L G { t with cellstart := a } { S with w1 := w } ∧
      Rep L { t with cellstart := a } { S with w1 := w } ∧ Frame L m m' ∧
      PTree.get id.«k» le' = some (.Vint (ir k)) ∧ ∀ x, x ≠ id.«k» → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ k a w, v = V3 - k ∧ V2 ≤ k ∧ k < V3 ∧ a.size = n ∧
      fin = (List.range' (k + 1) (V3 - (k + 1))).foldl (fun a k => a.set! t.lab[k]! V2) a ∧
      Mem m' L G { t with cellstart := a } { S with w1 := w } ∧
      Rep L { t with cellstart := a } { S with w1 := w } ∧ Frame L m m' ∧
      PTree.get id.«k» le' = some (.Vint (ir k)) ∧ ∀ x, x ≠ id.«k» → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := V3 - V2)
    ⟨rfl, rfl, V2, t.cellstart, S.w1, rfl, Nat.le_refl _, h23, hsz, Count.startsLit_eq _ _ _ _, hm, hr,
      Frame.refl _ _, hk, fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, k, a, w, rfl, hk1, hk2, ha, hfin, hm', hr', hf, hkk, ho⟩
    have ht' : Tmp le' L { t with cellstart := a } := (ht.frame (ws := [id.«k»])
      (fun x hx => ho x (by simpa using hx)) (by decide)).congr rfl rfl
    have hv3' : PTree.get id.«v3» le' = some (.Vint (ir V3)) := by rw [ho _ (by decide)]; exact hv3
    have hv2' : PTree.get id.«v2» le' = some (.Vint (ir V2)) := by rw [ho _ (by decide)]; exact hv2
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [eval_cmp hkk hv3']
    simp only [typeof, cop]
    rw [ir_lt (a := (k : Int)) (b := (V3 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hkv : k < V3
    · rw [show decide ((k : Int) < V3) = true from decide_eq_true (by omega)]
      simp (config := {decide := true}) only [ite_true]
      apply wp_skip
      wp_step; wp_step
      have hlk := hlab k (by omega)
      refine wp_w1F hok hm' (eval_lab hok hm' ht' (show Exec.evalExpr sge empty_env le' m' (tv id.«k») = _
        from hkk) rfl (by omega)) rfl (show t.lab[k]! < L.c1 by have := hok.c1; omega)
        (show Exec.evalExpr sge empty_env le' m' (tv id.«v2») = _ from hv2') rfl ?_
      intro m'' hm'' hf'
      refine ⟨by simp, rfl, k, a.set! t.lab[k]! V2, upd w t.lab[k]! (.Vint (ir V2)), rfl, hk1, hkv,
        by simp [ha], by rw [hfin, foldl_starts _ _ _ _ _ hkv], hm''.congr rfl rfl rfl rfl,
        Rep.setStart hr' ha hlk, hf.trans hf', hkk, ho⟩
    · rw [show decide ((k : Int) < V3) = false from decide_eq_false (by omega)]
      simp (config := {decide := true}) only [ite_false]
      apply wp_break
      have hkV : k = V3 := by omega
      subst hkV
      rw [show k - k = 0 by omega] at hfin
      simp only [List.range'_zero, List.foldl_nil] at hfin
      have hfin' : Count.startsLit t.lab t.cellstart V2 k = a := hfin
      rw [← hfin'] at hm' hr'
      exact hQ le' m' w hm' hr' hf hkk ho
  · rintro v tr e' le' m' ⟨rfl, rfl, k, a, w, rfl, hk1, hk2, ha, hfin, hm', hr', hf, hkk, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hkk, typeof, cop, ir_add]
    refine ⟨V3 - (k + 1), by omega, by simp, rfl, k + 1, a, w, rfl, by omega, by omega, ha, hfin, hm', hr', hf,
      by simp, fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩

end NautyVerified.Proofs.Sparse.Refine.Count
