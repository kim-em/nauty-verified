import NautyVerified.Proofs.Search.Processnode.Stats

/-!
# The automorphism workspace as a ring

nauty stores the `(fix, mcr)` pair of each automorphism at `fmptr`, wrapping
back one slot when the workspace is full. Slot `k` starts at word `2 * M * k`.
`eval_full`: `fmptr == worktop` holds when the workspace is full.
`wp_wrap`: `if (fmptr == worktop) fmptr -= 2 * m;` leaves `fmptr` at the slot
`pushAuto` writes (`slotOf`).
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

/-- The slot `pushAuto` writes. -/
def slotOf (k : Nat) : Nat := if k = wsPairs then wsPairs - 1 else k

/-- `p - j` for `p` at element `k + j`. -/
theorem sub_ptrTo8 (ce : composite_env) (base : Int) (k j : Nat) (hj : (j : Int) < 2147483648) :
    Ptrofs.sub (ptrTo base 8 (k + j)) (Ptrofs.mul (Ptrofs.repr (sizeof ce tulong))
      (Ptrofs.of_ints (ir j))) = ptrTo base 8 k := by
  have h8 : intOfZ (sizeof ce tulong) = 8 := rfl
  apply bvp_inj.1
  rw [bvp_sub, bvp_mul, bvp_repr, bvp_of_ints, toInt_ir ⟨by omega, hj⟩, bvp_repr, bvp_repr,
    intOfZ_zOfInt, intOfZ_zOfInt, h8, ← BitVec.ofInt_mul]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add]
  congr 1
  push_cast
  rw [Int.mul_add]
  omega

theorem fmptr_ptrTo (S : SLoc) (k : Nat) :
    Ptrofs.repr (zOfInt (S.wb + 8 * (2 * S.M * k))) = ptrTo S.wb 8 (2 * S.M * k) := by
  simp only [ptrTo, Int.natCast_mul]; rfl

theorem worktop_ptrTo (S : SLoc) :
    Ptrofs.repr (zOfInt (S.wb + 8 * (2 * wsPairs * S.M))) = ptrTo S.wb 8 (2 * S.M * wsPairs) := by
  simp only [ptrTo, Int.natCast_mul]
  rw [Int.mul_right_comm (2 : Int)]; rfl

theorem wsT (M : Nat) : 2 * wsPairs * M = 2 * M * wsPairs := Nat.mul_right_comm 2 wsPairs M

theorem eq_pp (ce : composite_env) (m : mem) (b1 b2 : block) (o1 o2 : ptrofs) (t1 t2 : type)
    (a b : attr) :
    Cfrontend.Cop.sem_binary_operation ce .Oeq (.Vptr b1 o1) (Tpointer t1 a) (.Vptr b2 o2)
      (Tpointer t2 b) m =
      (Val.cmplu_bool (Mem.valid_pointer m) .Ceq (.Vptr b1 o1) (.Vptr b2 o2)).map Val.of_bool := rfl

/-- `fmptr == worktop`. -/
theorem eval_full {n : Nat} {e : env} {le : temp_env} {m : mem} {S : SLoc} {gl : D.GLoc}
    {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (h1 : PTree.get dense.id.«nauty:fmptr» e = none) (h2 : PTree.get dense.id.«nauty:worktop» e = none) :
    Exec.evalExpr ge e le m (.Ebinop .Oeq (.Evar dense.id.«nauty:fmptr» (tptr tulong))
      (.Evar dense.id.«nauty:worktop» (tptr tulong)) tint) =
      some (Val.of_bool (decide (st.autos.size = wsPairs))) := by
  obtain ⟨ww, hws, -⟩ := h.arrays.autos.arr
  rw [wsT] at hws
  have hsz := h.arrays.autos.size
  have hM := h.M1
  have hf := hws.fits
  have hb := hws.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf
  generalize hT : 2 * S.M * wsPairs = T at hws hf
  have hk1 : 2 * S.M * st.autos.size ≤ T := hT ▸ Nat.mul_le_mul_left _ hsz
  generalize hK : 2 * S.M * st.autos.size = K at hk1
  have hT0 : 0 < T := by rw [← hT]; exact Nat.mul_pos (by omega) (by decide)
  have hu : ∀ j, j ≤ T → intOfZ (Ptrofs.unsigned (ptrTo S.wb 8 j)) = S.wb + 8 * j :=
    fun j hj => by apply unsigned_ptrTo <;> omega
  have hz : ∀ j, j ≤ T → Ptrofs.unsigned (ptrTo S.wb 8 j) = zOfInt (S.wb + 8 * j) :=
    fun j hj => by rw [← hu j hj, zOfInt_intOfZ]
  have hcmp : Val.cmplu_bool (Mem.valid_pointer m) .Ceq (.Vptr S.bws (ptrTo S.wb 8 K))
      (.Vptr S.bws (ptrTo S.wb 8 T)) = some (decide (K = T)) := by
    rw [cmplu_same _ _ _ _ _
      (by rw [hz _ hk1]; exact hws.weak_valid hT0 (by omega) (by rw [h8]; omega))
      (by rw [hz _ (Nat.le_refl _)]; exact hws.weak_valid hT0 (by omega) (by rw [h8]; omega))]
    congr 1
    show Ptrofs.eq _ _ = _
    rw [bvp_eq]
    apply decide_eq_decide.2
    constructor
    · intro he
      have := congrArg (fun b => (b.toNat : Int)) he
      simp only [← intOfZ_Ptrofs_unsigned, hu _ hk1, hu _ (Nat.le_refl _)] at this
      omega
    · intro he; rw [he]
  have hfm : PtrAt m E.fmptr (.Vptr S.bws (ptrTo S.wb 8 K)) := by
    rw [← hK, ← fmptr_ptrTo]; exact h.arrays.autos.fmptr
  have hwt : PtrAt m E.worktop (.Vptr S.bws (ptrTo S.wb 8 T)) := by
    rw [← hT, ← worktop_ptrTo]; exact h.fixed.worktop
  rw [Exec.evalExpr, eval_gptr h1 E.find_fmptr rfl hfm, eval_gptr h2 E.find_worktop rfl hwt]
  simp only [typeof, eq_pp, hcmp, Option.map]
  have : (K = T) ↔ st.autos.size = wsPairs := by
    rw [← hK, ← hT]
    exact ⟨fun h => Nat.eq_of_mul_eq_mul_left (by omega) h, fun h => by rw [h]⟩
  rw [decide_eq_decide.2 this]

/-- `g = rhs` for a pointer global. -/
theorem wp_gptrSet {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {g : ident}
    {bg : block} (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some bg)
    (hw : Mem.valid_access m .Mint64 bg (zOfInt 0) .Writable) {rhs : expr} {b : block} {o : ptrofs}
    (hr : Exec.evalExpr ge e le m rhs = some (.Vptr b o)) (hrt : typeof rhs = tptr tulong)
    (hQ : ∀ m', PtrAt m' bg (.Vptr b o) → Unch m m' (· = bg) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar g (tptr tulong)) rhs) Q e le m := by
  obtain ⟨m', hst⟩ := Mem.valid_access_store _ _ _ _ (.Vptr b o) hw
  apply wp_assign_eval
  simp only [hr, hrt]
  simp only [Exec.evalLvalue, Exec.lvalOfVar, hge, hg, typeof, cop, Exec.assignLoc,
    Cfrontend.Ctypes.access_mode, Mem.storev, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
    Alloc.Mptr_eq, hst]
  exact hQ m' ⟨by rw [Mem.load_store_same _ _ _ _ _ _ hst]; rfl,
    Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ hw⟩ (Unch.store hst rfl)
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)

/-- `if (fmptr == worktop) fmptr -= 2 * m;` -/
theorem wp_wrap {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (h1 : PTree.get dense.id.«nauty:fmptr» e = none) (h2 : PTree.get dense.id.«nauty:worktop» e = none)
    (h3 : PTree.get dense.id.«nauty:m» e = none)
    (hQ : ∀ m', PtrAt m' E.fmptr (.Vptr S.bws (ptrTo S.wb 8 (2 * S.M * slotOf st.autos.size))) →
      Unch m m' (· = E.fmptr) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (Set.sk (.Sifthenelse
      (.Ebinop .Oeq (.Evar dense.id.«nauty:fmptr» (tptr tulong))
        (.Evar dense.id.«nauty:worktop» (tptr tulong)) tint)
      (Set.sk (.Sassign (.Evar dense.id.«nauty:fmptr» (tptr tulong))
        (.Ebinop .Osub (.Evar dense.id.«nauty:fmptr» (tptr tulong))
          (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint) (tptr tulong))))
      .Sskip)) Q e le m := by
  have hM := h.M1
  have hMl := h.Mlt
  have hfm : PtrAt m E.fmptr (.Vptr S.bws (ptrTo S.wb 8 (2 * S.M * st.autos.size))) := by
    rw [← fmptr_ptrTo]; exact h.arrays.autos.fmptr
  wp_step; wp_step
  refine wp_ifB (eval_full h h1 h2) rfl ?_
  by_cases hf : st.autos.size = wsPairs
  · rw [decide_eq_true hf, ite_eq_left rfl]
    wp_step; wp_step
    have hk : 2 * S.M * wsPairs = 2 * S.M * (wsPairs - 1) + 2 * S.M := by
      rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by decide))]
    refine wp_gptrSet h1 E.find_fmptr hfm.writable (b := S.bws)
      (o := ptrTo S.wb 8 (2 * S.M * (wsPairs - 1))) ?_ rfl ?_
    · rw [Exec.evalExpr, eval_gptr h1 E.find_fmptr rfl hfm, Exec.evalExpr, eval_ci,
        eval_gint h3 E.find_m h.fixed.mm]
      simp only [typeof, cop, ir_mul]
      rw [hf, hk, show (2 : Int) * (S.M : Int) = ((2 * S.M : Nat) : Int) by push_cast; rfl,
        sub_ptrTo8 _ _ _ _ (by omega)]
    · intro m' hp hu hv
      exact hQ m' (by simp only [slotOf, hf, ite_true]; exact hp) hu hv
  · rw [decide_eq_false hf, ite_eq_right (by decide)]
    apply wp_skip
    exact hQ m (by simp only [slotOf, hf, ite_false]; exact hfm) (Unch.refl _ _) fun _ h => h

/-- The words of slot `o` replaced by `wf` then `wm`. -/
def slotSet (ww wf wm : Nat → Lib.Integers.int64) (o M : Nat) (w : Nat) : Lib.Integers.int64 :=
  if o ≤ w ∧ w < o + M then wf (w - o) else if o + M ≤ w ∧ w < o + M + M then wm (w - (o + M))
  else ww w

/-- A workspace after its slot at word `o` was rewritten and nothing else in it changed. -/
theorem ArrayAt.slot {m m' : mem} {b : block} {base : Int} {ww wf wm : Nat → Lib.Integers.int64}
    {W o M : Nat} (h : ArrayAt m .Mint64 b base (longs ww) W)
    (hf : ArrayAt m' .Mint64 b (base + 8 * o) (longs wf) M)
    (hm : ArrayAt m' .Mint64 b (base + 8 * (o + M)) (longs wm) M) (hle : o + M + M ≤ W)
    (hr : Rest m m' b (base + 8 * o) b (base + 8 * (o + M)) M) (hk : Alloc.Keep m m' b) :
    ArrayAt m' .Mint64 b base (longs (slotSet ww wf wm o M)) W := by
  have h8 : csize .Mint64 = 8 := rfl
  have hb := h.base_nonneg
  refine ⟨h.base_nonneg, h.fits, fun i hi => ?_, fun i hi => Keep.access' hk (h.writable i hi)⟩
  simp only [longs, slotSet]
  by_cases h1 : o ≤ i ∧ i < o + M
  · rw [ite_eq_left h1]
    have := hf.load (i - o) (by omega)
    rw [show base + 8 * (o : Int) = base + csize .Mint64 * o by rw [h8], elemOfs_slice,
      show o + (i - o) = i by omega] at this
    exact this
  · rw [ite_eq_right h1]
    by_cases h2 : o + M ≤ i ∧ i < o + M + M
    · rw [ite_eq_left h2]
      have := hm.load (i - (o + M)) (by omega)
      rw [show base + 8 * ((o : Int) + M) = base + csize .Mint64 * (o + M : Nat) by rw [h8]; push_cast; rfl,
        elemOfs_slice, show o + M + (i - (o + M)) = i by omega] at this
      exact this
    · rw [ite_eq_right h2]
      have := hr rfl .Mint64 (base + 8 * i) (by
        rw [h8]; rcases Nat.lt_or_ge i o with h3 | h3
        · left; omega
        · right; omega) (by
        rw [h8]; rcases Nat.lt_or_ge i (o + M) with h3 | h3
        · left; push_cast at *; omega
        · right; push_cast at *; omega)
      simp only [elemOfs, h8] at this ⊢
      rw [this]; exact h.load i hi

end NautyVerified.Proofs.Search.Processnode
