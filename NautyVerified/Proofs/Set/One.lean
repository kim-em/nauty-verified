import NautyVerified.Proofs.Set.Bit

/-!
# `ISELEMENT1`, `ADDELEMENT1`, `DELELEMENT1`

nauty's one-word set macros, as `refine1` (the `m == 1` refine) uses them:
`ISELEMENT1(s, a)` is `(*s & bit[a]) != 0`, `ADDELEMENT1(s, a)` is
`*s |= bit[a]` and `DELELEMENT1(s, a)` is `*s &= ~bit[a]`, with no word index
and no `& 63`. For a one-word set and `a < 64` they agree with the general
macros: `eval_isElement1`, `wp_addElement1` (the words become `addW ws c`)
and `wp_delElement1` (`delW ws c`).
-/

namespace NautyVerified.Proofs.Set

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec

variable {xi : ExternalCalls}

/-- `bitId[a]`. -/
abbrev bit1 (bitId : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar bitId (tarray tulong 64)) a (tptr tulong)) tulong

/-- `ISELEMENT1(s, a)`. -/
abbrev isElement1 (s bitId : Common.AST.ident) (a : expr) : expr :=
  .Ebinop .One (.Ebinop .Oand (.Ederef (pv s) tulong) (bit1 bitId a) tulong) (ci 0 tint) tint

/-- `ADDELEMENT1(s, a)`. -/
abbrev addElement1 (s bitId : Common.AST.ident) (a : expr) : statement :=
  sk (.Sassign (.Ederef (pv s) tulong) (.Ebinop .Oor (.Ederef (pv s) tulong) (bit1 bitId a) tulong))

/-- `DELELEMENT1(s, a)`. -/
abbrev delElement1 (s bitId : Common.AST.ident) (a : expr) : statement :=
  sk (.Sassign (.Ederef (pv s) tulong)
    (.Ebinop .Oand (.Ederef (pv s) tulong) (.Eunop .Onotint (bit1 bitId a) tulong) tulong))

theorem ofs_word0 (ofs : ptrofs) :
    Ptrofs.unsigned ofs = elemOfs .Mint64 (intOfZ (Ptrofs.unsigned ofs)) 0 := by
  unfold elemOfs
  rw [show csize .Mint64 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ]

private theorem bit_addr {c : Nat} (hc : c < 64) :
    Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) (Ptrofs.of_ints (ir (c : Int))))) =
      elemOfs .Mint64 0 c := by
  apply addr_elem _ _ .Mint64 rfl (base := 0) (by decide) (by omega)
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8]; omega

theorem load_bit {m : mem} {bb : block} (hbit : BitTable m bb) {c : Nat} (hc : c < 64) :
    Mem.loadv .Mint64 m (.Vptr bb (Ptrofs.add Ptrofs.zero (Ptrofs.mul
      (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) (Ptrofs.of_ints (ir (c : Int)))))) =
      some (.Vlong (lr ((2 ^ (63 - c) : Nat) : Int))) := by
  show Mem.load _ _ _ _ = _
  rw [bit_addr hc]; exact hbit _ hc

/-- `bitId[a]` for `a` holding `c < 64`. -/
theorem eval_bit1 {e : env} {le : temp_env} {m : mem} {bitId : Common.AST.ident} {a : expr}
    {bb : block} {c : Nat}
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) (hc : c < 64)
    (hbit : BitTable m bb) (he : PTree.get bitId e = none)
    (hfind : Genv.find_symbol ge.genv_genv bitId = some bb) :
    Exec.evalExpr ge e le m (bit1 bitId a) = some (.Vlong (lr ((2 ^ (63 - c) : Nat) : Int))) := by
  simp only [bit1, Exec.evalExpr, Exec.lvalOfVar, ha, hty, he, hfind]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  exact load_bit hbit hc

theorem eval_isElement1 {e : env} {le : temp_env} {m : mem} {s bitId : Common.AST.ident}
    {a : expr} {ba bb : block} {ofs : ptrofs} {ws : Nat → Lib.Integers.int64} {c : Nat}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) 1)
    (hs : PTree.get s le = some (.Vptr ba ofs))
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) (hc : c < 64)
    (hbit : BitTable m bb) (he : PTree.get bitId e = none)
    (hfind : Genv.find_symbol ge.genv_genv bitId = some bb) :
    Exec.evalExpr ge e le m (isElement1 s bitId a) =
      some (Val.of_bool (SetwordsMem (fun w => bv64 (ws w)) c)) := by
  have hl1 := load_array harr (i := 0) (by decide) (ofs_word0 ofs)
  simp only [bit1, Exec.evalExpr, Exec.lvalOfVar, hs, ha, hty, he, hfind]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  rw [hl1, load_bit hbit hc]
  simp only [longs, cop]
  rw [cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
  apply congrArg some; apply congrArg Val.of_bool
  have hw : c / 64 = 0 := by omega
  have hm : c % 64 = c := by omega
  have hbv : bv64 (lr ((2 ^ (63 - c) : Nat) : Int)) = bitAt c := by
    simp only [bv64_repr, intOfZ_zOfInt, bitAt, BitVec.ofInt_natCast]
  rw [bv64_eq, bv64_and, hbv, show bv64 (lr 0) = 0 by simp [intOfZ_zOfInt]]
  simp only [SetwordsMem, hw, hm]
  by_cases h : (bv64 (ws 0)).getMsbD c = true
  · rw [h]; simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    exact (and_bitAt_ne_zero _ hc).2 h
  · have : bv64 (ws 0) &&& bitAt c = 0 :=
      Classical.byContradiction fun h' => h ((and_bitAt_ne_zero _ hc).1 h')
    simp [this, h]

theorem wp_addElement1 {s bitId : Common.AST.ident} {a : expr} {f : function} {Q : Post} {e : env}
    {le : temp_env} {m : mem} {ba bb : block} {ofs : ptrofs} {ws : Nat → Lib.Integers.int64}
    {c : Nat}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) 1)
    (hact : PTree.get s le = some (.Vptr ba ofs))
    (htc : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) (hc : c < 64)
    (hfind : Genv.find_symbol ge.genv_genv bitId = some bb)
    (hbit : BitTable m bb) (he : PTree.get bitId e = none)
    (hQ : ∀ m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs (addW ws c)) 1 →
      Unch m m' (· = ba) →
      Outside m m' ba (intOfZ (Ptrofs.unsigned ofs)) (intOfZ (Ptrofs.unsigned ofs) + 8 * 1) →
      Q.normal E0 e le m') :
    Wp xi ge f (addElement1 s bitId a) Q e le m := by
  have hw : c / 64 = 0 := by omega
  have hm : c % 64 = c := by omega
  obtain ⟨m', hst, harr', -⟩ := store_array harr (i := 0) (by decide)
    (.Vlong (Int64.or (ws 0) (lr ((2 ^ (63 - c) : Nat) : Int)))) rfl
  simp only [addElement1, bit1, sk]
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hact, htc, hty, he, hfind]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Exec.assignLoc]
  rw [load_array harr (i := 0) (by decide) (ofs_word0 ofs), load_bit hbit hc]
  simp only [longs, cop, Mem.storev]
  rw [ofs_word0 ofs, hst]
  rw [longs_upd] at harr'
  refine hQ m' ?_ (Unch.store hst rfl) (Outside.store harr (by decide) hst (Int.le_refl _)
    (by rw [show csize .Mint64 = 8 from rfl]; exact Int.le_refl _))
  simp only [addW, hw, hm]
  exact harr'

theorem wp_delElement1 {s bitId : Common.AST.ident} {a : expr} {f : function} {Q : Post} {e : env}
    {le : temp_env} {m : mem} {ba bb : block} {ofs : ptrofs} {ws : Nat → Lib.Integers.int64}
    {c : Nat}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) 1)
    (hact : PTree.get s le = some (.Vptr ba ofs))
    (htc : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) (hc : c < 64)
    (hfind : Genv.find_symbol ge.genv_genv bitId = some bb)
    (hbit : BitTable m bb) (he : PTree.get bitId e = none)
    (hQ : ∀ m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs (delW ws c)) 1 →
      Unch m m' (· = ba) →
      Outside m m' ba (intOfZ (Ptrofs.unsigned ofs)) (intOfZ (Ptrofs.unsigned ofs) + 8 * 1) →
      Q.normal E0 e le m') :
    Wp xi ge f (delElement1 s bitId a) Q e le m := by
  have hw : c / 64 = 0 := by omega
  have hm : c % 64 = c := by omega
  obtain ⟨m', hst, harr', -⟩ := store_array harr (i := 0) (by decide)
    (.Vlong (Int64.and (ws 0) (Int64.not (lr ((2 ^ (63 - c) : Nat) : Int))))) rfl
  simp only [delElement1, bit1, sk]
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hact, htc, hty, he, hfind]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Exec.assignLoc]
  rw [load_array harr (i := 0) (by decide) (ofs_word0 ofs), load_bit hbit hc]
  simp only [longs, cop, Mem.storev]
  rw [ofs_word0 ofs, hst]
  rw [longs_upd] at harr'
  refine hQ m' ?_ (Unch.store hst rfl) (Outside.store harr (by decide) hst (Int.le_refl _)
    (by rw [show csize .Mint64 = 8 from rfl]; exact Int.le_refl _))
  simp only [delW, hw, hm]
  exact harr'

end NautyVerified.Proofs.Set
