import NautyVerified.Proofs.Set.Add

/-!
# `ISELEMENT`

`eval_isElement`: `(s[a >> 6] & bit[a & 63]) != 0`, for an `int` expression
`a` holding `c`, a `bit` table at `bb`, and `s` holding words `ws`, is
whether `c` is a member (`SetwordsMem`).
-/

namespace NautyVerified.Proofs.Set

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec

/-- `(s[a >> 6] & bit[a & 63]) != 0`, with `bit` the table named `bitId`. -/
abbrev isElement (s : Common.AST.ident) (bitId : Common.AST.ident) (a : expr) : expr :=
  .Ebinop .One
    (.Ebinop .Oand (setWord s a)
      (.Ederef (.Ebinop .Oadd (.Evar bitId (tarray tulong 64)) (.Ebinop .Oand a (ci 63 tint) tint)
        (tptr tulong)) tulong) tulong)
    (ci 0 tint) tint

theorem and_bitAt_ne_zero (x : BitVec 64) {j : Nat} (hj : j < 64) :
    (x &&& bitAt j ≠ 0) ↔ x.getMsbD j = true := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hx
    apply h
    apply BitVec.eq_of_getMsbD_eq
    intro i hi
    rw [BitVec.getMsbD_and, getMsbD_bitAt hj hi]
    by_cases hij : i = j
    · subst hij; simp at hx; simp [hx]
    · simp [hij]
  · intro hx h
    have := congrArg (fun y => y.getMsbD j) h
    simp only [BitVec.getMsbD_and, getMsbD_bitAt hj hj, decide_true, hx] at this
    simp at this

theorem eval_isElement {e : env} {le : temp_env} {m : mem} {s bitId : Common.AST.ident} {a : expr}
    {ba bb : block} {ofs : ptrofs} {ws : Nat → Lib.Integers.int64} {M c : Nat}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M)
    (hM : M < 2147483648) (hs : PTree.get s le = some (.Vptr ba ofs))
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < 64 * M) (hc2 : c < 2147483648)
    (hbit : BitTable m bb) (he : PTree.get bitId e = none)
    (hfind : Genv.find_symbol ge.genv_genv bitId = some bb) :
    Exec.evalExpr ge e le m (isElement s bitId a) =
      some (Val.of_bool (SetwordsMem (fun w => bv64 (ws w)) c)) := by
  have hw : c / 64 < M := by omega
  have hb : c % 64 < 64 := Nat.mod_lt _ (by decide)
  have h6 : Lib.Integers.Int.ltu (ir 6) Lib.Integers.Int.iwordsize = true := by decide
  have hshr : Lib.Integers.Int.shr (ir c) (ir 6) = ir ((c / 64 : Nat) : Int) := by
    rw [ir_shr6 ⟨by omega, by omega⟩]; congr 1
  have hand : Lib.Integers.Int.and (ir c) (ir 63) = ir ((c % 64 : Nat) : Int) := by
    rw [ir_and63 (by omega) (by omega)]; congr 1
  have hbaddr : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) (Ptrofs.of_ints (ir ((c % 64 : Nat) : Int))))) =
      elemOfs .Mint64 0 (c % 64) := by
    apply addr_elem _ _ .Mint64 rfl (base := 0) (by decide) (by omega)
    have h8 : csize .Mint64 = 8 := rfl
    rw [h8]; omega
  have hl1 := load_array harr hw (addr_word harr hw hM)
  have hl2 : Mem.loadv .Mint64 m (.Vptr bb (Ptrofs.add Ptrofs.zero (Ptrofs.mul
      (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong))
      (Ptrofs.of_ints (ir ((c % 64 : Nat) : Int)))))) =
      some (.Vlong (lr ((2 ^ (63 - c % 64) : Nat) : Int))) := by
    show Mem.load _ _ _ _ = _
    rw [hbaddr]; exact hbit _ hb
  simp only [setWord, Exec.evalExpr, Exec.lvalOfVar, hs, ha, hty, he, hfind]
  simp only [typeof, cop, h6, hshr, hand, ite_true]
  simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  simp only [cop]
  rw [hl1, hl2]
  simp only [longs, cop]
  rw [cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
  apply congrArg some; apply congrArg Val.of_bool
  have hbv : bv64 (lr ((2 ^ (63 - c % 64) : Nat) : Int)) = bitAt (c % 64) := by
    simp only [bv64_repr, intOfZ_zOfInt, bitAt, BitVec.ofInt_natCast]
  rw [bv64_eq, bv64_and, hbv, show bv64 (lr 0) = 0 by simp [intOfZ_zOfInt]]
  simp only [SetwordsMem]
  by_cases h : (bv64 (ws (c / 64))).getMsbD (c % 64) = true
  · rw [h]; simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]; exact (and_bitAt_ne_zero _ hb).2 h
  · have : bv64 (ws (c / 64)) &&& bitAt (c % 64) = 0 :=
      Classical.byContradiction fun h' => h ((and_bitAt_ne_zero _ hb).1 h')
    simp [this, h]

end NautyVerified.Proofs.Set
