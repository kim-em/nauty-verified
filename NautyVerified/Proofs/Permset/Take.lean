import NautyVerified.Program.Env
import NautyVerified.Proofs.Permset.Syntax
import NautyVerified.Proofs.Nextelement.Tree
import NautyVerified.Proofs.Set.Add

/-!
# `TAKEBIT`

`wp_takebit`: `TAKEBIT(b, setw)` on a nonzero word `x` sets `b` to the index
`k` of its first set bit and clears that bit of `setw`.
-/

namespace NautyVerified.Proofs.Permset

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (BitTable)
open NautyVerified.Proofs.Nextelement (LeadBit LeftbitTable)

variable {xi : ExternalCalls}

/-- `bit[e]` for `e` holding `k < 64`. -/
theorem eval_bitAt {e : env} {le : temp_env} {m : mem} (hbit : BitTable m E.nautilBit)
    (he : PTree.get Set.bit e = none) (a : expr) (k : Nat) (hk : k < 64)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir k))) (hty : typeof a = tint) :
    Exec.evalExpr ge e le m (bitAt a) = some (.Vlong (lr ((2 ^ (63 - k) : Nat) : Int))) := by
  have hbaddr : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) (Ptrofs.of_ints (ir k)))) =
      elemOfs .Mint64 0 k := by
    apply addr_elem _ _ .Mint64 rfl (base := 0) (by decide) (by omega)
    have h8 : csize .Mint64 = 8 := rfl
    rw [h8]; omega
  simp only [Exec.evalExpr, Exec.lvalOfVar, he, E.find_nautilBit, ha, hty]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  show Mem.load _ _ _ _ = _
  rw [hbaddr]; exact hbit k hk

/-- The word with bit `k` (from the most significant end) of `x` cleared. -/
abbrev clearBit (x : Lib.Integers.int64) (k : Nat) : Lib.Integers.int64 :=
  Lib.Integers.Int64.xor x (lr ((2 ^ (63 - k) : Nat) : Int))

theorem wp_takebit {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    (t : Common.AST.ident) (ht2 : t ≠ id.setw) (x : Lib.Integers.int64)
    (hsw : PTree.get id.setw le = some (.Vlong x)) (hx : bv64 x ≠ 0)
    (he : PTree.get Nextelement.id.leftbit e = none) (hbe : PTree.get Set.bit e = none)
    (hlb : LeftbitTable m) (hbit : BitTable m E.nautilBit)
    (hQ : ∀ k le', LeadBit (bv64 x) k → PTree.get id.setw le' = some (.Vlong (clearBit x k)) →
      PTree.get id.b le' = some (.Vint (ir k)) →
      (∀ y, y ≠ t → y ≠ id.b → y ≠ id.setw → PTree.get y le' = PTree.get y le) →
      Q.normal E0 e le' m) :
    Wp xi ge f (takebit t) Q e le m := by
  wp_step; wp_step
  refine Nextelement.wp_fbTree t x hsw hx he hlb ?_
  intro k hk
  simp only
  have hk64 := hk.1
  let v := Vint (Lib.Integers.Int.repr (zOfInt (k : Int)))
  let le1 := PTree.set t v (PTree.set t v (PTree.set t v le))
  have ho1 : ∀ y, y ≠ t → PTree.get y le1 = PTree.get y le := fun y hy => by
    simp only [le1]; rw [temps_gso _ _ hy, temps_gso _ _ hy, temps_gso _ _ hy]
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gss]
  let le2 := PTree.set id.b v le1
  wp_step; wp_step
  apply wp_set_eval
  have hb : Exec.evalExpr ge e le2 m (bitAt (tv id.b)) = some (.Vlong (lr ((2 ^ (63 - k) : Nat) : Int))) :=
    eval_bitAt hbit hbe (tv id.b) k hk64 (by simp only [Exec.evalExpr, le2]; rw [temps_gss]) rfl
  rw [Exec.evalExpr, show Exec.evalExpr ge e le2 m sw = some (.Vlong x) by
    simp only [Exec.evalExpr, le2]; rw [temps_gso _ _ (by decide), ho1 _ (Ne.symm ht2)]; exact hsw, hb]
  simp only [typeof, cop]
  refine hQ k _ hk (temps_gss _ _ _) (by rw [temps_gso _ _ (by decide), temps_gss])
    fun y h1 h2 h3 => ?_
  rw [temps_gso _ _ h3, temps_gso _ _ h2, ho1 y h1]

theorem bv64_clearBit (x : Lib.Integers.int64) (k : Nat) :
    bv64 (clearBit x k) = bv64 x ^^^ Spec.bitAt k := by
  simp only [clearBit, bv64_xor, bv64_repr, intOfZ_zOfInt, Spec.bitAt, BitVec.ofInt_natCast]

theorem getMsbD_clearBit (x : Lib.Integers.int64) {k j : Nat} (hk : k < 64) (hj : j < 64)
    (hx : (bv64 x).getMsbD k = true) :
    (bv64 (clearBit x k)).getMsbD j = ((bv64 x).getMsbD j && decide (j ≠ k)) := by
  rw [bv64_clearBit, BitVec.getMsbD_xor, getMsbD_bitAt hk hj]
  by_cases h : j = k
  · subst h; simp [hx]
  · simp [h]

/-- Clearing the leading bit makes the word smaller. -/
theorem clearBit_lt (x : Lib.Integers.int64) {k : Nat} (hk : LeadBit (bv64 x) k) :
    (bv64 (clearBit x k)).toNat < (bv64 x).toNat := by
  have hk64 := hk.1
  have hand : bv64 (clearBit x k) = bv64 x &&& ~~~ Spec.bitAt k := by
    apply BitVec.eq_of_getMsbD_eq
    intro j hj
    rw [getMsbD_clearBit x hk64 hj hk.2.1, BitVec.getMsbD_and, BitVec.getMsbD_not, getMsbD_bitAt hk64 hj]
    by_cases h : j = k <;> simp [h, hj]
  have hle : (bv64 (clearBit x k)).toNat ≤ (bv64 x).toNat := by
    rw [hand, BitVec.toNat_and]; exact Nat.and_le_left
  have hne : bv64 (clearBit x k) ≠ bv64 x := fun h => by
    have := congrArg (fun y => y.getMsbD k) h
    simp only [getMsbD_clearBit x hk64 hk64 hk.2.1, hk.2.1] at this
    simp at this
  have hne' : (bv64 (clearBit x k)).toNat ≠ (bv64 x).toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  omega

end NautyVerified.Proofs.Permset
