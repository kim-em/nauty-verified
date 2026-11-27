import NautyVerified.Logic.Pointer
import NautyVerified.Exec.Cop

/-!
# Pointers into arrays

A pointer to element `k` of an array of `csize chunk`-byte elements at offset
`base` is `Ptrofs.repr (base + csize * k)` (`ptrTo`). The lemmas here compute
C's `p + i`, `p - 1` and `p > q` on such pointers.
-/

namespace NautyVerified.Logic

open CompCert4Lean CompCert4Lean.Common.Memory CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified.Word

/-- The offset of element `k`. -/
abbrev ptrTo (base : Int) (sz : Int) (k : Nat) : Lib.Integers.ptrofs :=
  Ptrofs.repr (zOfInt (base + sz * k))

theorem unsigned_ptrTo {base sz : Int} {k : Nat} (h0 : 0 ≤ base + sz * k)
    (h1 : base + sz * k < 2 ^ 64) :
    intOfZ (Ptrofs.unsigned (ptrTo base sz k)) = base + sz * k := by
  rw [intOfZ_Ptrofs_unsigned, bvp_repr, intOfZ_zOfInt, BitVec.toNat_ofInt]
  have : (((2 ^ 64 : Nat) : Int)) = 2 ^ 64 := by norm_cast
  omega

theorem cmpu_gt (x y : Lib.Integers.ptrofs) :
    Ptrofs.cmpu .Cgt x y = decide ((bvp y).toNat < (bvp x).toNat) := by
  show WordCore.ltu y x = _
  exact toBV_ltu y x

theorem bvp_eq_ofInt (x : Lib.Integers.ptrofs) :
    bvp x = BitVec.ofInt 64 (intOfZ (Ptrofs.unsigned x)) := by
  rw [intOfZ_Ptrofs_unsigned]; exact (ofInt_toNat _).symm

/-- `p + i`, for `p` at `base` and an `int` index `i`. -/
theorem add_ptrTo (ofs : Lib.Integers.ptrofs) (sz : Z) (k : Nat) (hk : (k : Int) < 2147483648) :
    Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_ints (ir k))) =
      ptrTo (intOfZ (Ptrofs.unsigned ofs)) (intOfZ sz) k := by
  apply bvp_inj.1
  rw [bvp_add, bvp_mul, bvp_repr, bvp_of_ints, toInt_ir ⟨by omega, hk⟩, bvp_repr, intOfZ_zOfInt,
    bvp_eq_ofInt ofs, ← BitVec.ofInt_mul, ← BitVec.ofInt_add]

theorem cmpu_lt (x y : Lib.Integers.ptrofs) :
    Ptrofs.cmpu .Clt x y = decide ((bvp x).toNat < (bvp y).toNat) := by
  show WordCore.ltu x y = _
  exact toBV_ltu x y

/-- `p + j` for `p` at element `k`. -/
theorem add_ptrTo_ptrTo (base : Int) (sz : Z) (k j : Nat) (hj : (j : Int) < 2147483648) :
    Ptrofs.add (ptrTo base (intOfZ sz) k) (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_ints (ir j))) =
      ptrTo base (intOfZ sz) (k + j) := by
  apply bvp_inj.1
  rw [bvp_add, bvp_mul, bvp_repr, bvp_of_ints, toInt_ir ⟨by omega, hj⟩, bvp_repr, bvp_repr,
    intOfZ_zOfInt, intOfZ_zOfInt, ← BitVec.ofInt_mul, ← BitVec.ofInt_add]
  congr 1
  push_cast
  rw [Int.mul_add]
  omega

/-- `p - 1` for `p` at element `k + 1`. -/
theorem sub_ptrTo (base : Int) (sz : Z) (k : Nat) :
    Ptrofs.sub (ptrTo base (intOfZ sz) (k + 1)) (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_ints (ir 1))) =
      ptrTo base (intOfZ sz) k := by
  apply bvp_inj.1
  rw [bvp_sub, bvp_mul, bvp_repr, bvp_of_ints, toInt_ir ⟨by decide, by decide⟩, bvp_repr,
    bvp_repr, intOfZ_zOfInt, intOfZ_zOfInt, ← BitVec.ofInt_mul]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add]
  congr 1
  push_cast
  rw [Int.mul_add, Int.mul_one]
  omega

end NautyVerified.Logic
