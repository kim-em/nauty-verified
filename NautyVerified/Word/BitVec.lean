import CompCert4Lean.Lib.Integers

/-!
# Machine words as bit vectors

CompCert4Lean's machine words (`WordCore.Word bits`: `Int.int`, `Int64.int`,
`Ptrofs.int`) carry a Rocq `Z` with a range proof, and their operations are
defined through `Z` and `Nat`. `toBV` views a word as a `BitVec bits`; the
lemmas here rewrite each operation into the corresponding `BitVec` operation,
so that `bv_decide`, `omega` and `BitVec` lemmas apply to C arithmetic.

`intOfZ` similarly views a Rocq `Z` as an `Int`; the `Z` lemmas rewrite the
arithmetic and comparisons of `Z` into those of `Int`.
-/

namespace NautyVerified.Word

open CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

/-! ## Rocq `Z` as `Int` -/

section Z
open ZArith.BinInt

@[simp] theorem intOfZ_add (a b : Z) : intOfZ (Z.add a b) = intOfZ a + intOfZ b := by
  simp [Z.add, intOfZ_zOfInt]
@[simp] theorem intOfZ_sub (a b : Z) : intOfZ (Z.sub a b) = intOfZ a - intOfZ b := by
  simp [Z.sub, intOfZ_zOfInt]
@[simp] theorem intOfZ_mul (a b : Z) : intOfZ (Z.mul a b) = intOfZ a * intOfZ b := by
  simp [Z.mul, intOfZ_zOfInt]
@[simp] theorem intOfZ_opp (a : Z) : intOfZ (Z.opp a) = -intOfZ a := by
  simp [Z.opp, intOfZ_zOfInt]
@[simp] theorem intOfZ_of_nat (n : Nat) : intOfZ (Z.of_nat n) = (n : Int) := by
  simp [Z.of_nat, intOfZ_zOfInt]
@[simp] theorem intOfZ_Z0 : intOfZ .Z0 = 0 := rfl
@[simp] theorem Z_le_iff (a b : Z) : Z.le a b ↔ intOfZ a ≤ intOfZ b := Iff.rfl
@[simp] theorem Z_lt_iff (a b : Z) : Z.lt a b ↔ intOfZ a < intOfZ b := Iff.rfl
theorem Z_eq_iff (a b : Z) : a = b ↔ intOfZ a = intOfZ b :=
  ⟨congrArg _, fun h => intOfZ_injective h⟩

end Z

/-! ## Words as bit vectors -/

section Word
open WordCore

variable {bits : Nat}

/-- A word as a bit vector. -/
def toBV (x : Word bits) : BitVec bits := BitVec.ofNatLT x.val (val_lt_two_pow x)

@[simp] theorem toNat_toBV (x : Word bits) : (toBV x).toNat = x.val := rfl

theorem toBV_inj {x y : Word bits} : toBV x = toBV y ↔ x = y := by
  constructor
  · intro h
    exact ext_of_val_eq (by simpa using congrArg BitVec.toNat h)
  · rintro rfl; rfl

theorem intOfZ_intval (x : Word bits) : intOfZ x.intval = (x.val : Int) := by
  rw [intval_eq_of_nat_val, intOfZ_of_nat]

@[simp] theorem intOfZ_unsigned (x : Word bits) : intOfZ (unsigned x) = ((toBV x).toNat : Int) :=
  intOfZ_intval x

theorem val_repr (z : Z) : (repr bits z).val = Int.toNat (intOfZ z % ((2 ^ bits : Nat) : Int)) := by
  rw [← zOfInt_intOfZ z, val_repr_of_int, intOfZ_zOfInt]

@[simp] theorem toBV_repr (z : Z) : toBV (repr bits z) = BitVec.ofInt bits (intOfZ z) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_toBV, val_repr, BitVec.toNat_ofInt]

@[simp] theorem toBV_add (x y : Word bits) : toBV (add x y) = toBV x + toBV y := by
  apply BitVec.eq_of_toNat_eq
  simp [val_add, BitVec.toNat_add]

@[simp] theorem toBV_eq (x y : Word bits) : eq x y = decide (toBV x = toBV y) := by
  unfold eq
  have : x.intval = y.intval ↔ toBV x = toBV y := by
    rw [toBV_inj]
    exact ⟨fun h => ext h, fun h => h ▸ rfl⟩
  simp only [this]

end Word

end NautyVerified.Word
