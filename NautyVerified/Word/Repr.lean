import NautyVerified.Word.Machine
import CompCert4Lean.Cfrontend.Cop

/-!
# `int` values held as integers

Most `int` temporaries hold small integers. `ir a` is the `int` representing
the integer `a`; the lemmas here compute C's `int` operations on such values
as operations on integers, under the range conditions that make them exact,
so that proofs about loop counters and indices stay in `Int` and `omega`.
-/

namespace NautyVerified.Word

open CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

/-- The `int` representing the integer `a` (modulo `2^32`). -/
abbrev ir (a : _root_.Int) : Lib.Integers.int := Lib.Integers.Int.repr (zOfInt a)

/-- The `long` representing the integer `a` (modulo `2^64`). -/
abbrev lr (a : _root_.Int) : Lib.Integers.int64 := Lib.Integers.Int64.repr (zOfInt a)

/-- `a` is a value of type `int`. -/
abbrev InInt (a : _root_.Int) : Prop := -2147483648 ≤ a ∧ a < 2147483648

theorem bv32_ir (a : _root_.Int) : bv32 (ir a) = BitVec.ofInt 32 a := by
  simp [ir, intOfZ_zOfInt]

theorem toInt_ir {a : _root_.Int} (h : InInt a) : (bv32 (ir a)).toInt = a := by
  rw [bv32_ir, BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le_mul_two (by simp; omega) (by simp; omega)

theorem toNat_ir {a : _root_.Int} (h0 : 0 ≤ a) (h : a < 4294967296) : (bv32 (ir a)).toNat = a.toNat := by
  rw [bv32_ir, BitVec.toNat_ofInt]
  simp only [Nat.reducePow]
  omega

theorem ir_eq_ir {a b : _root_.Int} (ha : InInt a) (hb : InInt b) : ir a = ir b ↔ a = b := by
  constructor
  · intro h
    rw [← toInt_ir ha, ← toInt_ir hb, h]
  · rintro rfl; rfl

@[simp] theorem ir_add (a b : _root_.Int) : Lib.Integers.Int.add (ir a) (ir b) = ir (a + b) :=
  bv32_inj.1 (by simp [intOfZ_zOfInt, BitVec.ofInt_add])

@[simp] theorem ir_sub (a b : _root_.Int) : Lib.Integers.Int.sub (ir a) (ir b) = ir (a - b) := by
  apply bv32_inj.1
  simp only [bv32_sub, bv32_ir, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
    BitVec.sub_eq_add_neg]

@[simp] theorem ir_mul (a b : _root_.Int) : Lib.Integers.Int.mul (ir a) (ir b) = ir (a * b) :=
  bv32_inj.1 (by simp [intOfZ_zOfInt, BitVec.ofInt_mul])

@[simp] theorem ir_neg (a : _root_.Int) : Lib.Integers.Int.neg (ir a) = ir (-a) :=
  bv32_inj.1 (by simp [intOfZ_zOfInt, BitVec.ofInt_neg])

theorem ir_eq {a b : _root_.Int} (ha : InInt a) (hb : InInt b) :
    Lib.Integers.Int.eq (ir a) (ir b) = decide (a = b) := by
  rw [bv32_eq]
  exact decide_eq_decide.2 (bv32_inj.trans (ir_eq_ir ha hb))

theorem ir_lt {a b : _root_.Int} (ha : InInt a) (hb : InInt b) :
    Lib.Integers.Int.lt (ir a) (ir b) = decide (a < b) := by
  rw [bv32_lt, toInt_ir ha, toInt_ir hb]

theorem ir_shr {a : _root_.Int} (s : Nat) (ha : InInt a) (hs : s < 32) :
    Lib.Integers.Int.shr (ir a) (ir s) = ir (a / 2 ^ s) := by
  apply bv32_inj.1
  rw [bv32_shr, toInt_ir ha, toNat_ir (by omega) (by omega), bv32_ir]
  simp

theorem ir_shl6 {a : _root_.Int} (h0 : 0 ≤ a) (ha : a < 4294967296) :
    Lib.Integers.Int.shl (ir a) (ir 6) = ir (a * 64) := by
  apply bv32_inj.1
  rw [bv32_shl, toNat_ir (by omega) (by omega), bv32_ir, bv32_ir]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofInt, Nat.shiftLeft_eq,
    show Int.toNat 6 = 6 from rfl, Nat.reducePow]
  omega

theorem ir_and63 {a : _root_.Int} (h0 : 0 ≤ a) (ha : a < 4294967296) :
    Lib.Integers.Int.and (ir a) (ir 63) = ir (a % 64) := by
  apply bv32_inj.1
  rw [bv32_and, bv32_ir, bv32_ir, bv32_ir]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofInt]
  rw [show ((63 : _root_.Int) % ((2 ^ 32 : Nat) : _root_.Int)).toNat = 2 ^ 6 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem cast_int_long_ir {a : _root_.Int} (h : InInt a) :
    Cfrontend.Cop.cast_int_long .Signed (ir a) = lr a := by
  apply bv64_inj.1
  show bv64 (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir a))) = _
  rw [bv64_repr, intOfZ_Int_signed, toInt_ir h, bv64_repr, intOfZ_zOfInt]

/-- The address `p + i` of element `i` of an array of 8-byte words. -/
theorem ofs_word8 (ofs : Lib.Integers.ptrofs) (sz : Z) (hsz : intOfZ sz = 8)
    {i : _root_.Int} (h : InInt i) :
    Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_ints (ir i))) =
      Ptrofs.add ofs (Ptrofs.repr (zOfInt (8 * i))) := by
  apply bvp_inj.1
  simp only [bvp_add, bvp_mul, bvp_repr, bvp_of_ints, toInt_ir h, hsz, intOfZ_zOfInt,
    BitVec.ofInt_mul]

end NautyVerified.Word
