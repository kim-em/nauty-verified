import NautyVerified.Word.BitVec

/-!
# `int`, `long` and pointer offsets as fixed-width bit vectors

`bv32`, `bv64` and `bvp` view CompCert4Lean's `Int.int`, `Int64.int` and
`Ptrofs.int` as `BitVec 32`, `BitVec 64` and `BitVec 64` (x86-64 pointers), so
that the widths are literals and `bv_decide` and `omega` apply. Each operation
of the three namespaces gets a rewrite lemma to the `BitVec` operation.
-/

namespace NautyVerified.Word

open CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

/-- An `int` as a bit vector. -/
def bv32 (x : Lib.Integers.int) : BitVec 32 := toBV x
/-- A `long` as a bit vector. -/
def bv64 (x : Lib.Integers.int64) : BitVec 64 := toBV x
/-- A pointer offset as a bit vector (x86-64). -/
def bvp (x : Lib.Integers.ptrofs) : BitVec 64 := toBV x

theorem bv32_inj {x y : Lib.Integers.int} : bv32 x = bv32 y ↔ x = y := toBV_inj
theorem bv64_inj {x y : Lib.Integers.int64} : bv64 x = bv64 y ↔ x = y := toBV_inj
theorem bvp_inj {x y : Lib.Integers.ptrofs} : bvp x = bvp y ↔ x = y := toBV_inj

/-! ## `Int` -/

@[simp] theorem bv32_repr (z : Z) : bv32 (Lib.Integers.Int.repr z) = BitVec.ofInt 32 (intOfZ z) := toBV_repr z
@[simp] theorem bv32_zero : bv32 Lib.Integers.Int.zero = 0 := by
  rw [show Lib.Integers.Int.zero = Lib.Integers.Int.repr .Z0 from rfl, bv32_repr]; rfl
@[simp] theorem intOfZ_Int_unsigned (x : Lib.Integers.int) : intOfZ (Lib.Integers.Int.unsigned x) = ((bv32 x).toNat : Int) :=
  intOfZ_unsigned x
@[simp] theorem bv32_add (x y : Lib.Integers.int) : bv32 (Lib.Integers.Int.add x y) = bv32 x + bv32 y := toBV_add x y
@[simp] theorem bv32_sub (x y : Lib.Integers.int) : bv32 (Lib.Integers.Int.sub x y) = bv32 x - bv32 y := toBV_sub x y
@[simp] theorem bv32_mul (x y : Lib.Integers.int) : bv32 (Lib.Integers.Int.mul x y) = bv32 x * bv32 y := toBV_mul x y
@[simp] theorem bv32_and (x y : Lib.Integers.int) : bv32 (Lib.Integers.Int.and x y) = bv32 x &&& bv32 y := toBV_and x y
@[simp] theorem bv32_or (x y : Lib.Integers.int) : bv32 (Lib.Integers.Int.or x y) = bv32 x ||| bv32 y := toBV_or x y
@[simp] theorem bv32_xor (x y : Lib.Integers.int) : bv32 (Lib.Integers.Int.xor x y) = bv32 x ^^^ bv32 y := toBV_xor x y
@[simp] theorem bv32_neg (x : Lib.Integers.int) : bv32 (Lib.Integers.Int.neg x) = -bv32 x := toBV_neg x
@[simp] theorem bv32_eq (x y : Lib.Integers.int) : Lib.Integers.Int.eq x y = decide (bv32 x = bv32 y) := toBV_eq x y
@[simp] theorem bv32_ltu (x y : Lib.Integers.int) : Lib.Integers.Int.ltu x y = decide ((bv32 x).toNat < (bv32 y).toNat) :=
  toBV_ltu x y
@[simp] theorem bv32_shl (x y : Lib.Integers.int) : bv32 (Lib.Integers.Int.shl x y) = bv32 x <<< (bv32 y).toNat := toBV_shl x y
@[simp] theorem bv32_shru (x y : Lib.Integers.int) : bv32 (Lib.Integers.Int.shru x y) = bv32 x >>> (bv32 y).toNat :=
  toBV_shru x y

/-! ## `Int64` -/

@[simp] theorem bv64_repr (z : Z) : bv64 (Lib.Integers.Int64.repr z) = BitVec.ofInt 64 (intOfZ z) := toBV_repr z
@[simp] theorem bv64_zero : bv64 Lib.Integers.Int64.zero = 0 := by
  rw [show Lib.Integers.Int64.zero = Lib.Integers.Int64.repr .Z0 from rfl, bv64_repr]; rfl
@[simp] theorem intOfZ_Int64_unsigned (x : Lib.Integers.int64) : intOfZ (Lib.Integers.Int64.unsigned x) = ((bv64 x).toNat : Int) :=
  intOfZ_unsigned x
@[simp] theorem bv64_add (x y : Lib.Integers.int64) : bv64 (Lib.Integers.Int64.add x y) = bv64 x + bv64 y := toBV_add x y
@[simp] theorem bv64_sub (x y : Lib.Integers.int64) : bv64 (Lib.Integers.Int64.sub x y) = bv64 x - bv64 y := toBV_sub x y
@[simp] theorem bv64_mul (x y : Lib.Integers.int64) : bv64 (Lib.Integers.Int64.mul x y) = bv64 x * bv64 y := toBV_mul x y
@[simp] theorem bv64_and (x y : Lib.Integers.int64) : bv64 (Lib.Integers.Int64.and x y) = bv64 x &&& bv64 y := toBV_and x y
@[simp] theorem bv64_or (x y : Lib.Integers.int64) : bv64 (Lib.Integers.Int64.or x y) = bv64 x ||| bv64 y := toBV_or x y
@[simp] theorem bv64_xor (x y : Lib.Integers.int64) : bv64 (Lib.Integers.Int64.xor x y) = bv64 x ^^^ bv64 y := toBV_xor x y
@[simp] theorem bv64_neg (x : Lib.Integers.int64) : bv64 (Lib.Integers.Int64.neg x) = -bv64 x := toBV_neg x
@[simp] theorem bv64_eq (x y : Lib.Integers.int64) : Lib.Integers.Int64.eq x y = decide (bv64 x = bv64 y) := toBV_eq x y
@[simp] theorem bv64_ltu (x y : Lib.Integers.int64) : Lib.Integers.Int64.ltu x y = decide ((bv64 x).toNat < (bv64 y).toNat) :=
  toBV_ltu x y
@[simp] theorem bv64_shl (x y : Lib.Integers.int64) : bv64 (Lib.Integers.Int64.shl x y) = bv64 x <<< (bv64 y).toNat := toBV_shl x y
@[simp] theorem bv64_shru (x y : Lib.Integers.int64) : bv64 (Lib.Integers.Int64.shru x y) = bv64 x >>> (bv64 y).toNat :=
  toBV_shru x y

/-! ## `Ptrofs` -/

@[simp] theorem bvp_repr (z : Z) : bvp (Lib.Integers.Ptrofs.repr z) = BitVec.ofInt 64 (intOfZ z) := toBV_repr z
@[simp] theorem bvp_zero : bvp Lib.Integers.Ptrofs.zero = 0 := by
  rw [show Lib.Integers.Ptrofs.zero = Lib.Integers.Ptrofs.repr .Z0 from rfl, bvp_repr]; rfl
@[simp] theorem intOfZ_Ptrofs_unsigned (x : Lib.Integers.ptrofs) : intOfZ (Lib.Integers.Ptrofs.unsigned x) = ((bvp x).toNat : Int) :=
  intOfZ_unsigned x
@[simp] theorem bvp_add (x y : Lib.Integers.ptrofs) : bvp (Lib.Integers.Ptrofs.add x y) = bvp x + bvp y := toBV_add x y
@[simp] theorem bvp_sub (x y : Lib.Integers.ptrofs) : bvp (Lib.Integers.Ptrofs.sub x y) = bvp x - bvp y := toBV_sub x y
@[simp] theorem bvp_mul (x y : Lib.Integers.ptrofs) : bvp (Lib.Integers.Ptrofs.mul x y) = bvp x * bvp y := toBV_mul x y
@[simp] theorem bvp_and (x y : Lib.Integers.ptrofs) : bvp (Lib.Integers.Ptrofs.and x y) = bvp x &&& bvp y := toBV_and x y
@[simp] theorem bvp_or (x y : Lib.Integers.ptrofs) : bvp (Lib.Integers.Ptrofs.or x y) = bvp x ||| bvp y := toBV_or x y
@[simp] theorem bvp_xor (x y : Lib.Integers.ptrofs) : bvp (Lib.Integers.Ptrofs.xor x y) = bvp x ^^^ bvp y := toBV_xor x y
@[simp] theorem bvp_neg (x : Lib.Integers.ptrofs) : bvp (Lib.Integers.Ptrofs.neg x) = -bvp x := toBV_neg x
@[simp] theorem bvp_eq (x y : Lib.Integers.ptrofs) : Lib.Integers.Ptrofs.eq x y = decide (bvp x = bvp y) := toBV_eq x y
@[simp] theorem bvp_ltu (x y : Lib.Integers.ptrofs) : Lib.Integers.Ptrofs.ltu x y = decide ((bvp x).toNat < (bvp y).toNat) :=
  toBV_ltu x y

@[simp] theorem bvp_of_int64 (y : Lib.Integers.int64) : bvp (Ptrofs.of_int64 y) = bv64 y := by
  rw [show Ptrofs.of_int64 y = Ptrofs.repr (Int64.unsigned y) from rfl, bvp_repr,
    intOfZ_Int64_unsigned]
  exact ofInt_toNat (bv64 y)

end NautyVerified.Word
