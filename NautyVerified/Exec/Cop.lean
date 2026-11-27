import CompCert4Lean.Cfrontend.Cop

/-!
# CompCert's C operators on the types nauty uses

`sem_binary_operation`, `sem_unary_operation`, `sem_cast` and `bool_val`
dispatch on the static types of their operands. For each combination of
operator and types that occurs in the linked dense program, a lemma here
states the result in terms of the machine-word operations, generically in the
values (and in the types' attributes). They are all proved by `rfl`, and they
are what `simp` uses to evaluate expressions during symbolic execution.
-/

namespace NautyVerified.Exec

open CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Ctypes CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Flocq.IEEE754.Binary (BinaryNormalizeCertificate)

variable [binary64_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable (ce : composite_env) (m : mem) (a b : attr)

/-! ## `int` with `int` -/

section IntInt
variable (x y : Lib.Integers.int)

@[simp] theorem add_ii : sem_binary_operation ce .Oadd (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (.Vint (Lib.Integers.Int.add x y)) := rfl
@[simp] theorem sub_ii : sem_binary_operation ce .Osub (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (.Vint (Lib.Integers.Int.sub x y)) := rfl
@[simp] theorem mul_ii : sem_binary_operation ce .Omul (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (.Vint (Lib.Integers.Int.mul x y)) := rfl
@[simp] theorem and_ii : sem_binary_operation ce .Oand (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (.Vint (Lib.Integers.Int.and x y)) := rfl
@[simp] theorem eq_ii : sem_binary_operation ce .Oeq (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (Lib.Integers.Int.eq x y)) := rfl
@[simp] theorem ne_ii : sem_binary_operation ce .One (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (!Lib.Integers.Int.eq x y)) := rfl
@[simp] theorem lt_ii : sem_binary_operation ce .Olt (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (Lib.Integers.Int.lt x y)) := rfl
@[simp] theorem gt_ii : sem_binary_operation ce .Ogt (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (Lib.Integers.Int.lt y x)) := rfl
@[simp] theorem le_ii : sem_binary_operation ce .Ole (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (!Lib.Integers.Int.lt y x)) := rfl
@[simp] theorem ge_ii : sem_binary_operation ce .Oge (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (!Lib.Integers.Int.lt x y)) := rfl
@[simp] theorem shl_ii : sem_binary_operation ce .Oshl (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m =
      if Lib.Integers.Int.ltu y Lib.Integers.Int.iwordsize then some (.Vint (Lib.Integers.Int.shl x y)) else none := rfl
@[simp] theorem shr_ii : sem_binary_operation ce .Oshr (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m =
      if Lib.Integers.Int.ltu y Lib.Integers.Int.iwordsize then some (.Vint (Lib.Integers.Int.shr x y)) else none := rfl

end IntInt

/-! ## `unsigned long` -/

section ULong
variable (x y : Lib.Integers.int64) (n : Lib.Integers.int)

@[simp] theorem add_ll : sem_binary_operation ce .Oadd (.Vlong x) (Tlong .Unsigned a)
    (.Vlong y) (Tlong .Unsigned b) m = some (.Vlong (Lib.Integers.Int64.add x y)) := rfl
@[simp] theorem and_ll : sem_binary_operation ce .Oand (.Vlong x) (Tlong .Unsigned a)
    (.Vlong y) (Tlong .Unsigned b) m = some (.Vlong (Lib.Integers.Int64.and x y)) := rfl
@[simp] theorem or_ll : sem_binary_operation ce .Oor (.Vlong x) (Tlong .Unsigned a)
    (.Vlong y) (Tlong .Unsigned b) m = some (.Vlong (Lib.Integers.Int64.or x y)) := rfl
@[simp] theorem xor_ll : sem_binary_operation ce .Oxor (.Vlong x) (Tlong .Unsigned a)
    (.Vlong y) (Tlong .Unsigned b) m = some (.Vlong (Lib.Integers.Int64.xor x y)) := rfl
@[simp] theorem shr_li : sem_binary_operation ce .Oshr (.Vlong x) (Tlong .Unsigned a)
    (.Vint n) (Tint .I32 .Signed b) m =
      if Lib.Integers.Int.ltu n Lib.Integers.Int64.iwordsize' then some (.Vlong (Lib.Integers.Int64.shru x (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned n))))
      else none := rfl
@[simp] theorem shl_li : sem_binary_operation ce .Oshl (.Vlong x) (Tlong .Unsigned a)
    (.Vint n) (Tint .I32 .Signed b) m =
      if Lib.Integers.Int.ltu n Lib.Integers.Int64.iwordsize' then some (.Vlong (Lib.Integers.Int64.shl x (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned n))))
      else none := rfl
@[simp] theorem and_li : sem_binary_operation ce .Oand (.Vlong x) (Tlong .Unsigned a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (.Vlong (Lib.Integers.Int64.and x (cast_int_long .Signed n))) := rfl
@[simp] theorem eq_li : sem_binary_operation ce .Oeq (.Vlong x) (Tlong .Unsigned a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (Val.of_bool (Lib.Integers.Int64.eq x (cast_int_long .Signed n))) := rfl
@[simp] theorem ne_li : sem_binary_operation ce .One (.Vlong x) (Tlong .Unsigned a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (Val.of_bool (!Lib.Integers.Int64.eq x (cast_int_long .Signed n))) := rfl

@[simp] theorem bool_ulong : bool_val (.Vlong x) (Tlong .Unsigned a) m =
    some (!Lib.Integers.Int64.eq x Lib.Integers.Int64.zero) := rfl
@[simp] theorem bool_int : bool_val (.Vint n) (Tint .I32 .Signed a) m =
    some (!Lib.Integers.Int.eq n Lib.Integers.Int.zero) := rfl

@[simp] theorem bool_of_bool (c : Bool) : bool_val (Val.of_bool c) (Tint .I32 .Signed a) m =
    some c := by cases c <;> rfl

end ULong

/-! ## Pointer arithmetic -/

section Ptr
variable (blk : block) (ofs : ptrofs) (t : type) (n : Lib.Integers.int) (y : Lib.Integers.int64)

@[simp] theorem add_pi : sem_binary_operation ce .Oadd (.Vptr blk ofs) (Tpointer t a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (.Vptr blk (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr (sizeof ce t)) (Ptrofs.of_ints n)))) :=
  rfl
@[simp] theorem add_pul : sem_binary_operation ce .Oadd (.Vptr blk ofs) (Tpointer t a)
    (.Vlong y) (Tlong .Unsigned b) m =
      some (.Vptr blk (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr (sizeof ce t)) (Ptrofs.of_int64 y)))) :=
  rfl
@[simp] theorem add_ai (len : Z) : sem_binary_operation ce .Oadd (.Vptr blk ofs) (Tarray t len a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (.Vptr blk (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr (sizeof ce t)) (Ptrofs.of_ints n)))) :=
  rfl
@[simp] theorem add_aul (len : Z) : sem_binary_operation ce .Oadd (.Vptr blk ofs) (Tarray t len a)
    (.Vlong y) (Tlong .Unsigned b) m =
      some (.Vptr blk (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr (sizeof ce t)) (Ptrofs.of_int64 y)))) :=
  rfl

end Ptr

/-! ## Casts -/

section Cast
variable (x : Lib.Integers.int) (y : Lib.Integers.int64)

@[simp] theorem cast_ii : sem_cast (.Vint x) (Tint .I32 .Signed a) (Tint .I32 .Signed b) m =
    some (.Vint x) := rfl
@[simp] theorem cast_ll : sem_cast (.Vlong y) (Tlong .Unsigned a) (Tlong .Unsigned b) m =
    some (.Vlong y) := rfl
@[simp] theorem cast_il : sem_cast (.Vint x) (Tint .I32 .Signed a) (Tlong .Unsigned b) m =
    some (.Vlong (cast_int_long .Signed x)) := rfl
@[simp] theorem cast_li : sem_cast (.Vlong y) (Tlong .Unsigned a) (Tint .I32 .Signed b) m =
    some (.Vint (Lib.Integers.Int.repr (Lib.Integers.Int64.unsigned y))) := rfl

end Cast

end NautyVerified.Exec
