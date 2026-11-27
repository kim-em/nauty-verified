import CompCert4Lean.Cfrontend.Cop
import NautyVerified.Exec.CopAttr

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

@[simp, cop] theorem add_ii : sem_binary_operation ce .Oadd (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (.Vint (Lib.Integers.Int.add x y)) := rfl
@[simp, cop] theorem sub_ii : sem_binary_operation ce .Osub (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (.Vint (Lib.Integers.Int.sub x y)) := rfl
@[simp, cop] theorem mul_ii : sem_binary_operation ce .Omul (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (.Vint (Lib.Integers.Int.mul x y)) := rfl
@[simp, cop] theorem and_ii : sem_binary_operation ce .Oand (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (.Vint (Lib.Integers.Int.and x y)) := rfl
@[simp, cop] theorem eq_ii : sem_binary_operation ce .Oeq (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (Lib.Integers.Int.eq x y)) := rfl
@[simp, cop] theorem ne_ii : sem_binary_operation ce .One (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (!Lib.Integers.Int.eq x y)) := rfl
@[simp, cop] theorem lt_ii : sem_binary_operation ce .Olt (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (Lib.Integers.Int.lt x y)) := rfl
@[simp, cop] theorem gt_ii : sem_binary_operation ce .Ogt (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (Lib.Integers.Int.lt y x)) := rfl
@[simp, cop] theorem le_ii : sem_binary_operation ce .Ole (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (!Lib.Integers.Int.lt y x)) := rfl
@[simp, cop] theorem ge_ii : sem_binary_operation ce .Oge (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (!Lib.Integers.Int.lt x y)) := rfl
@[simp, cop] theorem shl_ii : sem_binary_operation ce .Oshl (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m =
      if Lib.Integers.Int.ltu y Lib.Integers.Int.iwordsize then some (.Vint (Lib.Integers.Int.shl x y)) else none := rfl
@[simp, cop] theorem shr_ii : sem_binary_operation ce .Oshr (.Vint x) (Tint .I32 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m =
      if Lib.Integers.Int.ltu y Lib.Integers.Int.iwordsize then some (.Vint (Lib.Integers.Int.shr x y)) else none := rfl

end IntInt

/-! ## `unsigned long` -/

section ULong
variable (x y : Lib.Integers.int64) (n : Lib.Integers.int)

@[simp, cop] theorem add_ll : sem_binary_operation ce .Oadd (.Vlong x) (Tlong .Unsigned a)
    (.Vlong y) (Tlong .Unsigned b) m = some (.Vlong (Lib.Integers.Int64.add x y)) := rfl
@[simp, cop] theorem and_ll : sem_binary_operation ce .Oand (.Vlong x) (Tlong .Unsigned a)
    (.Vlong y) (Tlong .Unsigned b) m = some (.Vlong (Lib.Integers.Int64.and x y)) := rfl
@[simp, cop] theorem or_ll : sem_binary_operation ce .Oor (.Vlong x) (Tlong .Unsigned a)
    (.Vlong y) (Tlong .Unsigned b) m = some (.Vlong (Lib.Integers.Int64.or x y)) := rfl
@[simp, cop] theorem xor_ll : sem_binary_operation ce .Oxor (.Vlong x) (Tlong .Unsigned a)
    (.Vlong y) (Tlong .Unsigned b) m = some (.Vlong (Lib.Integers.Int64.xor x y)) := rfl
@[simp, cop] theorem shr_li : sem_binary_operation ce .Oshr (.Vlong x) (Tlong .Unsigned a)
    (.Vint n) (Tint .I32 .Signed b) m =
      if Lib.Integers.Int.ltu n Lib.Integers.Int64.iwordsize' then some (.Vlong (Lib.Integers.Int64.shru x (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned n))))
      else none := rfl
@[simp, cop] theorem shl_li : sem_binary_operation ce .Oshl (.Vlong x) (Tlong .Unsigned a)
    (.Vint n) (Tint .I32 .Signed b) m =
      if Lib.Integers.Int.ltu n Lib.Integers.Int64.iwordsize' then some (.Vlong (Lib.Integers.Int64.shl x (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned n))))
      else none := rfl
@[simp, cop] theorem and_li : sem_binary_operation ce .Oand (.Vlong x) (Tlong .Unsigned a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (.Vlong (Lib.Integers.Int64.and x (cast_int_long .Signed n))) := rfl
@[simp, cop] theorem eq_li : sem_binary_operation ce .Oeq (.Vlong x) (Tlong .Unsigned a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (Val.of_bool (Lib.Integers.Int64.eq x (cast_int_long .Signed n))) := rfl
@[simp, cop] theorem ne_li : sem_binary_operation ce .One (.Vlong x) (Tlong .Unsigned a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (Val.of_bool (!Lib.Integers.Int64.eq x (cast_int_long .Signed n))) := rfl

@[simp, cop] theorem bool_ulong : bool_val (.Vlong x) (Tlong .Unsigned a) m =
    some (!Lib.Integers.Int64.eq x Lib.Integers.Int64.zero) := rfl
@[simp, cop] theorem bool_int : bool_val (.Vint n) (Tint .I32 .Signed a) m =
    some (!Lib.Integers.Int.eq n Lib.Integers.Int.zero) := rfl

@[simp, cop] theorem bool_of_bool (c : Bool) : bool_val (Val.of_bool c) (Tint .I32 .Signed a) m =
    some c := by cases c <;> rfl

end ULong

/-! ## Pointer arithmetic -/

section Ptr
variable (blk : block) (ofs : ptrofs) (t : type) (n : Lib.Integers.int) (y : Lib.Integers.int64)

@[simp, cop] theorem add_pi : sem_binary_operation ce .Oadd (.Vptr blk ofs) (Tpointer t a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (.Vptr blk (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr (sizeof ce t)) (Ptrofs.of_ints n)))) :=
  rfl
@[simp, cop] theorem add_pul : sem_binary_operation ce .Oadd (.Vptr blk ofs) (Tpointer t a)
    (.Vlong y) (Tlong .Unsigned b) m =
      some (.Vptr blk (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr (sizeof ce t)) (Ptrofs.of_int64 y)))) :=
  rfl
@[simp, cop] theorem add_ai (len : Z) : sem_binary_operation ce .Oadd (.Vptr blk ofs) (Tarray t len a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (.Vptr blk (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr (sizeof ce t)) (Ptrofs.of_ints n)))) :=
  rfl
@[simp, cop] theorem add_aul (len : Z) : sem_binary_operation ce .Oadd (.Vptr blk ofs) (Tarray t len a)
    (.Vlong y) (Tlong .Unsigned b) m =
      some (.Vptr blk (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr (sizeof ce t)) (Ptrofs.of_int64 y)))) :=
  rfl

end Ptr

/-! ## Casts -/

section Cast
variable (x : Lib.Integers.int) (y : Lib.Integers.int64)

@[simp, cop] theorem cast_ii : sem_cast (.Vint x) (Tint .I32 .Signed a) (Tint .I32 .Signed b) m =
    some (.Vint x) := rfl
@[simp, cop] theorem cast_ll : sem_cast (.Vlong y) (Tlong .Unsigned a) (Tlong .Unsigned b) m =
    some (.Vlong y) := rfl
@[simp, cop] theorem cast_il : sem_cast (.Vint x) (Tint .I32 .Signed a) (Tlong .Unsigned b) m =
    some (.Vlong (cast_int_long .Signed x)) := rfl
@[simp, cop] theorem cast_li : sem_cast (.Vlong y) (Tlong .Unsigned a) (Tint .I32 .Signed b) m =
    some (.Vint (Lib.Integers.Int.repr (Lib.Integers.Int64.unsigned y))) := rfl

end Cast

section PtrCmp
variable (b1 b2 : block) (o1 o2 : ptrofs) (t1 t2 : type) (n : Lib.Integers.int)

@[simp, cop] theorem sub_pi : sem_binary_operation ce .Osub (.Vptr b1 o1) (Tpointer t1 a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (.Vptr b1 (Ptrofs.sub o1 (Ptrofs.mul (Ptrofs.repr (sizeof ce t1)) (Ptrofs.of_ints n)))) :=
  rfl

@[simp, cop] theorem gt_pp : sem_binary_operation ce .Ogt (.Vptr b1 o1) (Tpointer t1 a)
    (.Vptr b2 o2) (Tpointer t2 b) m =
      (CompCert4Lean.Common.Values.Val.cmplu_bool (Mem.valid_pointer m) .Cgt
        (.Vptr b1 o1) (.Vptr b2 o2)).map Val.of_bool := rfl

@[simp, cop] theorem lt_pp : sem_binary_operation ce .Olt (.Vptr b1 o1) (Tpointer t1 a)
    (.Vptr b2 o2) (Tpointer t2 b) m =
      (CompCert4Lean.Common.Values.Val.cmplu_bool (Mem.valid_pointer m) .Clt
        (.Vptr b1 o1) (.Vptr b2 o2)).map Val.of_bool := rfl

@[simp, cop] theorem cast_pp (t : type) : sem_cast (.Vptr b1 o1) (Tpointer t1 a) (Tpointer t b) m =
    some (.Vptr b1 o1) := rfl

end PtrCmp

@[simp, cop] theorem neg_i (x : Lib.Integers.int) :
    sem_unary_operation .Oneg (.Vint x) (Tint .I32 .Signed a) m = some (.Vint (Lib.Integers.Int.neg x)) :=
  rfl

@[simp, cop] theorem notint_l (x : Lib.Integers.int64) :
    sem_unary_operation .Onotint (.Vlong x) (Tlong .Unsigned a) m =
      some (.Vlong (Lib.Integers.Int64.not x)) :=
  rfl

section LongMixed
variable (x y : Lib.Integers.int64) (n : Lib.Integers.int)

@[simp, cop] theorem lt_ll : sem_binary_operation ce .Olt (.Vlong x) (Tlong .Unsigned a)
    (.Vlong y) (Tlong .Unsigned b) m = some (Val.of_bool (Lib.Integers.Int64.ltu x y)) := rfl
@[simp, cop] theorem add_li : sem_binary_operation ce .Oadd (.Vlong x) (Tlong .Unsigned a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (.Vlong (Lib.Integers.Int64.add x (Lib.Integers.Int64.repr (Lib.Integers.Int.signed n)))) :=
  rfl
@[simp, cop] theorem cast_i_uc : sem_cast (.Vint n) (Tint .I32 .Signed a) (Tint .I8 .Unsigned b) m =
    some (.Vint (Lib.Integers.Int.zero_ext (zOfInt 8) n)) := rfl
end LongMixed

@[simp, cop] theorem bool_ptr (blk : block) (ofs : ptrofs) (t : type) :
    bool_val (.Vptr blk ofs) (Tpointer t a) m =
      if Mem.weak_valid_pointer m blk (Ptrofs.unsigned ofs) then some true else none := rfl

end NautyVerified.Exec
