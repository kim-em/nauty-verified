import NautyVerified.Exec.Cop

/-!
# C operators on the types nausparse.c adds

The combinations of operator and operand types that occur in nausparse.c and
not in the dense program (`short` stamps, `size_t` loop counters compared
with `int` degrees), stated as `Exec/Cop.lean` does, each by `rfl`.
-/

namespace NautyVerified.Proofs.Sparse

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

variable (ce : composite_env) (m : mem) (a b : attr) (x y : Lib.Integers.int) (u : Lib.Integers.int64)

@[simp, cop] theorem add_si : sem_binary_operation ce .Oadd (.Vint x) (Tint .I16 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (.Vint (Lib.Integers.Int.add x y)) := rfl
@[simp, cop] theorem ge_si : sem_binary_operation ce .Oge (.Vint x) (Tint .I16 .Signed a)
    (.Vint y) (Tint .I32 .Signed b) m = some (Val.of_bool (!Lib.Integers.Int.lt x y)) := rfl
@[simp, cop] theorem ne_ss : sem_binary_operation ce .One (.Vint x) (Tint .I16 .Signed a)
    (.Vint y) (Tint .I16 .Signed b) m = some (Val.of_bool (!Lib.Integers.Int.eq x y)) := rfl
@[simp, cop] theorem eq_ss : sem_binary_operation ce .Oeq (.Vint x) (Tint .I16 .Signed a)
    (.Vint y) (Tint .I16 .Signed b) m = some (Val.of_bool (Lib.Integers.Int.eq x y)) := rfl
@[simp, cop] theorem lt_li : sem_binary_operation ce .Olt (.Vlong u) (Tlong .Unsigned a)
    (.Vint y) (Tint .I32 .Signed b) m =
      some (Val.of_bool (Lib.Integers.Int64.ltu u (Lib.Integers.Int64.repr (Lib.Integers.Int.signed y)))) :=
  rfl
@[simp, cop] theorem cast_si : sem_cast (.Vint x) (Tint .I16 .Signed a) (Tint .I32 .Signed b) m =
    some (.Vint x) := rfl
@[simp, cop] theorem ne_ll (v : Lib.Integers.int64) : sem_binary_operation ce .One (.Vlong u) (Tlong .Unsigned a)
    (.Vlong v) (Tlong .Unsigned b) m = some (Val.of_bool (!Lib.Integers.Int64.eq u v)) := rfl
@[simp, cop] theorem ne_pp (b1 b2 : Common.Values.block) (o1 o2 : ptrofs) (t1 t2 : type) :
    sem_binary_operation ce .One (.Vptr b1 o1) (Tpointer t1 a) (.Vptr b2 o2) (Tpointer t2 b) m =
      (Val.cmplu_bool (Mem.valid_pointer m) .Cne (.Vptr b1 o1) (.Vptr b2 o2)).map Val.of_bool := rfl
@[simp, cop] theorem ne_nn (v : Lib.Integers.int64) (t1 t2 : type) :
    sem_binary_operation ce .One (.Vlong u) (Tpointer t1 a) (.Vlong v) (Tpointer t2 b) m =
      some (Val.of_bool (!Lib.Integers.Int64.eq u v)) := rfl
omit binary64_certificate binary32_certificate in
@[simp, cop] theorem bool_lp (t : type) : bool_val (.Vlong u) (Tpointer t a) m =
    some (!Lib.Integers.Int64.eq u Lib.Integers.Int64.zero) := rfl

end NautyVerified.Proofs.Sparse
