import NautyVerified.Exec.Cop

/-!
# C operators the sorts use beyond `Exec.Cop`

Pointer comparisons `<=` and `>=`, the pointer difference `p - q` (a
`long`), its cast to `int`, and signed `int` division, each by `rfl` as in
`Exec.Cop`.
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
variable (b1 b2 : block) (o1 o2 : ptrofs) (t1 t2 : type)

@[simp, cop] theorem le_pp : sem_binary_operation ce .Ole (.Vptr b1 o1) (Tpointer t1 a)
    (.Vptr b2 o2) (Tpointer t2 b) m =
      (Val.cmplu_bool (Mem.valid_pointer m) .Cle (.Vptr b1 o1) (.Vptr b2 o2)).map Val.of_bool := rfl

@[simp, cop] theorem ge_pp : sem_binary_operation ce .Oge (.Vptr b1 o1) (Tpointer t1 a)
    (.Vptr b2 o2) (Tpointer t2 b) m =
      (Val.cmplu_bool (Mem.valid_pointer m) .Cge (.Vptr b1 o1) (.Vptr b2 o2)).map Val.of_bool := rfl

/-- `p - q` for two `int *` into one block. -/
@[simp, cop] theorem sub_pp (c : attr) :
    sem_binary_operation ce .Osub (.Vptr b1 o1) (Tpointer (Tint .I32 .Signed c) a)
      (.Vptr b1 o2) (Tpointer (Tint .I32 .Signed c) b) m =
      some (.Vlong (Ptrofs.to_int64 (Ptrofs.divs (Ptrofs.sub o1 o2) (Ptrofs.repr (zOfInt 4))))) := by
  show (if decide (b1 = b1) = true then _ else _) = _
  simp only [decide_true, ite_true]
  rfl

@[simp, cop] theorem cast_sli (y : int64) : sem_cast (.Vlong y) (Tlong .Signed a) (Tint .I32 .Signed b) m =
    some (.Vint (Lib.Integers.Int.repr (Int64.unsigned y))) := rfl

@[simp, cop] theorem div_ii (x y : Lib.Integers.int) :
    sem_binary_operation ce .Odiv (.Vint x) (Tint .I32 .Signed a) (.Vint y) (Tint .I32 .Signed b) m =
      if Lib.Integers.Int.eq y Lib.Integers.Int.zero ||
          (Lib.Integers.Int.eq x (Lib.Integers.Int.repr Lib.Integers.Int.min_signed) &&
            Lib.Integers.Int.eq y Lib.Integers.Int.mone) then none
      else some (.Vint (Lib.Integers.Int.divs x y)) := rfl

end NautyVerified.Exec
