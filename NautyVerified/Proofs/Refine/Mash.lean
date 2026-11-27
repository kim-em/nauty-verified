import NautyVerified.Proofs.Refine.State

/-!
# `MASH` on `long`

nauty's `MASH(l, i)` is `((l ^ 065435) + i) & 077777` on `long`, with `i` an
`int`. `wp_mash`: for `0 ≤ l < 2^62` and `0 ≤ i < 2^31` the statement
`longcode = MASH(longcode, a)` leaves `lr (Hex.GraphIso.Nauty.mash l i)`, and
`mash_lt` bounds the result by `2^15`.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Source

section Cop
variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
variable (ce : composite_env) (m : mem) (a b : attr) (x : Lib.Integers.int64) (n : Lib.Integers.int)

/-! The operators on a signed `long` and an `int`. -/

@[simp, cop] theorem xor_sli : sem_binary_operation ce .Oxor (.Vlong x) (Tlong .Signed a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (.Vlong (Lib.Integers.Int64.xor x (Lib.Integers.Int64.repr (Lib.Integers.Int.signed n)))) := rfl
@[simp, cop] theorem add_sli : sem_binary_operation ce .Oadd (.Vlong x) (Tlong .Signed a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (.Vlong (Lib.Integers.Int64.add x (Lib.Integers.Int64.repr (Lib.Integers.Int.signed n)))) := rfl
@[simp, cop] theorem and_sli : sem_binary_operation ce .Oand (.Vlong x) (Tlong .Signed a)
    (.Vint n) (Tint .I32 .Signed b) m =
      some (.Vlong (Lib.Integers.Int64.and x (Lib.Integers.Int64.repr (Lib.Integers.Int.signed n)))) := rfl

end Cop

theorem mash_lt (l i : Nat) : Hex.GraphIso.Nauty.mash l i < 32768 := by
  unfold Hex.GraphIso.Nauty.mash
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- `Int.signed (ir i) = i` for `0 ≤ i < 2^31`. -/
theorem signed_ir {i : Nat} (hi : i < 2147483648) :
    intOfZ (Lib.Integers.Int.signed (ir (i : Int))) = i := by
  rw [intOfZ_Int_signed, toInt_ir ⟨by omega, by omega⟩]

/-- The machine `MASH` is HexGraphIso's `mash`. -/
theorem mash_eq {l i : Nat} (hl : l < 2 ^ 62) (hi : i < 2147483648) :
    Lib.Integers.Int64.and (Lib.Integers.Int64.add (Lib.Integers.Int64.xor (lr l) (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir 27421))))
      (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir (i : Int)))))
      (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir 32767))) =
      lr (Hex.GraphIso.Nauty.mash l i : Nat) := by
  apply bv64_inj.1
  have h1 : intOfZ (Lib.Integers.Int.signed (ir 27421)) = ((27421 : Nat) : Int) := signed_ir (by decide)
  have h2 : intOfZ (Lib.Integers.Int.signed (ir 32767)) = ((32767 : Nat) : Int) := signed_ir (by decide)
  simp only [bv64_and, bv64_add, bv64_xor, bv64_repr, intOfZ_zOfInt, h1, h2, signed_ir hi,
    BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  have hx : l ^^^ 27421 < 2 ^ 62 := Nat.xor_lt_two_pow hl (by decide)
  simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_ofNat,
    Hex.GraphIso.Nauty.mash]
  rw [Nat.mod_eq_of_lt (show l < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 27421 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (32767 : Nat) < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show (l ^^^ 27421) + i < 2 ^ 64 by omega)]
  have hb : ((l ^^^ 27421) + i) &&& 32767 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [Nat.mod_eq_of_lt hb]

variable {xi : ExternalCalls}

/-- `longcode = MASH(longcode, a)`. -/
theorem wp_mash {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : expr}
    {l i : Nat} (hl : PTree.get dense.id.longcode le = some (.Vlong (lr l))) (hl2 : l < 2 ^ 62)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir i))) (hty : typeof a = tint)
    (hi : i < 2147483648)
    (hQ : Q.normal E0 e (PTree.set dense.id.longcode
      (.Vlong (lr (Hex.GraphIso.Nauty.mash l i : Nat))) le) m) :
    Wp xi ge f (mash a) Q e le m := by
  apply wp_set_eval
  simp only [Exec.evalExpr, ha, hty]
  simp only [hl, typeof, cop]
  rw [mash_eq hl2 hi]
  exact hQ

end NautyVerified.Proofs.Refine
