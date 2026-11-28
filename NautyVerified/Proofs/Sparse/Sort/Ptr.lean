import NautyVerified.Logic.PtrArith
import NautyVerified.Logic.Ints
import NautyVerified.Proofs.Sparse.Sort.Syntax

/-!
# Pointers into an `int` array

`sortindirect` and `sortints` walk an `int` array with pointer cursors. A
cursor at element `k` of an array whose element 0 is at byte offset `base` is
`Vptr b (pt base k)`. The lemmas here evaluate what the sorts do with such
cursors: reading and writing `*p` and `p[i]`, `p + i` and `p - i`, the
comparisons `p <= q`, `p >= q`, `p > q` (both cursors at most one past the
end, so CompCert's weak validity holds), and the element distance `p - q`
cast to `int`.
-/

namespace NautyVerified.Proofs.Sparse.Sort

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

/-- The offset of element `k` of an `int` array at `base`. -/
abbrev pt (base : Int) (k : Nat) : ptrofs := ptrTo base 4 k

section
omit binary64_certificate binary32_certificate

theorem toNat_pt {base : Int} {k : Nat} (h0 : 0 ≤ base) (h1 : base + 4 * k < 2 ^ 64) :
    ((bvp (pt base k)).toNat : Int) = base + 4 * k := by
  rw [← intOfZ_Ptrofs_unsigned]
  exact unsigned_ptrTo (by omega) h1

theorem unsigned_pt {base : Int} {k : Nat} (h0 : 0 ≤ base) (h1 : base + 4 * k < 2 ^ 64) :
    Ptrofs.unsigned (pt base k) = elemOfs .Mint32 base k := by
  apply intOfZ_injective
  rw [unsigned_ptrTo (by omega) h1, elemOfs, intOfZ_zOfInt]
  rfl

theorem pt_add (ce : composite_env) (base : Int) (k j : Nat) (hj : (j : Int) < 2147483648) :
    Ptrofs.add (pt base k) (Ptrofs.mul (Ptrofs.repr (sizeof ce tint)) (Ptrofs.of_ints (ir j))) =
      pt base (k + j) :=
  add_ptrTo_ptrTo base (sizeof ce tint) k j hj

theorem pt_sub (ce : composite_env) (base : Int) (k j : Nat) (hj : (j : Int) < 2147483648) :
    Ptrofs.sub (pt base (k + j)) (Ptrofs.mul (Ptrofs.repr (sizeof ce tint)) (Ptrofs.of_ints (ir j))) =
      pt base k := by
  apply bvp_inj.1
  rw [bvp_sub, bvp_mul, bvp_repr, bvp_of_ints, toInt_ir ⟨by omega, hj⟩, bvp_repr,
    bvp_repr, intOfZ_zOfInt, intOfZ_zOfInt, ← BitVec.ofInt_mul]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add]
  congr 1
  have : intOfZ (sizeof ce tint) = 4 := rfl
  rw [this]
  push_cast
  omega

theorem ltu_pt {base : Int} {k1 k2 : Nat} (h0 : 0 ≤ base) (h1 : base + 4 * k1 < 2 ^ 64)
    (h2 : base + 4 * k2 < 2 ^ 64) :
    Ptrofs.ltu (pt base k1) (pt base k2) = decide (k1 < k2) := by
  rw [bvp_ltu]
  have e1 := toNat_pt h0 h1
  have e2 := toNat_pt h0 h2
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq]
  omega

/-- Comparing two cursors into one array, each at most one past its end. -/
theorem cmp_pt {m : mem} {b : block} {base : Int} {vals : Nat → val} {N : Nat}
    (harr : ArrayAt m .Mint32 b base vals N) (hN : 0 < N) {k1 k2 : Nat} (hk1 : k1 ≤ N)
    (hk2 : k2 ≤ N) (c : Lib.Integers.comparison) :
    Val.cmplu_bool (Mem.valid_pointer m) c (.Vptr b (pt base k1)) (.Vptr b (pt base k2)) =
      some (Ptrofs.cmpu c (pt base k1) (pt base k2)) := by
  have hf := harr.fits
  have hb := harr.base_nonneg
  have h4 : csize .Mint32 = 4 := rfl
  rw [h4] at hf
  have w (k : Nat) (hk : k ≤ N) :
      (Mem.valid_pointer m b (Ptrofs.unsigned (pt base k)) ||
        Mem.valid_pointer m b (ZArith.BinInt.Z.sub (Ptrofs.unsigned (pt base k)) (.Zpos .xH))) =
        true := by
    have hu : Ptrofs.unsigned (pt base k) = zOfInt (base + 4 * k) := by
      apply intOfZ_injective
      rw [unsigned_ptrTo (by omega) (by omega), intOfZ_zOfInt]
    rw [hu]
    exact harr.weak_valid hN (by omega) (by rw [h4]; omega)
  exact cmplu_same _ c b _ _ (w k1 hk1) (w k2 hk2)

theorem cmpu_le_pt {base : Int} {k1 k2 : Nat} (h0 : 0 ≤ base) (h1 : base + 4 * k1 < 2 ^ 64)
    (h2 : base + 4 * k2 < 2 ^ 64) :
    Ptrofs.cmpu .Cle (pt base k1) (pt base k2) = decide (k1 ≤ k2) := by
  show (!Ptrofs.ltu _ _) = _
  rw [ltu_pt h0 h2 h1]
  by_cases h : k1 ≤ k2 <;> simp [h] <;> omega

theorem cmpu_ge_pt {base : Int} {k1 k2 : Nat} (h0 : 0 ≤ base) (h1 : base + 4 * k1 < 2 ^ 64)
    (h2 : base + 4 * k2 < 2 ^ 64) :
    Ptrofs.cmpu .Cge (pt base k1) (pt base k2) = decide (k2 ≤ k1) := by
  show (!Ptrofs.ltu _ _) = _
  rw [ltu_pt h0 h1 h2]
  by_cases h : k2 ≤ k1 <;> simp [h] <;> omega

theorem cmpu_gt_pt {base : Int} {k1 k2 : Nat} (h0 : 0 ≤ base) (h1 : base + 4 * k1 < 2 ^ 64)
    (h2 : base + 4 * k2 < 2 ^ 64) :
    Ptrofs.cmpu .Cgt (pt base k1) (pt base k2) = decide (k2 < k1) :=
  ltu_pt h0 h2 h1

/-- `(int)(p - q)` for cursors at elements `k1` and `k2`. -/
theorem diff_pt (base : Int) {k1 k2 : Nat} (hk1 : k1 < 2147483648) (hk2 : k2 < 2147483648) :
    Lib.Integers.Int.repr (Int64.unsigned (Ptrofs.to_int64
      (Ptrofs.divs (Ptrofs.sub (pt base k1) (pt base k2)) (Ptrofs.repr (zOfInt 4))))) =
      ir ((k1 : Int) - k2) := by
  have hb : ∀ k : Nat, bvp (pt base k) = BitVec.ofInt 64 (base + 4 * k) := by
    intro k; show bvp (Ptrofs.repr _) = _; rw [bvp_repr, intOfZ_zOfInt]
  have hsub : bvp (Ptrofs.sub (pt base k1) (pt base k2)) = BitVec.ofInt 64 (4 * ((k1 : Int) - k2)) := by
    rw [bvp_sub, hb, hb, BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add]
    congr 1; omega
  have hq : Ptrofs.divs (Ptrofs.sub (pt base k1) (pt base k2)) (Ptrofs.repr (zOfInt 4)) =
      Ptrofs.repr (zOfInt ((k1 : Int) - k2)) := by
    show WordCore.repr 64 (ZArith.BinInt.Z.quot (WordCore.signed _) (WordCore.signed _)) = _
    congr 1
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.quot, intOfZ_zOfInt]
    rw [intOfZ_signed (by decide), intOfZ_signed (by decide)]
    have hs1 : (toBV (Ptrofs.sub (pt base k1) (pt base k2))).toInt = 4 * ((k1 : Int) - k2) := by
      show (bvp _).toInt = _
      rw [hsub, BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
    have hs2 : (toBV (Ptrofs.repr (zOfInt 4))).toInt = 4 := by
      show (bvp _).toInt = _
      rw [bvp_repr, intOfZ_zOfInt]; decide
    rw [hs1, hs2, Int.mul_tdiv_cancel_left _ (by decide)]
  rw [hq]
  apply bv32_inj.1
  show bv32 (Lib.Integers.Int.repr _) = bv32 (Lib.Integers.Int.repr _)
  rw [bv32_repr, bv32_repr, intOfZ_Int64_unsigned]
  show BitVec.ofInt 32 ((bv64 (Int64.repr (Ptrofs.unsigned _))).toNat : Int) = _
  rw [bv64_repr, intOfZ_Ptrofs_unsigned, bvp_repr, intOfZ_zOfInt, ofInt_toNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  omega

end

end NautyVerified.Proofs.Sparse.Sort
