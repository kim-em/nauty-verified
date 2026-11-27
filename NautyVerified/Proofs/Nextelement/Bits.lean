import NautyVerified.Spec.Set

/-!
# Bit facts behind `nextelement`

Pure statements about 64-bit words used by the `nextelement` proof: the
`leftbit` table (leading zeros of a byte), the leading-bit index computed by a
leaf of nauty's `FIRSTBITNZ` decision tree, and the masks its tests use.
Ported from the CLean-based experiment (`/tmp/nauty-verif`), where machine
words were already `BitVec 64`.
-/

namespace NautyVerified.Proofs.Nextelement


/-- `leftbit[i]`: the number of leading zeros of the byte `i` (8 for `i = 0`). -/
def lbv (i : Nat) : Nat := if i = 0 then 8 else 7 - Nat.log2 i

theorem lbv_bounds : ∀ y < 256, 1 ≤ y → lbv y ≤ 7 ∧ 2^(7 - lbv y) ≤ y ∧ y < 2^(8 - lbv y) := by
  decide +kernel

/-- `r` is the index of the first (most significant) set bit of `x`. -/
def LeadBit (x : BitVec 64) (r : Nat) : Prop :=
  r < 64 ∧ x.getMsbD r = true ∧ ∀ i < r, x.getMsbD i = false

theorem getMsbD_toNat (x : BitVec 64) (i : Nat) (hi : i < 64) :
    x.getMsbD i = x.toNat.testBit (63 - i) := by
  rw [BitVec.getMsbD_eq_getLsbD, BitVec.testBit_toNat]
  simp [hi]

theorem lead_of_bounds (x : BitVec 64) (r : Nat) (hr : r < 64)
    (h1 : 2^(63-r) ≤ x.toNat) (h2 : x.toNat < 2^(64-r)) : LeadBit x r := by
  refine ⟨hr, ?_, fun i hi => ?_⟩
  · rw [getMsbD_toNat x r hr, Nat.testBit_eq_decide_div_mod_eq]
    have hq1 : 1 ≤ x.toNat / 2^(63-r) := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 (by simpa using h1)
    have hq2 : x.toNat / 2^(63-r) < 2 := by
      refine (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 ?_
      rw [show 2 * 2^(63-r) = 2^(64-r) by
        rw [← Nat.pow_succ']; congr 1; omega]
      exact h2
    simp only [decide_eq_true_eq]
    omega
  · rw [getMsbD_toNat x i (by omega)]
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega))

/-- One leaf of `FIRSTBITMAC`: if `2^s ≤ x < 2^(s+8)`, then `c + leftbit[x >> s]` with
    `c = 56 - s` is the leading-bit index. -/
theorem leaf_lead (x : BitVec 64) (s c : Nat) (hc : c + s = 56)
    (h1 : 2^s ≤ x.toNat) (h2 : x.toNat < 2^(s+8)) :
    LeadBit x (c + lbv (x.toNat / 2^s)) := by
  have hy1 : 1 ≤ x.toNat / 2^s := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 (by simpa using h1)
  have hy2 : x.toNat / 2^s < 256 := by
    refine (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 ?_
    rw [show 256 * 2^s = 2^(s+8) by rw [Nat.pow_add, Nat.mul_comm]]; exact h2
  obtain ⟨hl, hlo, hhi⟩ := lbv_bounds _ hy2 hy1
  generalize hl' : lbv (x.toNat / 2^s) = l at hl hlo hhi
  refine lead_of_bounds x _ (by omega) ?_ ?_
  · have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos s)).1 hlo
    rw [← Nat.pow_add] at this
    rw [show 63 - (c + l) = 7 - l + s by omega]; exact this
  · have := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)).1 hhi
    rw [← Nat.pow_add] at this
    rw [show 64 - (c + l) = 8 - l + s by omega]; exact this

/-- A mask `M` whose set bits are exactly `[k, hi)`.  Below `2^hi`, `n &&& M = 0`
    exactly when `n < 2^k`. -/
theorem and_mask_eq_zero (n M k hi : Nat) (hM : ∀ i, M.testBit i = decide (k ≤ i ∧ i < hi))
    (hn : n < 2^hi) : (n &&& M = 0 ↔ n < 2^k) := by
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi'
    by_cases hih : i < hi
    · have := congrArg (fun t => t.testBit i) h
      simp only [Nat.testBit_and, hM, Nat.zero_testBit] at this
      simpa [hi', hih] using this
    · exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega)))
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, hM, Nat.zero_testBit]
    by_cases hik : k ≤ i
    · rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hik))]
      simp
    · simp [hik]

theorem mask_bits (M k hi : Nat) (hM : M < 2^64) (hhi : hi ≤ 64)
    (h : ∀ i < 64, M.testBit i = decide (k ≤ i ∧ i < hi)) :
    ∀ i, M.testBit i = decide (k ≤ i ∧ i < hi) := by
  intro i
  by_cases hi : i < 64
  · exact h i hi
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hM (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp; omega

/-- The machine test `x & C` against one of the seven `FIRSTBITNZ` masks. -/
theorem tst_iff (x : BitVec 64) (C : _root_.Int) (k hi : Nat)
    (hC : ∀ i, (BitVec.ofInt 64 C).toNat.testBit i = decide (k ≤ i ∧ i < hi))
    (hn : x.toNat < 2^hi) :
    (x &&& BitVec.ofInt 64 C = 0) ↔ x.toNat < 2^k := by
  have := and_mask_eq_zero x.toNat _ k hi hC hn
  rw [← BitVec.toNat_and] at this
  constructor
  · intro h; exact this.1 (by rw [h]; rfl)
  · intro h; exact BitVec.eq_of_toNat_eq (by simpa using this.2 h)

macro "mask_tac" : tactic => `(tactic| exact mask_bits _ _ _ (by decide) (by decide) (by decide +kernel))

end NautyVerified.Proofs.Nextelement
