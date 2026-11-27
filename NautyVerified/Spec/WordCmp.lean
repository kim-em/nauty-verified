import NautyVerified.Spec.Setwords

/-!
# Comparing setwords as numbers

nauty compares graph rows word by word with unsigned `<`. `lt_of_first_diff`:
numerically, the word with a 1 at the highest differing bit is the larger.
For most-significant-bit-first setwords that bit is the least vertex where
the sets differ, which is how HexGraphIso's `rowCmp` orders rows.
-/

namespace NautyVerified.Spec

theorem nat_lt_of_first_diff {x y p : Nat} (hhi : ∀ i, p < i → x.testBit i = y.testBit i)
    (hx : x.testBit p = false) (hy : y.testBit p = true) : x < y := by
  have hq : x / 2 ^ (p + 1) = y / 2 ^ (p + 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    exact hhi _ (by omega)
  have hxl : x % 2 ^ (p + 1) < 2 ^ p := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [Nat.testBit_mod_two_pow]
    by_cases h : i < p + 1
    · rw [show i = p by omega, hx]; simp
    · simp [h]
  have hyl : 2 ^ p ≤ y % 2 ^ (p + 1) := by
    apply Nat.ge_two_pow_of_testBit
    rw [Nat.testBit_mod_two_pow]
    simp [hy]
  have h1 := Nat.div_add_mod x (2 ^ (p + 1))
  have h2 := Nat.div_add_mod y (2 ^ (p + 1))
  rw [hq] at h1
  omega

/-- For words agreeing on positions (from the most significant end) before
`k` and differing at `k`, the one with a 1 there is the larger. -/
theorem lt_of_first_diff {x y : BitVec 64} {k : Nat} (hk : k < 64)
    (hpre : ∀ i < k, x.getMsbD i = y.getMsbD i) (hx : x.getMsbD k = false)
    (hy : y.getMsbD k = true) : x.toNat < y.toNat := by
  apply nat_lt_of_first_diff (p := 63 - k)
  · intro i hi
    by_cases hi64 : i < 64
    · have := hpre (63 - i) (by omega)
      rw [BitVec.getMsbD_eq_getLsbD, BitVec.getMsbD_eq_getLsbD] at this
      simp only [show 63 - i < 64 by omega, decide_true, Bool.true_and,
        show 64 - 1 - (63 - i) = i by omega] at this
      rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat] at this
      exact this
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) (by omega)))]
  · rw [BitVec.getMsbD_eq_getLsbD] at hx
    simp only [hk, decide_true, Bool.true_and, show 64 - 1 - k = 63 - k by omega] at hx
    rw [← BitVec.testBit_toNat] at hx; exact hx
  · rw [BitVec.getMsbD_eq_getLsbD] at hy
    simp only [hk, decide_true, Bool.true_and, show 64 - 1 - k = 63 - k by omega] at hy
    rw [← BitVec.testBit_toNat] at hy; exact hy

end NautyVerified.Spec
