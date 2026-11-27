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

open Hex.GraphIso.Nauty

/-- nauty's row comparison: the first differing word, compared as a number. -/
def wordScan (ws wt : Nat → BitVec 64) : Nat → Nat → Ordering
  | 0, _ => .eq
  | fuel + 1, j =>
    if (ws j).toNat < (wt j).toNat then .lt
    else if (wt j).toNat < (ws j).toNat then .gt
    else wordScan ws wt fuel (j + 1)

theorem exists_least {P : Nat → Prop} [DecidablePred P] : ∀ (k : Nat), P k → ∃ j, P j ∧ ∀ i < j, ¬ P i
  | k, hk => by
    by_cases h : ∃ i < k, P i
    · obtain ⟨i, hi, hPi⟩ := h
      exact exists_least i hPi
    · exact ⟨k, hk, fun i hi hPi => h ⟨i, hi, hPi⟩⟩

theorem wordScan_eq {n M : Nat} {ws wt : Nat → BitVec 64} {s t : VSet n} (hs : SetRep ws M s)
    (ht : SetRep wt M t) :
    ∀ (F j : Nat), j + F = M → (∀ w < j, ws w = wt w) → wordScan ws wt F j = s.rowCmp t
  | 0, j, hj, heq => by
    rw [wordScan]
    symm
    rw [VSet.rowCmp_eq_iff]
    apply VSet.ext
    intro v
    rcases Nat.lt_or_ge v (64 * M) with hv | hv
    · rw [← hs.2 v hv, ← ht.2 v hv]
      simp only [SetwordsMem]
      rw [heq _ (by omega)]
    · rw [VSet.mem_of_ge (by have := hs.1; omega), VSet.mem_of_ge (by have := hs.1; omega)]
  | F + 1, j, hj, heq => by
    rw [wordScan]
    by_cases hw : ws j = wt j
    · rw [hw, ite_eq_right (Nat.lt_irrefl _), ite_eq_right (Nat.lt_irrefl _)]
      exact wordScan_eq hs ht F (j + 1) (by omega) fun w hw' => by
        rcases Nat.lt_or_ge w j with h | h
        · exact heq w h
        · rw [show w = j by omega]; exact hw
    · -- the least position (from the most significant end) where the words differ
      have hex : ∃ k, k < 64 ∧ (ws j).getMsbD k ≠ (wt j).getMsbD k :=
        Classical.byContradiction fun h => hw (BitVec.eq_of_getMsbD_eq fun i hi =>
          Classical.byContradiction fun hne => h ⟨i, hi, hne⟩)
      obtain ⟨k0, hk0, hne0⟩ := hex
      obtain ⟨k, ⟨hk, hne⟩, hmin⟩ := exists_least (P := fun k => k < 64 ∧ (ws j).getMsbD k ≠ (wt j).getMsbD k) k0 ⟨hk0, hne0⟩
      have hpre : ∀ i < k, (ws j).getMsbD i = (wt j).getMsbD i := fun i hi =>
        Classical.byContradiction fun h => hmin i hi ⟨by omega, h⟩
      let d := 64 * j + k
      have hd : d < 64 * M := by omega
      have hdj : d / 64 = j := by omega
      have hdk : d % 64 = k := by omega
      have hsd : s.mem d = (ws j).getMsbD k := by rw [← hs.2 d hd]; simp [SetwordsMem, hdj, hdk]
      have htd : t.mem d = (wt j).getMsbD k := by rw [← ht.2 d hd]; simp [SetwordsMem, hdj, hdk]
      have hbelow : ∀ i, i < d → s.mem i = t.mem i := by
        intro i hi
        rw [← hs.2 i (by omega), ← ht.2 i (by omega)]
        simp only [SetwordsMem]
        rcases Nat.lt_or_ge (i / 64) j with h | h
        · rw [heq _ h]
        · have : i / 64 = j := by omega
          rw [this]; exact hpre _ (by omega)
      cases hx : (ws j).getMsbD k with
      | false =>
        have hy : (wt j).getMsbD k = true := by
          cases h' : (wt j).getMsbD k
          · rw [hx, h'] at hne; exact absurd rfl hne
          · rfl
        have hlt := lt_of_first_diff hk hpre hx hy
        rw [ite_eq_left hlt]
        symm
        exact VSet.rowCmp_lt_iff.2 ⟨d, by rw [hsd, hx], by rw [htd, hy], hbelow⟩
      | true =>
        have hy : (wt j).getMsbD k = false := by
          cases h' : (wt j).getMsbD k
          · rfl
          · rw [hx, h'] at hne; exact absurd rfl hne
        have hgt := lt_of_first_diff hk (fun i hi => (hpre i hi).symm) hy hx
        rw [ite_eq_right (Nat.not_lt.2 (Nat.le_of_lt hgt)), ite_eq_left hgt]
        symm
        exact VSet.rowCmp_gt_iff.2 ⟨d, by rw [hsd, hx], by rw [htd, hy], hbelow⟩

end NautyVerified.Spec
