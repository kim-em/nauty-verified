import NautyVerified.Spec.Setwords
import NautyVerified.Statement.Harness
import NautyVerified.Word.Machine

/-!
# The canonical graph's words as `expected` writes them

`rowWords_of_setRep`: when the `M` setwords `ws` represent the set `s`,
`Statement.rowWords M s` is the list of their values as signed `long`s.
`words_eq_rowWords`: the `M * n` words of `canong` are written as
`expected`'s block of rows.
-/

namespace NautyVerified.Proofs.Harness

open NautyVerified NautyVerified.Spec NautyVerified.Word
open Hex.GraphIso.Nauty

/-- Summing the set bits of the first `k` positions (from the most
significant end) of a word gives its top `k` bits. -/
theorem foldl_bits (x : BitVec 64) (p : Nat → Prop) [DecidablePred p]
    (hp : ∀ b < 64, p b ↔ x.getMsbD b = true) :
    ∀ k ≤ 64, (List.range k).foldl (fun acc b => if p b then acc + 2 ^ (63 - b) else acc) 0 =
      x.toNat / 2 ^ (64 - k) * 2 ^ (64 - k)
  | 0, _ => by
    simp only [List.range_zero, List.foldl_nil, Nat.sub_zero]
    rw [Nat.div_eq_of_lt (by have := x.isLt; simpa using this)]
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, foldl_bits x p hp k (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [show 64 - (k + 1) = 63 - k by omega, show 64 - k = (63 - k) + 1 by omega]
    have hbit : p k ↔ x.toNat / 2 ^ (63 - k) % 2 = 1 := by
      rw [hp k (by omega), BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD, Nat.testBit,
        Nat.shiftRight_eq_div_pow]
      simp only [show k < 64 by omega, decide_true, Bool.true_and,
        show 64 - 1 - k = 63 - k by omega]
      simp [Nat.one_and_eq_mod_two]
    generalize 63 - k = j at *
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.mul_assoc]
    generalize x.toNat / 2 ^ j = y at *
    generalize 2 ^ j = P
    have hy := Nat.div_add_mod y 2
    split
    · rename_i h
      have h1 := hbit.1 h
      rw [h1] at hy
      conv => rhs; rw [← hy]
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm 2, Nat.mul_right_comm]
    · rename_i h
      have h0 : y % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one y with h' | h'
        · exact h'
        · exact absurd (hbit.2 h') h
      rw [h0] at hy
      conv => rhs; rw [← hy]
      rw [Nat.add_zero, Nat.mul_comm 2, Nat.mul_right_comm]

/-- A word is the sum of its set bits. -/
theorem ofNat_foldl_bits (x : BitVec 64) (p : Nat → Prop) [DecidablePred p]
    (hp : ∀ b < 64, p b ↔ x.getMsbD b = true) :
    BitVec.ofNat 64 ((List.range 64).foldl
      (fun acc b => if p b then acc + 2 ^ (63 - b) else acc) 0) = x := by
  rw [foldl_bits x p hp 64 (by omega)]
  simp

theorem rowWords_of_setRep {n M : Nat} {ws : Nat → BitVec 64} {s : VSet n} (h : SetRep ws M s) :
    Statement.rowWords M s = (List.range M).map fun w => (ws w).toInt := by
  unfold Statement.rowWords
  refine List.map_congr_left fun w hw => ?_
  rw [List.mem_range] at hw
  congr 1
  refine ofNat_foldl_bits (ws w) _ fun b hb => ?_
  have hv : 64 * w + b < 64 * M := by omega
  have hm := h.2 _ hv
  simp only [SetwordsMem, show (64 * w + b) / 64 = w by omega,
    show (64 * w + b) % 64 = b by omega] at hm
  rw [hm]
  constructor
  · exact fun h => h.2
  · exact fun h' => ⟨VSet.mem_lt h', h'⟩

/-- The words of `canong`, row by row, are `expected`'s rows. -/
theorem words_eq_rowWords {n M : Nat} (cw : Nat → BitVec 64) (c : Array (VSet n))
    (hc : c.size = n) (h : ∀ v < n, SetRep (fun w => cw (M * v + w)) M c[v]!) :
    (List.range (M * n)).map (fun j => (cw j).toInt) = c.toList.flatMap (Statement.rowWords M) := by
  have key : ∀ N ≤ n, ((List.range N).map fun v => c[v]!).flatMap (Statement.rowWords M) =
      (List.range (M * N)).map (fun j => (cw j).toInt) := by
    intro N
    induction N with
    | zero => intro; simp
    | succ N ih =>
      intro hN
      rw [List.range_succ, List.map_append, List.flatMap_append, ih (by omega),
        Nat.mul_succ, List.range_add, List.map_append]
      simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.map_map]
      rw [rowWords_of_setRep (h N (by omega))]
      rfl
  rw [← key n (Nat.le_refl _)]
  congr 1
  apply List.ext_getElem (by simp [hc])
  intro i h1 h2
  simp [getElem!_pos c i (by simp at h1; omega)]

end NautyVerified.Proofs.Harness
