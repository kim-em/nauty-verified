import NautyVerified.Spec.SparseSort
import HexGraphIso.Nauty.Sparse.SortSegments
import HexGraphIso.Nauty.Sparse.SortStack
import HexGraphIso.Nauty.Sparse.TouchSort

/-!
# Facts about HexGraphIso's sort for `sortints`

`sortints` has direct keys and is called on an array that starts at the
base of its block (`HITCELL`), so the right cursor `xc` must never step
below the segment's first element: CompCert compares pointers only when both
are (weakly) valid. With distinct entries this holds, because the median
pivot always has a strictly smaller key in the segment away from its first
entry, unless the first entry itself is at most the pivot (`pivot_low`).
`Win x lo hi` (the window `[lo, hi)` has no repeated entry) is preserved by
the insertion and partition steps inside it (`win_insertion`,
`win_partition`). `scanL_same` and `scanL_adv` are the first step of the
left scan.
-/

namespace NautyVerified.Spec.SortC

open Hex.GraphIso.Nauty.Sparse Hex.GraphIso.Nauty.Sparse.Sort

/-- The left scan leaves the array alone unless its cursor moves. -/
theorem scanL_same (y : Array Nat) (v c : Nat) (f : Nat) (x : Array Nat) (aa b : Nat)
    (hab : aa ≤ b) (hbc : b ≤ c + 1) (h : (iterF (bodyL y v c) f (x, aa, b)).2.2 = b) :
    (iterF (bodyL y v c) f (x, aa, b)).1 = x := by
  cases f with
  | zero => rfl
  | succ f =>
    simp only [iterF, bodyL] at h ⊢
    by_cases hb : (decide (b ≥ c) || decide (y[x[b]!]! > v)) = true
    · simp only [hb, ite_true]
    · simp only [hb, Bool.false_eq_true, ite_false] at h ⊢
      have hbc' : b < c := by simp at hb; omega
      by_cases he : (y[x[b]!]! == v) = true
      · simp only [he, ite_true] at h ⊢
        have := scanL_inv y v c f (x.swapIfInBounds aa b) (aa + 1) (b + 1) (by omega) (by omega)
        omega
      · simp only [he, Bool.false_eq_true, ite_false] at h ⊢
        have := scanL_inv y v c f x aa (b + 1) (by omega) (by omega)
        omega

/-- The left scan moves past an entry at most the pivot. -/
theorem scanL_adv (y : Array Nat) (v c : Nat) (f : Nat) (x : Array Nat) (aa b : Nat)
    (hab : aa ≤ b) (hbc : b < c) (hk : y[x[b]!]! ≤ v) (hf : 1 ≤ f) :
    b + 1 ≤ (iterF (bodyL y v c) f (x, aa, b)).2.2 := by
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  simp only [iterF, bodyL]
  have hb : (decide (b ≥ c) || decide (y[x[b]!]! > v)) = false := by simp; omega
  simp only [hb, Bool.false_eq_true, ite_false]
  by_cases he : (y[x[b]!]! == v) = true
  · simp only [he, ite_true]
    have := scanL_inv y v c f (x.swapIfInBounds aa b) (aa + 1) (b + 1) (by omega) (by omega)
    omega
  · simp only [he, Bool.false_eq_true, ite_false]
    have := scanL_inv y v c f x aa (b + 1) (by omega) (by omega)
    omega

theorem swap_get_ne (a : Array Nat) {i j p : Nat} (hi : p ≠ i) (hj : p ≠ j) :
    (a.swapIfInBounds i j)[p]! = a[p]! := by
  by_cases hp : p < a.size
  · rw [getElem!_pos _ p (by simpa using hp), getElem!_pos a p hp]
    unfold Array.swapIfInBounds
    split
    · split
      · simp only [Array.swap, Array.getElem_set]
        rw [ite_eq_right (Ne.symm hj), ite_eq_right (Ne.symm hi)]
      · rfl
    · rfl
  · rw [getElem!_neg _ p (by simpa using hp), getElem!_neg a p hp]

/-- Of three distinct values, one other than the median is below it. -/
theorem median_low (a b c : Nat) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (median a b c = a ∧ (b < a ∨ c < a)) ∨ (median a b c = b ∧ (a < b ∨ c < b)) ∨
      (median a b c = c ∧ (a < c ∨ b < c)) := by
  unfold median
  split <;> split <;> (try split) <;> omega

/-- Distinct keys: the pivot is at least the first key, or a later key is
below it. -/
theorem pivot_low (x y : Array Nat) (s len : Nat) (hl : 11 ≤ len)
    (hd : ∀ i j, i < j → j < len → y[x[s + i]!]! ≠ y[x[s + j]!]!) :
    y[x[s]!]! ≤ pivot x y s len ∨
      ∃ p, s < p ∧ p < s + len ∧ y[x[p]!]! < pivot x y s len := by
  have hk : ∀ i j, i < len → j < len → i ≠ j → y[x[s + i]!]! ≠ y[x[s + j]!]! := by
    intro i j hi hj hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hd i j h hj
    · exact fun e => hd j i h hi e.symm
  have h0 : y[x[s]!]! = y[x[s + 0]!]! := rfl
  unfold pivot
  dsimp only
  split
  · rename_i hlt
    have := median_low (y[x[s + 0]!]!) (y[x[s + len / 2]!]!) (y[x[s + (len - 1)]!]!)
      (hk _ _ (by omega) (by omega) (by omega)) (hk _ _ (by omega) (by omega) (by omega))
      (hk _ _ (by omega) (by omega) (by omega))
    rw [h0]
    rcases this with ⟨he, h | h⟩ | ⟨he, h | h⟩ | ⟨he, h | h⟩ <;> rw [he]
    · exact .inr ⟨s + len / 2, by omega, by omega, h⟩
    · exact .inr ⟨s + (len - 1), by omega, by omega, h⟩
    · exact .inl (by omega)
    · exact .inr ⟨s + (len - 1), by omega, by omega, h⟩
    · exact .inl (by omega)
    · exact .inr ⟨s + len / 2, by omega, by omega, h⟩
  · rename_i hge
    -- each inner median is the key of a position in its triple
    have tri : ∀ i, i + 2 < len → ∃ q, i ≤ q ∧ q ≤ i + 2 ∧
        median (y[x[s + i]!]!) (y[x[s + (i + 1)]!]!) (y[x[s + (i + 2)]!]!) = y[x[s + q]!]! := by
      intro i hi
      rcases median_mem (y[x[s + i]!]!) (y[x[s + (i + 1)]!]!) (y[x[s + (i + 2)]!]!) with
        h | h | h
      · exact ⟨i, by omega, by omega, h⟩
      · exact ⟨i + 1, by omega, by omega, h⟩
      · exact ⟨i + 2, by omega, by omega, h⟩
    obtain ⟨q1, h1a, h1b, e1⟩ := tri 0 (by omega)
    obtain ⟨q2, h2a, h2b, e2⟩ := tri (len / 2 - 1) (by omega)
    obtain ⟨q3, h3a, h3b, e3⟩ := tri (len - 3) (by omega)
    have r2 : len / 2 - 1 + 1 = len / 2 := by omega
    have r2' : len / 2 - 1 + 2 = len / 2 + 1 := by omega
    have r3 : len - 3 + 1 = len - 2 := by omega
    have r3' : len - 3 + 2 = len - 1 := by omega
    rw [r2, r2'] at e2
    rw [r3, r3'] at e3
    simp only [Nat.zero_add] at e1
    rw [e1, e2, e3]
    have := median_low (y[x[s + q1]!]!) (y[x[s + q2]!]!) (y[x[s + q3]!]!)
      (hk _ _ (by omega) (by omega) (by omega)) (hk _ _ (by omega) (by omega) (by omega))
      (hk _ _ (by omega) (by omega) (by omega))
    -- a key below the median: at position `s` gives the first disjunct
    have low : ∀ q, q < len → ∀ w, y[x[s + q]!]! < w → y[x[s]!]! ≤ w ∨
        ∃ p, s < p ∧ p < s + len ∧ y[x[p]!]! < w := by
      intro q hq w hw
      by_cases hq0 : q = 0
      · subst hq0; exact .inl (by rw [h0]; omega)
      · exact .inr ⟨s + q, by omega, by omega, hw⟩
    rcases this with ⟨he, h | h⟩ | ⟨he, h | h⟩ | ⟨he, h | h⟩ <;> rw [he]
    · exact low q2 (by omega) _ h
    · exact low q3 (by omega) _ h
    · exact low q1 (by omega) _ h
    · exact low q3 (by omega) _ h
    · exact low q1 (by omega) _ h
    · exact low q2 (by omega) _ h

/-- The window `[lo, hi)` of `x` has no repeated entry. -/
def Win (x : Array Nat) (lo hi : Nat) : Prop := (x.extract lo hi).toList.Nodup

theorem Win.ne {x : Array Nat} {lo hi : Nat} (h : Win x lo hi) (hx : hi ≤ x.size) {i j : Nat}
    (hli : lo ≤ i) (hij : i < j) (hj : j < hi) : x[i]! ≠ x[j]! := by
  intro e
  have get : ∀ k, k < hi - lo → (x.extract lo hi).toList[k]! = x[lo + k]! := by
    intro k hk
    rw [getElem!_pos _ k (by simp; omega), getElem!_pos x (lo + k) (by omega)]
    simp
  have := (h.getElem!_inj (i := i - lo) (j := j - lo) (by simp; omega) (by simp; omega)).1
    (by rw [get _ (by omega), get _ (by omega), show lo + (i - lo) = i by omega,
      show lo + (j - lo) = j by omega]; exact e)
  omega

theorem Win.step {a b : Array Nat} {lo hi : Nat} (h : Win a lo hi) (hb : lo ≤ hi ∧ hi ≤ a.size)
    (hp : b.toList.Perm a.toList) (he : ∀ q, q < lo ∨ hi ≤ q → b[q]! = a[q]!) : Win b lo hi :=
  (segment_perm hb hp he).nodup_iff.2 h

theorem win_insertion {x : Array Nat} (y : Array Nat) {lo hi s len : Nat} (h : Win x lo hi)
    (hx : hi ≤ x.size) (hs : lo ≤ s) (hsl : s + len ≤ hi) : Win (insertion x y s len) lo hi :=
  h.step ⟨by omega, hx⟩ (insertion_perm x y s len (by omega))
    (fun q hq => insertion_outside x y s len q (by omega))

theorem win_partition {x : Array Nat} (y : Array Nat) {lo hi s len : Nat} (h : Win x lo hi)
    (hx : hi ≤ x.size) (hs : lo ≤ s) (hsl : s + len ≤ hi) (hl : 0 < len) :
    Win (partition x y s len).1 lo hi :=
  h.step ⟨by omega, hx⟩ (partition_perm x y s len)
    (fun q hq => (partition_proper x y s len (by omega) hl).2 q (by omega))

/-- A block swap leaves the entries outside its two blocks alone. -/
theorem swapRun_outside (p q : Nat) (x : Array Nat) (r : Nat) :
    ∀ k, (r < p ∨ p + k ≤ r) → (r < q ∨ q + k ≤ r) → (swapRun p q k x)[r]! = x[r]!
  | 0, _, _ => rfl
  | k + 1, h1, h2 => by
    have e : swapRun p q (k + 1) x = (swapRun p q k x).swapIfInBounds (p + k) (q + k) := by
      simp only [swapRun, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.zero_add, Nat.one_mul]
    rw [e, swap_get_ne _ (by omega) (by omega)]
    exact swapRun_outside p q x r k (by omega) (by omega)

/-- The left scan keeps HexGraphIso's partition invariant `Cuts` and stops at
the bound or at a key above the pivot. -/
theorem cutsL (y : Array Nat) (lo hi v c d : Nat) :
    ∀ (f : Nat) (x : Array Nat) (aa b : Nat), Cuts x y lo hi v aa b c d → hi ≤ x.size →
      c - b ≤ f →
      Cuts (iterF (bodyL y v c) f (x, aa, b)).1 y lo hi v (iterF (bodyL y v c) f (x, aa, b)).2.1
          (iterF (bodyL y v c) f (x, aa, b)).2.2 c d ∧
        ((iterF (bodyL y v c) f (x, aa, b)).2.2 = c ∨
          v < y[(iterF (bodyL y v c) f (x, aa, b)).1[(iterF (bodyL y v c) f (x, aa, b)).2.2]!]!)
  | 0, x, aa, b, h, _, hf => ⟨h, .inl (by have := h.bounds; simp only [iterF]; omega)⟩
  | f + 1, x, aa, b, h, hs, hf => by
    have hb := h.bounds
    simp only [iterF, bodyL]
    by_cases hstop : (decide (b ≥ c) || decide (y[x[b]!]! > v)) = true
    · simp only [hstop, ite_true]
      refine ⟨h, ?_⟩
      simp at hstop
      rcases hstop with h1 | h1
      · exact .inl (by omega)
      · exact .inr h1
    · simp only [hstop, Bool.false_eq_true, ite_false]
      have hbc : b < c := by simp at hstop; omega
      have hk : y[x[b]!]! ≤ v := by simp at hstop; omega
      by_cases he : (y[x[b]!]! == v) = true
      · simp only [he, ite_true]
        exact cutsL y lo hi v c d f _ _ _ (h.left_eq_step hs hbc (by simpa using he))
          (by simpa using hs) (by omega)
      · simp only [he, Bool.false_eq_true, ite_false]
        have hlt : y[x[b]!]! < v := by simp at he; omega
        exact cutsL y lo hi v c d f _ _ _ (h.left_lt_step hbc hlt) hs (by omega)

/-- The right scan keeps `Cuts`, keeps the left scan's stop, and stops at the
left cursor or at a key below the pivot. -/
theorem cutsR (y : Array Nat) (lo hi v aa b : Nat) :
    ∀ (f : Nat) (x : Array Nat) (c d : Nat), Cuts x y lo hi v aa b c d → hi ≤ x.size →
      (b = c ∨ v < y[x[b]!]!) → c - b ≤ f →
      Cuts (iterF (bodyR y v b) f (x, c, d)).1 y lo hi v aa b (iterF (bodyR y v b) f (x, c, d)).2.1
          (iterF (bodyR y v b) f (x, c, d)).2.2 ∧
        (b = (iterF (bodyR y v b) f (x, c, d)).2.1 ∨ v < y[(iterF (bodyR y v b) f (x, c, d)).1[b]!]!) ∧
        ((iterF (bodyR y v b) f (x, c, d)).2.1 = b ∨
          y[(iterF (bodyR y v b) f (x, c, d)).1[(iterF (bodyR y v b) f (x, c, d)).2.1 - 1]!]! < v)
  | 0, x, c, d, h, _, hst, hf => ⟨h, hst, .inl (by have := h.bounds; simp only [iterF]; omega)⟩
  | f + 1, x, c, d, h, hs, hst, hf => by
    have hb := h.bounds
    simp only [iterF, bodyR]
    by_cases hstop : (decide (c ≤ b) || decide (y[x[c - 1]!]! < v)) = true
    · simp only [hstop, ite_true]
      refine ⟨h, hst, ?_⟩
      simp at hstop
      rcases hstop with h1 | h1
      · exact .inl (by omega)
      · exact .inr h1
    · simp only [hstop, Bool.false_eq_true, ite_false]
      have hbc : b < c := by simp at hstop; omega
      have hk : v ≤ y[x[c - 1]!]! := by simp at hstop; omega
      by_cases he : (y[x[c - 1]!]! == v) = true
      · simp only [he, ite_true]
        exact cutsR y lo hi v aa b f _ _ _ (h.right_eq_step hs hbc (by simpa using he))
          (by simpa using hs) (right_stop x y b c d v hbc hb.2.2.2.1 (by omega) hst) (by omega)
      · simp only [he, Bool.false_eq_true, ite_false]
        have hlt : v < y[x[c - 1]!]! := by simp at he; omega
        refine cutsR y lo hi v aa b f _ _ _ (h.right_gt_step hbc hlt) hs ?_ (by omega)
        rcases hst with h1 | h1
        · omega
        · exact .inr h1

theorem sizeL (y : Array Nat) (v c : Nat) :
    ∀ (f : Nat) (x : Array Nat) (aa b : Nat), (iterF (bodyL y v c) f (x, aa, b)).1.size = x.size
  | 0, _, _, _ => rfl
  | f + 1, x, aa, b => by
    simp only [iterF, bodyL]
    by_cases h1 : (decide (b ≥ c) || decide (y[x[b]!]! > v)) = true
    · simp only [h1, ite_true]
    · simp only [h1, Bool.false_eq_true, ite_false]
      by_cases h2 : (y[x[b]!]! == v) = true
      · simp only [h2, ite_true]; rw [sizeL y v c f]; simp
      · simp only [h2, Bool.false_eq_true, ite_false]; exact sizeL y v c f _ _ _

theorem sizeR (y : Array Nat) (v b : Nat) :
    ∀ (f : Nat) (x : Array Nat) (c d : Nat), (iterF (bodyR y v b) f (x, c, d)).1.size = x.size
  | 0, _, _, _ => rfl
  | f + 1, x, c, d => by
    simp only [iterF, bodyR]
    by_cases h1 : (decide (c ≤ b) || decide (y[x[c - 1]!]! < v)) = true
    · simp only [h1, ite_true]
    · simp only [h1, Bool.false_eq_true, ite_false]
      by_cases h2 : (y[x[c - 1]!]! == v) = true
      · simp only [h2, ite_true]; rw [sizeR y v b f]; simp
      · simp only [h2, Bool.false_eq_true, ite_false]; exact sizeR y v b f _ _ _

/-- The partition passes keep `Cuts`. -/
theorem cutsP (y : Array Nat) (lo hi v len : Nat) :
    ∀ (f : Nat) (x : Array Nat) (aa b c d : Nat), Cuts x y lo hi v aa b c d → hi ≤ x.size →
      c - b ≤ len →
      Cuts (iterF (bodyP y v len) f (x, aa, b, c, d)).1 y lo hi v
        (iterF (bodyP y v len) f (x, aa, b, c, d)).2.1
        (iterF (bodyP y v len) f (x, aa, b, c, d)).2.2.1
        (iterF (bodyP y v len) f (x, aa, b, c, d)).2.2.2.1
        (iterF (bodyP y v len) f (x, aa, b, c, d)).2.2.2.2
  | 0, _, _, _, _, _, h, _, _ => h
  | f + 1, x, aa, b, c, d, h, hs, hl => by
    have hL := cutsL y lo hi v c d len x aa b h hs hl
    have hsL := sizeL y v c len x aa b
    have hm := scanL_inv y v c len x aa b (by have := h.bounds; omega) (by have := h.bounds; omega)
    generalize hl1 : iterF (bodyL y v c) len (x, aa, b) = l at hL hsL hm
    obtain ⟨x1, aa1, b1⟩ := l
    simp only at hL hsL hm
    have hb1 := hL.1.bounds
    have hR := cutsR y lo hi v aa1 b1 len x1 c d hL.1 (by omega) hL.2 (by omega)
    have hsR := sizeR y v b1 len x1 c d
    have hmR := scanR_inv y v b1 len x1 c d (by omega) (by omega)
    generalize hr1 : iterF (bodyR y v b1) len (x1, c, d) = r at hR hsR hmR
    obtain ⟨x2, c2, d2⟩ := r
    simp only at hR hsR hmR
    have hb2 := hR.1.bounds
    have hP : bodyP y v len (x, aa, b, c, d) = if b1 ≥ c2 then .done (x2, aa1, b1, c2, d2)
        else .yield (x2.swapIfInBounds b1 (c2 - 1), aa1, b1 + 1, c2 - 1, d2) := by
      simp only [bodyP, hl1, hr1]
    simp only [iterF, hP]
    by_cases hst : b1 ≥ c2
    · simp only [hst, ite_true]; exact hR.1
    · simp only [hst, ite_false]
      have hlt : v < y[x2[b1]!]! := by rcases hR.2.1 with h | h; omega; exact h
      have hgt : y[x2[c2 - 1]!]! < v := by rcases hR.2.2 with h | h; omega; exact h
      exact cutsP y lo hi v len f _ _ _ _ _ (hR.1.cross (by omega) (by omega) hlt hgt)
        (by simp; omega) (by omega)

/-- With identity keys, the indirect sort puts HexGraphIso's `sortCells` of the
segment in place. -/
theorem indirect_ident (x y : Array Nat) (start len M : Nat) (hb : start + len ≤ x.size)
    (hy : ∀ i < M, y[i]! = i) (hx : ∀ q, start ≤ q → q < start + len → x[q]! < M) :
    (indirect x y start len).extract start (start + len) =
      sortCells (x.extract start (start + len)) := by
  have hseg := indirect_segment x y start len hb
  have hsize := indirect_size x y start len
  have hsorted := indirect_sorted x y start len hb
  apply Array.toList_inj.1
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · intro a b _ _ h1 h2; omega
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [Array.length_toList, Array.size_extract] at hi hj
    simp only [Array.getElem_toList, Array.getElem_extract]
    have hm : ∀ k, k < len → (indirect x y start len)[start + k]! < M := by
      intro k hk
      obtain ⟨r, hr1, hr2, hr⟩ := segment_mem (by rw [hsize]; exact hb) hseg
        (q := start + k) ⟨by omega, by omega⟩
      rw [hr]; exact hx r hr1 hr2
    have h := hsorted i j hij (by omega)
    rw [hy _ (hm i (by omega)), hy _ (hm j (by omega))] at h
    rwa [getElem!_pos _ _ (by rw [hsize]; omega), getElem!_pos _ _ (by rw [hsize]; omega)] at h
  · exact sortCells_order _
  · exact hseg.trans (sortCells_perm _).symm

end NautyVerified.Spec.SortC
