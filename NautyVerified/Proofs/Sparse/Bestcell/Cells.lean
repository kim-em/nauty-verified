import NautyVerified.Proofs.Sparse.Bestcell.Model
import NautyVerified.Spec.Fmptn

/-!
# Facts about `cells` and the joins

`cellRun_fuel`: the scan needs only `n - first` more steps (`cellStep`
moves past the cell it reads). `Good`: what the scan keeps true of its state
when `lab` is injective: the indices are `n` or a cell's index, positions not
yet scanned still hold `n`, and at most `first / 2` cells are found (each
nontrivial cell has two positions), so `START` and `SIZE` (`work1` and
`work1 + n/2`) do not overlap. `joins_zero`: from all-zero hits, `joins`
leaves all-zero hits (its second pass clears every entry the first pass
raised).
-/

namespace NautyVerified.Proofs.Sparse.Bestcell

open Hex.GraphIso.Nauty (cellEnd)
open Hex.GraphIso.Nauty.Sparse

theorem get_set (a : Array Nat) (i x j : Nat) :
    (a.set! i x)[j]! = if i = j ∧ i < a.size then x else a[j]! := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hj : j < a.size
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_setIfInBounds hj, getElem!_pos a j hj]
    by_cases h : i = j
    · subst h; simp [hj]
    · simp [h]
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg a j hj]
    split
    · omega
    · rfl

theorem size_set (a : Array Nat) (i x : Nat) : (a.set! i x).size = a.size := by
  simp [Array.set!_eq_setIfInBounds]

/-! ## The cell scan -/

theorem mark_size (lab : Array Nat) (idx : Nat) : ∀ (l : List Nat) (a : Array Nat),
    (mark lab idx a l).size = a.size
  | [], _ => rfl
  | j :: l, a => by
    simp only [mark, List.foldl_cons] at *
    rw [show List.foldl (fun a j => a.set! lab[j]! idx) (a.set! lab[j]! idx) l =
      mark lab idx (a.set! lab[j]! idx) l from rfl, mark_size lab idx l, size_set]

theorem mark_get (lab : Array Nat) (idx : Nat) : ∀ (l : List Nat) (a : Array Nat) (v : Nat),
    v < a.size → (mark lab idx a l)[v]! = if ∃ j ∈ l, lab[j]! = v then idx else a[v]!
  | [], a, v, _ => by simp [mark]
  | j :: l, a, v, hv => by
    rw [show mark lab idx a (j :: l) = mark lab idx (a.set! lab[j]! idx) l from rfl,
      mark_get lab idx l _ v (by rw [size_set]; exact hv), get_set]
    by_cases h1 : ∃ j' ∈ l, lab[j']! = v
    · rw [ite_eq_left h1, ite_eq_left (by obtain ⟨j', hj', he⟩ := h1; exact ⟨j', .tail _ hj', he⟩)]
    · rw [ite_eq_right h1]
      by_cases h2 : lab[j]! = v
      · rw [ite_eq_left ⟨h2, by omega⟩, ite_eq_left ⟨j, .head _, h2⟩]
      · rw [ite_eq_right (fun h => h2 h.1), ite_eq_right]
        rintro ⟨j', hj', he⟩
        cases hj' with
        | head => exact h2 he
        | tail _ h => exact h1 ⟨j', h, he⟩

theorem cellEnd_eq {ptn : Array Nat} {level n i : Nat} (hs : ptn.size = n) (hi : i < n)
    (hlast : ptn[n - 1]! ≤ level) (hp : ptn[i]! ≤ level) : cellEnd ptn level i = i := by
  have sp := Spec.cellEnd_spec hs hi hlast
  rcases Nat.lt_or_ge i (cellEnd ptn level i) with h | h
  · have := sp.2.2.2 i (Nat.le_refl _) h; omega
  · omega

theorem cellEnd_gt {ptn : Array Nat} {level n i : Nat} (hs : ptn.size = n) (hi : i < n)
    (hlast : ptn[n - 1]! ≤ level) (hp : level < ptn[i]!) : i < cellEnd ptn level i := by
  have sp := Spec.cellEnd_spec hs hi hlast
  rcases Nat.lt_or_ge i (cellEnd ptn level i) with h | h
  · exact h
  · have : cellEnd ptn level i = i := by omega
    have h3 := sp.2.2.1
    rw [this] at h3
    omega

theorem cellStep_first {ptn : Array Nat} {level n : Nat} (lab : Array Nat) (hs : ptn.size = n)
    (hlast : ptn[n - 1]! ≤ level) {s : Cells} (hf : s.first < n) :
    s.first < (cellStep lab ptn level s).first := by
  have sp := Spec.cellEnd_spec hs hf hlast
  unfold cellStep
  split <;> (simp only; omega)

theorem cellRun_succ {n : Nat} {lab ptn : Array Nat} {level : Nat} {s : Cells} (k : Nat)
    (h : s.first < n) : cellRun n lab ptn level (k + 1) s = cellRun n lab ptn level k (cellStep lab ptn level s) := by
  simp [cellRun, show ¬ n ≤ s.first by omega]

/-- With fuel at least `n - first`, the scan's result does not depend on the fuel. -/
theorem cellRun_fuel {n : Nat} {lab ptn : Array Nat} {level : Nat} (hs : ptn.size = n)
    (hlast : ptn[n - 1]! ≤ level) :
    ∀ (k k' : Nat) (s : Cells), n - s.first ≤ k → n - s.first ≤ k' →
      cellRun n lab ptn level k s = cellRun n lab ptn level k' s
  | k, k', s, hk, hk' => by
    by_cases hf : n ≤ s.first
    · rw [cellRun_stop hf, cellRun_stop hf]
    · obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, k' = b + 1 := ⟨k' - 1, by omega⟩
      have h1 := cellStep_first lab hs hlast (s := s) (by omega)
      rw [cellRun_succ a (by omega), cellRun_succ b (by omega)]
      exact cellRun_fuel hs hlast a b _ (by omega) (by omega)
termination_by k => k

/-- The scan's state, as `bestcell_sg` keeps it. -/
structure Good (n : Nat) (lab : Array Nat) (s : Cells) : Prop where
  nsize : s.nntcell.size = n
  sizes : s.sizes.size = s.starts.size
  half : 2 * s.starts.size ≤ s.first
  fle : s.first ≤ n
  startLt : ∀ k < s.starts.size, s.starts[k]! < n
  sizeLe : ∀ k < s.starts.size, s.sizes[k]! ≤ n
  idx : ∀ v < n, s.nntcell[v]! = n ∨ s.nntcell[v]! < s.starts.size
  rest : ∀ p, s.first ≤ p → p < n → s.nntcell[lab[p]!]! = n

theorem good_start {n : Nat} {lab : Array Nat} (hls : ∀ j < n, lab[j]! < n) :
    Good n lab ⟨#[], #[], Array.replicate n n, 0⟩ where
  nsize := by simp
  sizes := rfl
  half := by simp
  fle := Nat.zero_le _
  startLt := fun k hk => by simp at hk
  sizeLe := fun k hk => by simp at hk
  idx := fun v hv => .inl (by simp [hv])
  rest := fun p _ hp => by simp [hls p hp]

theorem push_get (a : Array Nat) (x k : Nat) :
    (a.push x)[k]! = if k < a.size then a[k]! else if k = a.size then x else 0 := by
  by_cases h1 : k < a.size
  · rw [ite_eq_left h1, getElem!_pos _ k (by simp; omega), getElem!_pos a k h1, Array.getElem_push_lt h1]
  · rw [ite_eq_right h1]
    by_cases h2 : k = a.size
    · subst h2; rw [ite_eq_left rfl, getElem!_pos _ _ (by simp), Array.getElem_push_eq]
    · rw [ite_eq_right h2, getElem!_neg _ k (by simp; omega)]; rfl

section
variable {n : Nat} {lab ptn : Array Nat} {level : Nat}

theorem cellStep_single {s : Cells} (hs : ptn.size = n) (hf : s.first < n)
    (hlast : ptn[n - 1]! ≤ level) (hp : ptn[s.first]! ≤ level) :
    cellStep lab ptn level s = ⟨s.starts, s.sizes, s.nntcell, s.first + 1⟩ := by
  unfold cellStep
  rw [cellEnd_eq hs hf hlast hp, ite_eq_right (Nat.lt_irrefl _)]

theorem cellStep_nontriv {s : Cells} (hs : ptn.size = n) (hf : s.first < n)
    (hlast : ptn[n - 1]! ≤ level) (hp : level < ptn[s.first]!) :
    cellStep lab ptn level s = ⟨s.starts.push s.first,
      s.sizes.push (cellEnd ptn level s.first - s.first + 1),
      mark lab s.starts.size s.nntcell
        (List.range' s.first (cellEnd ptn level s.first + 1 - s.first)),
      cellEnd ptn level s.first + 1⟩ := by
  unfold cellStep
  rw [ite_eq_left (cellEnd_gt hs hf hlast hp)]

theorem good_single {s : Cells} (h : Good n lab s) (hs : ptn.size = n) (hf : s.first < n)
    (hlast : ptn[n - 1]! ≤ level) (hp : ptn[s.first]! ≤ level) :
    Good n lab (cellStep lab ptn level s) := by
  rw [cellStep_single hs hf hlast hp]
  exact { h with
    half := by have := h.half; simp only; omega
    fle := by simp only; omega
    rest := fun p hp1 hp2 => h.rest p (by simp only at hp1; omega) hp2 }

theorem good_nontriv {s : Cells} (h : Good n lab s) (hs : ptn.size = n) (hf : s.first < n)
    (hlast : ptn[n - 1]! ≤ level) (hp : level < ptn[s.first]!)
    (hls : ∀ j < n, lab[j]! < n) (hinj : ∀ a b, a < n → b < n → lab[a]! = lab[b]! → a = b) :
    Good n lab (cellStep lab ptn level s) := by
  have sp := Spec.cellEnd_spec hs hf hlast
  have hgt := cellEnd_gt hs hf hlast hp
  rw [cellStep_nontriv hs hf hlast hp]
  have hsz := h.sizes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only; rw [mark_size]; exact h.nsize
  · simp [hsz]
  · simp only [Array.size_push]; have := h.half; omega
  · simp only; omega
  · intro k hk
    simp only [Array.size_push] at hk ⊢
    rw [push_get]
    split
    · exact h.startLt k ‹_›
    · rw [ite_eq_left (by omega)]; exact hf
  · intro k hk
    simp only [Array.size_push] at hk ⊢
    rw [push_get, hsz]
    split
    · exact h.sizeLe k ‹_›
    · rw [ite_eq_left (by omega)]; omega
  · intro v hv
    simp only [Array.size_push]
    rw [mark_get _ _ _ _ _ (by rw [h.nsize]; exact hv)]
    split
    · exact .inr (by omega)
    · rcases h.idx v hv with h1 | h1
      · exact .inl h1
      · exact .inr (by omega)
  · intro p hp1 hp2
    simp only at hp1 ⊢
    have hl := h.nsize
    rw [mark_get _ _ _ _ _ ?_, ite_eq_right]
    · exact h.rest p (by omega) hp2
    · rintro ⟨j, hj, he⟩
      rw [List.mem_range'_1] at hj
      have := hinj j p (by omega) hp2 he
      omega
    · rw [hl]; exact hls p hp2

end

/-! ## The joins -/

section
variable {n : Nat} (g : Graph n) (nntcell sizes : Array Nat)

theorem hit_fold : ∀ (L : List Nat) (h : Array Nat),
    (L.foldl (hitStep g nntcell) h).size = h.size ∧
    (∀ k : Nat, (L.foldl (hitStep g nntcell) h)[k]! ≤ h[k]! + L.length) ∧
    (∀ k : Nat, (L.foldl (hitStep g nntcell) h)[k]! ≠ h[k]! →
      ∃ j ∈ L, nntcell[g.neighbor j]! = k ∧ k ≠ n)
  | [], h => ⟨rfl, fun _ => by simp, fun _ h' => absurd rfl h'⟩
  | j :: L, h => by
    simp only [List.foldl_cons, List.length_cons]
    obtain ⟨h1, h2, h3⟩ := hit_fold L (hitStep g nntcell h j)
    have e1 : (hitStep g nntcell h j).size = h.size := by
      unfold hitStep; split <;> simp [size_set]
    have e2 : ∀ k, (hitStep g nntcell h j)[k]! ≤ h[k]! + 1 := fun k => by
      unfold hitStep; split
      · rw [get_set]; split
        · rename_i hk; rw [hk.1]; omega
        · omega
      · omega
    have e3 : ∀ k, (hitStep g nntcell h j)[k]! ≠ h[k]! → nntcell[g.neighbor j]! = k ∧ k ≠ n :=
      fun k hk => by
        unfold hitStep at hk; split at hk
        · rw [get_set] at hk; split at hk
          · rename_i hne hk'
            exact ⟨hk'.1, by rw [← hk'.1]; simpa using hne⟩
          · exact absurd rfl hk
        · exact absurd rfl hk
    refine ⟨by rw [h1, e1], fun k => ?_, fun k hk => ?_⟩
    · have := h2 k; have := e2 k; omega
    · by_cases hk' : (L.foldl (hitStep g nntcell) (hitStep g nntcell h j))[k]! =
          (hitStep g nntcell h j)[k]!
      · rw [hk'] at hk
        obtain ⟨a, b⟩ := e3 k hk
        exact ⟨j, .head _, a, b⟩
      · obtain ⟨j', hj', a, b⟩ := h3 k hk'
        exact ⟨j', .tail _ hj', a, b⟩

theorem count_fold : ∀ (L : List Nat) (h : Array Nat) (c : Nat),
    (∀ k : Nat, h[k]! ≠ 0 → ∃ j ∈ L, nntcell[g.neighbor j]! = k ∧ k ≠ n) →
    (L.foldl (countStep g nntcell sizes) (h, c)).1.size = h.size ∧
    (∀ k : Nat, (L.foldl (countStep g nntcell sizes) (h, c)).1[k]! = 0) ∧
    (L.foldl (countStep g nntcell sizes) (h, c)).2 ≤ c + L.length
  | [], h, c, hyp => by
    refine ⟨rfl, fun k => Classical.byContradiction fun hk => ?_, by simp⟩
    obtain ⟨j, hj, -⟩ := hyp k hk
    cases hj
  | j :: L, h, c, hyp => by
    rw [List.foldl_cons, List.length_cons]
    by_cases hv : (nntcell[g.neighbor j]! != n) = true
    · obtain ⟨c', e, hc'⟩ : ∃ c', countStep g nntcell sizes (h, c) j =
          (h.set! nntcell[g.neighbor j]! 0, c') ∧ c' ≤ c + 1 := by
        refine ⟨if h[nntcell[g.neighbor j]!]! > 0 && h[nntcell[g.neighbor j]!]! <
            sizes[nntcell[g.neighbor j]!]! then c + 1 else c, by simp only [countStep, hv, ite_true], ?_⟩
        split <;> omega
      rw [e]
      obtain ⟨h1, h2, h3⟩ := count_fold L (h.set! nntcell[g.neighbor j]! 0) c' (fun k hk => by
        rw [get_set] at hk
        split at hk
        · exact absurd rfl hk
        · rename_i hn
          obtain ⟨j', hj', a, b⟩ := hyp k hk
          cases hj' with
          | head =>
            exfalso
            apply hk
            rw [getElem!_neg h k (by intro hlt; exact hn ⟨a, a ▸ hlt⟩)]
            rfl
          | tail _ hm => exact ⟨j', hm, a, b⟩)
      exact ⟨by rw [h1, size_set], h2, by omega⟩
    · have e : countStep g nntcell sizes (h, c) j = (h, c) := by
        simp only [countStep, hv, Bool.false_eq_true, ite_false]
      rw [e]
      obtain ⟨h1, h2, h3⟩ := count_fold L h c (fun k hk => by
        obtain ⟨j', hj', a, b⟩ := hyp k hk
        cases hj' with
        | head => exact absurd (by rw [a]; simpa using b) hv
        | tail _ hm => exact ⟨j', hm, a, b⟩)
      exact ⟨h1, h2, by omega⟩

theorem count_bound : ∀ (L : List Nat) (h : Array Nat) (c : Nat),
    (L.foldl (countStep g nntcell sizes) (h, c)).1.size = h.size ∧
    (∀ k : Nat, (L.foldl (countStep g nntcell sizes) (h, c)).1[k]! ≤ h[k]!) ∧
    (L.foldl (countStep g nntcell sizes) (h, c)).2 ≤ c + L.length
  | [], h, c => ⟨rfl, fun _ => Nat.le_refl _, by simp⟩
  | j :: L, h, c => by
    rw [List.foldl_cons, List.length_cons]
    by_cases hv : (nntcell[g.neighbor j]! != n) = true
    · obtain ⟨c', e, hc'⟩ : ∃ c', countStep g nntcell sizes (h, c) j =
          (h.set! nntcell[g.neighbor j]! 0, c') ∧ c' ≤ c + 1 := by
        refine ⟨if h[nntcell[g.neighbor j]!]! > 0 && h[nntcell[g.neighbor j]!]! <
            sizes[nntcell[g.neighbor j]!]! then c + 1 else c, by simp only [countStep, hv, ite_true], ?_⟩
        split <;> omega
      rw [e]
      obtain ⟨h1, h2, h3⟩ := count_bound L (h.set! nntcell[g.neighbor j]! 0) c'
      refine ⟨by rw [h1, size_set], fun k => ?_, by omega⟩
      have := h2 k
      rw [get_set] at this
      split at this <;> omega
    · have e : countStep g nntcell sizes (h, c) j = (h, c) := by
        simp only [countStep, hv, Bool.false_eq_true, ite_false]
      rw [e]
      obtain ⟨h1, h2, h3⟩ := count_bound L h c
      exact ⟨h1, h2, by omega⟩

/-- `joins` from all-zero hits leaves them all zero, with at most a row's count. -/
theorem joins_zero {h : Array Nat} (hz : ∀ k : Nat, h[k]! = 0) (v : Nat) :
    (joins g nntcell sizes h v).1.size = h.size ∧ (∀ k : Nat, (joins g nntcell sizes h v).1[k]! = 0) ∧
      (joins g nntcell sizes h v).2 ≤ (row g v).length := by
  obtain ⟨h1, -, h3⟩ := hit_fold g nntcell (row g v) h
  obtain ⟨c1, c2, c3⟩ := count_fold g nntcell sizes (row g v) _ 0 fun k hk =>
    h3 k (by rw [hz k]; exact hk)
  exact ⟨by unfold joins; rw [c1, h1], c2, by unfold joins; omega⟩

end

/-- All-zero hits of size `S`. -/
def Zero (S : Nat) (h : Array Nat) : Prop := h.size = S ∧ ∀ k : Nat, h[k]! = 0

theorem zero_pick {n : Nat} (g : Graph n) (lab : Array Nat) (c : Cells) :
    ∀ (L : List Nat) (s : Array Nat × Nat × Nat), Zero c.starts.size s.1 →
      Zero c.starts.size (L.foldl (pick g lab c) s).1
  | [], _, h => h
  | i :: L, s, h => by
    simp only [List.foldl_cons]
    apply zero_pick g lab c L
    obtain ⟨a, b, -⟩ := joins_zero g c.nntcell c.sizes h.2 lab[c.starts[i]!]!
    exact ⟨by simp only [pick]; rw [a, h.1], b⟩

theorem zero_init (S : Nat) : Zero S (Array.replicate S 0) :=
  ⟨by simp, fun k => by
    by_cases hk : k < S
    · simp [hk]
    · rw [getElem!_neg _ k (by simpa using hk)]; rfl⟩

end NautyVerified.Proofs.Sparse.Bestcell
