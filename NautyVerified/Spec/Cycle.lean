/-!
# Cycles of a permutation

`pigeon`: `n + 1` values below `n` repeat. `cycle_return`: iterating a map
that is injective on `0 .. n-1` (and stays there) returns to its start within
`n` steps; `firstReturn` is the least such step.
-/

namespace NautyVerified.Spec

/-- Among `g 0, …, g n`, all below `n`, two are equal. -/
theorem pigeon : ∀ (n : Nat) (g : Nat → Nat), (∀ k, k ≤ n → g k < n) →
    ∃ a b, a < b ∧ b ≤ n ∧ g a = g b
  | 0, g, h => absurd (h 0 (Nat.le_refl _)) (by omega)
  | n + 1, g, h => by
    by_cases hex : ∃ k, k ≤ n ∧ g k = g (n + 1)
    · obtain ⟨k, hk, he⟩ := hex
      exact ⟨k, n + 1, by omega, Nat.le_refl _, he⟩
    · have hne : ∀ k, k ≤ n → g k ≠ g (n + 1) := fun k hk he => hex ⟨k, hk, he⟩
      let g' := fun k => if g k < g (n + 1) then g k else g k - 1
      obtain ⟨a, b, hab, hb, he⟩ := pigeon n g' fun k hk => by
        have h1 := h k (by omega)
        have h2 := h (n + 1) (Nat.le_refl _)
        have h3 := hne k hk
        simp only [g']
        split <;> omega
      refine ⟨a, b, hab, by omega, ?_⟩
      have h1 := hne a (by omega)
      have h2 := hne b hb
      simp only [g'] at he
      split at he <;> split at he <;> omega

/-- The `k`-th iterate of `p` at `i`. -/
def iter (p : Nat → Nat) : Nat → Nat → Nat
  | 0, i => i
  | k + 1, i => p (iter p k i)

theorem iter_succ' (p : Nat → Nat) : ∀ k i, iter p (k + 1) i = iter p k (p i)
  | 0, _ => rfl
  | k + 1, i => by rw [iter, iter_succ' p k i, iter]

theorem iter_lt {p : Nat → Nat} {n : Nat} (hp : ∀ x, x < n → p x < n) :
    ∀ k i, i < n → iter p k i < n
  | 0, _, hi => hi
  | k + 1, i, hi => hp _ (iter_lt hp k i hi)

/-- On `0 .. n-1`, iterating an injective map returns to the start within
`n` steps. -/
theorem cycle_return {p : Nat → Nat} {n : Nat} (hp : ∀ x, x < n → p x < n)
    (hinj : ∀ x y, x < n → y < n → p x = p y → x = y) {i : Nat} (hi : i < n) :
    ∃ r, 1 ≤ r ∧ r ≤ n ∧ iter p r i = i := by
  obtain ⟨a, b, hab, hb, he⟩ := pigeon n (fun k => iter p k i) fun k _ => iter_lt hp k i hi
  -- peel `a` applications off both sides
  have peel : ∀ a b, a < b → iter p a i = iter p b i → iter p (b - a) i = i := by
    intro a
    induction a with
    | zero => intro b _ h; simpa [iter] using h.symm
    | succ a ih =>
      intro b hab h
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [iter, iter] at h
      have := hinj _ _ (iter_lt hp a i hi) (iter_lt hp b' i hi) h
      rw [show b' + 1 - (a + 1) = b' - a by omega]
      exact ih b' (by omega) this
  exact ⟨b - a, by omega, by omega, peel a b hab he⟩

end NautyVerified.Spec
