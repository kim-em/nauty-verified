import HexGraphIso.Nauty.Search.Refine
import NautyVerified.Spec.Orbjoin

/-!
# HexGraphIso's `fmptn`, unrolled

`fmptn_eq` rewrites HexGraphIso's `fmptn` as a fold of `cellStep` over the
cells of the partition, with the inner minimum search as `scanMin`. When the
last position closes a cell (`ptn[n-1] ≤ level`), `cellEnd_spec` says the
cell starting at `c1` ends at the least `c2 ≥ c1` with `ptn[c2] ≤ level`,
which is where nauty's `do … while (ptn[i] > level)` stops.
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty

/-- The least `lab[i]` over `i ∈ l`, starting from `m`. -/
def scanMin (lab : Array Nat) (l : List Nat) (m : Nat) : Nat :=
  l.foldl (fun m i => if lab[i]! < m then lab[i]! else m) m

/-- One cell of `fmptn`. -/
def cellStep {n : Nat} (lab : Array Nat) (s : VSet n × VSet n) (c : Nat × Nat) : VSet n × VSet n :=
  if c.1 == c.2 then (s.1.insert lab[c.1]!, s.2.insert lab[c.1]!)
  else (s.1, s.2.insert (scanMin lab (List.range' (c.1 + 1) (c.2 - c.1)) lab[c.1]!))

theorem forIn_foldl {α β : Type} (l : List α) (f : β → α → β) (b : β) :
    (forIn l b (fun i b => pure (ForInStep.yield (f b i))) : Id β) = l.foldl f b := by
  induction l generalizing b with
  | nil => rfl
  | cons i l ih =>
    rw [List.forIn_cons, List.foldl_cons]
    exact ih _

theorem forIn_range'_eq {β : Type} (a b : Nat) (init : β) (f : Nat → β → Id (ForInStep β)) :
    (forIn [a:b] init f : Id β) = forIn (List.range' a (b - a)) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size]

theorem fmptn_eq (lab ptn : Array Nat) (level n : Nat) :
    fmptn lab ptn level n = (cells ptn level n).foldl (cellStep lab) (.empty, .empty) := by
  rw [fmptn]
  simp only [forIn_range'_eq]
  have hin : ∀ c1 c2 : Nat, (forIn (List.range' (c1 + 1) (c2 + 1 - (c1 + 1))) lab[c1]!
      (fun i s => if lab[i]! < s then pure (ForInStep.yield lab[i]!) else pure (ForInStep.yield s)) :
      Id Nat) = scanMin lab (List.range' (c1 + 1) (c2 - c1)) lab[c1]! := by
    intro c1 c2
    rw [show c2 + 1 - (c1 + 1) = c2 - c1 by omega, scanMin, ← forIn_foldl]
    congr 1
    funext i s
    split <;> rfl
  simp only [hin]
  rw [← forIn_foldl]
  show (forIn (cells ptn level n) _ _ : Id _) = _
  congr 1
  funext c s
  simp only [cellStep]
  split <;> rfl

theorem cellEnd_go (ptn : Array Nat) (level : Nat) :
    ∀ (fuel j k : Nat), j ≤ k → k < j + fuel → ptn[k]! ≤ level →
      j ≤ cellEnd.go ptn level fuel j ∧ cellEnd.go ptn level fuel j ≤ k ∧
      ptn[cellEnd.go ptn level fuel j]! ≤ level ∧
      ∀ i, j ≤ i → i < cellEnd.go ptn level fuel j → level < ptn[i]!
  | 0, _, _, _, h, _ => absurd h (by omega)
  | fuel + 1, j, k, hjk, hk, hl => by
    rw [cellEnd.go]
    by_cases hj : ptn[j]! > level
    · rw [ite_eq_left hj]
      have hjk' : j ≠ k := fun h => by subst h; omega
      have ih := cellEnd_go ptn level fuel (j + 1) k (by omega) (by omega) hl
      refine ⟨by omega, ih.2.1, ih.2.2.1, fun i hi hlt => ?_⟩
      by_cases hij : i = j
      · subst hij; exact hj
      · exact ih.2.2.2 i (by omega) hlt
    · rw [ite_eq_right hj]
      exact ⟨Nat.le_refl _, hjk, by omega, fun i hi hlt => absurd hlt (by omega)⟩

/-- The cell starting at `c1` ends at the least `c2 ≥ c1` with `ptn[c2] ≤ level`. -/
theorem cellEnd_spec {ptn : Array Nat} {level n c1 : Nat} (hs : ptn.size = n) (hc : c1 < n)
    (hlast : ptn[n - 1]! ≤ level) :
    c1 ≤ cellEnd ptn level c1 ∧ cellEnd ptn level c1 < n ∧ ptn[cellEnd ptn level c1]! ≤ level ∧
      ∀ i, c1 ≤ i → i < cellEnd ptn level c1 → level < ptn[i]! := by
  have h := cellEnd_go ptn level (ptn.size - c1) c1 (n - 1) (by omega) (by omega) hlast
  exact ⟨h.1, by have := h.2.1; unfold cellEnd; omega, h.2.2.1, h.2.2.2⟩

theorem cells_go_succ (ptn : Array Nat) (level n fuel c1 : Nat) (hc : c1 < n) :
    cells.go ptn level n (fuel + 1) c1 =
      (c1, cellEnd ptn level c1) :: cells.go ptn level n fuel (cellEnd ptn level c1 + 1) := by
  rw [cells.go, ite_eq_left hc]

theorem cells_go_ge (ptn : Array Nat) (level n fuel c1 : Nat) (hc : ¬ c1 < n) :
    cells.go ptn level n fuel c1 = [] := by
  cases fuel <;> simp [cells.go, hc]

end NautyVerified.Spec
