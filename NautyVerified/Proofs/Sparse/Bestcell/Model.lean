import HexGraphIso.Nauty.Sparse.Target
import Std.Tactic.Do

/-!
# HexGraphIso's `Sparse.bestcell`, step by step

`bestcell_eq`: `Sparse.bestcell g lab ptn level` is the start of the cell
`choose` picks, where `cells` (repeating `cellStep` while `first < n`)
lists the nontrivial cells' starts and sizes and fills `nntcell`, and
`choose` runs `pick` over them: `joins` counts the nontrivial joins of a
cell's first vertex (`hitStep` then `countStep` over its row), and the
first cell with the greatest count is kept. `choose_arg`: that index is
the one `bestcell_sg`'s final loop finds over the counts (`countAt`) from
`j = 0, maxcnt = COUNT[0]`. This is the form `bestcell_sg`'s loops
establish.
-/

namespace NautyVerified.Proofs.Sparse.Bestcell

open Std.Do
open Hex.GraphIso.Nauty (cellEnd)
open Hex.GraphIso.Nauty.Sparse
set_option mvcgen.warning false
set_option linter.deprecated.syntax false

/-- The cell scan's state: the nontrivial cells' starts and sizes, the
vertex-to-cell indices and the next position. -/
structure Cells where
  starts : Array Nat
  sizes : Array Nat
  nntcell : Array Nat
  first : Nat

/-- Mark the vertices at positions `l` of `lab` as in cell `idx`. -/
def mark (lab : Array Nat) (idx : Nat) (a : Array Nat) (l : List Nat) : Array Nat :=
  l.foldl (fun a j => a.set! lab[j]! idx) a

/-- One cell of the scan. -/
def cellStep (lab ptn : Array Nat) (level : Nat) (s : Cells) : Cells :=
  if s.first < cellEnd ptn level s.first then
    ⟨s.starts.push s.first, s.sizes.push (cellEnd ptn level s.first - s.first + 1),
      mark lab s.starts.size s.nntcell
        (List.range' s.first (cellEnd ptn level s.first + 1 - s.first)),
      cellEnd ptn level s.first + 1⟩
  else ⟨s.starts, s.sizes, s.nntcell, cellEnd ptn level s.first + 1⟩

/-- At most `k` cells of the scan. -/
def cellRun (n : Nat) (lab ptn : Array Nat) (level : Nat) : Nat → Cells → Cells
  | 0, s => s
  | k + 1, s => if n ≤ s.first then s else cellRun n lab ptn level k (cellStep lab ptn level s)

/-- The scan from position 0. -/
def cells (n : Nat) (lab ptn : Array Nat) (level : Nat) : Cells :=
  cellRun n lab ptn level n ⟨#[], #[], Array.replicate n n, 0⟩

/-- The edges of row `v`. -/
abbrev row {n : Nat} (g : Graph n) (v : Nat) : List Nat :=
  List.range' g.offsets[v]! (g.offsets[v + 1]! - g.offsets[v]!)

/-- The first pass over an edge: count a hit on its end's nontrivial cell. -/
def hitStep {n : Nat} (g : Graph n) (nntcell : Array Nat) (hits : Array Nat) (j : Nat) :
    Array Nat :=
  if nntcell[g.neighbor j]! != n then
    hits.set! nntcell[g.neighbor j]! (hits[nntcell[g.neighbor j]!]! + 1)
  else hits

/-- The second pass: count a nontrivial join once, and clear its hits. -/
def countStep {n : Nat} (g : Graph n) (nntcell sizes : Array Nat) (s : Array Nat × Nat) (j : Nat) :
    Array Nat × Nat :=
  if nntcell[g.neighbor j]! != n then
    (s.1.set! nntcell[g.neighbor j]! 0,
      if s.1[nntcell[g.neighbor j]!]! > 0 && s.1[nntcell[g.neighbor j]!]! < sizes[nntcell[g.neighbor j]!]!
      then s.2 + 1 else s.2)
  else s

/-- The joins of vertex `v`: the hits after both passes and the count. -/
def joins {n : Nat} (g : Graph n) (nntcell sizes : Array Nat) (hits : Array Nat) (v : Nat) :
    Array Nat × Nat :=
  (row g v).foldl (countStep g nntcell sizes) ((row g v).foldl (hitStep g nntcell) hits, 0)

/-- Cell `i` against the best so far (`hits`, best index, its count). -/
def pick {n : Nat} (g : Graph n) (lab : Array Nat) (c : Cells) (s : Array Nat × Nat × Nat)
    (i : Nat) : Array Nat × Nat × Nat :=
  let r := joins g c.nntcell c.sizes s.1 lab[c.starts[i]!]!
  (r.1, if r.2 > s.2.2 then i else s.2.1, if r.2 > s.2.2 then r.2 else s.2.2)

/-- The best cell's index. -/
def choose {n : Nat} (g : Graph n) (lab : Array Nat) (c : Cells) : Array Nat × Nat × Nat :=
  (List.range c.starts.size).foldl (pick g lab c) (Array.replicate c.starts.size 0, 0, 0)

theorem cellRun_stop {n : Nat} {lab ptn : Array Nat} {level : Nat} {s : Cells} (h : n ≤ s.first) :
    ∀ k, cellRun n lab ptn level k s = s
  | 0 => rfl
  | _ + 1 => by simp [cellRun, h]

theorem bestcell_eq {n : Nat} (g : Graph n) (lab ptn : Array Nat) (level : Nat) :
    bestcell g lab ptn level =
      if (cells n lab ptn level).starts.isEmpty then n
      else (cells n lab ptn level).starts[(choose g lab (cells n lab ptn level)).2.1]! := by
  unfold bestcell
  apply Id.of_wp_run_eq rfl (fun r => r = _)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, s⟩ => ⌜cellRun n lab ptn level cursor.suffix.length
      ⟨s.1, s.2.1, s.2.2.1, s.2.2.2⟩ = cells n lab ptn level⌝
  | inv2 pref cur suff h b starts s1 sizes s2 nntcell first hf last jp hlt index starts' sizes' hinv =>
      ⇓⟨cursor, a⟩ => ⌜a = mark lab b.1.size b.2.2.1 cursor.prefix⌝
  | inv3 r starts s1 sizes s2 nntcell hne hits hinv1 => ⇓⟨cursor, s⟩ =>
      ⌜s = cursor.prefix.foldl (pick g lab ⟨r.1, r.2.1, r.2.2.1, r.2.2.2⟩)
        (Array.replicate r.1.size 0, 0, 0)⌝
  | inv4 r starts s1 sizes s2 nntcell hne hits hinv1 pref cur suff h b hits' s3 best maxcnt v hinv3 =>
      ⇓⟨cursor, a⟩ => ⌜a = cursor.prefix.foldl (hitStep g r.2.2.1) b.1⌝
  | inv5 r starts s1 sizes s2 nntcell hne hits hinv1 pref cur suff h b hits' s3 best maxcnt v hinv3
      r' hinv4 => ⇓⟨cursor, a⟩ => ⌜a = cursor.prefix.foldl (countStep g r.2.2.1 r.2.1) (r', 0)⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.div_one, List.length_cons, List.length_nil] at *
  case vc1.step.isTrue =>
    have hrun : cellRun n lab ptn level (_ + 1) _ = cells n lab ptn level := ‹_›
    rw [← hrun, cellRun_stop (by omega), cellRun_stop (by omega)]
  case vc2.step =>
    subst ‹_ = mark _ _ _ _›
    simp [mark, List.foldl_append]
  case vc4.step.isFalse.isTrue.post.success =>
    subst ‹_ = mark _ _ _ _›
    have hrun : cellRun n lab ptn level (_ + 1) _ = cells n lab ptn level := ‹_›
    rw [← hrun, cellRun, ite_eq_right (by omega)]
    simp only [cellStep, ite_eq_left ‹_ < cellEnd ptn level _›]
  case vc5.step.isFalse.isFalse =>
    have hrun : cellRun n lab ptn level (_ + 1) _ = cells n lab ptn level := ‹_›
    rw [← hrun, cellRun, ite_eq_right (by omega)]
    simp only [cellStep, ite_eq_right ‹¬ _ < cellEnd ptn level _›]
  case vc6.pre => simp [cells]
  case vc7.post.success.isTrue =>
    have hrun : cellRun n lab ptn level 0 _ = cells n lab ptn level := ‹_›
    simp only [cellRun] at hrun
    rw [← hrun]
    simp_all
  case vc8.step.isTrue =>
    subst ‹_ = List.foldl (hitStep _ _) _ _›
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, hitStep]
    rw [ite_eq_left ‹_›]
  case vc9.step.isFalse =>
    subst ‹_ = List.foldl (hitStep _ _) _ _›
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, hitStep]
    rw [ite_eq_right ‹_›]
  case vc11.step.isTrue.isTrue =>
    subst ‹_ = List.foldl (countStep _ _ _) _ _›
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, countStep]
    rw [ite_eq_left ‹_›]
    simp_all
  case vc12.step.isTrue.isFalse =>
    subst ‹_ = List.foldl (countStep _ _ _) _ _›
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, countStep]
    rw [ite_eq_left ‹_›]
    simp_all
  case vc13.step.isFalse =>
    subst ‹_ = List.foldl (countStep _ _ _) _ _›
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, countStep]
    rw [ite_eq_right ‹_›]
  case vc15.step.post.success.post.success.isTrue =>
    subst ‹_ = List.foldl (pick _ _ _) _ _›
    subst ‹_ = List.foldl (hitStep _ _) _ _›
    subst ‹_ = List.foldl (countStep _ _ _) _ _›
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, pick, joins, row]
    simp only [gt_iff_lt, ‹_ < _›, ite_true]
  case vc16.step.post.success.post.success.isFalse =>
    subst ‹_ = List.foldl (pick _ _ _) _ _›
    subst ‹_ = List.foldl (hitStep _ _) _ _›
    subst ‹_ = List.foldl (countStep _ _ _) _ _›
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, pick, joins, row]
    simp only [gt_iff_lt, ‹¬ _ < _›, ite_false]
  case vc18.post.success.isFalse.post.success =>
    have hrun : cellRun n lab ptn level 0 _ = cells n lab ptn level := ‹_›
    simp only [cellRun] at hrun
    subst ‹_ = List.foldl (pick _ _ _) _ _›
    rw [← hrun]
    simp only [choose, List.range_eq_range']
    rw [ite_eq_right ‹_›]

/-- The count of cell `i`, with the hits the cells before it leave. -/
def countAt {n : Nat} (g : Graph n) (lab : Array Nat) (c : Cells) (i : Nat) : Nat :=
  (joins g c.nntcell c.sizes
    ((List.range i).foldl (pick g lab c) (Array.replicate c.starts.size 0, 0, 0)).1
    lab[c.starts[i]!]!).2

/-- `bestcell_sg`'s final loop: `if (COUNT[i] > maxcnt) { j = i; maxcnt = COUNT[i]; }`. -/
def argStep (cnt : Nat → Nat) (s : Nat × Nat) (i : Nat) : Nat × Nat :=
  if cnt i > s.2 then (i, cnt i) else s

/-- `choose`'s index and count are the C's: `j = 0; maxcnt = COUNT[0];` and
`argStep` from cell 1 (`choose` starts from count 0, which a first count of
0 leaves alone). -/
theorem choose_arg {n : Nat} (g : Graph n) (lab : Array Nat) (c : Cells) :
    ∀ k, 0 < k → ((List.range k).foldl (pick g lab c) (Array.replicate c.starts.size 0, 0, 0)).2 =
      (List.range' 1 (k - 1)).foldl (argStep (countAt g lab c)) (0, countAt g lab c 0)
  | 0, h => absurd h (by omega)
  | 1, _ => by
    simp only [List.range_one, List.foldl_cons, List.foldl_nil, Nat.sub_self, List.range'_zero,
      pick, countAt, List.range_zero]
    by_cases h0 : (joins g c.nntcell c.sizes (Array.replicate c.starts.size 0) lab[c.starts[0]!]!).2 > 0
    · simp only [h0, ite_true]
    · simp only [h0, ite_false]
      congr 1
      omega
  | k + 2, _ => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      show k + 2 - 1 = (k + 1 - 1) + 1 by omega, List.range'_1_concat, List.foldl_append,
      List.foldl_cons, List.foldl_nil, ← choose_arg g lab c (k + 1) (by omega)]
    simp only [pick, argStep, countAt]
    rw [show 1 + (k + 1 - 1) = k + 1 by omega]
    split
    · simp only [‹_ > _›, ite_true]
    · simp only [‹¬ _ > _›, ite_false]

end NautyVerified.Proofs.Sparse.Bestcell
