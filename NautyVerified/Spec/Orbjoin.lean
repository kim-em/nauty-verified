import HexGraphIso.Nauty.Search.Refine
import HexGraphIso.Nauty.Invariant.OrbitComplete

/-!
# HexGraphIso's `orbjoin`, unrolled

HexGraphIso's `orbjoin` is written with `for` loops in `Id.run do`. To compare
it with nauty's C loop by loop, `orbjoin_eq` rewrites it as two folds: `join`
(link the roots of `i` and `map[i]`) over `0 .. n-1`, then `compress` (point
each vertex at its root's parent, counting roots). The chase loops become
`chaseList` with fuel `n`; `chaseList_root` shows that on a descending forest
the fuel is never exhausted, so the chase reaches the root, as nauty's
unbounded `while` loop does.

The unrolling follows `HexGraphIso/Nauty/Invariant/OrbitComplete.lean`, where
the corresponding lemmas are private.
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty Hex.GraphIso.Nauty.Orbit

/-- Follow parent pointers until a root, or until the fuel list runs out. -/
def chaseList (orbits : Array Nat) : List Nat → Nat → Nat
  | [], j => j
  | _ :: l, j => if orbits[j]! == j then j else chaseList orbits l orbits[j]!

theorem forIn_range_eq {β : Type} (n : Nat) (init : β) (f : Nat → β → Id (ForInStep β)) :
    (forIn [:n] init f : Id β) = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [:n].start [:n].size [:n].step = List.range n := by
    simp [List.range_eq_range']
  rw [hrange]

theorem forIn_chase_eq {orbits : Array Nat} :
    ∀ (l : List Nat) (j : Nat),
      (forIn l j (fun _ j =>
        if orbits[j]! == j then pure (ForInStep.done j)
        else pure (ForInStep.yield orbits[j]!)) : Id Nat) =
      chaseList orbits l j
  | [], _ => rfl
  | _ :: l, j => by
    rw [List.forIn_cons, chaseList]
    rcases Decidable.em ((orbits[j]! == j) = true) with hc | hc
    · rw [ite_eq_left hc, ite_eq_left hc]
      rfl
    · rw [ite_eq_right hc, ite_eq_right hc]
      exact forIn_chase_eq l _

/-- One step of `orbjoin`'s first loop: link the roots of `i` and `map[i]`. -/
def join (map : Array Nat) (n : Nat) (o : Array Nat) (i : Nat) : Array Nat :=
  if map[i]! != i then
    let a := chaseList o (List.range n) o[i]!
    let b := chaseList o (List.range n) o[map[i]!]!
    if a < b then o.set! b a else if a > b then o.set! a b else o
  else o

/-- One step of `orbjoin`'s second loop: point `i` at its grandparent and
count it if it is then a root. -/
def compress (s : Array Nat × Nat) (i : Nat) : Array Nat × Nat :=
  let o := s.1.set! i s.1[s.1[i]!]!
  (o, if o[i]! == i then s.2 + 1 else s.2)

theorem forIn_fold {β : Type} (l : List Nat) (f : β → Nat → β) (b : β) :
    (forIn l b (fun i b => pure (ForInStep.yield (f b i))) : Id β) = l.foldl f b := by
  induction l generalizing b with
  | nil => rfl
  | cons i l ih =>
    rw [List.forIn_cons, List.foldl_cons]
    exact ih _

theorem orbjoin_eq (o map : Array Nat) (n : Nat) :
    orbjoin o map n = (List.range n).foldl compress ((List.range n).foldl (join map n) o, 0) := by
  rw [orbjoin]
  simp only [forIn_range_eq, forIn_chase_eq]
  have hjoin : ∀ o : Array Nat,
      (forIn (List.range n) o (fun i o => do
        if map[i]! != i then
          let a := chaseList o (List.range n) o[i]!
          let b := chaseList o (List.range n) o[map[i]!]!
          if a < b then pure (.yield (o.set! b a))
          else if a > b then pure (.yield (o.set! a b))
          else pure (.yield o)
        else pure (.yield o)) : Id (Array Nat)) =
        (List.range n).foldl (join map n) o := by
    intro o
    rw [← forIn_fold]
    congr 1
    funext i o
    simp only [join]
    split <;> try rfl
    split <;> try rfl
    split <;> rfl
  simp only [bind, pure, Id.run] at hjoin ⊢
  rw [hjoin]
  change (forIn (List.range n) _ _ : Id (Array Nat × Nat)) = _
  rw [← forIn_fold (List.range n) compress]
  congr 1
  funext i s
  simp only [compress]
  split <;> rfl

/-! ## The chase reaches the root -/

/-- On a descending forest, chasing from `j` with at least `j + 1` units of
fuel reaches a root, and more fuel changes nothing. -/
theorem chaseList_root {o : Array Nat} {n : Nat} (hd : Descending o n) :
    ∀ (l : List Nat) (j : Nat), j < n → j < l.length →
      (o[chaseList o l j]! = chaseList o l j) ∧ chaseList o l j < n ∧
      ∀ l' : List Nat, j < l'.length → chaseList o l' j = chaseList o l j
  | [], _, _, h => absurd h (by simp)
  | _ :: l, j, hj, hl => by
    have hle := hd.2 j hj
    by_cases hr : o[j]! = j
    · refine ⟨?_, ?_, ?_⟩
      · simp [chaseList, hr]
      · simp [chaseList, hr, hj]
      · intro l' hl'
        cases l' with
        | nil => simp at hl'
        | cons _ l' => simp [chaseList, hr]
    · have hlt : o[j]! < j := by omega
      have ih := chaseList_root hd l o[j]! (by omega) (by simp at hl; omega)
      refine ⟨by simpa [chaseList, hr] using ih.1, by simpa [chaseList, hr] using ih.2.1, ?_⟩
      intro l' hl'
      cases l' with
      | nil => simp at hl'
      | cons _ l' =>
        simp only [chaseList, hr, beq_iff_eq, ite_false]
        exact ih.2.2 l' (by simp at hl'; omega)

theorem chase_lt {o : Array Nat} {n : Nat} (hd : Descending o n) {j : Nat} (hj : j < n) :
    chaseList o (List.range n) j < n :=
  (chaseList_root hd (List.range n) j hj (by simpa using hj)).2.1

/-- `join` keeps the forest descending. -/
theorem join_desc {o map : Array Nat} {n : Nat} (hd : Descending o n) {i : Nat} (hi : i < n)
    (hm : map[i]! < n) : Descending (join map n o i) n := by
  have ha := chase_lt hd (Nat.lt_of_le_of_lt (hd.2 i hi) hi)
  have hb := chase_lt hd (Nat.lt_of_le_of_lt (hd.2 _ hm) hm)
  unfold join
  split
  · dsimp only
    split
    · exact hd.set hb (by omega)
    · split
      · exact hd.set ha (by omega)
      · exact hd
  · exact hd

/-- The first loop of `orbjoin` keeps the forest descending. -/
theorem joins_desc {o map : Array Nat} {n : Nat} (hd : Descending o n)
    (hm : ∀ i < n, map[i]! < n) :
    ∀ k ≤ n, Descending ((List.range k).foldl (join map n) o) n
  | 0, _ => hd
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact join_desc (joins_desc hd hm k (by omega)) (by omega) (hm k (by omega))

end NautyVerified.Spec
