import HexGraphIso.Nauty.Sparse.SingletonTrace
import NautyVerified.Spec.SparseSort

/-!
# `splitSingleton`, loop by loop

HexGraphIso's singleton splitter with each loop `refine_sg`'s `trivial`
runs written as a `foldl` of a step function: the neighbour scan
(`markStep`), the partition of one touched cell into untouched and touched
vertices (`partStep`), and the reverse write-back of the touched ones
(`revStep`). `cellT` is one touched cell (HexGraphIso's body `cellDo` with
these folds, `cellT_eq`) and `splitSingleton_eq` the whole pass.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Trivial

open Hex.GraphIso.Nauty.Sparse NautyVerified.Spec.SortC

variable {n : Nat}

/-- One edge of the neighbour scan: state `(marks, touched, hit vertices)`. -/
def markStep (g : Graph n) (starts : Array Nat) (stamp : Nat)
    (r : Array Nat × Array Nat × Array Nat) (e : Nat) : Array Nat × Array Nat × Array Nat :=
  if (starts[g.neighbor e]! != n && r.1[starts[g.neighbor e]!]! != stamp) = true then
    (r.1.set! starts[g.neighbor e]! stamp, r.2.1.push starts[g.neighbor e]!,
      r.2.2.set! (g.neighbor e) stamp)
  else (r.1, r.2.1, r.2.2.set! (g.neighbor e) stamp)

/-- The neighbour scan of `vertex`. -/
def markScan (g : Graph n) (starts marks vmarks : Array Nat) (stamp vertex : Nat) :
    Array Nat × Array Nat × Array Nat :=
  (List.range' g.offsets[vertex]! (g.offsets[vertex + 1]! - g.offsets[vertex]!)).foldl
    (markStep g starts stamp) (marks, #[], vmarks)

/-- One position of the partition: state `(lab, v2, hit)`. -/
def partStep (vm : Array Nat) (stamp : Nat) (st : Array Nat × Nat × Array Nat) (j : Nat) :
    Array Nat × Nat × Array Nat :=
  if (vm[st.1[j]!]! == stamp) = true then (st.1, st.2.1, st.2.2.push st.1[j]!)
  else (st.1.set! st.2.1 st.1[j]!, st.2.1 + 1, st.2.2)

/-- One touched vertex written back: state `(lab, starts, v3)`. -/
def revStep (v2 : Nat) (hit : Array Nat) (st : Array Nat × Array Nat × Nat) (t : Nat) :
    Array Nat × Array Nat × Nat :=
  (st.1.set! st.2.2 hit[hit.size - 1 - t]!, st.2.1.set! hit[hit.size - 1 - t]! v2, st.2.2 + 1)

/-- One touched cell, as HexGraphIso's `splitSingleton` writes it. -/
def cellDo (level stamp first : Nat) (s : RefineSt n) : RefineSt n := Id.run do
  let mut s := s.hash first
  let last := s.cellend[first]! + 1
  let mut lab := s.lab
  s := { s with lab := #[] }
  let mut v2 := first
  let mut hit := #[]
  for j in [first:last] do
    let v := lab[j]!
    if s.vmarks[v]! == stamp then hit := hit.push v
    else
      lab := lab.set! v2 v
      v2 := v2 + 1
  s := s.hash hit.size
  let mut starts := s.cellstart
  s := { s with cellstart := #[] }
  let mut v3 := v2
  for t in [0:hit.size] do
    let j := hit[hit.size - 1 - t]!
    starts := starts.set! j v2
    lab := lab.set! v3 j
    v3 := v3 + 1
  if v2 != v3 && v2 != first then
    if v2 == first + 1 then starts := starts.set! lab[first]! n
    if v3 == v2 + 1 then starts := starts.set! lab[v2]! n
    s := { s with
      numcells := s.numcells + 1, ptn := s.ptn.set! (v2 - 1) level
      cellend := (s.cellend.set! first (v2 - 1)).set! v2 (v3 - 1) }
    s := s.hash v2
    if v2 - first <= v3 - v2 && !s.active.mem first then s := s.push first
    else s := s.push v2
  return { s with lab, cellstart := starts }

theorem ite_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

/-- `cellDo` with its two loops as folds. -/
def cellT (level stamp first : Nat) (s : RefineSt n) : RefineSt n := Id.run do
  let mut s := s.hash first
  let last := s.cellend[first]! + 1
  let p := (List.range' first (last - first)).foldl (partStep s.vmarks stamp) (s.lab, first, #[])
  let mut lab := p.1
  s := { s with lab := #[] }
  let mut v2 := p.2.1
  let hit := p.2.2
  s := s.hash hit.size
  let r := (List.range' 0 hit.size).foldl (revStep v2 hit) (lab, s.cellstart, v2)
  let mut starts := r.2.1
  s := { s with cellstart := #[] }
  lab := r.1
  let mut v3 := r.2.2
  if v2 != v3 && v2 != first then
    if v2 == first + 1 then starts := starts.set! lab[first]! n
    if v3 == v2 + 1 then starts := starts.set! lab[v2]! n
    s := { s with
      numcells := s.numcells + 1, ptn := s.ptn.set! (v2 - 1) level
      cellend := (s.cellend.set! first (v2 - 1)).set! v2 (v3 - 1) }
    s := s.hash v2
    if v2 - first <= v3 - v2 && !s.active.mem first then s := s.push first
    else s := s.push v2
  return { s with lab, cellstart := starts }

theorem part_loop (vm : Array Nat) (stamp : Nat) (l : List Nat) (init : Array Nat × Nat × Array Nat) :
    (forIn (m := Id) l init fun j r =>
      if (vm[r.1[j]!]! == stamp) = true then pure (ForInStep.yield (r.1, r.2.1, r.2.2.push r.1[j]!))
      else pure (ForInStep.yield (r.1.set! r.2.1 r.1[j]!, r.2.1 + 1, r.2.2))) =
      l.foldl (partStep vm stamp) init := by
  simp only [ite_yield]
  exact forIn_yield l _ init

theorem rev_loop (v2 : Nat) (hit : Array Nat) (l : List Nat) (init : Array Nat × Array Nat × Nat) :
    (forIn (m := Id) l init fun t r =>
      pure (ForInStep.yield (r.1.set! r.2.2 hit[hit.size - 1 - t]!,
        r.2.1.set! hit[hit.size - 1 - t]! v2, r.2.2 + 1))) =
      l.foldl (revStep v2 hit) init :=
  forIn_yield l _ init

theorem cellT_eq (level stamp first : Nat) (s : RefineSt n) :
    cellDo level stamp first s = cellT level stamp first s := by
  unfold cellDo cellT
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, part_loop, rev_loop]
  rfl

theorem splitSingleton_do (g : Graph n) (level split : Nat) (s : RefineSt n) :
    splitSingleton g level split s =
      let r : Array Nat × Array Nat × Array Nat := Id.run do
        let mut marks := s.marks
        let mut touched := #[]
        let mut hitVertices := s.vmarks
        for e in [g.offsets[s.lab[split]!]!:g.offsets[s.lab[split]! + 1]!] do
          let j := g.neighbor e
          hitVertices := hitVertices.set! j (s.stamp + 1)
          let k := s.cellstart[j]!
          if k != n && marks[k]! != s.stamp + 1 then
            marks := marks.set! k (s.stamp + 1)
            touched := touched.push k
        return (marks, touched, hitVertices)
      let touched := sortCells r.2.1
      Id.run do
        let mut t := ({ s with marks := r.1, vmarks := r.2.2, stamp := s.stamp + 1 } : RefineSt n).hash
          touched.size
        for first in touched do t := cellDo level (s.stamp + 1) first t
        return t := by
  unfold splitSingleton cellDo
  simp only [Id.run, bind, pure, apply_ite ForInStep.yield]

theorem mark_loop (g : Graph n) (starts : Array Nat) (stamp : Nat) (l : List Nat)
    (init : Array Nat × Array Nat × Array Nat) :
    (forIn (m := Id) l init fun e r =>
      if (starts[g.neighbor e]! != n && r.1[starts[g.neighbor e]!]! != stamp) = true then
        pure (ForInStep.yield (r.1.set! starts[g.neighbor e]! stamp, r.2.1.push starts[g.neighbor e]!,
          r.2.2.set! (g.neighbor e) stamp))
      else pure (ForInStep.yield (r.1, r.2.1, r.2.2.set! (g.neighbor e) stamp))) =
      l.foldl (markStep g starts stamp) init := by
  simp only [ite_yield]
  exact forIn_yield l _ init

theorem splitSingleton_eq (g : Graph n) (level split : Nat) (s : RefineSt n) :
    splitSingleton g level split s =
      let r := markScan g s.cellstart s.marks s.vmarks (s.stamp + 1) s.lab[split]!
      (sortCells r.2.1).toList.foldl (fun t first => cellT level (s.stamp + 1) first t)
        (({ s with marks := r.1, vmarks := r.2.2, stamp := s.stamp + 1 } : RefineSt n).hash
          (sortCells r.2.1).size) := by
  rw [splitSingleton_do]
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, ← Array.forIn_toList, mark_loop, forIn_yield, cellT_eq]
  rfl

end NautyVerified.Proofs.Sparse.Refine.Trivial
