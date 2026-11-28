import NautyVerified.Proofs.Sparse.Refine.Model
import HexGraphIso.Nauty.Sparse.CountNeighbors
import HexGraphIso.Nauty.Sparse.RefineState
import HexGraphIso.Nauty.Sparse.CellClear
import HexGraphIso.Nauty.Sparse.CountBound

/-!
# `splitNontrivial`, phase by phase

HexGraphIso's `splitNontrivial` (`splitNontrivial_eq`) is the count phase
`countPhase` (a fold over the splitter cell's positions, `countVertex`, of a
fold over each position's neighbours, `countEdge`, on the state
`(marks, hits, touched)`), the state `countState` it leaves (marks, hits and
the new stamp in place, hashed with the number of touched cells), then a fold
of `splitCounts` over the sorted touched starts.

`edge_scan`: each neighbour keeps HexGraphIso's `CountScan` (`clear_writes`
for the first-touch clearing). `Fold`: the invariant of the touched-cell fold
(admissible state, a step from `countState`, the count phase's hit counts,
each remaining start a nontrivial cell with its counts bounded), established
by `Fold.initial` from HexGraphIso's `count_neighbors` and carried by
`Fold.next`.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Nontrivial

open Hex.GraphIso.Nauty.Sparse NautyVerified.Spec.SortC
open Hex.GraphIso.Nauty (VSet mash cleanup cellEnd IsCell)

variable {n : Nat}

/-- The count phase's state `(marks, hits, touched)`. -/
abbrev CS := Array Nat × Array Nat × Array Nat

/-- One neighbour `j` of the splitter cell. -/
def countEdge (s : RefineSt n) (c : CS) (j : Nat) : CS :=
  if (s.cellstart[j]! != n) = true then
    if (c.1[s.cellstart[j]!]! != s.stamp + 1) = true then
      let cl := (List.range' s.cellstart[j]! (s.cellend[s.cellstart[j]!]! + 1 - s.cellstart[j]!)).foldl
        (fun h l => h.set! s.lab[l]! 0) c.2.1
      (c.1.set! s.cellstart[j]! (s.stamp + 1), cl.set! j (cl[j]! + 1), c.2.2.push s.cellstart[j]!)
    else (c.1, c.2.1.set! j (c.2.1[j]! + 1), c.2.2)
  else c

/-- The neighbours of the vertex at position `i`. -/
def countVertex (g : Graph n) (s : RefineSt n) (c : CS) (i : Nat) : CS :=
  (List.range' g.offsets[s.lab[i]!]! (g.offsets[s.lab[i]! + 1]! - g.offsets[s.lab[i]!]!)).foldl
    (fun c e => countEdge s c (g.neighbor e)) c

/-- The count phase over the splitter cell at `split`. -/
def countPhase (g : Graph n) (s : RefineSt n) (split : Nat) : CS :=
  (List.range' split (s.cellend[split]! + 1 - split)).foldl (countVertex g s) (s.marks, s.hits, #[])

/-- The state after the count phase, before its hash. -/
def countRaw (g : Graph n) (s : RefineSt n) (split : Nat) : RefineSt n :=
  let c := countPhase g s split
  { s with hits := c.2.1, marks := c.1, stamp := s.stamp + 1 }

/-- The state after the count phase. -/
def countState (g : Graph n) (s : RefineSt n) (split : Nat) : RefineSt n :=
  (countRaw g s split).hash (sortCells (countPhase g s split).2.2).size

theorem forIn_eq_foldl {α β : Type} (l : List α) (b : β) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (h : ∀ x b, f x b = pure (ForInStep.yield (g b x))) :
    forIn (m := Id) l b f = l.foldl g b := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih => rw [List.forIn_cons, h]; exact ih _

theorem splitNontrivial_eq (g : Graph n) (level split : Nat) (s : RefineSt n) :
    splitNontrivial g level split s =
      (sortCells (countPhase g s split).2.2).toList.foldl
        (fun t first => splitCounts level first false t) (countState g s split) := by
  unfold splitNontrivial
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one,
    Nat.add_sub_cancel, forIn_yield, ← Array.forIn_toList]
  rw [forIn_eq_foldl (g := countVertex g s)]
  · rfl
  intro i c
  simp only [countVertex]
  rw [forIn_eq_foldl (g := fun c e => countEdge s c (g.neighbor e))]
  · rfl
  intro e c
  unfold countEdge
  split
  · split
    · rfl
    · rfl
  · rfl

theorem countPhase_eq (G : Hex.SparseGraph n) (s : RefineSt n) (split : Nat) :
    let r : Array Nat × Array Nat × Array Nat := Id.run do
      let mut marks := s.marks
      let mut hits := s.hits
      let mut touched := #[]
      for i in [split:s.cellend[split]! + 1] do
        let vertex := s.lab[i]!
        for e in [G.offsets[vertex]!:G.offsets[vertex + 1]!] do
          let j := (Graph.ofGraph G).neighbor e
          let k := s.cellstart[j]!
          if k != n then
            if marks[k]! != s.stamp + 1 then
              marks := marks.set! k (s.stamp + 1)
              touched := touched.push k
              for l in [k:s.cellend[k]! + 1] do
                hits := hits.set! s.lab[l]! 0
            hits := hits.set! j (hits[j]! + 1)
      return (marks, sortCells touched, hits)
    r = ((countPhase (.ofGraph G) s split).1, sortCells (countPhase (.ofGraph G) s split).2.2,
      (countPhase (.ofGraph G) s split).2.1) := by
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one,
    Nat.add_sub_cancel, forIn_yield]
  rw [forIn_eq_foldl (g := countVertex (.ofGraph G) s)]
  · rfl
  intro i c
  simp only [countVertex]
  rw [forIn_eq_foldl (g := fun c e => countEdge s c ((Graph.ofGraph G).neighbor e))]
  · rfl
  intro e c
  unfold countEdge
  split
  · split
    · rfl
    · rfl
  · rfl

/-- The first-touch clearing of the cell at `k`. -/
theorem clear_writes {hits lab : Array Nat} (hs : hits.size = n) (k : Nat) :
    ∀ (len : Nat), (∀ q, k ≤ q → q < k + len → lab[q]! < n) →
    Index.Writes n hits ((List.range' k len).foldl (fun h l => h.set! lab[l]! 0) hits)
      ((List.range' k len).map fun q => lab[q]!) 0 := by
  intro len
  induction len with
  | zero => intro _; exact Index.Writes.initial hs
  | succ len ih =>
    intro hb
    rw [List.range'_concat, List.foldl_append, List.map_append]
    simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
    rw [Array.set!_eq_setIfInBounds]
    exact (ih fun q h1 h2 => hb q h1 (by omega)).step (hb _ (by omega) (by omega))

/-- One neighbour of the count phase keeps `CountScan`. -/
theorem edge_scan {level : Nat} {s : RefineSt n} (hv : s.Valid level) {c : CS} {seen : List Nat}
    {j : Nat} (hj : j < n)
    (h : CountScan n s.stamp s.marks c.1 c.2.2 s.cellstart c.2.1 seen) :
    CountScan n s.stamp s.marks (countEdge s c j).1 (countEdge s c j).2.2 s.cellstart
      (countEdge s c j).2.1 (seen ++ [j]) := by
  unfold countEdge
  by_cases hk : s.cellstart[j]! = n
  · simp only [hk, bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact h.sentinel hk
  · have hkn : (s.cellstart[j]! != n) = true := by simpa using hk
    simp only [hkn, ite_true]
    have hle := hv.index.vertex_le hv.size hv.closed hv.lab hj
    have hc := hv.index.vertex_cell hv.size hv.closed hv.lab hj hk
    dsimp only at hc
    by_cases hm : c.1[s.cellstart[j]!]! = s.stamp + 1
    · simp only [hm, bne_self_eq_false, Bool.false_eq_true, ite_false]
      have := h.repeated hj (by omega) hm
      rw [← Array.set!_eq_setIfInBounds] at this
      exact this
    · have hmb : (c.1[s.cellstart[j]!]! != s.stamp + 1) = true := by simpa using hm
      simp only [hmb, ite_true]
      have hw := clear_writes (lab := s.lab) h.counts.size s.cellstart[j]!
        (s.cellend[s.cellstart[j]!]! + 1 - s.cellstart[j]!)
        (fun q _ h2 => perm_bound hv.lab (by omega))
      have := h.fresh hj (by omega) hm hw.size (by
        intro v hvn
        rw [hw.get v hvn]
        simp only [hv.index.cell_mem hv.lab hv.size hv.closed (last := s.cellend[s.cellstart[j]!]! + 1)
          (by simpa using hc.1) (by omega) (by omega) hvn])
      simp only [← Array.set!_eq_setIfInBounds] at this
      exact this

/-- The state after the count phase is admissible. -/
theorem countState_valid {level : Nat} (G : Hex.SparseGraph n) {s : RefineSt n} (hv : s.Valid level)
    (split len : Nat) (hc : IsCell s.ptn level split len) (hb : split + len ≤ n) :
    (countState (.ofGraph G) s split).Valid level := by
  have hlen := hc.1
  have he := hv.index.ends_eq split len hc hb (by omega)
  have hscan := count_neighbors G s.lab s.ptn s.cellstart s.cellend s.marks s.hits level s.stamp
    split (s.cellend[split]! + 1) hv.lab hv.size hv.closed hv.index
    ⟨hv.scratch.marks_size, hv.scratch.marks_le⟩ hv.scratch.hits_size (by omega) (by omega)
  rw [countPhase_eq] at hscan
  have hw := hscan.touch.writes
  have h0 : RefineSt.Valid level (countRaw (.ofGraph G) s split) :=
    ⟨hv.lab, hv.size, hv.closed, hv.index,
      ⟨hv.scratch.starts_size, hv.scratch.ends_size, hscan.counts.size, hw.size,
        hv.scratch.vmarks_size, fun i hi => ?_, fun i hi => ?_⟩, hv.queue⟩
  · exact h0.hash _
  · change (countPhase (.ofGraph G) s split).1[i]! ≤ s.stamp + 1
    rw [hw.get i hi]
    split
    · exact Nat.le_refl _
    · have : s.marks[i]! ≤ s.stamp := hv.scratch.marks_le i hi
      omega
  · change s.vmarks[i]! ≤ s.stamp + 1
    have : s.vmarks[i]! ≤ s.stamp := hv.scratch.vmarks_le i hi
    omega

/-- The touched-cell fold of the nontrivial pass at state `b`, with the touched
starts `rest` still to split: `b` is admissible and a step from `s0`, its
hit counts are the count phase's, and each remaining start is a nontrivial
cell of `b` with its original end, its counts at most `len`. -/
structure Fold (level len : Nat) (ends : Array Nat) (s0 b : RefineSt n) (rest : List Nat) : Prop where
  valid : b.Valid level
  step : RefineSt.Step level s0 b
  hits : b.hits = s0.hits
  cells : ∀ a ∈ rest, IsCell b.ptn level a (ends[a]! + 1 - a) ∧ a < ends[a]! ∧ ends[a]! < n ∧
    ∀ q, a ≤ q → q ≤ ends[a]! → b.hits[b.lab[q]!]! ≤ len
  nodup : rest.Nodup

/-- At the head of the fold, the cell has its end in `b`. -/
theorem Fold.head {level len : Nat} {ends : Array Nat} {s0 b : RefineSt n} {cur : Nat} {rest : List Nat}
    (h : Fold level len ends s0 b (cur :: rest)) :
    b.cellend[cur]! = ends[cur]! ∧
      IsCell b.ptn level cur (b.cellend[cur]! + 1 - cur) ∧ cur < b.cellend[cur]! ∧
      b.cellend[cur]! < n ∧ ∀ q, cur ≤ q → q ≤ b.cellend[cur]! → b.hits[b.lab[q]!]! ≤ len := by
  have hc := h.cells cur (by simp)
  have he := h.valid.index.ends_eq cur (ends[cur]! + 1 - cur) hc.1 (by omega) (by omega)
  have he' : b.cellend[cur]! = ends[cur]! := by omega
  rw [he']
  exact ⟨rfl, hc⟩

/-- One count split of the fold. -/
theorem Fold.next {level len : Nat} {ends : Array Nat} {s0 b : RefineSt n} {cur : Nat} {rest : List Nat}
    (h : Fold level len ends s0 b (cur :: rest)) (hs0 : s0.Valid level) (hlen : len ≤ n) :
    Fold level len ends s0 (splitCounts level cur false b) rest := by
  obtain ⟨he, hc, hlt, hb, hk⟩ := h.head
  have hk' : ∀ q, cur ≤ q → q ≤ b.cellend[cur]! → b.hits[b.lab[q]!]! < n + 2 :=
    fun q h1 h2 => by have := hk q h1 h2; omega
  have hn := h.valid.counts cur false hc hb hk'
  have hl : b.lab.size = n := by simpa using h.valid.lab.length_eq
  refine ⟨hn.1, h.step.trans hn.2 hs0 h.valid hn.1,
    (splitCounts_frame level cur false b).hits.trans h.hits, ?_,
    (List.nodup_cons.mp h.nodup).2⟩
  intro a ha
  have hother := h.cells a (List.mem_cons_of_mem _ ha)
  have hne : a ≠ cur := fun e => (List.nodup_cons.mp h.nodup).1 (e ▸ ha)
  have ho := splitCounts_other level cur a (ends[a]! + 1 - a) len false b hl h.valid.size
    (by omega) hb hc hk' hother.1 hne (fun q hq hu => hother.2.2.2 q hq (by omega))
  exact ⟨ho.1, hother.2.1, hother.2.2.1, fun q hq hu => ho.2 q hq (by omega)⟩

/-- The fold starts at the state after the count phase. -/
theorem Fold.initial {level : Nat} (G : Hex.SparseGraph n) {s : RefineSt n} (hv : s.Valid level)
    (split len : Nat) (hc : IsCell s.ptn level split len) (hb : split + len ≤ n) :
    Fold level len s.cellend (countState (.ofGraph G) s split) (countState (.ofGraph G) s split)
      (sortCells (countPhase (.ofGraph G) s split).2.2).toList := by
  have hlen := hc.1
  have he := hv.index.ends_eq split len hc hb (by omega)
  have hscan := count_neighbors G s.lab s.ptn s.cellstart s.cellend s.marks s.hits level s.stamp
    split (s.cellend[split]! + 1) hv.lab hv.size hv.closed hv.index
    ⟨hv.scratch.marks_size, hv.scratch.marks_le⟩ hv.scratch.hits_size (by omega) (by omega)
  rw [countPhase_eq] at hscan
  have hcells := hscan.cells G _ hv.lab hv.size hv.closed hv.index (by
    intro q hq
    simp only [List.mem_range'_1] at hq
    omega)
  have hl : s.cellend[split]! + 1 - split = len := by omega
  refine ⟨countState_valid G hv split len hc hb, RefineSt.Step.refl _ _, rfl, ?_,
    hscan.touch.nodup⟩
  intro a ha
  have := hcells a ha
  simpa only [List.length_range', hl, countState, countRaw, RefineSt.hash] using this

end NautyVerified.Proofs.Sparse.Refine.Nontrivial
