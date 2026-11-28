import NautyVerified.Proofs.Sparse.Refine.Model

/-!
# `splitCounts`, loop by loop

HexGraphIso's `splitCounts level first d s` (one count split of the cell at
`first`) in the shape `refine_sg` runs it: `splitCounts_split` separates the
first run (`firstRun`, spelled out by `firstRun_spec`), the three-way
insertion (`minima`, a fold of `minStep`: `minima_eq`) and `finish`.
`finish_split`: `finish` hashes, stops when the first run is the whole
cell, and otherwise installs the first two fragments (`install2`, with the
second fragment's cell starts `startsLit`, a fold by `startsLit_eq`) and runs
`tail`: either the two fragments are the whole cell, or the rest is sorted,
`big` records the larger of the first two, the later fragments are split off
by `fragLit` (`iterF` of `fragStep`, with the run loop `runStep`:
`fragLit_eq`) and `replace` gives the largest fragment's queue place to the
first when that is not active.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open Hex.GraphIso.Nauty.Sparse NautyVerified.Spec.SortC
open Hex.GraphIso.Nauty (VSet mash cleanup cellEnd IsCell)

variable {n : Nat}

set_option linter.unusedSimpArgs false
/-- One step of the three-way insertion at `j`: state `(w1, v2, w2, v3, lab)`. -/
def minStep (hits : Array Nat) (first : Nat) (st : Nat × Nat × Nat × Nat × Array Nat) (j : Nat) :
    Nat × Nat × Nat × Nat × Array Nat :=
  let (w1, v2, w2, v3, lab) := st
  let lj := lab[j]!
  let w3 := hits[lj]!
  if w3 == w1 then
    let l1 := lab.set! j lab[v3]!
    let l2 := l1.set! v3 l1[v2]!
    (w1, v2 + 1, w2, v3 + 1, l2.set! v2 lj)
  else if w3 == w2 then
    (w1, v2, w2, v3 + 1, (lab.set! j lab[v3]!).set! v3 lj)
  else if w3 < w1 then
    let l1 := lab.set! j lab[v2]!
    let l2 := l1.set! v2 l1[first]!
    (w3, first + 1, w1, v2 + 1, l2.set! first lj)
  else if w3 < w2 then
    (w1, v2, w3, v2 + 1, (lab.set! j lab[v2]!).set! v2 lj)
  else (w1, v2, w2, v3, lab)

theorem minima_eq (lab hits : Array Nat) (cap first last begin : Nat) :
    CountSort.minima lab hits cap first last begin =
      (List.range' begin (last - begin)).foldl (minStep hits first)
        (hits[lab[first]!]!, begin, cap, begin, lab) := by
  unfold CountSort.minima
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  rw [← forIn_yield]
  refine congrArg (forIn (m := Id) (List.range' begin (last - begin)) (hits[lab[first]!]!, begin, cap, begin, lab))
    (funext fun j => funext fun st => ?_)
  rcases st with ⟨w1, v2, w2, v3, lab⟩
  simp only [minStep]
  split <;> (try split) <;> (try split) <;> (try split) <;> rfl
/-- The run loop of one later fragment from `l` with key `w3`: state `(s, k)`. -/
def runStep (l w3 : Nat) (st : RefineSt n × Nat) : ForInStep (RefineSt n × Nat) :=
  if st.1.hits[st.1.lab[st.2 + 1]!]! != w3 then .done st
  else .yield ({ st.1 with cellstart := st.1.cellstart.set! st.1.lab[st.2 + 1]! l }, st.2 + 1)

/-- One later fragment: state `(s, bigpos, bigsize, k)`. -/
def fragStep (level last : Nat) (d : Bool) (st : RefineSt n × Option Nat × Nat × Nat) :
    ForInStep (RefineSt n × Option Nat × Nat × Nat) :=
  let (s, bigpos, bigsize, k) := st
  if k ≥ last - 1 then .done st
  else
    let s := { s with ptn := s.ptn.set! k level, numcells := s.numcells + 1 }
    let s := if d then s.hash k else s
    let l := k + 1
    let s := s.push l
    let w3 := s.hits[s.lab[l]!]!
    let s := if !d then s.hash w3 else s
    let r := iterF (runStep l w3) (last - 1 - l) (s, l)
    let s := { r.1 with cellend := r.1.cellend.set! l r.2 }
    if r.2 - l + 1 == 1 then
      .yield ({ s with cellstart := s.cellstart.set! s.lab[l]! n }, bigpos, bigsize, r.2)
    else
      let s := { s with cellstart := s.cellstart.set! s.lab[l]! l }
      if r.2 - l + 1 > bigsize then .yield (s, some (s.queue.size - 1), r.2 - l + 1, r.2)
      else .yield (s, bigpos, bigsize, r.2)

theorem runLoop_eq (l w3 len k0 : Nat) (s0 : RefineSt n) :
    (forIn (m := Id) (List.range' (k0 + 1) len) (s0, l) fun _ st =>
      if (st.1.hits[st.1.lab[st.2 + 1]!]! != w3) = true then pure (ForInStep.done (st.1, st.2))
      else pure (ForInStep.yield ({ st.1 with cellstart := st.1.cellstart.set! st.1.lab[st.2 + 1]! l },
        st.2 + 1))) =
    forIn (m := Id) (List.range' (k0 + 1) len) (s0, l) fun _ st => runStep l w3 st := by
  refine congrArg (forIn (m := Id) (List.range' (k0 + 1) len) (s0, l))
    (funext fun x => funext fun st => ?_)
  simp only [runStep]
  split <;> rfl

/-- The later-fragment loop of `finish`, as HexGraphIso writes it. -/
def fragLit (level last : Nat) (distance : Bool) (s0 : RefineSt n) (bigpos0 : Option Nat)
    (bigsize0 k0 v3 : Nat) : RefineSt n × Option Nat × Nat × Nat := Id.run do
  let mut s := s0
  let mut bigpos := bigpos0
  let mut bigsize := bigsize0
  let mut k := k0
  for _ in [v3:last] do
    if k >= last - 1 then break
    s := { s with ptn := s.ptn.set! k level, numcells := s.numcells + 1 }
    if distance then s := s.hash k
    let l := k + 1
    s := s.push l
    let w3 := s.hits[s.lab[l]!]!
    if !distance then s := s.hash w3
    k := l
    for _ in [l:last - 1] do
      if s.hits[s.lab[k + 1]!]! != w3 then break
      s := { s with cellstart := s.cellstart.set! s.lab[k + 1]! l }
      k := k + 1
    let size := k - l + 1
    s := { s with cellend := s.cellend.set! l k }
    if size == 1 then
      s := { s with cellstart := s.cellstart.set! s.lab[l]! n }
    else
      s := { s with cellstart := s.cellstart.set! s.lab[l]! l }
      if size > bigsize then
        bigsize := size
        bigpos := some (s.queue.size - 1)
  return (s, bigpos, bigsize, k)

theorem fragLit_eq (level last : Nat) (d : Bool) (s : RefineSt n) (bp : Option Nat)
    (bs k v3 : Nat) :
    fragLit level last d s bp bs k v3 = iterF (fragStep level last d) (last - v3) (s, bp, bs, k) := by
  unfold fragLit
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.add_sub_cancel,
    Nat.div_one]
  rw [← forIn_iter (k := v3)]
  refine congrArg (forIn (m := Id) (List.range' v3 (last - v3)) (s, bp, bs, k))
    (funext fun x => funext fun st => ?_)
  rcases st with ⟨s, bp, bs, k⟩
  simp only [fragStep]
  split
  · rfl
  · cases d <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false] <;>
      rw [← forIn_iter (k := k + 1), runLoop_eq] <;> rfl

/-- The cell starts of the second fragment `[v2, v3)`. -/
def startsLit (lab starts : Array Nat) (v2 v3 : Nat) : Array Nat := Id.run do
  let mut starts := starts
  for k in [v2:v3] do starts := starts.set! lab[k]! v2
  return starts

def finishM (level first last : Nat) (distance : Bool)
    (s : RefineSt n) (w1 v2 w2 v3 : Nat) : RefineSt n := Id.run do
  let mut s := (s.hash (if distance then w2 else w1)).hash v2
  if last == v2 then return s
  let mut starts := s.cellstart
  s := { s with cellstart := #[] }
  if v2 == first + 1 then starts := starts.set! s.lab[first]! n
  if v3 == v2 + 1 then starts := starts.set! s.lab[v2]! n
  else
    starts := startsLit s.lab starts v2 v3
  s := { s with
    cellstart := starts, numcells := s.numcells + 1
    cellend := (s.cellend.set! first (v2 - 1)).set! v2 (v3 - 1)
    ptn := s.ptn.set! (v2 - 1) level }
  if last == v3 then
    if v2 - first <= v3 - v2 && !s.active.mem first then return s.push first
    else return s.push v2
  if !distance then s := s.hash v3
  s := { s with lab := Sort.indirect s.lab s.hits v3 (last - v3) }
  s := s.push v2
  let mut bigpos : Option Nat := none
  let mut bigsize := v2 - first
  if v2 - first < v3 - v2 then
    bigpos := some (s.queue.size - 1)
    bigsize := v3 - v2
    if !distance then s := s.hash bigsize
  let r := fragLit level last distance s bigpos bigsize (v3 - 1) v3
  s := r.1
  bigpos := r.2.1
  if let some pos := bigpos then
    if !s.active.mem first then
      if distance then s := s.hash pos
      s := { s with
        active := (s.active.erase s.queue[pos]!).insert first
        queue := s.queue.set! pos first }
  return s

theorem finish_eqM (level first last : Nat) (d : Bool) (s : RefineSt n) (w1 v2 w2 v3 : Nat) :
    CountSort.finish level first last d s w1 v2 w2 v3 = finishM level first last d s w1 v2 w2 v3 := rfl

/-- The two leading fragments installed. -/
def install2 (level first : Nat) (s : RefineSt n) (v2 v3 : Nat) : RefineSt n :=
  let starts := if v2 == first + 1 then s.cellstart.set! s.lab[first]! n else s.cellstart
  let starts := if v3 == v2 + 1 then starts.set! s.lab[v2]! n else startsLit s.lab starts v2 v3
  { s with
    cellstart := starts, numcells := s.numcells + 1
    cellend := (s.cellend.set! first (v2 - 1)).set! v2 (v3 - 1)
    ptn := s.ptn.set! (v2 - 1) level }

/-- The end: the largest fragment's place goes to the first when that is not active. -/
def replace (first : Nat) (distance : Bool) (s : RefineSt n) (bigpos : Option Nat) : RefineSt n :=
    Id.run do
  let mut s := s
  if let some pos := bigpos then
    if !s.active.mem first then
      if distance then s := s.hash pos
      s := { s with
        active := (s.active.erase s.queue[pos]!).insert first
        queue := s.queue.set! pos first }
  return s

/-- The largest fragment after the first two: state, position, size. -/
def big (first : Nat) (d : Bool) (s : RefineSt n) (v2 v3 : Nat) : RefineSt n × Option Nat × Nat :=
  if v2 - first < v3 - v2 then
    (if !d then s.hash (v3 - v2) else s, some (s.queue.size - 1), v3 - v2)
  else (s, none, v2 - first)

/-- After the first two fragments: either they are the whole cell, or the rest
is sorted and split into later fragments. -/
def tail (level first last : Nat) (d : Bool) (s : RefineSt n) (v2 v3 : Nat) : RefineSt n :=
  if last == v3 then
    if v2 - first <= v3 - v2 && !s.active.mem first then s.push first else s.push v2
  else
    let s := if !d then s.hash v3 else s
    let s := ({ s with lab := Sort.indirect s.lab s.hits v3 (last - v3) }).push v2
    let b := big first d s v2 v3
    let r := fragLit level last d b.1 b.2.1 b.2.2 (v3 - 1) v3
    replace first d r.1 r.2.1

theorem finish_split (level first last : Nat) (d : Bool) (s : RefineSt n) (w1 v2 w2 v3 : Nat) :
    CountSort.finish level first last d s w1 v2 w2 v3 =
      if last == v2 then (s.hash (if d then w2 else w1)).hash v2
      else tail level first last d (install2 level first ((s.hash (if d then w2 else w1)).hash v2) v2 v3)
        v2 v3 := by
  rw [finish_eqM]
  unfold finishM
  generalize (s.hash (if d = true then w2 else w1)).hash v2 = σ
  unfold tail install2 big
  cases h1 : (last == v2) <;> cases h2 : (v2 == first + 1) <;> cases h3 : (v3 == v2 + 1) <;>
    cases h4 : (last == v3) <;>
    simp only [Id.run, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] <;>
    (try rfl) <;> cases d <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;>
    by_cases h5 : v2 - first < v3 - v2 <;> simp only [h5, ↓reduceIte] <;> rfl

/-- One step of the first run: stop at a different key. -/
def runBody (lab hits : Array Nat) (w1 : Nat) (v2 : Nat) : ForInStep Nat :=
  if hits[lab[v2]!]! != w1 then .done v2 else .yield (v2 + 1)

theorem firstRun_eq (lab hits : Array Nat) (first last : Nat) :
    CountSort.firstRun lab hits first last =
      iterF (runBody lab hits hits[lab[first]!]!) (last - (first + 1)) (first + 1) := by
  unfold CountSort.firstRun
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  rw [← forIn_iter (k := first + 1)]
  refine congrArg (forIn (m := Id) (List.range' (first + 1) (last - (first + 1))) (first + 1))
    (funext fun x => funext fun v => ?_)
  simp only [runBody]
  split <;> rfl

theorem iterF_run (lab hits : Array Nat) (w1 : Nat) :
    ∀ (f v u : Nat), v ≤ u → u ≤ v + f → (∀ q, v ≤ q → q < u → hits[lab[q]!]! = w1) →
      (u = v + f ∨ hits[lab[u]!]! ≠ w1) → iterF (runBody lab hits w1) f v = u
  | 0, v, u, h1, h2, _, _ => by simp only [iterF]; omega
  | f + 1, v, u, h1, h2, heq, hstop => by
    simp only [iterF, runBody]
    by_cases hvu : v = u
    · subst hvu
      rcases hstop with h | h
      · omega
      · simp [h]
    · have := heq v (Nat.le_refl _) (by omega)
      simp only [this, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact iterF_run lab hits w1 f (v + 1) u (by omega) (by omega) (fun q h h' => heq q (by omega) h')
        (by omega)

/-- The first run ends at `u`. -/
theorem firstRun_spec (lab hits : Array Nat) {first last u : Nat} (h1 : first + 1 ≤ u) (h2 : u ≤ last)
    (heq : ∀ q, first + 1 ≤ q → q < u → hits[lab[q]!]! = hits[lab[first]!]!)
    (hstop : u = last ∨ hits[lab[u]!]! ≠ hits[lab[first]!]!) :
    CountSort.firstRun lab hits first last = u := by
  rw [firstRun_eq]
  exact iterF_run lab hits _ _ _ u h1 (by omega) heq (by omega)

theorem startsLit_eq (lab starts : Array Nat) (v2 v3 : Nat) :
    startsLit lab starts v2 v3 = (List.range' v2 (v3 - v2)).foldl (fun a k => a.set! lab[k]! v2) starts := by
  unfold startsLit
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  rw [← forIn_yield]
  rfl

theorem splitCounts_split (level first : Nat) (d : Bool) (s : RefineSt n) :
    splitCounts level first d s =
      if CountSort.firstRun s.lab s.hits first (s.cellend[first]! + 1) == s.cellend[first]! + 1 then
        s.hash first
      else
        let m := CountSort.minima s.lab s.hits (n + 2) first (s.cellend[first]! + 1)
          (CountSort.firstRun s.lab s.hits first (s.cellend[first]! + 1))
        CountSort.finish level first (s.cellend[first]! + 1) d { s.hash first with lab := m.2.2.2.2 }
          m.1 m.2.1 m.2.2.1 m.2.2.2.1 := by
  unfold splitCounts
  rfl

end NautyVerified.Proofs.Sparse.Refine.Count
