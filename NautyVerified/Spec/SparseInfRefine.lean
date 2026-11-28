import NautyVerified.Spec.SearchInf
import HexGraphIso.Nauty.Sparse.Search
import HexGraphIso.Nauty.Sparse.CountParts
import HexGraphIso.Nauty.Sparse.RefineParts

/-!
# Sparse refinement does not depend on the value written for "infinity"

The sparse counterpart of `Spec/SearchInf.lean`'s refinement section.
`Sparse.refineWith` reads `ptn` only through comparisons `ptn[i]! ≤ level`
(directly and through `cellEnd` in `indexCells`) and writes only `level` into
it, so with `level` below both `a` and `b` it commutes with mapping `ptn`
through `phi a b` (`refineWith_map`). `maketargetCached` reads `ptn` only
through comparisons (`maketargetCached_congr`).

The splitting procedures `splitSingleton`, `splitNontrivial` and
`CountSort.finish` never read `ptn`. Their `for` loops are restated through
small named loop bodies, equal to the executed ones by `rfl`, so each
commutation is proved one loop body at a time (`forIn_comm`).
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {n : Nat}

/-! ## Read-only uses of `ptn` -/

theorem indexCells_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q)
    (lab starts ends : Array Nat) :
    Sparse.indexCells n lab p level starts ends = Sparse.indexCells n lab q level starts ends := by
  unfold Sparse.indexCells
  simp only [cellEnd_congr h]

theorem sparse_bestcell_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q)
    (g : Sparse.Graph n) (lab : Array Nat) :
    Sparse.bestcell g lab p level = Sparse.bestcell g lab q level := by
  unfold Sparse.bestcell
  simp only [cellEnd_congr h]

theorem sparse_targetcell_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q)
    (g : Sparse.Graph n) (lab : Array Nat) (tcLevel : Nat) (hint : Int) :
    Sparse.targetcell g lab p level tcLevel hint = Sparse.targetcell g lab q level tcLevel hint := by
  unfold Sparse.targetcell
  simp only [sparse_bestcell_congr h, GT.gt, h.2, h.le]

theorem sparse_maketargetcell_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q)
    (g : Sparse.Graph n) (lab : Array Nat) (tcLevel : Nat) (hint : Int) :
    Sparse.maketargetcell g lab p level tcLevel hint = Sparse.maketargetcell g lab q level tcLevel hint := by
  unfold Sparse.maketargetcell
  simp only [sparse_targetcell_congr h, cellEnd_congr h]

theorem maketargetCached_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q)
    (g : Sparse.Graph n) (lab : Array Nat) (tcLevel : Nat) (hint : Int) (s : Sparse.Scratch) :
    Sparse.maketargetCached g lab p level tcLevel hint s =
      Sparse.maketargetCached g lab q level tcLevel hint s := by
  unfold Sparse.maketargetCached Sparse.maketargetcell
  simp only [sparse_targetcell_congr h, cellEnd_congr h, GT.gt, h.2, h.le]

/-! ## Loops commuting with a map of their state -/

/-- `s` with its `ptn` mapped. -/
def mapS (f : Nat → Nat) (s : Sparse.RefineSt n) : Sparse.RefineSt n := { s with ptn := s.ptn.map f }

/-- A loop step with its state mapped by `F`. -/
def stepMap {α β : Type} (F : α → β) : Id (ForInStep α) → Id (ForInStep β)
  | .done a => .done (F a)
  | .yield a => .yield (F a)

theorem forIn_comm {α β γ : Type} (F : α → β) (xs : List γ) (f : γ → α → Id (ForInStep α))
    (g : γ → β → Id (ForInStep β)) (h : ∀ x a, g x (F a) = stepMap F (f x a)) (a : α) :
    forIn xs (F a) g = F (forIn xs a f) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons, h]
    cases f x a with
    | done b => rfl
    | yield b => exact ih b

theorem forIn_range_comm {α β : Type} (F : α → β) (lo hi : Nat) (f : Nat → α → Id (ForInStep α))
    (g : Nat → β → Id (ForInStep β)) (h : ∀ x a, g x (F a) = stepMap F (f x a)) (a : α) :
    forIn [lo:hi] (F a) g = F (forIn [lo:hi] a f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn_comm F _ f g h a

section
variable (f : Nat → Nat) (s : Sparse.RefineSt n)
@[simp] theorem mapS_lab : (mapS f s).lab = s.lab := rfl
@[simp] theorem mapS_ptn : (mapS f s).ptn = s.ptn.map f := rfl
@[simp] theorem mapS_active : (mapS f s).active = s.active := rfl
@[simp] theorem mapS_queue : (mapS f s).queue = s.queue := rfl
@[simp] theorem mapS_cellstart : (mapS f s).cellstart = s.cellstart := rfl
@[simp] theorem mapS_cellend : (mapS f s).cellend = s.cellend := rfl
@[simp] theorem mapS_indexed : (mapS f s).indexed = s.indexed := rfl
@[simp] theorem mapS_hits : (mapS f s).hits = s.hits := rfl
@[simp] theorem mapS_marks : (mapS f s).marks = s.marks := rfl
@[simp] theorem mapS_vmarks : (mapS f s).vmarks = s.vmarks := rfl
@[simp] theorem mapS_stamp : (mapS f s).stamp = s.stamp := rfl
@[simp] theorem mapS_numcells : (mapS f s).numcells = s.numcells := rfl
@[simp] theorem mapS_longcode : (mapS f s).longcode = s.longcode := rfl
theorem mapS_hash (v : Nat) : (mapS f s).hash v = mapS f (s.hash v) := rfl
theorem mapS_push (v : Nat) : (mapS f s).push v = mapS f (s.push v) := rfl
end

theorem forIn_map1 {γ : Type} {f : Nat → Nat} {xs : List γ}
    {g : γ → Sparse.RefineSt n → Id (ForInStep (Sparse.RefineSt n))}
    (h : ∀ x a, g x (mapS f a) = stepMap (mapS f) (g x a)) (a : Sparse.RefineSt n) :
    forIn xs (mapS f a) g = mapS f (forIn xs a g) := forIn_comm _ xs g g h a

theorem arr_map1 {γ : Type} {f : Nat → Nat} {xs : Array γ}
    {g : γ → Sparse.RefineSt n → Id (ForInStep (Sparse.RefineSt n))}
    (h : ∀ x a, g x (mapS f a) = stepMap (mapS f) (g x a)) (a : Sparse.RefineSt n) :
    forIn xs (mapS f a) g = mapS f (forIn xs a g) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact forIn_comm _ _ g g h a

theorem range_map1 {f : Nat → Nat} {lo hi : Nat}
    {g : Nat → Sparse.RefineSt n → Id (ForInStep (Sparse.RefineSt n))}
    (h : ∀ x a, g x (mapS f a) = stepMap (mapS f) (g x a)) (a : Sparse.RefineSt n) :
    forIn [lo:hi] (mapS f a) g = mapS f (forIn [lo:hi] a g) :=
  forIn_range_comm _ lo hi g g h a

theorem range_map2 {β : Type} {f : Nat → Nat} {lo hi : Nat}
    {g : Nat → Sparse.RefineSt n × β → Id (ForInStep (Sparse.RefineSt n × β))}
    (h : ∀ x a b, g x (mapS f a, b) = stepMap (fun p => (mapS f p.1, p.2)) (g x (a, b)))
    (a : Sparse.RefineSt n) (b : β) :
    forIn [lo:hi] (mapS f a, b) g = (mapS f (forIn [lo:hi] (a, b) g).1, (forIn [lo:hi] (a, b) g).2) :=
  forIn_range_comm (fun p => (mapS f p.1, p.2)) lo hi g g (fun x p => h x p.1 p.2) (a, b)

theorem stepMap_yield {α β : Type} (F : α → β) (x : α) :
    stepMap F (pure (ForInStep.yield x) : Id _) = pure (ForInStep.yield (F x)) := rfl

theorem stepMap_done {α β : Type} (F : α → β) (x : α) :
    stepMap F (pure (ForInStep.done x) : Id _) = pure (ForInStep.done (F x)) := rfl

theorem stepMap_bind {α β γ : Type} (F : α → β) (x : Id γ) (k : γ → Id (ForInStep α)) :
    stepMap F (x >>= k) = x >>= fun y => stepMap F (k y) := rfl

theorem stepMap_ite {α β : Type} (F : α → β) (c : Prop) [Decidable c] (x y : Id (ForInStep α)) :
    stepMap F (if c then x else y) = if c then stepMap F x else stepMap F y := by
  split <;> rfl

theorem mk_map (f : Nat → Nat) (l p : Array Nat) (a : VSet n) (q cs ce : Array Nat) (ix : Bool)
    (h m vm : Array Nat) (st nc lc : Nat) :
    (Sparse.RefineSt.mk l (p.map f) a q cs ce ix h m vm st nc lc) =
      mapS f (Sparse.RefineSt.mk l p a q cs ce ix h m vm st nc lc) := rfl

/-- Split an `if` on the left against `mapS` of the same `if` on the right. -/
macro "ite_map" f:term : tactic =>
  `(tactic| (rw [apply_ite (mapS $f)]; refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)))

/-- Split an `if` and reduce both sides. -/
macro "ite_close" : tactic => `(tactic| (split <;> (rename_i h; (try simp only [h, ↓reduceIte,
  Bool.false_eq_true]) <;> rfl)))

/-- Push `mapS` outwards through field reads, `hash`, `push` and the writes of `level`. -/
macro "map_norm" h:term : tactic => `(tactic| simp only [← set_phi $h, mapS_lab, mapS_ptn,
  mapS_active, mapS_queue, mapS_cellstart, mapS_cellend, mapS_indexed, mapS_hits, mapS_marks,
  mapS_vmarks, mapS_stamp, mapS_numcells, mapS_longcode, mapS_hash, mapS_push, mk_map])

/-! ## `CountSort.finish` -/

namespace Finish

local notation "RefineSt" => Sparse.RefineSt

/-- The run loop after a later count fragment's start. -/
def run (l w3 : Nat) (_ : Nat) (st : RefineSt n × Nat) : Id (ForInStep (RefineSt n × Nat)) :=
  have s := st.fst
  have k := st.snd
  if (s.hits[s.lab[k + 1]!]! != w3) = true then pure (ForInStep.done (s, k))
  else
    have s := { s with cellstart := s.cellstart.set! s.lab[k + 1]! l }
    have k := k + 1
    pure (ForInStep.yield (s, k))

/-- The fragment's end and the largest-fragment update. -/
def frag (l : Nat) (bigpos : Option Nat) (bigsize : Nat) (r : RefineSt n × Nat) :
    Id (ForInStep (RefineSt n × Option Nat × Nat × Nat)) :=
  have s := r.fst
  have k := r.snd
  have size := k - l + 1
  have s := { s with cellend := s.cellend.set! l k }
  if (size == 1) = true then
    have s := { s with cellstart := s.cellstart.set! s.lab[l]! n }
    pure (ForInStep.yield (s, bigpos, bigsize, k))
  else
    have s := { s with cellstart := s.cellstart.set! s.lab[l]! l }
    if size > bigsize then
      have bigsize := size
      have bigpos := some (s.queue.size - 1)
      pure (ForInStep.yield (s, bigpos, bigsize, k))
    else pure (ForInStep.yield (s, bigpos, bigsize, k))

def jp2 (last l w3 : Nat) (bigpos : Option Nat) (bigsize : Nat) (s : RefineSt n) :
    Id (ForInStep (RefineSt n × Option Nat × Nat × Nat)) :=
  frag l bigpos bigsize (forIn (m := Id) [l:last - 1] (s, l) (run l w3))

def jp1 (last : Nat) (distance : Bool) (k : Nat) (bigpos : Option Nat) (bigsize : Nat)
    (s : RefineSt n) : Id (ForInStep (RefineSt n × Option Nat × Nat × Nat)) :=
  have l := k + 1
  have s := s.push l
  have w3 := s.hits[s.lab[l]!]!
  if (!distance) = true then jp2 last l w3 bigpos bigsize (s.hash w3)
  else jp2 last l w3 bigpos bigsize s

/-- One step of the loop over the later count fragments. -/
def step (level last : Nat) (distance : Bool) (_ : Nat) (st : RefineSt n × Option Nat × Nat × Nat) :
    Id (ForInStep (RefineSt n × Option Nat × Nat × Nat)) :=
  have s := st.fst
  have bigpos := st.snd.fst
  have bigsize := st.snd.snd.fst
  have k := st.snd.snd.snd
  if k ≥ last - 1 then pure (ForInStep.done (s, bigpos, bigsize, k))
  else
    have s := { s with ptn := s.ptn.set! k level, numcells := s.numcells + 1 }
    if distance = true then jp1 last distance k bigpos bigsize (s.hash k)
    else jp1 last distance k bigpos bigsize s

/-- The largest fragment's activation. -/
def tail (first : Nat) (distance : Bool) (r : RefineSt n × Option Nat × Nat × Nat) : RefineSt n :=
  match r.snd.fst with
  | some pos =>
    if (!r.fst.active.mem first) = true then
      if distance = true then
        { r.fst.hash pos with
          active := ((r.fst.hash pos).active.erase (r.fst.hash pos).queue[pos]!).insert first
          queue := (r.fst.hash pos).queue.set! pos first }
      else
        { r.fst with
          active := (r.fst.active.erase r.fst.queue[pos]!).insert first
          queue := r.fst.queue.set! pos first }
    else r.fst
  | _ => r.fst

def part4 (level first last : Nat) (distance : Bool) (v3 : Nat) (s : RefineSt n) (bigpos : Option Nat)
    (bigsize : Nat) : RefineSt n :=
  tail first distance (forIn (m := Id) [v3:last] (s, bigpos, bigsize, v3 - 1) (step level last distance))

def part3 (level first last : Nat) (distance : Bool) (v2 v3 : Nat) (s : RefineSt n) : RefineSt n :=
  have s := { s with lab := Sparse.Sort.indirect s.lab s.hits v3 (last - v3) }
  have s := s.push v2
  if v2 - first < v3 - v2 then
    if (!distance) = true then
      part4 level first last distance v3 (s.hash (v3 - v2)) (some (s.queue.size - 1)) (v3 - v2)
    else part4 level first last distance v3 s (some (s.queue.size - 1)) (v3 - v2)
  else part4 level first last distance v3 s none (v2 - first)

def part2 (level first last : Nat) (distance : Bool) (v2 v3 : Nat) (s : RefineSt n) (starts : Array Nat) :
    RefineSt n :=
  have s := { s with
    ptn := s.ptn.set! (v2 - 1) level
    cellstart := starts
    cellend := (s.cellend.set! first (v2 - 1)).set! v2 (v3 - 1)
    numcells := s.numcells + 1 }
  if (last == v3) = true then
    if (decide (v2 - first ≤ v3 - v2) && !s.active.mem first) = true then s.push first
    else s.push v2
  else
    if (!distance) = true then part3 level first last distance v2 v3 (s.hash v3)
    else part3 level first last distance v2 v3 s

/-- The second fragment's cell indices, then the rest. -/
def mid (level first last : Nat) (distance : Bool) (v2 v3 : Nat) (s : RefineSt n) (starts : Array Nat) :
    RefineSt n :=
  if (v3 == v2 + 1) = true then part2 level first last distance v2 v3 s (starts.set! s.lab[v2]! n)
  else part2 level first last distance v2 v3 s
    (forIn (m := Id) [v2:v3] starts fun k starts => pure (ForInStep.yield (starts.set! s.lab[k]! v2)))

def finish (level first last : Nat) (distance : Bool) (s : RefineSt n) (w1 v2 w2 v3 : Nat) : RefineSt n :=
  have s := (s.hash (if distance = true then w2 else w1)).hash v2
  if (last == v2) = true then s
  else if (v2 == first + 1) = true then
    mid level first last distance v2 v3 s (s.cellstart.set! s.lab[first]! n)
  else mid level first last distance v2 v3 s s.cellstart

theorem finish_eq (level first last : Nat) (distance : Bool) (s : RefineSt n) (w1 v2 w2 v3 : Nat) :
    Sparse.CountSort.finish level first last distance s w1 v2 w2 v3 =
      finish level first last distance s w1 v2 w2 v3 := by
  rfl

section
variable {f : Nat → Nat}

/-- `mapS` on the first component. -/
abbrev mapP {β : Type} (f : Nat → Nat) (p : RefineSt n × β) : RefineSt n × β := (mapS f p.1, p.2)

theorem run_map (l w3 x : Nat) (s : RefineSt n) (k : Nat) :
    run l w3 x (mapS f s, k) = stepMap (mapP f) (run l w3 x (s, k)) := by
  unfold run
  dsimp only
  simp only [mapS_lab, mapS_hits]
  ite_close

theorem runs_map (l w3 last : Nat) (s : RefineSt n) (k : Nat) :
    forIn (m := Id) [l:last - 1] (mapS f s, k) (run l w3) =
      mapP f (forIn (m := Id) [l:last - 1] (s, k) (run l w3)) :=
  forIn_range_comm (mapP f) _ _ _ _ (fun x p => run_map l w3 x p.1 p.2) (s, k)

theorem frag_map (l : Nat) (bigpos : Option Nat) (bigsize : Nat) (r : RefineSt n × Nat) :
    frag l bigpos bigsize (mapP f r) = stepMap (mapP f) (frag l bigpos bigsize r) := by
  unfold frag
  dsimp only
  split
  · rfl
  · ite_close

theorem jp2_map (last l w3 : Nat) (bigpos : Option Nat) (bigsize : Nat) (s : RefineSt n) :
    jp2 last l w3 bigpos bigsize (mapS f s) = stepMap (mapP f) (jp2 last l w3 bigpos bigsize s) := by
  unfold jp2
  rw [runs_map, frag_map]

theorem jp1_map (last : Nat) (distance : Bool) (k : Nat) (bigpos : Option Nat) (bigsize : Nat)
    (s : RefineSt n) :
    jp1 last distance k bigpos bigsize (mapS f s) =
      stepMap (mapP f) (jp1 last distance k bigpos bigsize s) := by
  unfold jp1
  dsimp only
  simp only [mapS_push, mapS_hash, mapS_lab, mapS_hits, jp2_map]
  ite_close

end

section
variable {a b level : Nat} (hL : level ≠ a)
include hL

theorem step_map (last : Nat) (distance : Bool) (x : Nat) (s : RefineSt n) (rest : Option Nat × Nat × Nat) :
    step level last distance x (mapS (phi a b) s, rest) =
      stepMap (mapP (phi a b)) (step level last distance x (s, rest)) := by
  unfold step
  dsimp only
  split
  · rfl
  · have e : ({ mapS (phi a b) s with
        ptn := (mapS (phi a b) s).ptn.set! rest.2.2 level,
        numcells := (mapS (phi a b) s).numcells + 1 } : RefineSt n) =
        mapS (phi a b) { s with ptn := s.ptn.set! rest.2.2 level, numcells := s.numcells + 1 } := by
      simp only [mapS, mapS_ptn, set_phi hL]
    rw [e]
    simp only [mapS_hash, jp1_map]
    ite_close

theorem part4_map (first last : Nat) (distance : Bool) (v3 : Nat) (s : RefineSt n) (bigpos : Option Nat)
    (bigsize : Nat) :
    part4 level first last distance v3 (mapS (phi a b) s) bigpos bigsize =
      mapS (phi a b) (part4 level first last distance v3 s bigpos bigsize) := by
  unfold part4
  rw [show ((mapS (phi a b) s, bigpos, bigsize, v3 - 1) : RefineSt n × Option Nat × Nat × Nat) =
    mapP (phi a b) (s, bigpos, bigsize, v3 - 1) from rfl,
    forIn_range_comm (mapP (phi a b)) _ _ _ _ (fun x p => step_map hL last distance x p.1 p.2)]
  generalize forIn (m := Id) [v3:last] (s, bigpos, bigsize, v3 - 1) (step level last distance) = r
  obtain ⟨r1, _ | pos, r3⟩ := r
  · rfl
  · unfold tail
    dsimp only
    simp only [mapS_active, mapS_queue, mapS_hash]
    cases distance <;> by_cases h : (!r1.active.mem first) = true <;>
      simp only [h, ↓reduceIte, Bool.false_eq_true] <;> rfl

theorem part3_map (first last : Nat) (distance : Bool) (v2 v3 : Nat) (s : RefineSt n) :
    part3 level first last distance v2 v3 (mapS (phi a b) s) =
      mapS (phi a b) (part3 level first last distance v2 v3 s) := by
  unfold part3
  dsimp only
  map_norm hL
  simp only [mapS_push, mapS_queue, mapS_hash, part4_map hL]
  split
  · ite_close
  · rfl

theorem part2_map (first last : Nat) (distance : Bool) (v2 v3 : Nat) (s : RefineSt n) (starts : Array Nat) :
    part2 level first last distance v2 v3 (mapS (phi a b) s) starts =
      mapS (phi a b) (part2 level first last distance v2 v3 s starts) := by
  unfold part2
  dsimp only
  map_norm hL
  simp only [mapS_active, mapS_push, mapS_hash, part3_map hL]
  split
  · ite_close
  · ite_close

theorem mid_map (first last : Nat) (distance : Bool) (v2 v3 : Nat) (s : RefineSt n) (starts : Array Nat) :
    mid level first last distance v2 v3 (mapS (phi a b) s) starts =
      mapS (phi a b) (mid level first last distance v2 v3 s starts) := by
  unfold mid
  simp only [mapS_lab, part2_map hL]
  ite_close

theorem finish_map (first last : Nat) (distance : Bool) (s : RefineSt n) (w1 v2 w2 v3 : Nat) :
    finish level first last distance (mapS (phi a b) s) w1 v2 w2 v3 =
      mapS (phi a b) (finish level first last distance s w1 v2 w2 v3) := by
  unfold finish
  dsimp only
  rw [mapS_hash, mapS_hash]
  simp only [mapS_lab, mapS_cellstart, mid_map hL]
  split
  · rfl
  · ite_close

end

end Finish

/-! ## The splitting procedures -/

section
variable {a b level : Nat} (hL : level ≠ a)
include hL

theorem splitCounts_map (first : Nat) (distance : Bool) (s : Sparse.RefineSt n) :
    Sparse.splitCounts level first distance (mapS (phi a b) s) =
      mapS (phi a b) (Sparse.splitCounts level first distance s) := by
  rw [Sparse.splitCounts_parts, Sparse.splitCounts_parts]
  dsimp only
  simp only [mapS_lab, mapS_hits, mapS_cellend]
  ite_map (phi a b)
  · rfl
  · rw [show ({ (mapS (phi a b) s).hash first with lab := (Sparse.CountSort.minima s.lab s.hits (n + 2)
        first (s.cellend[first]! + 1) (Sparse.CountSort.firstRun s.lab s.hits first
          (s.cellend[first]! + 1))).2.2.2.2 } : Sparse.RefineSt n) =
        mapS (phi a b) { s.hash first with lab := (Sparse.CountSort.minima s.lab s.hits (n + 2)
        first (s.cellend[first]! + 1) (Sparse.CountSort.firstRun s.lab s.hits first
          (s.cellend[first]! + 1))).2.2.2.2 } from rfl,
      Finish.finish_eq, Finish.finish_eq, Finish.finish_map hL]

theorem splitNontrivial_map (g : Sparse.Graph n) (split : Nat) (s : Sparse.RefineSt n) :
    Sparse.splitNontrivial g level split (mapS (phi a b) s) =
      mapS (phi a b) (Sparse.splitNontrivial g level split s) := by
  unfold Sparse.splitNontrivial
  dsimp only
  map_norm hL
  simp only [Id.run_bind, Id.run_pure]
  rw [arr_map1]
  · rfl
  · intro x s
    exact congrArg (fun r => (pure (ForInStep.yield r) : Id _)) (splitCounts_map hL x false s)

theorem splitSingleton_map (g : Sparse.Graph n) (split : Nat) (s : Sparse.RefineSt n) :
    Sparse.splitSingleton g level split (mapS (phi a b) s) =
      mapS (phi a b) (Sparse.splitSingleton g level split s) := by
  unfold Sparse.splitSingleton
  dsimp only
  map_norm hL
  simp only [Id.run_bind, Id.run_pure]
  rw [arr_map1]
  · rfl
  · intro x s
    dsimp only [mapS_hash, mapS_lab, mapS_ptn, mapS_active, mapS_queue, mapS_cellstart, mapS_cellend,
      mapS_indexed, mapS_hits, mapS_marks, mapS_vmarks, mapS_stamp, mapS_numcells, mapS_longcode, mk_map]
    simp only [← set_phi hL, stepMap_bind, stepMap_ite, stepMap_yield, mapS_push, mapS_hash, mapS_ptn, mk_map]
    rfl

end

/-! ## `refineWith` -/

section
variable {a b level : Nat} (ha : level < a) (hb : level < b)
include ha hb

theorem map_le (p : Array Nat) (i : Nat) : ((p.map (phi a b))[i]! ≤ level) ↔ (p[i]! ≤ level) :=
  ((sameAt_map ha hb p).le i).symm

theorem indexed_map (s : Sparse.RefineSt n) :
    Sparse.Refinement.indexed level (mapS (phi a b) s) = mapS (phi a b) (Sparse.Refinement.indexed level s) := by
  unfold Sparse.Refinement.indexed
  rw [mapS_ptn, mapS_lab, mapS_cellstart, mapS_cellend,
    ← indexCells_congr (sameAt_map ha hb s.ptn)]
  rfl

theorem distance_map (s : Sparse.RefineSt n) :
    Sparse.Refinement.distance level (mapS (phi a b) s) = mapS (phi a b) (Sparse.Refinement.distance level s) := by
  have hL : level ≠ a := by omega
  unfold Sparse.Refinement.distance
  simp only [Id.run_bind, Id.run_pure]
  rw [range_map2]
  · rfl
  · intro x s first
    simp only [mapS_cellend, splitCounts_map hL, stepMap_ite, stepMap_yield, stepMap_done]

theorem loop_map (g : Sparse.Graph n) (s : Sparse.RefineSt n) :
    Sparse.Refinement.loop g level (mapS (phi a b) s) = mapS (phi a b) (Sparse.Refinement.loop g level s) := by
  have hL : level ≠ a := by omega
  unfold Sparse.Refinement.loop
  simp only [Id.run_bind, Id.run_pure]
  rw [range_map1]
  · rfl
  · intro x s
    simp only [mapS_lab, mapS_ptn, mapS_active, mapS_queue, mapS_cellstart, mapS_cellend, mapS_indexed,
      mapS_hits, mapS_marks, mapS_vmarks, mapS_stamp, mapS_numcells, mapS_longcode, mk_map, mapS_hash,
      map_le ha hb, splitSingleton_map hL, splitNontrivial_map hL, stepMap_ite, stepMap_bind, stepMap_yield,
      stepMap_done]
    rfl

/-- Sparse refinement commutes with mapping `ptn` through `phi a b`, for `level` below `a` and `b`. -/
theorem refineWith_map (g : Sparse.Graph n) (lab ptn : Array Nat) (active : VSet n) (numcells : Nat)
    (scratch : Sparse.Scratch) :
    Sparse.refineWith g level lab (ptn.map (phi a b)) active numcells scratch =
      mapS (phi a b) (Sparse.refineWith g level lab ptn active numcells scratch) := by
  rw [Sparse.refineWith_parts, Sparse.refineWith_parts]
  dsimp only
  have hs : Sparse.Refinement.start lab (ptn.map (phi a b)) active numcells scratch =
      mapS (phi a b) (Sparse.Refinement.start lab ptn active numcells scratch) := rfl
  rw [hs]
  simp only [mapS_queue, map_le ha hb, indexed_map ha hb]
  ite_map (phi a b)
  · rfl
  · ite_map (phi a b)
    · rw [show Sparse.Refinement.distanceStart g (mapS (phi a b) (Sparse.Refinement.indexed level
          (Sparse.Refinement.start lab ptn active numcells scratch))) = mapS (phi a b)
          (Sparse.Refinement.distanceStart g (Sparse.Refinement.indexed level
            (Sparse.Refinement.start lab ptn active numcells scratch))) from rfl,
        distance_map ha hb, loop_map ha hb]
      rfl
    · rw [loop_map ha hb]
      rfl

end

end NautyVerified.Spec.SearchInf
