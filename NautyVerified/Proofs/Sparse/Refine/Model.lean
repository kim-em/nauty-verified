import HexGraphIso.Nauty.Sparse.RefineParts
import HexGraphIso.Nauty.Sparse.RefineCongr
import HexGraphIso.Nauty.Sparse.RefineFuel
import NautyVerified.Spec.SparseSort

/-!
# `refineWith`, loop by loop

HexGraphIso's `refineWith` (through `Refinement.*`, `refineWith_parts`) with
each `for` loop that `refine_sg` runs as a C loop written as `iterF` of a
step function on the loop's state: `queueStep` (the initial active scan),
`indexStep` (`CELLSTART`), `distStep` (the distance split's cell scan) and
`loopStep` (the main loop, one splitter per step). The fuel of each
`for _ in [0:n]` is not visible in the C; `entry_saturated` (from
HexGraphIso's `refineWith_saturated`) says the main loop stops by its own
test, and the other loops' fuel is accounted for at the C loops.

`Same a b`: `a` and `b` agree on every field `refine_sg` keeps in memory
apart from its scratch arrays (`lab`, `ptn`, `active`, `queue`, `numcells`,
`longcode`). `loop_same`: the main loop from two admissible states that are
`Same` gives `Same` results (HexGraphIso's `RefineSt.Equiv.selected` and
`selected_lab`), so a C step may run on the scratch it finds and still follow
the model.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open Hex.GraphIso.Nauty.Sparse NautyVerified.Spec.SortC
open Hex.GraphIso.Nauty (VSet mash cleanup cellEnd IsCell renamingOf cellsPerm_refl)
open Hex.GraphIso (Perm)

variable {n : Nat}

def loopStep (g : Graph n) (level : Nat) (s : RefineSt n) : ForInStep (RefineSt n) :=
  if s.queue.isEmpty || s.numcells ≥ n then .done s
  else .yield (RefineSt.selected g level (RefineSt.position level s) s)

theorem loop_eq (g : Graph n) (level : Nat) (s : RefineSt n) :
    Refinement.loop g level s = iterF (loopStep g level) n s := by
  unfold Refinement.loop
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [show Std.Legacy.Range.size [0:n] = n by simp [Std.Legacy.Range.size]]
  simp only [Id.run, bind_pure]
  rw [← forIn_iter (k := 0)]
  refine congrArg (forIn (m := Id) (List.range' 0 n) s) (funext fun x => funext fun st => ?_)
  unfold loopStep RefineSt.selected
  split
  · rfl
  · exact (apply_ite ForInStep.yield _ _ _).symm

def distStep (level : Nat) (st : RefineSt n × Nat) : ForInStep (RefineSt n × Nat) :=
  if st.2 ≥ n then .done st
  else if st.2 < st.1.cellend[st.2]! then
    .yield (splitCounts level st.2 true st.1, st.1.cellend[st.2]! + 1)
  else .yield (st.1, st.1.cellend[st.2]! + 1)

theorem distance_eq (level : Nat) (s : RefineSt n) :
    Refinement.distance level s = (iterF (distStep level) n (s, 0)).1 := by
  unfold Refinement.distance
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [show Std.Legacy.Range.size [0:n] = n by simp [Std.Legacy.Range.size]]
  rw [← forIn_iter (k := 0)]
  show (forIn (m := Id) (List.range' 0 n) (s, 0) _).1 = _
  refine congrArg (fun r => Prod.fst r)
    (congrArg (forIn (m := Id) (List.range' 0 n) (s, 0)) (funext fun x => funext fun st => ?_))
  unfold distStep
  split
  · rfl
  · split <;> rfl

/-- The fields `refine_sg` keeps in memory, besides its scratch. -/
structure Same (a b : RefineSt n) : Prop where
  lab : a.lab = b.lab
  ptn : a.ptn = b.ptn
  active : a.active = b.active
  queue : a.queue = b.queue
  numcells : a.numcells = b.numcells
  longcode : a.longcode = b.longcode

theorem Same.refl (a : RefineSt n) : Same a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Same.symm {a b : RefineSt n} (h : Same a b) : Same b a :=
  ⟨h.1.symm, h.2.symm, h.3.symm, h.4.symm, h.5.symm, h.6.symm⟩

theorem Same.trans {a b c : RefineSt n} (h : Same a b) (k : Same b c) : Same a c :=
  ⟨h.1.trans k.1, h.2.trans k.2, h.3.trans k.3, h.4.trans k.4, h.5.trans k.5, h.6.trans k.6⟩

theorem Same.equiv {level : Nat} {a b : RefineSt n} (h : Same a b) :
    RefineSt.Equiv (renamingOf (Perm.id n)) level a b := by
  have hid : (renamingOf (Perm.id n)).toFun = id := by funext v; simp [renamingOf]
  refine ⟨h.ptn.symm, ?_, ?_, h.numcells⟩
  · rw [hid, Array.map_id, h.lab]; exact cellsPerm_refl _ _ _
  · simp only [CountTrace.control, h.active, h.queue, h.longcode]

theorem Same.of_equiv {level : Nat} {a b : RefineSt n}
    (h : RefineSt.Equiv (renamingOf (Perm.id n)) level a b) (hl : b.lab = a.lab) : Same a b :=
  ⟨hl.symm, h.ptn.symm, h.active, h.queue, h.count, h.code⟩

/-- The main loop from two admissible states with the same fields. -/
theorem loop_same (G : Hex.SparseGraph n) (level : Nat) :
    ∀ (F : Nat) (a b : RefineSt n), a.Valid level → b.Valid level → Same a b →
      (iterF (loopStep (.ofGraph G) level) F a).Valid level ∧
      (iterF (loopStep (.ofGraph G) level) F b).Valid level ∧
      Same (iterF (loopStep (.ofGraph G) level) F a) (iterF (loopStep (.ofGraph G) level) F b)
  | 0, _, _, ha, hb, h => ⟨ha, hb, h⟩
  | F + 1, a, b, ha, hb, h => by
    have he : RefineSt.Equiv (renamingOf (Perm.id n)) level a b := h.equiv
    simp only [iterF, loopStep, ← h.queue, ← h.numcells]
    by_cases hstop : (a.queue.isEmpty || decide (a.numcells ≥ n)) = true
    · simp only [hstop, ite_true]
      exact ⟨ha, hb, h⟩
    · simp only [hstop, Bool.false_eq_true, ite_false]
      have hsize : 0 < a.queue.size := by
        simp only [Bool.or_eq_true, Array.isEmpty, decide_eq_true_eq] at hstop
        omega
      have hp := RefineSt.position_lt level a hsize
      have hp' : RefineSt.position level a < b.queue.size := h.queue ▸ hp
      rw [← he.position]
      exact loop_same G level F _ _ (ha.selected G level _ a hp) (hb.selected G level _ b hp')
        (Same.of_equiv (he.selected G G (Perm.id n) (by intro u v; simp) ha hb _ hp)
          (he.selected_lab G ha hb h.lab.symm _ hp).symm)

/-- One step of the initial active scan: state `(queue, next)`. -/
def queueStep (active : VSet n) (st : Array Nat × Option Nat) : ForInStep (Array Nat × Option Nat) :=
  match st.2 with
  | none => .done st
  | some i => .yield (st.1.push i, active.nextElem (some i))

theorem queue_eq (active : VSet n) :
    Refinement.queue active = (iterF (queueStep active) n (#[], active.nextElem none)).1 := by
  unfold Refinement.queue
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [show Std.Legacy.Range.size [0:n] = n by simp [Std.Legacy.Range.size]]
  rw [← forIn_iter (k := 0)]
  show (forIn (m := Id) (List.range' 0 n) (#[], active.nextElem none) _).1 = _
  refine congrArg (fun r => Prod.fst r)
    (congrArg (forIn (m := Id) (List.range' 0 n) (#[], active.nextElem none))
      (funext fun x => funext fun st => ?_))
  unfold queueStep
  rcases st with ⟨q, _ | i⟩ <;> rfl

/-- One cell of `indexCells`: state `(starts, ends, first)`. -/
def indexStep (n : Nat) (lab ptn : Array Nat) (level : Nat) (st : Array Nat × Array Nat × Nat) :
    ForInStep (Array Nat × Array Nat × Nat) :=
  if st.2.2 ≥ n then .done st
  else
    let first := st.2.2
    let last := cellEnd ptn level first
    if first < last then
      .yield ((List.range' first (last + 1 - first)).foldl (fun s i => s.set! lab[i]! first) st.1,
        st.2.1.set! first last, last + 1)
    else .yield (st.1.set! lab[first]! n, st.2.1.set! first last, last + 1)

theorem indexCells_eq (n : Nat) (lab ptn : Array Nat) (level : Nat) (starts ends : Array Nat) :
    indexCells n lab ptn level starts ends =
      ((iterF (indexStep n lab ptn level) n (starts, ends, 0)).1,
        (iterF (indexStep n lab ptn level) n (starts, ends, 0)).2.1) := by
  unfold indexCells
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [show Std.Legacy.Range.size [0:n] = n by simp [Std.Legacy.Range.size]]
  rw [← forIn_iter (k := 0)]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one, forIn_yield,
    Nat.add_sub_cancel]
  have h : ∀ st : Array Nat × Array Nat × Nat, indexStep n lab ptn level st =
      if st.2.2 ≥ n then ForInStep.done (st.1, st.2.1, st.2.2)
      else if st.2.2 < cellEnd ptn level st.2.2 then
        ForInStep.yield ((List.range' st.2.2 (cellEnd ptn level st.2.2 + 1 - st.2.2)).foldl
          (fun s i => s.set! lab[i]! st.2.2) st.1,
          st.2.1.set! st.2.2 (cellEnd ptn level st.2.2), cellEnd ptn level st.2.2 + 1)
      else ForInStep.yield (st.1.set! lab[st.2.2]! n, st.2.1.set! st.2.2 (cellEnd ptn level st.2.2),
        cellEnd ptn level st.2.2 + 1) := fun st => rfl
  simp only [h]
  rfl

/-- The state `refine_sg`'s main loop starts from: the indexed initial state,
after the distance split when it applies. -/
def entry (g : Graph n) (level : Nat) (lab ptn : Array Nat) (active : VSet n) (numcells : Nat)
    (scratch : Scratch) : RefineSt n :=
  let s := Refinement.start lab ptn active numcells scratch
  let r := Refinement.indexed level s
  if level <= 2 && s.queue.size == 1 && ptn[s.queue[0]!]! <= level && numcells <= n / 8 then
    Refinement.distance level (Refinement.distanceStart g r)
  else r

theorem refineWith_entry (g : Graph n) (level : Nat) (lab ptn : Array Nat) (active : VSet n)
    (numcells : Nat) (scratch : Scratch) (hne : (Refinement.queue active).isEmpty = false) :
    refineWith g level lab ptn active numcells scratch =
      Refinement.finish (iterF (loopStep g level) n (entry g level lab ptn active numcells scratch)) := by
  rw [refineWith_parts]
  have hne' : (Refinement.start lab ptn active numcells scratch).queue.isEmpty = false := hne
  simp only [hne', Bool.false_eq_true, ite_false, entry, loop_eq]
  split <;> rfl

theorem entry_saturated (g : Graph n) (level : Nat) (lab ptn : Array Nat) (active : VSet n)
    (numcells : Nat) (scratch : Scratch) (hne : (Refinement.queue active).isEmpty = false)
    (hcard : active.card ≤ numcells) :
    (iterF (loopStep g level) n (entry g level lab ptn active numcells scratch)).queue.isEmpty = true ∨
      n ≤ (iterF (loopStep g level) n (entry g level lab ptn active numcells scratch)).numcells := by
  have h := refineWith_saturated g level lab ptn active numcells scratch hcard
  rw [refineWith_entry g level lab ptn active numcells scratch hne] at h
  exact h

end NautyVerified.Proofs.Sparse.Refine
