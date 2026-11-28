import NautyVerified.Proofs.Search.Node.Policy
import NautyVerified.Proofs.Dispatch.Sparse.Rep
import NautyVerified.Spec.SparseRefine
import HexGraphIso.Nauty.Sparse.SearchBounds
import HexGraphIso.Nauty.Sparse.TargetValid
import HexGraphIso.Nauty.Sparse.TargetDispatch

/-!
# HexGraphIso's sparse policy runs nauty.c's node operations

`sparseLink : PolicyLink sparseOps n` for HexGraphIso's sparse policy
`Sparse.policy`. The carried store is `Sparse.Storage`: the canonical rows and
the refinement scratch, which `refine_sg` and `targetcell_sg` do not see. The
invariant `Inv` is `Scratch.Bounded` (kept by every transition,
`Sparse.boundsPolicy`).

- `visit` is `refineWith` on the retained scratch; on a node whose `lab` is a
  permutation and whose active cells start at closed positions (`VisitOk`) its
  C-visible outputs are fresh `Sparse.refine`'s (`refineWith_refine`).
- `chooseTarget` calls `maketargetCached`; with the scratch `Scratch.Valid` for
  the partition and a nontrivial cell (`TargetOk`) it is `maketargetcell`
  (`maketargetCached_eq`), whose cell is nautil.c's scan `mtcOf` from the
  target's start (`maketargetcell_mtc`).
- `child` and `recover` are HexGraphIso's followed by `Storage.invalidate`, and
  `afterSweep` also multiplies `order`; neither changes the rows.
-/

namespace NautyVerified.Proofs.Dispatch

open NautyVerified.Proofs.Search
open NautyVerified.Proofs.Maketargetcell (mtcOf)
open Hex.GraphIso.Nauty

variable {n : Nat}

theorem cellEnd_succ {ptn : Array Nat} {level a : Nat} (ha : a < ptn.size) (hgt : ptn[a]! > level) :
    cellEnd ptn level a = cellEnd ptn level (a + 1) := by
  unfold cellEnd
  rw [show ptn.size - a = (ptn.size - (a + 1)) + 1 by omega, cellEnd.go, ite_eq_left hgt]

/-- A nontrivial cell exists, so `Sparse.targetcell` picks the start of one. -/
theorem targetcell_mem' (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hne : Sparse.Target.nontrivial (cells ptn level n) ≠ []) :
    Sparse.targetcell (.ofGraph G) lab ptn level tcLevel hint ∈
      Sparse.Target.nontrivial (cells ptn level n) := by
  obtain ⟨l, hl⟩ := Hex.GraphIso.Label.ofArray?_exists hp
  let idx := Sparse.indexCells n lab ptn level (.replicate n n) (.replicate n 0)
  let scratch : Sparse.Scratch := { Sparse.Scratch.fresh n with cellstart := idx.1, cellend := idx.2 }
  have hi := Sparse.indexCells_valid lab ptn (.replicate n n) (.replicate n 0) level hs hend
    (fun i hi => Sparse.perm_bound hp hi) (fun i j hi hj he => Sparse.perm_injective hp hi hj he)
    (by simp) (by simp)
  exact Sparse.targetcell_mem G lab ptn level tcLevel hint scratch l hl hs hend hi hne

/-- `Sparse.maketargetcell` is nautil.c's cell scan from the target's start. -/
theorem maketargetcell_mtc (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hne : Sparse.Target.nontrivial (cells ptn level n) ≠ []) :
    Sparse.maketargetcell (.ofGraph G) lab ptn level tcLevel hint =
      mtcOf n lab ptn level (Sparse.targetcell (.ofGraph G) lab ptn level tcLevel hint) := by
  have hm := targetcell_mem' G lab ptn level tcLevel hint hp hs hend hne
  have hb := Sparse.Target.bound hs hend hm
  have ho := (Sparse.Target.open_of_mem hs hend hm).1
  unfold Sparse.maketargetcell mtcOf
  rw [← cellEnd_succ (by omega) ho]

/-- What `Sparse.visit` needs: the node's partition facts `refineWith_refine` reads. -/
def SparseVisitOk (G : Sparse.Graph n) (level : Nat) (st : Sparse.State n) : Prop :=
  (∃ H : Hex.SparseGraph n, G = .ofGraph H) ∧ st.lab.toList.Perm (List.range n) ∧
    st.ptn.size = n ∧ st.ptn[n - 1]! ≤ level ∧
    ∀ v, st.active.mem v = true → v = 0 ∨ st.ptn[v - 1]! ≤ level

/-- What `Sparse.chooseTarget` needs: `maketargetCached_eq`'s conditions, the
nontrivial cell whenever the node has fewer than `n` cells. -/
def SparseTargetOk (G : Sparse.Graph n) (level numcells : Nat) (st : Sparse.State n) : Prop :=
  (∃ H : Hex.SparseGraph n, G = .ofGraph H) ∧ st.lab.toList.Perm (List.range n) ∧
    st.ptn.size = n ∧ st.ptn[n - 1]! ≤ level ∧
    Sparse.Scratch.Valid n st.lab st.ptn level st.canong.scratch ∧
    (numcells ≠ n → Sparse.Target.nontrivial (cells st.ptn level n) ≠ [])

theorem sparse_visit_eq {G : Sparse.Graph n} {level numcells : Nat} {st : Sparse.State n}
    (hb : Sparse.Scratch.Bounded n st.canong.scratch) (h : SparseVisitOk G level st) :
    let a := Sparse.refineWith G level st.lab st.ptn st.active numcells st.canong.scratch
    let b := Sparse.refine G level st.lab st.ptn st.active numcells
    a.lab = b.lab ∧ a.ptn = b.ptn ∧ a.active = b.active ∧ a.numcells = b.numcells ∧
      a.longcode = b.longcode := by
  obtain ⟨⟨H, rfl⟩, hp, hs, hend, ha⟩ := h
  exact Spec.refineWith_refine H level st.lab st.ptn st.active numcells _ hp hs hend ha hb

/-- `Sparse.chooseTarget` is `chooseTargetG` with the scratch `maketargetCached` leaves. -/
theorem sparse_chooseTarget_eq (first : Bool) {G : Sparse.Graph n} (tcLevel : Nat)
    {level numcells : Nat} {st : Sparse.State n} (h : SparseTargetOk G level numcells st) :
    ∃ c : Sparse.Storage n, c.toRows = st.canong.toRows ∧
      Sparse.chooseTarget first G tcLevel level numcells st =
        let r := chooseTargetG sparseOps first G tcLevel level numcells st
        (r.1, r.2.1, r.2.2.1, { r.2.2.2 with canong := c }) := by
  obtain ⟨⟨H, rfl⟩, hp, hs, hend, hv, hne⟩ := h
  by_cases hg : (if first then numcells != n
      else numcells < n && (st.eqlevFirst == level || st.compCanon >= 0)) = true
  · have hn : numcells ≠ n := by
      cases first
      · simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq] at hg
        omega
      · simpa using hg
    have he : ∀ hint, (Sparse.maketargetCached (.ofGraph H) st.lab st.ptn level tcLevel hint
        st.canong.scratch).1 = (mtcOf n st.lab st.ptn level
          (Sparse.targetcell (.ofGraph H) st.lab st.ptn level tcLevel hint)).1 ∧
        (Sparse.maketargetCached (.ofGraph H) st.lab st.ptn level tcLevel hint
          st.canong.scratch).2.1 = (mtcOf n st.lab st.ptn level
            (Sparse.targetcell (.ofGraph H) st.lab st.ptn level tcLevel hint)).2.1 ∧
        (Sparse.maketargetCached (.ofGraph H) st.lab st.ptn level tcLevel hint
          st.canong.scratch).2.2.1 = (mtcOf n st.lab st.ptn level
            (Sparse.targetcell (.ofGraph H) st.lab st.ptn level tcLevel hint)).2.2 := by
      intro hint
      have e := Sparse.maketargetCached_eq H st.lab st.ptn level tcLevel hint st.canong.scratch
        (Hex.GraphIso.Label.ofArray?_exists hp).choose
        (Hex.GraphIso.Label.ofArray?_exists hp).choose_spec hs hend hv (hne hn)
      rw [maketargetcell_mtc H _ _ _ _ _ hp hs hend (hne hn)] at e
      exact ⟨congrArg (·.1) e, congrArg (·.2.1) e, congrArg (·.2.2) e⟩
    refine ⟨{ st.canong with scratch := (Sparse.maketargetCached (.ofGraph H) st.lab st.ptn level
      tcLevel (if !first && st.compCanon < 0 then st.firsttc[level]! else -1)
      st.canong.scratch).2.2.2 }, rfl, ?_⟩
    unfold Sparse.chooseTarget chooseTargetG
    simp only [Id.run, pure, hg, ite_true, sparseOps]
    have he1 := fun hint => (he hint).1
    have he2 := fun hint => (he hint).2.1
    have he3 := fun hint => (he hint).2.2
    simp only [he1, he2, he3]
    cases first <;> by_cases hc : st.compCanon < 0 <;> simp [hc] <;> split <;> simp_all
  · refine ⟨st.canong, rfl, ?_⟩
    unfold Sparse.chooseTarget chooseTargetG
    simp only [Id.run, pure, hg, Bool.false_eq_true, ite_false]
    cases first <;> rfl

/-- HexGraphIso's sparse policy as nauty.c's search runs it. -/
def sparseLink : PolicyLink sparseOps n where
  Inv _ c := Sparse.Scratch.Bounded n c.scratch
  VisitOk G level _ st := SparseVisitOk G level st
  TargetOk G level numcells st := SparseTargetOk G level numcells st
  visit_numcells _ _ _ _ hb h := (sparse_visit_eq hb h).2.2.2.1
  visit_code _ _ _ _ hb h := (sparse_visit_eq hb h).2.2.2.2
  visit_same G level numcells st hb h := by
    have e := sparse_visit_eq (numcells := numcells) hb h
    refine ⟨⟨{ st.canong with scratch :=
      (Sparse.refineWith G level st.lab st.ptn st.active numcells st.canong.scratch).toScratch },
      st.order, ?_⟩, rfl⟩
    show (Sparse.visit G level numcells st).2.2 = _
    unfold Sparse.visit
    simp only [sparseOps, ofSparseSt, e.1, e.2.1, e.2.2.1]
  visit_inv G level numcells st hb _ := Sparse.visit_bounded G level numcells st hb
  recordFirst_eq _ _ _ := rfl
  compareCodes_eq _ _ _ := rfl
  target_eq first G tcLevel level numcells st _ h := by
    obtain ⟨c, -, e⟩ := sparse_chooseTarget_eq first tcLevel h
    have e' : Generic.Policy.chooseTarget (n := n) first G tcLevel level numcells st = _ := e
    rw [e']
    exact ⟨rfl, rfl, rfl⟩
  target_same first G tcLevel level numcells st _ h := by
    obtain ⟨c, hc, e⟩ := sparse_chooseTarget_eq first tcLevel h
    have e' : Generic.Policy.chooseTarget (n := n) first G tcLevel level numcells st = _ := e
    rw [e']
    refine ⟨⟨c, _, rfl⟩, ?_⟩
    · have hk : ∀ first, (chooseTargetG sparseOps first G tcLevel level numcells st).2.2.2.canong =
          st.canong := by
        intro first
        unfold chooseTargetG
        cases first <;> simp only [Id.run, pure] <;> (repeat' split) <;> simp
      show (chooseTargetG sparseOps first G tcLevel level numcells st).2.2.2.canong.toRows = c.toRows
      rw [hk, hc]
  target_inv first G tcLevel level numcells st hb _ :=
    Sparse.chooseTarget_bounded first G tcLevel level numcells st hb
  firstterminal_eq _ _ := rfl
  classify_eq _ _ _ _ := rfl
  classify_inv G level numcells st hb := by
    show Sparse.Scratch.Bounded n (Sparse.classify G level numcells st).2.canong.scratch
    rw [Sparse.classify_scratch]
    exact hb
  leafExit_eq _ _ _ := rfl
  cheapCheck_eq _ _ _ := rfl
  cheapautom_eq _ _ := rfl
  child_same _ _ _ _ _ := ⟨⟨_, _, rfl⟩, rfl⟩
  child_inv G first level tc tv st hb := (Sparse.child_valid first level tc tv st hb).toBounded
  afterChildFirst_eq _ _ _ := rfl
  leaveChild_eq _ _ := rfl
  orbit_eq _ _ := rfl
  shortprune_eq _ _ := rfl
  longprune_eq _ _ := rfl
  recover_same _ _ _ := ⟨⟨_, _, rfl⟩, rfl⟩
  recover_inv G inf level st hb := (Sparse.recover_valid inf level st hb).toBounded
  afterSweep_same first _ _ index _ := by
    cases first
    · exact Same.refl _
    · exact ⟨⟨_, _, rfl⟩, rfl⟩
  afterSweep_inv G first level size index st hb :=
    (Sparse.boundsPolicy G 0 0).afterSweep first level size index st hb

end NautyVerified.Proofs.Dispatch
