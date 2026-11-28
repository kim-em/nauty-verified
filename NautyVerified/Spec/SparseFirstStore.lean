import NautyVerified.Spec.SparseInfRun
import HexGraphIso.Nauty.Sparse.FirstStore

/-!
# The canonical store after the first sparse leaf

`sparse_firstPath_of`: a first-path node of HexGraphIso's sparse search
(identity orbits) that does not run out of fuel descends along a
`Generic.FirstPath` to its first leaf. With `Sparse.firstPath_store`, a
first-path node entered with the blank canonical rows returns, unless it runs
out of fuel, with the native store `Sparse.Store` installed
(`sparse_first_store`).
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso.Nauty

variable {n k : Nat}

theorem sparse_firstPath_of {G : Hex.GraphIso.Sparse.Colored n k} (hn : 0 < n)
    {tcLevel fuel level numcells : Nat} {st : Sparse.State n} (hl : 1 ≤ level)
    (h : Sparse.NodeInv G level numcells st) (horbit : ∀ v, v < n → st.orbits[v]! = v)
    (hne : (Generic.node true (.ofGraph G.graph : Sparse.Graph n) (n + 2) tcLevel fuel level numcells
      st).1 ≠ .fuel) :
    ∃ last leaf, Generic.FirstPath (.ofGraph G.graph : Sparse.Graph n) tcLevel fuel level numcells st
      last leaf := by
  induction fuel generalizing level numcells st with
  | zero => exact absurd (by simp [Generic.node]) hne
  | succ fuel ih =>
    let r := Generic.prepareFirst (.ofGraph G.graph : Sparse.Graph n) tcLevel level numcells st
    obtain ⟨hr, ht⟩ := h.prepare (tcLevel := tcLevel) hn hl
    by_cases hdisc : r.1 = n
    · exact ⟨level, _, .leaf fuel level numcells st hdisc⟩
    · have hc : r.1 < n := by
        have hh : r.1 = bcount r.2.2.2.2.ptn level n := hr.ok.count
        have hb := bcount_le r.2.2.2.2.ptn level n
        omega
      have hv := h.visit_ready hn hl
      have hrec := (hv.record (Sparse.visit (.ofGraph G.graph) level numcells st).2.1).ready
      have hne' : r.2.2.1 ≠ VSet.empty := hrec.first_nonempty hn hl hc
      have htv := VSet.nextElem_none_eq_minElem hne'
      have hmem : r.2.2.1.mem r.2.2.1.minElem = true := VSet.nextElem_mem htv
      have hcheap := hr.cheap true
      have htarget := ht.of_out hcheap.frame.effect
      have hchild := hcheap.ready.child hn hl true htarget hmem
      have hoready : (cheapCheck true level r.2.2.2.2).orbits = st.orbits := by
        unfold cheapCheck
        split <;> exact Sparse.prepareFirst_orbits (.ofGraph G.graph) tcLevel level numcells st
      have hochild : ∀ v, v < n → ((Sparse.policy (n := n)).child true level r.2.1.toNat
          r.2.2.1.minElem (cheapCheck true level r.2.2.2.2)).orbits[v]! = v := by
        intro v hv
        change (cheapCheck true level r.2.2.2.2).orbits[v]! = v
        rw [hoready]
        exact horbit v hv
      have horb : Generic.Policy.orbit (n := n) (Generic.Policy.cheapCheck (n := n) true level r.2.2.2.2)
          r.2.2.1.minElem = r.2.2.1.minElem := by
        change (cheapCheck true level r.2.2.2.2).orbits[r.2.2.1.minElem]! = _
        rw [hoready]
        exact horbit _ (VSet.mem_lt hmem)
      have hcne : (Generic.node true (.ofGraph G.graph : Sparse.Graph n) (n + 2) tcLevel fuel (level + 1)
          (r.1 + 1) ((Sparse.policy (n := n)).child true level r.2.1.toNat r.2.2.1.minElem
            (cheapCheck true level r.2.2.2.2))).1 ≠ .fuel := by
        intro hf
        apply hne
        rw [Generic.node]
        unfold Generic.nodeStep
        change (Id.run do
          let r := Generic.prepareFirst (.ofGraph G.graph : Sparse.Graph n) tcLevel level numcells st
          if r.1 == n then
            return (.unwind (level - 1) false, Generic.Policy.firstterminal (n := n) level r.2.2.2.2)
          let s := Generic.sweep true (.ofGraph G.graph : Sparse.Graph n) (n + 2) tcLevel fuel (n + 1)
            level r.1 r.2.1.toNat ((r.2.2.1.nextElem none).getD 0)
            (r.2.2.1.nextElem none) r.2.2.1 0
            (Generic.Policy.cheapCheck (n := n) true level r.2.2.2.2)
          match s.1 with
          | .done => return (.unwind (level - 1) false,
              Generic.Policy.afterSweep (n := n) true level r.2.2.2.1 s.2.1 s.2.2)
          | _ => return (s.1, s.2.2)).1 = .fuel
        have hdisc' : ((Generic.prepareFirst (.ofGraph G.graph : Sparse.Graph n) tcLevel level numcells
            st).1 == n) = false := beq_eq_false_iff_ne.mpr hdisc
        have htv' : (Generic.prepareFirst (.ofGraph G.graph : Sparse.Graph n) tcLevel level numcells
            st).2.2.1.nextElem none = some r.2.2.1.minElem := htv
        simp only [hdisc', Bool.false_eq_true, ite_false, htv', Option.getD_some, Id.run]
        rw [Generic.sweep.eq_def]
        dsimp only
        unfold Generic.sweepStep
        simp only [Bool.not_true, horb, beq_self_eq_true, Bool.or_true, Bool.and_self, ite_true, Id.run]
        have hf' : (Generic.node true (Sparse.Graph.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1)
            (r.1 + 1) (Generic.Policy.child (n := n) true level r.2.1.toNat r.2.2.1.minElem
              (Generic.Policy.cheapCheck (n := n) true level r.2.2.2.2))).1 = .fuel := hf
        have hrR : r = Generic.prepareFirst (.ofGraph G.graph : Sparse.Graph n) tcLevel level numcells st := rfl
        rw [← hrR]
        simp only [horb, beq_self_eq_true, Bool.false_or, ite_true, Bool.and_self]
        simp only [hf', Generic.advance]
        rfl
      obtain ⟨last, leaf, hp⟩ := ih (by omega) hchild hochild hcne
      exact ⟨last, leaf, .step hdisc htv horb hp⟩

/-- A first-path node entered with the blank rows that does not run out of fuel
returns with the native store installed. -/
theorem sparse_first_store {G : Hex.GraphIso.Sparse.Colored n k} (hn : 0 < n)
    {tcLevel fuel level numcells : Nat} {st : Sparse.State n} (hl : 1 ≤ level)
    (h : Sparse.NodeInv G level numcells st) (horbit : ∀ v, v < n → st.orbits[v]! = v)
    (hb : st.canong.toRows = (Sparse.Graph.ofGraph G.graph).blank)
    (hne : (Generic.node true (.ofGraph G.graph : Sparse.Graph n) (n + 2) tcLevel fuel level numcells
      st).1 ≠ .fuel) :
    Sparse.Store G.graph
      (Generic.node true (.ofGraph G.graph : Sparse.Graph n) (n + 2) tcLevel fuel level numcells st).2 := by
  obtain ⟨_, _, path⟩ := sparse_firstPath_of hn hl h horbit hne
  exact Sparse.firstPath_store hn path hl h hb

end NautyVerified.Spec.SearchInf
