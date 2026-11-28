import NautyVerified.Spec.SparseFirstStore
import NautyVerified.Spec.Gca
import HexGraphIso.Nauty.Sparse.StoreSearch
import HexGraphIso.Nauty.Sparse.StoreOps
import HexGraphIso.Nauty.Sparse.Controls

/-!
# What nauty.c's search nodes need of HexGraphIso's sparse state

The sparse counterparts of `Spec/NodeOk.lean`, `Spec/NodeOkOff.lean` and
`Node/OkFirst.lean`. `SparseNodeOk G first level numcells st`: the node call's
state is the renamed image of a state of HexGraphIso's sparse run at `n + 2`
meeting the contract's node precondition (`SparseNodeOk₀`); on the first path
the canonical rows are still the blank allocation, off it the native store
`Sparse.Store` is installed and the level counters satisfy `GcaOk`.

`SparseSweepOff` and `SparseSweepFirst` are the sweep invariants:
the renamed-run part (the contract's sweep precondition `Sparse.Ready` with
the target cell), and the store and counters as for the node; on the first
path before its first child the rows are blank, and past it the store is
installed. `sparse_sweepOff_start`, `sparse_sweepFirst_start`: a node that
reaches its sweep starts it in the invariant; `sparse_sweepOff_child`,
`sparse_sweepFirst_child`: each child call satisfies `SparseNodeOk`;
`sparse_sweepOff_next`, `sparse_sweepFirst_next`: a child step that does not
end the sweep keeps the invariant.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso.Nauty
open Std.Do
set_option mvcgen.warning false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {n k : Nat}

local notation "SState" => Hex.GraphIso.Nauty.Sparse.State

/-! ## The invariants -/

/-- The sparse node precondition. -/
def SparseNodeOk (G : Hex.GraphIso.Sparse.Colored n k) (first : Bool) (level numcells : Nat)
    (st : SState n) : Prop :=
  SparseNodeOk₀ G first level numcells st ∧
    (first = true → st.canong.toRows = (Sparse.Graph.ofGraph G.graph).blank) ∧
    (first = false → Sparse.Store G.graph st ∧ GcaOk level st)

/-- The renamed-run part of the off-path sweep invariant. -/
def SparseSweepOff₀ (G : Hex.GraphIso.Sparse.Colored n k) (level numcells tc : Nat) (cell : VSet n)
    (cursor : Option Nat) (st : SState n) : Prop :=
  ∃ t st₂, st = twG (phi (n + 2) nautyInfinity) t st₂ ∧ 1 ≤ level ∧ Sparse.Ready G level numcells st₂ ∧
    Generic.Target Sparse.State.frame level tc cell st₂ ∧ (∀ v, cursor = some v → cell.mem v = true) ∧
    InvS st₂ ∧ ∃ last, Depth last st₂ ∧ AgreeTo (last + 1) t st₂.firsttc

/-- The off-path sweep invariant. -/
def SparseSweepOff (G : Hex.GraphIso.Sparse.Colored n k) (level numcells tc : Nat) (cell : VSet n)
    (cursor : Option Nat) (st : SState n) : Prop :=
  SparseSweepOff₀ G level numcells tc cell cursor st ∧ Sparse.Store G.graph st ∧ GcaSw level st

/-- The renamed-run part of the first-path sweep invariant. -/
def SparseSweepFirst₀ (G : Hex.GraphIso.Sparse.Colored n k) (level numcells tc tv1 : Nat) (cell : VSet n)
    (cursor : Option Nat) (st : SState n) : Prop :=
  ∃ t st₂, st = twG (phi (n + 2) nautyInfinity) t st₂ ∧ 1 ≤ level ∧ Sparse.Ready G level numcells st₂ ∧
    Generic.Target Sparse.State.frame level tc cell st₂ ∧ (∀ v, cursor = some v → cell.mem v = true) ∧
    InvS st₂ ∧
    ((cursor = some tv1 ∧ OrbIdS st₂ ∧ AgreeTo level t st₂.firsttc) ∨
      (Generic.Past true tv1 cursor ∧ ∃ last, Depth last st₂ ∧ AgreeTo (last + 1) t st₂.firsttc))

/-- The first-path sweep invariant. -/
def SparseSweepFirst (G : Hex.GraphIso.Sparse.Colored n k) (level numcells tc tv1 : Nat) (cell : VSet n)
    (cursor : Option Nat) (st : SState n) : Prop :=
  SparseSweepFirst₀ G level numcells tc tv1 cell cursor st ∧
    (cursor = some tv1 → st.canong.toRows = (Sparse.Graph.ofGraph G.graph).blank) ∧
    ∀ v, cursor = some v → v ≠ tv1 → Sparse.Store G.graph st ∧ GcaSw level st

theorem SparseNodeOk.level_pos {G : Hex.GraphIso.Sparse.Colored n k} {first : Bool} {level numcells : Nat}
    {st : SState n} (h : SparseNodeOk G first level numcells st) : 1 ≤ level := h.1.level_pos

theorem SparseNodeOk.level_le {G : Hex.GraphIso.Sparse.Colored n k} {first : Bool} {level numcells : Nat}
    {st : SState n} (h : SparseNodeOk G first level numcells st) : level ≤ n := h.1.level_le

theorem sparseNodeOk_root' (G : Hex.GraphIso.Sparse.Colored n k) (hn0 : 0 < n) :
    let p := Sparse.initialPartitionWith n k G.coloring.cells.toArray Fin.val
    SparseNodeOk G true 1 p.2.length (sparseInitialC (.ofGraph G.graph) p.1 p.2) :=
  ⟨sparseNodeOk_root G hn0, fun _ => rfl, fun h => absurd h (by decide)⟩

/-! ## Fields the sparse steps keep -/

theorem sparse_gcaF_target (first : Bool) (g : Sparse.Graph n) (tcLevel level numcells : Nat)
    (st : SState n) : gcaF (Sparse.chooseTarget first g tcLevel level numcells st).2.2.2 = gcaF st := by
  unfold Sparse.chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × SState n => gcaF out.2.2.2 = gcaF st)
  mvcgen
  all_goals simp_all +zetaDelta [gcaF]

theorem sparse_gcaF_classify (g : Sparse.Graph n) (level nc : Nat) (st : SState n) :
    gcaF (Sparse.classify g level nc st).2 = gcaF st := by
  unfold gcaF Sparse.classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.gcaFirst, apply_ite SearchState.gcaCanon,
    apply_ite SearchState.noncheaplevel, ite_self]

/-- An off-path node that continues to its sweep starts the sweep in `GcaSw`. -/
theorem sparse_gcaSw_sweepOff (g : Sparse.Graph n) (tl level nc : Nat) (st : SState n)
    (h : GcaOk level st) :
    let v := Sparse.visit g level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := Sparse.chooseTarget false g tl level v.1 st₁
    let cl := Sparse.classify g level v.1 ct.2.2.2
    let lx := leafExit cl.1 level cl.2
    lx.1 = .done → GcaSw level (cheapCheck false level lx.2) := by
  intro v st₁ ct cl lx hd
  have hint : cl.1 = .internal := (leafExit_done _ _ _).1 hd
  have hlx : lx.2 = cl.2 := by
    show (leafExit cl.1 level cl.2).2 = cl.2
    rw [hint]; rfl
  have hf : gcaF cl.2 = gcaF st := by
    show gcaF (Sparse.classify g level v.1 ct.2.2.2).2 = gcaF st
    rw [sparse_gcaF_classify, sparse_gcaF_target, gcaF_compare]
    rfl
  unfold gcaF at hf
  simp only [Prod.mk.injEq] at hf
  obtain ⟨h1, h2, h3⟩ := hf
  obtain ⟨g1, g2, g3⟩ := h
  rw [hlx]
  unfold cheapCheck
  split
  · exact ⟨by rw [h1]; omega, by rw [h2]; omega, by simp⟩
  · exact ⟨by rw [h1]; omega, by rw [h2]; omega, by rw [h3]; omega⟩

/-- An off-path node with the store installed keeps it up to its sweep. -/
theorem sparse_store_sweepOff {G : Hex.GraphIso.Sparse.Colored n k} (tl level nc : Nat) (st : SState n)
    (h : Sparse.Store G.graph st)
    (hl : ∃ l : Hex.GraphIso.Label n, Hex.GraphIso.Label.ofArray? n (Sparse.visit (.ofGraph G.graph) level nc st).2.2.lab = some l) :
    let g : Sparse.Graph n := .ofGraph G.graph
    let v := Sparse.visit g level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := Sparse.chooseTarget false g tl level v.1 st₁
    let cl := Sparse.classify g level v.1 ct.2.2.2
    let lx := leafExit cl.1 level cl.2
    Sparse.Store G.graph ct.2.2.2 ∧ Sparse.Store G.graph (cheapCheck false level lx.2) := by
  intro g v st₁ ct cl lx
  obtain ⟨l, hl⟩ := hl
  have h3 : Sparse.Store G.graph ct.2.2.2 := ((h.visit level nc).compare level _).target false tl level _
  have hlab : Hex.GraphIso.Label.ofArray? n ct.2.2.2.lab = some l := by
    rw [(Sparse.chooseTarget_frame false g tl level v.1 st₁).1]
    obtain ⟨e, -⟩ := compareCodes_frame level v.2.1 v.2.2
    rw [e]; exact hl
  obtain ⟨h4, hc⟩ := h3.classify level v.1 l hlab
  exact ⟨h3, (h4.leaf cl.1 level hc).cheap false level⟩

end NautyVerified.Spec.SearchInf
