import NautyVerified.Proofs.Search.Node.Laws
import NautyVerified.Proofs.Search.Node.SparseOk
import NautyVerified.Proofs.Dispatch.Sparse.Link
import HexGraphIso.Nauty.Sparse.ReturnOrigin

/-!
# The node laws of HexGraphIso's sparse search

`sparseLaws G hn0 hn : NodeLaws sparseLink (.ofGraph G.graph)`, built as
`denseLaws` is: the node precondition is `SparseNodeOk` with `ActiveOk`, the
sweep invariants `SparseSweepFirst` and `SparseSweepOff`
(`Spec/SparseNodeOk.lean`, `Spec/SparseSweepOk.lean`, `Node/SparseOk.lean`).
The partition facts of a renamed sparse state come from the dense `PartOk`
of its `Sparse.State.frame` (`sparse_partFacts`); `sparse_store_fits`: an
installed native store leaves room for `updatecan` (`sparseOps.Fits`).
-/

namespace NautyVerified.Proofs.Search

open NautyVerified.Proofs.Dispatch
open Hex.GraphIso.Nauty
open NautyVerified.Spec.SearchInf

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {n k : Nat}

local notation "SState" => Hex.GraphIso.Nauty.Sparse.State

/-! ### Partition facts -/

theorem PartFactsG.congr {κ : Type} {level numcells : Nat} {s t : SearchState n κ}
    (h : PartFactsG n level numcells s) (hl : t.lab = s.lab) (hp : t.ptn = s.ptn) :
    PartFactsG n level numcells t := by
  obtain ⟨a, b, c, d, e, f, g, i, j⟩ := h
  exact ⟨hl ▸ a, hl ▸ b, hl ▸ c, hp ▸ d, hp ▸ e, hp ▸ f, hp ▸ g, i, j⟩

/-- The partition facts of a renamed state of the sparse run at `n + 2`. -/
theorem sparse_partFacts {G : Hex.GraphIso.Sparse.Colored n k} {level numcells : Nat} {s : SState n}
    (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (hok : SearchOk G.toDense level numcells s.frame)
    (t : Array Int) : PartFactsG n level numcells (twG (phi (n + 2) nautyInfinity) t s) := by
  have h := (PartOk.of_tw hn hok t).facts hn0 hn
  exact ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9⟩

theorem sparse_labPerm' {G : Hex.GraphIso.Sparse.Colored n k} {level numcells : Nat} {s : SState n}
    (hn0 : 0 < n) (hok : SearchOk G.toDense level numcells s.frame) : s.lab.toList.Perm (List.range n) :=
  isPerm_of_cellsReach hok.labSize hn0 hok.reach

theorem isCell_sameAt {level : Nat} {p q : Array Nat} (h : SameAt level p q) {a len : Nat}
    (hc : IsCell p level a len) : IsCell q level a len := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  refine ⟨h1, ?_, fun i hi hi' => (h.2 i).1 (h3 i hi hi'), (h.le _).1 h4⟩
  rcases h2 with h2 | h2
  · exact .inl h2
  · exact .inr ((h.le _).1 h2)

theorem scratch_valid_sameAt {level : Nat} {lab p q : Array Nat} {s : Sparse.Scratch}
    (h : SameAt level p q) (hv : Sparse.Scratch.Valid n lab p level s) :
    Sparse.Scratch.Valid n lab q level s := by
  refine ⟨hv.toBounded, fun hi => ?_⟩
  obtain ⟨a, b, c, d⟩ := hv.indices hi
  have h' : SameAt level q p := ⟨h.1.symm, fun i => (h.2 i).symm⟩
  exact ⟨a, b, fun x len hc => c x len (isCell_sameAt h' hc),
    fun x len hc => d x len (isCell_sameAt h' hc)⟩

/-- What `Sparse.chooseTarget` needs, at a renamed `Ready` state. -/
theorem sparse_targetOk {G : Hex.GraphIso.Sparse.Colored n k} {level numcells : Nat} {s : SState n}
    (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (hlevel : 1 ≤ level)
    (h : Sparse.Ready G level numcells s) (t : Array Int) :
    SparseTargetOk (.ofGraph G.graph) level numcells (twG (phi (n + 2) nautyInfinity) t s) := by
  have hf := sparse_partFacts hn0 hn h.ok t
  have hln := sparse_level_le h
  have hp := sparse_labPerm' hn0 h.ok
  refine ⟨⟨G.graph, rfl⟩, hp, hf.ptnSize, Nat.le_trans hf.ptnLast hlevel,
    scratch_valid_sameAt (sameAt_map (by omega) (by omega) s.ptn) h.scratch, fun hnc => ?_⟩
  have hc : bcount (twG (phi (n + 2) nautyInfinity) t s).ptn level n < n := by
    have := hf.count; have := hf.numcellsLe; omega
  have hm := Sparse.targetcell_nontrivial G.graph _ _ level 100 (-1) hp hf.ptnSize
    (Nat.le_trans hf.ptnLast hlevel) hc
  intro he
  rw [he] at hm
  cases hm

/-! ### The store -/

/-- An installed native store leaves room for the rows `updatecan` writes. -/
theorem sparse_store_fits {G : Hex.SparseGraph n} {st : SState n} (h : Sparse.Store G st) :
    sparseOps.Fits (.ofGraph G) st.canong.toRows st.canonlab st.samerows := by
  obtain ⟨l, hl, hp⟩ := h
  show NautyVerified.Proofs.Sparse.start (.ofGraph G) st.canonlab st.samerows
    (NautyVerified.Proofs.Sparse.base st.canong.toRows st.samerows) (n - st.samerows) ≤
      st.canong.toRows.neighbors.size
  have hsr := hp.count_le
  have key : ∀ j, st.samerows + j ≤ n →
      NautyVerified.Proofs.Sparse.start (.ofGraph G) st.canonlab st.samerows
        (NautyVerified.Proofs.Sparse.base st.canong.toRows st.samerows) j =
        (G.relabel l.perm).offsets[st.samerows + j]! := by
    intro j
    induction j with
    | zero =>
      intro _
      show NautyVerified.Proofs.Sparse.base st.canong.toRows st.samerows = _
      unfold NautyVerified.Proofs.Sparse.base
      split
      · rename_i h0; rw [h0, Nat.add_zero, Hex.SparseGraph.offset_zero]
      · exact hp.offsets_eq _ (Nat.le_refl _)
    | succ j ih =>
      intro hj
      have hi : st.samerows + j < n := by omega
      rw [NautyVerified.Proofs.Sparse.start, ih (by omega)]
      have hd := (G.degree_relabel l.perm ⟨st.samerows + j, hi⟩)
      have hv : st.canonlab[st.samerows + j]! = (l.get ⟨st.samerows + j, hi⟩).val :=
        (Hex.GraphIso.Label.ofArray?_get hl (st.samerows + j) hi).symm
      have hm := (G.relabel l.perm).offset_mono (i := st.samerows + j) (j := st.samerows + j + 1)
        (by omega) (by omega)
      have hd' : (G.relabel l.perm).offsets[st.samerows + j + 1]! -
          (G.relabel l.perm).offsets[st.samerows + j]! =
          G.offsets[(l.get ⟨st.samerows + j, hi⟩).val + 1]! - G.offsets[(l.get ⟨st.samerows + j, hi⟩).val]! :=
        hd
      rw [hv, show st.samerows + (j + 1) = st.samerows + j + 1 by omega]
      show (G.relabel l.perm).offsets[st.samerows + j]! + (G.offsets[(l.get ⟨st.samerows + j, hi⟩).val + 1]! -
        G.offsets[(l.get ⟨st.samerows + j, hi⟩).val]!) = (G.relabel l.perm).offsets[st.samerows + j + 1]!
      omega
  rw [key _ (by omega), show st.samerows + (n - st.samerows) = n by omega, Hex.SparseGraph.offset_last,
    Hex.SparseGraph.neighbors_size_relabel, hp.neighbors_size, Hex.SparseGraph.neighbors_size_relabel]
  exact Nat.le_refl _

/-! ### The leaf of an off-path node -/

theorem sparse_classify_internal {g : Sparse.Graph n} {level numcells : Nat} {st : SState n}
    (h : (Sparse.classify g level numcells st).1 = .internal) :
    ¬ (st.eqlevFirst ≠ level ∧ st.compCanon < 0) ∧ numcells ≠ n := by
  revert h
  unfold Sparse.classify
  simp only [Id.run_pure, Id.run_bind, apply_ite Id.run, apply_ite Prod.fst]
  repeat' split
  all_goals simp_all

theorem sparse_chooseTarget_skip (g : Sparse.Graph n) (tl level nc : Nat) (st : SState n)
    (h : ¬ (nc < n ∧ (st.eqlevFirst = level ∨ 0 ≤ st.compCanon))) :
    (Sparse.chooseTarget false g tl level nc st).2.2.2 = st := by
  unfold Sparse.chooseTarget
  simp only [Bool.false_eq_true, ite_false, Id.run]
  split
  · rename_i hc
    exfalso
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, ge_iff_le] at hc
    exact h hc
  · rfl

theorem autos_pos_of_backG {κ : Type} {out : SearchState n κ} {p : VSet n × VSet n}
    (h : out.autos.back? = some p) : 0 < out.autos.size := by
  rcases Nat.eq_zero_or_pos out.autos.size with h0 | h0
  · rw [Array.size_eq_zero_iff] at h0
    rw [h0] at h
    simp at h
  · exact h0

theorem leafExit_wsCap {κ : Type} (leaf : Leaf) (level : Nat) (st : SearchState n κ) :
    (leafExit leaf level st).2.wsCap = st.wsCap := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, Id.run_bind, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals simp_all [admit, pushAuto, pruneReturn, install]
  all_goals repeat' split
  all_goals simp_all

/-- A sparse node call returning a short prune leaves a nonempty workspace. -/
theorem sparse_short_autos (first : Bool) (g : Sparse.Graph n) (inf tcLevel fuel level nc : Nat)
    (st : SState n) {target : Nat}
    (hcap : 0 < (Generic.node first g inf tcLevel fuel level nc st).2.wsCap)
    (he : (Generic.node first g inf tcLevel fuel level nc st).1 = .unwind target true) :
    0 < (Generic.node first g inf tcLevel fuel level nc st).2.autos.size := by
  obtain ⟨leaf, lv, s, -, hx, ho⟩ := Sparse.node_origin first g inf tcLevel fuel level nc st he
  rw [ho] at hcap ⊢
  have hcap' : 0 < s.wsCap := by rw [← leafExit_wsCap leaf lv s]; exact hcap
  rcases leafExit_short_pair hcap' hx with h | h
  · exact autos_pos_of_backG h.2
  · exact autos_pos_of_backG h.2

/-! ### The node's refinement and target -/

section Node

variable {G : Hex.GraphIso.Sparse.Colored n k} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity)
include hn0 hn

theorem sparse_visit_part {first : Bool} {level nc : Nat} {st : SState n}
    (h : SparseNodeOk₀ G first level nc st) :
    PartFactsG n level (Sparse.visit (.ofGraph G.graph) level nc st).1
      (Sparse.visit (.ofGraph G.graph) level nc st).2.2 := by
  obtain ⟨t, s, rfl, hlevel, hni, -⟩ := h
  have hln := sparse_level_le' hni
  rw [sparse_visit_twG t _ level nc s (by omega) (by omega)]
  exact sparse_partFacts hn0 hn (hni.visit_ready hn0 hlevel).ok t

theorem sparse_visit_perm {first : Bool} {level nc : Nat} {st : SState n}
    (h : SparseNodeOk₀ G first level nc st) :
    (Sparse.visit (.ofGraph G.graph) level nc st).2.2.lab.toList.Perm (List.range n) := by
  obtain ⟨t, s, rfl, hlevel, hni, -⟩ := h
  have hln := sparse_level_le' hni
  rw [sparse_visit_twG t _ level nc s (by omega) (by omega)]
  exact sparse_labPerm' (s := (Sparse.visit (.ofGraph G.graph) level nc s).2.2) hn0
    (hni.visit_ready hn0 hlevel).ok

theorem sparse_visitOk {first : Bool} {level nc : Nat} {st : SState n}
    (h : SparseNodeOk₀ G first level nc st) (ha : ActiveOk st.ptn level nc st.active) :
    SparseVisitOk (.ofGraph G.graph) level st := by
  have hl := h.level_pos
  obtain ⟨t, s, rfl, hlevel, hni, -⟩ := h
  have hf := sparse_partFacts hn0 hn hni.ok t
  exact ⟨⟨G.graph, rfl⟩, hni.spec.label, hf.ptnSize, Nat.le_trans hf.ptnLast hl, ha.1⟩

theorem sparse_targetOk_node {first : Bool} {level nc : Nat} {st : SState n}
    (h : SparseNodeOk₀ G first level nc st) :
    SparseTargetOk (.ofGraph G.graph) level (Sparse.visit (.ofGraph G.graph) level nc st).1
      (if first then recordFirst level (Sparse.visit (.ofGraph G.graph) level nc st).2.1
          (Sparse.visit (.ofGraph G.graph) level nc st).2.2
        else compareCodes level (Sparse.visit (.ofGraph G.graph) level nc st).2.1
          (Sparse.visit (.ofGraph G.graph) level nc st).2.2) := by
  obtain ⟨t, s, rfl, hlevel, hni, -⟩ := h
  have hln := sparse_level_le' hni
  rw [sparse_visit_twG t _ level nc s (by omega) (by omega)]
  have hv := hni.visit_ready hn0 hlevel
  cases first
  · simp only [Bool.false_eq_true, ite_false]
    rw [compareCodes_twG]
    exact sparse_targetOk hn0 hn hlevel (hv.compare _).ready t
  · simp only [ite_true]
    rw [recordFirst_twG]
    exact sparse_targetOk hn0 hn hlevel (hv.record _).ready t

/-- `breakout` of a vertex of a sweep's target cell keeps `SInvG`. -/
theorem sparse_broken {level nc tc tv : Nat} {cell : VSet n} {s : SState n} (t : Array Int)
    (hlevel : 1 ≤ level) (hok : Sparse.Ready G level nc s)
    (htarget : Generic.Target Sparse.State.frame level tc cell s) (htv : cell.mem tv = true)
    (hs : SInvG sparseOps (.ofGraph G.graph) (twG (phi (n + 2) nautyInfinity) t s)) :
    SInvG sparseOps (.ofGraph G.graph) (brokenSt level tc tv (twG (phi (n + 2) nautyInfinity) t s)) := by
  have hln := sparse_level_le hok
  have hch := hok.child hn0 hlevel false htarget htv
  have hpf := sparse_partFacts hn0 hn hch.ok t
  rw [← sparse_child_twG t false level tc tv s (by omega)] at hpf
  exact SInvG.of (hpf.congr rfl rfl) { hs.rest with }

/-- The target cell of a sweep starts a cell. -/
theorem sparse_sweep_tc {level nc tc tv : Nat} {cell : VSet n} {s : SState n} (t : Array Int)
    (hok : Sparse.Ready G level nc s) (htarget : Generic.Target Sparse.State.frame level tc cell s)
    (htv : cell.mem tv = true) :
    tc = 0 ∨ (twG (phi (n + 2) nautyInfinity) t s).ptn[tc - 1]! ≤ level := by
  obtain ⟨len, hc, -⟩ := htarget
  have hne : cell ≠ VSet.empty := fun he => by rw [he, VSet.mem_empty] at htv; cases htv
  obtain ⟨⟨-, h2, -, -⟩, -, -⟩ := hc hne
  rcases h2 with h2 | h2
  · exact .inl h2
  · right
    show (s.ptn.map (phi (n + 2) nautyInfinity))[tc - 1]! ≤ level
    have hl := sparse_level_le hok
    have h2' : s.ptn[tc - 1]! ≤ level := h2
    rw [getElem!_map_phi (by omega), phi_ne (show s.ptn[tc - 1]! ≠ n + 2 by omega)]
    exact h2'

/-- The arguments of `breakout` at a sweep's vertex. -/
theorem sparse_sweep_args {level tc tv : Nat} {cell : VSet n} {s : SState n} (t : Array Int)
    (htarget : Generic.Target Sparse.State.frame level tc cell s) (hm : cell.mem tv = true) :
    tv < n ∧ tc < n ∧ ∃ j, tc ≤ j ∧ j < n ∧ (twG (phi (n + 2) nautyInfinity) t s).lab[j]! = tv := by
  obtain ⟨len, hc, hseg⟩ := htarget
  have hne : cell ≠ VSet.empty := fun he => by rw [he, VSet.mem_empty] at hm; cases hm
  obtain ⟨-, h2, h3⟩ := hc hne
  have hs := hseg _ hm
  rw [segN, List.mem_map] at hs
  obtain ⟨o, ho, e⟩ := hs
  rw [List.mem_range] at ho
  exact ⟨VSet.mem_lt hm, by omega, tc + o, by omega, by omega, e⟩

/-- `node_hlt` for the sparse search. -/
theorem sparse_leaf_lt {level nc : Nat} {st : SState n} (h : SparseNodeOk G false level nc st) :
    let g : Sparse.Graph n := .ofGraph G.graph
    let v := Sparse.visit g level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := Sparse.chooseTarget false g 100 level v.1 st₁
    ∀ tg s, (leafExit (Sparse.classify g level v.1 ct.2.2.2).1 level
      (Sparse.classify g level v.1 ct.2.2.2).2).1 = .unwind tg s → tg < level := by
  intro g v st₁ ct tg s he
  have hf : gcaF (Sparse.classify g level v.1 ct.2.2.2).2 = gcaF st := by
    rw [sparse_gcaF_classify, sparse_gcaF_target, gcaF_compare]; rfl
  unfold gcaF at hf
  simp only [Prod.mk.injEq] at hf
  obtain ⟨h1, h2, h3⟩ := hf
  obtain ⟨g1, g2, g3⟩ := (h.2.2 rfl).2
  exact leafExit_bound (by rw [h1]; exact g1) (by rw [h2]; exact g2) (by rw [h3]; exact g3) he

/-- `node_hDone` for the sparse search. -/
theorem sparse_leaf_done {level nc : Nat} {st : SState n} (h : SparseNodeOk₀ G false level nc st) :
    let g : Sparse.Graph n := .ofGraph G.graph
    let v := Sparse.visit g level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := Sparse.chooseTarget false g 100 level v.1 st₁
    (leafExit (Sparse.classify g level v.1 ct.2.2.2).1 level (Sparse.classify g level v.1 ct.2.2.2).2).1 =
        .done →
      v.1 < n ∧ (st₁.eqlevFirst = level ∨ 0 ≤ st₁.compCanon) := by
  intro g v st₁ ct hd
  have hint := sparse_classify_internal ((leafExit_done _ _ _).1 hd)
  have hle := (sparse_visit_part hn0 hn h).numcellsLe
  have hlt : v.1 < n := by
    have := hint.2
    change (Sparse.visit g level nc st).1 ≤ n at hle
    change (Sparse.visit g level nc st).1 ≠ n at this
    show (Sparse.visit g level nc st).1 < n
    omega
  refine ⟨hlt, ?_⟩
  apply Classical.byContradiction
  intro hno
  have hskip := sparse_chooseTarget_skip g 100 level v.1 st₁ (fun hc => hno hc.2)
  have h1 := hint.1
  rw [show ct.2.2.2 = st₁ from hskip] at h1
  apply h1
  constructor
  · exact fun he => hno (.inl he)
  · have : ¬ 0 ≤ st₁.compCanon := fun hc => hno (.inr hc)
    omega

/-- `proc_leafOk` for the sparse search. -/
theorem sparse_leafOk {level nc : Nat} {st : SState n} (h : SparseNodeOk₀ G false level nc st) :
    let g : Sparse.Graph n := .ofGraph G.graph
    let v := Sparse.visit g level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := Sparse.chooseTarget false g 100 level v.1 st₁
    LeafOkG ct.2.2.2 := by
  intro g v st₁ ct
  obtain ⟨t, s, rfl, -, -, hinv, -, hoff⟩ := h
  obtain ⟨last, hd, -⟩ := hoff rfl
  have hl : LeafI (twG (phi (n + 2) nautyInfinity) t s) := hinv.2.2.congr rfl rfl rfl rfl rfl rfl
  have hs : Sent (twG (phi (n + 2) nautyInfinity) t s) := ⟨last + 1, hd.2⟩
  have hl' : LeafI ct.2.2.2 :=
    sparse_leafI_target (leafI_compare (sparse_leafI_visit hl g level nc) _ _) false g 100 level _
  have hs' : Sent ct.2.2.2 := hs.congr (by
    rw [(sparse_chooseTarget_keeps false g 100 level v.1 st₁).2.1]
    exact compare_firstcode _ _ _)
  obtain ⟨h1, h2, h3⟩ := hl'
  obtain ⟨⟨f1, f2⟩, ⟨c1, c2⟩, e⟩ := h3 hs'
  exact ⟨f1, f2, c1, c2, e, h1, h2⟩

end Node

/-! ### The sparse instance -/

/-- The sparse node precondition with nauty.c's active set. -/
def sparseNodeOk (G : Hex.GraphIso.Sparse.Colored n k) (first : Bool) (level nc : Nat) (st : SState n) :
    Prop :=
  SparseNodeOk G first level nc st ∧ ActiveOk st.ptn level nc st.active

/-- The root call of `nauty()` on a sparse graph satisfies `sparseNodeOk`. -/
theorem sparseNodeOk_init (G : Hex.GraphIso.Sparse.Colored n k) (hn0 : 0 < n) :
    let p := Sparse.initialPartitionWith n k G.coloring.cells.toArray Fin.val
    sparseNodeOk G true 1 p.2.length (sparseInitialC (.ofGraph G.graph) p.1 p.2) := by
  intro p
  refine ⟨SparseNodeOk.root G hn0, fun v hv => ?_, initActive_card n _⟩
  have hok := (Sparse.NodeInv.initial G hn0).spec.node
  rcases hok.starts v hv with h | h
  · exact .inl h
  · right
    show (initPtn n nautyInfinity p.2)[v - 1]! ≤ 1
    have h' : (initPtn n (n + 2) p.2)[v - 1]! ≤ 1 := h
    rw [← initPtn_map (a := n + 2) (b := nautyInfinity) (by omega), getElem!_map_phi (by omega),
      phi_ne (show (initPtn n (n + 2) p.2)[v - 1]! ≠ n + 2 by omega)]
    exact h'

/-- HexGraphIso's sparse search laws on the coloured sparse graph `G`. -/
def sparseLaws (G : Hex.GraphIso.Sparse.Colored n k) (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) :
    NodeLaws (sparseLink (n := n)) (.ofGraph G.graph : Sparse.Graph n) where
  NodeOk := sparseNodeOk G
  SweepFirst := SparseSweepFirst G
  SweepOff := SparseSweepOff G
  level_pos h := h.1.level_pos
  level_le h := h.1.level_le
  inv h := by obtain ⟨⟨⟨t, s, rfl, -, hs, -⟩, -⟩, -⟩ := h; exact hs.scratch
  inv_first h := by obtain ⟨⟨t, s, rfl, -, hs, -⟩, -⟩ := h; exact hs.scratch.toBounded
  inv_off h := by obtain ⟨⟨t, s, rfl, -, hs, -⟩, -⟩ := h; exact hs.scratch.toBounded
  visitOk h := sparse_visitOk hn0 hn h.1.1 h.2
  targetOk h := sparse_targetOk_node hn0 hn h.1.1
  code_lt _ := sparse_visit_code_lt _ _ _ _
  visit_inv {first level nc st} h hs := by
    have hb : Sparse.Scratch.Bounded n st.canong.scratch := by
      obtain ⟨⟨⟨t, s, rfl, -, hs, -⟩, -⟩, -⟩ := h; exact hs.scratch
    have hsame := (sparseLink (n := n)).visit_same (.ofGraph G.graph) level nc st hb
      (sparse_visitOk hn0 hn h.1.1 h.2)
    have hpf := sparse_visit_part hn0 hn h.1.1
    have hl := hsame.field (·.lab) (fun _ _ => rfl)
    have hp := hsame.field (·.ptn) (fun _ _ => rfl)
    exact SInvG.of (hpf.congr hl.symm hp.symm) { hs.rest with }
  visit_active h := h.2
  visit_part h := sparse_visit_part hn0 hn h.1.1
  target_lt {_ level _ _} h hlt hint _ := by
    have hf := sparse_visit_part hn0 hn h.1.1
    exact sparse_targetcell_lt G.graph _ _ level 100 hint (sparse_visit_perm hn0 hn h.1.1) hf.ptnSize
      (Nat.le_trans hf.ptnLast h.1.level_pos) (hf.count ▸ hlt)
  first_start h := sparse_sweepFirst_start hn0 hn h.1 100
  first_child {level nc tc _ tv _ st} h := by
    refine ⟨sparse_sweepFirst_child hn0 h, activeOk_child true level nc tc tv st ?_⟩
    obtain ⟨⟨t, s, rfl, -, hok, htarget, hcur, -⟩, -⟩ := h
    exact sparse_sweep_tc hn0 hn t hok htarget (hcur tv rfl)
  first_next fuel h hd := sparse_sweepFirst_next hn0 hn h fuel hd
  first_broken hs h := by
    obtain ⟨⟨t, s, rfl, hlevel, hok, htarget, hcur, -⟩, -⟩ := h
    exact sparse_broken hn0 hn t hlevel hok htarget (hcur _ rfl) hs
  first_args h := by
    obtain ⟨⟨t, s, rfl, -, -, htarget, hcur, -⟩, -⟩ := h
    exact sparse_sweep_args hn0 hn t htarget (hcur _ rfl)
  first_orb {_ _ _ tv1 _ _} h := by
    obtain ⟨⟨t, st₀, rfl, -, -, -, hcur, -, hph⟩, -⟩ := h
    rcases hph with ⟨-, horb, -⟩ | ⟨hpast, -⟩
    · have h1 := horb tv1 (VSet.mem_lt (hcur tv1 rfl))
      show (st₀.orbits[tv1]! == tv1) = true
      simp [h1]
    · have := hpast rfl tv1 rfl
      omega
  off_start h := sparse_sweepOff_start hn0 hn h.1 100
  off_child {level nc tc tv _ st} h := by
    refine ⟨sparse_sweepOff_child hn0 h, activeOk_child false level nc tc tv st ?_⟩
    obtain ⟨⟨t, s, rfl, -, hok, htarget, hcur, -⟩, -⟩ := h
    exact sparse_sweep_tc hn0 hn t hok htarget (hcur tv rfl)
  off_next fuel h hd := sparse_sweepOff_next hn0 hn h fuel hd
  off_broken hs h := by
    obtain ⟨⟨t, s, rfl, hlevel, hok, htarget, hcur, -⟩, -⟩ := h
    exact sparse_broken hn0 hn t hlevel hok htarget (hcur _ rfl) hs
  off_args h := by
    obtain ⟨⟨t, s, rfl, -, -, htarget, hcur, -⟩, -⟩ := h
    exact sparse_sweep_args hn0 hn t htarget (hcur _ rfl)
  noFuel h hl := sparseNodeOk_noFuel hn0 hn h.1.1 100 hl
  unwind_lt {level nc st} h fuel tg s he := by
    have hl := h.1.level_pos
    cases fuel with
    | zero => simp [Generic.node] at he
    | succ fuel =>
      rw [Generic.node] at he
      revert tg s
      apply Generic.bound_node (fuel := fuel) ?_ _ 100 false level nc st hl
      · intro _
        dsimp only
        intro target short he
        exact sparse_leaf_lt hn0 hn h.1 target short he
      · intro first level numcells tc tv1 cursor cell index st _
        exact Generic.sweep_bound first _ nautyInf 100 fuel (n + 1)
          level numcells tc tv1 cursor cell index st
  leaf_lt h := sparse_leaf_lt hn0 hn h.1
  leaf_done h := sparse_leaf_done hn0 hn h.1.1
  leafOk h := sparse_leafOk hn0 hn h.1.1
  leafFits {level nc st} h _ :=
    sparse_store_fits (sparse_store_sweepOff 100 level nc st (h.1.2.2 rfl).1 (h.1.1.visit_parse hn0 hn)).1
  short_autos first fuel level nc st _ hcap he := sparse_short_autos first _ _ _ fuel level nc st hcap he

end NautyVerified.Proofs.Search
