import NautyVerified.Spec.SparseInfOps
import NautyVerified.Spec.SearchInfRun
import HexGraphIso.Nauty.Sparse.Reach
import HexGraphIso.Nauty.Sparse.Depth
import HexGraphIso.Nauty.Sparse.Reference
import HexGraphIso.Nauty.Sparse.DispatchFrame
import HexGraphIso.Nauty.Sparse.SelectedCell
import HexGraphIso.Nauty.Sparse.Fuel

/-!
# The sparse search with `inf = 2000000002`

The sparse counterpart of `Spec/SearchInfRun.lean`. HexGraphIso's sparse
search (`Generic.node` for `Sparse.policy`) run with `ptn`'s "infinity" `B`
from a state related by `twG (phi (n + 2) B) t` to a state of the run at
`n + 2` returns the related result (`sparseInfPolicy`). The relation is a
`Generic.SoundPolicy` for `sparseInfContract`, which extends HexGraphIso's
sparse partition-reachability contract `Sparse.reachContract`
(`NodeInv`/`Ready`/`FrameOut`), whose `SearchOk` bounds every level by `n`.
As in the dense proof, before the first leaf `t` agrees with the first run's
`firsttc` on the levels written so far (`AgreeTo`), and after it
`Depth last` keeps every hinted read at a level at most `last`.

`InvS` is what the transfer needs of a state besides the contract:
`noncheaplevel ≤ n + 1` (so `fmptn` at the noncheap level is unaffected) and
the size of `firstcode` (for the first leaf's `Depth`).
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso.Nauty
open Std.Do
set_option mvcgen.warning false

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {n k : Nat}

local notation "SState" => Hex.GraphIso.Nauty.Sparse.State

/-- No automorphism has been found: every vertex is its own orbit. -/
def OrbIdS (st : SState n) : Prop := ∀ v, v < n → st.orbits[v]! = v

/-- What the sparse transfer needs of a state besides the contract. -/
def InvS (st : SState n) : Prop :=
  st.noncheaplevel ≤ n + 1 ∧ st.firstcode.size = n + 2 ∧ LeafI st

theorem sparse_leafI_visit {st : SState n} (h : LeafI st) (g : Sparse.Graph n) (level numcells : Nat) :
    LeafI (Sparse.visit g level numcells st).2.2 := h.congr rfl rfl rfl rfl rfl rfl

theorem sparse_leafI_target {st : SState n} (h : LeafI st) (first : Bool) (g : Sparse.Graph n)
    (tcLevel level numcells : Nat) : LeafI (Sparse.chooseTarget first g tcLevel level numcells st).2.2.2 := by
  have e : leafF (Sparse.chooseTarget first g tcLevel level numcells st).2.2.2 = leafF st := by
    unfold Sparse.chooseTarget
    apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × SState n => leafF out.2.2.2 = leafF st)
    mvcgen
    all_goals simp_all +zetaDelta [leafF]
  exact h.of_leafF e

theorem sparse_leafF_classify (g : Sparse.Graph n) (level nc : Nat) (st : SState n) :
    leafF (Sparse.classify g level nc st).2 = leafF st := by
  unfold leafF Sparse.classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.noncheaplevel, apply_ite SearchState.cosetindex,
    apply_ite SearchState.firstcode, apply_ite SearchState.firstlab,
    apply_ite SearchState.canonlab, apply_ite SearchState.eqlevCanon, ite_self]

theorem sparse_leafI_classify {st : SState n} (h : LeafI st) (g : Sparse.Graph n) (level nc : Nat) :
    LeafI (Sparse.classify g level nc st).2 := h.of_leafF (sparse_leafF_classify g level nc st)

/-- The partition of a sparse state reached from the initial cells is a permutation. -/
theorem sparse_labPerm {G : Hex.GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : SState n}
    (hn0 : 0 < n) (h : Sparse.Ready G level numcells st) : LabPerm st.lab n :=
  labPerm_of_ok (st := st.frame) hn0 h.ok

theorem compareCodes_noncheapG {κ : Type} (level code : Nat) (st : SearchState n κ) :
    (compareCodes level code st).noncheaplevel = st.noncheaplevel := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.noncheaplevel, ite_self]

theorem sparse_level_le {G : Hex.GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : SState n}
    (h : Sparse.Ready G level numcells st) : level ≤ n :=
  level_le_of_ok h.ok

theorem sparse_level_le' {G : Hex.GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : SState n}
    (h : Sparse.NodeInv G level numcells st) : level ≤ n :=
  level_le_of_ok h.ok

theorem reference_fields {x y : SState n} (h : x.reference = y.reference) :
    x.firsttc = y.firsttc ∧ x.firstcode = y.firstcode :=
  ⟨congrArg (fun r => r.2.1) h, congrArg (fun r => r.1) h⟩

/-- A first-path node that is not a leaf has a nonempty target cell. -/
theorem sparse_first_cell {G : Hex.GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat}
    {st : SState n} (hn0 : 0 < n) (hlevel : 1 ≤ level) (h : Sparse.Ready G level numcells st)
    (hnc : numcells ≠ n) :
    ∃ v, (Sparse.chooseTarget true (.ofGraph G.graph) tcLevel level numcells st).2.1.nextElem none =
      some v := by
  have hc : numcells < n := by
    have := h.ok.count
    have := bcount_le st.ptn level n
    change numcells = bcount st.ptn level n at *
    omega
  obtain ⟨hcell, hlen, hb, hw⟩ := h.selected_cell (tcLevel := tcLevel) hn0 hlevel hc true (.inl rfl)
  have hv : (Sparse.chooseTarget true (.ofGraph G.graph) tcLevel level numcells st).2.1.mem
      st.lab[(Sparse.chooseTarget true (.ofGraph G.graph) tcLevel level numcells st).1.toNat]! = true := by
    rw [hw]
    apply mem_windowSet.mpr
    refine ⟨cellsReach_lt h.ok.reach _ (by omega), mem_segN_iff.mpr ⟨0, by omega, by simp⟩⟩
  rcases hs : (Sparse.chooseTarget true (.ofGraph G.graph) tcLevel level numcells st).2.1.nextElem none
    with _ | v
  · have := VSet.nextElem_none hs
      st.lab[(Sparse.chooseTarget true (.ofGraph G.graph) tcLevel level numcells st).1.toNat]! (Nat.zero_le _)
    rw [hv] at this; cases this
  · exact ⟨v, rfl⟩

/-- The relation between the two sparse runs: HexGraphIso's sparse
reachability contract, and under `InvS` the run with infinity `B`, from the
first run's state related by `twG (phi (n + 2) B) t`, returns the related
result. -/
def sparseInfContract (G : Hex.GraphIso.Sparse.Colored n k) (tcLevel B : Nat) :
    Generic.Contract (SState n) n where
  nodePre _ _ level numcells st := 1 ≤ level ∧ Sparse.NodeInv G level numcells st
  nodePost fuel first level numcells st r :=
    Sparse.FrameOut G (level - 1) level st r.2 ∧ (InvS st →
      (first = false → ∀ last t, Depth last st → AgreeTo (last + 1) t st.firsttc →
        Generic.node false (.ofGraph G.graph : Sparse.Graph n) B tcLevel fuel level numcells
            (twG (phi (n + 2) B) t st) = (r.1, twG (phi (n + 2) B) t r.2) ∧
          Depth last r.2 ∧ r.2.firsttc = st.firsttc ∧ InvS r.2) ∧
      (first = true → ∀ t, OrbIdS st → AgreeTo (level - 1) t st.firsttc →
        ∃ t', Generic.node true (.ofGraph G.graph : Sparse.Graph n) B tcLevel fuel level numcells
            (twG (phi (n + 2) B) t st) = (r.1, twG (phi (n + 2) B) t' r.2) ∧
          (r.1 = .fuel ∨ ∃ last, Depth last r.2 ∧ AgreeTo (last + 1) t' r.2.firsttc) ∧ InvS r.2))
  sweepPre _ _ _ level numcells tc _ cursor cell _ st :=
    1 ≤ level ∧ Sparse.Ready G level numcells st ∧ Generic.Target Sparse.State.frame level tc cell st ∧
      ∀ v, cursor = some v → cell.mem v = true
  sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st r :=
    Sparse.FrameOut G level level st r.2.2 ∧ (InvS st →
      (Generic.Past first tv1 cursor → ∀ last t, Depth last st → AgreeTo (last + 1) t st.firsttc →
        Generic.sweep first (.ofGraph G.graph : Sparse.Graph n) B tcLevel fuel cfuel level numcells tc tv1
            cursor cell index (twG (phi (n + 2) B) t st) = (r.1, r.2.1, twG (phi (n + 2) B) t r.2.2) ∧
          Depth last r.2.2 ∧ r.2.2.firsttc = st.firsttc ∧ InvS r.2.2) ∧
      (first = true → cursor = some tv1 → ∀ t, OrbIdS st → AgreeTo level t st.firsttc →
        ∃ t', Generic.sweep true (.ofGraph G.graph : Sparse.Graph n) B tcLevel fuel cfuel level numcells tc
            tv1 cursor cell index (twG (phi (n + 2) B) t st) = (r.1, r.2.1, twG (phi (n + 2) B) t' r.2.2) ∧
          (r.1 = .fuel ∨ ∃ last, Depth last r.2.2 ∧ AgreeTo (last + 1) t' r.2.2.firsttc) ∧ InvS r.2.2))

section
variable {G : Hex.GraphIso.Sparse.Colored n k} {tcLevel B : Nat}

theorem sparseInf_node_zero (first : Bool) (level numcells : Nat) (st : SState n)
    (hin : (sparseInfContract G tcLevel B).nodePre 0 first level numcells st) :
    (sparseInfContract G tcLevel B).nodePost 0 first level numcells st (.fuel, st) := by
  refine ⟨Sparse.FrameOut.refl hin.2, fun hinv => ⟨?_, ?_⟩⟩
  · intro _ last t hd _
    exact ⟨by simp [Generic.node], hd, rfl, hinv⟩
  · intro _ t _ _
    exact ⟨t, by simp [Generic.node], .inl rfl, hinv⟩

theorem sparseInf_sweep_none (fuel cfuel : Nat) (first : Bool) (level numcells tc tv1 : Nat)
    (cell : VSet n) (index : Nat) (st : SState n)
    (hin : (sparseInfContract G tcLevel B).sweepPre fuel cfuel first level numcells tc tv1 none cell
      index st) :
    (sparseInfContract G tcLevel B).sweepPost fuel cfuel first level numcells tc tv1 none cell index st
      (.done, index, st) := by
  refine ⟨hin.2.1.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hin.2.1.scratch.toBounded,
    fun hinv => ⟨?_, ?_⟩⟩
  · intro _ last t hd _
    exact ⟨by simp [Generic.sweep], hd, rfl, hinv⟩
  · intro _ h; cases h

theorem sparseInf_sweep_zero (fuel : Nat) (first : Bool) (level numcells tc tv1 tv : Nat)
    (cell : VSet n) (index : Nat) (st : SState n)
    (hin : (sparseInfContract G tcLevel B).sweepPre fuel 0 first level numcells tc tv1 (some tv) cell
      index st) :
    (sparseInfContract G tcLevel B).sweepPost fuel 0 first level numcells tc tv1 (some tv) cell index st
      (.fuel, index, st) := by
  refine ⟨hin.2.1.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hin.2.1.scratch.toBounded,
    fun hinv => ⟨?_, ?_⟩⟩
  · intro _ last t hd _
    exact ⟨by simp [Generic.sweep], hd, rfl, hinv⟩
  · intro _ _ t _ _
    exact ⟨t, by simp [Generic.sweep], .inl rfl, hinv⟩

theorem sparse_nodeStep_off (hn0 : 0 < n) (hB : n + 2 < B) (fuel : Nat)
    (next : Generic.SweepFn (SState n) n)
    (hnext : (sparseInfContract G tcLevel B).sweepValid fuel (n + 1) next)
    (level numcells : Nat) (st : SState n) (hlevel : 1 ≤ level) (h : Sparse.NodeInv G level numcells st)
    (hinv : InvS st) (last : Nat) (t : Array Int) (hd : Depth last st)
    (ha : AgreeTo (last + 1) t st.firsttc) :
    Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel
        (fun first level numcells tc tv1 cursor cell index st =>
          Generic.sweep first (.ofGraph G.graph : Sparse.Graph n) B tcLevel fuel (n + 1) level numcells tc
            tv1 cursor cell index st)
        false level numcells (twG (phi (n + 2) B) t st) =
      ((Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel next false level numcells st).1,
        twG (phi (n + 2) B) t
          (Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel next false level numcells st).2) ∧
      Depth last (Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel next false level numcells st).2 ∧
      (Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel next false level numcells st).2.firsttc =
        st.firsttc ∧
      InvS (Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel next false level numcells st).2 := by
  have hln := sparse_level_le' h
  have hL1 : level < n + 2 := by omega
  have hL2 : level < B := by omega
  have D := Sparse.depthPolicy (.ofGraph G.graph) (n + 2) tcLevel last
  have F := Sparse.referencePolicy (.ofGraph G.graph) (n + 2) tcLevel
  have hv := h.visit_ready hn0 hlevel
  have hvd := D.visit level numcells st hd
  have hvf := F.visit level numcells st
  have hcode := D.code level numcells st
  have hvi : InvS (Sparse.visit (.ofGraph G.graph) level numcells st).2.2 := hinv
  unfold Generic.nodeStep
  dsimp only [Sparse.policy, Generic.Policy.visit, Generic.Policy.recordFirst,
    Generic.Policy.compareCodes, Generic.Policy.chooseTarget, Generic.Policy.firstterminal,
    Generic.Policy.classify, Generic.Policy.leafExit, Generic.Policy.cheapCheck,
    Generic.Policy.afterSweep] at hvd hvf hcode ⊢
  rw [sparse_visit_twG t _ level numcells st hL1 hL2]
  generalize Sparse.visit (.ofGraph G.graph) level numcells st = r at hv hvd hvf hcode hvi ⊢
  obtain ⟨nc, code, s1⟩ := r
  dsimp only at hv hvd hvf hcode hvi ⊢
  simp only [Bool.false_eq_true, ite_false]
  -- code comparison
  have hcd := compareCodes_depth (level := level) hvd hcode
  have hcf := F.compare level code s1
  have hcl := hv.compare code
  dsimp only [Sparse.policy, Generic.Policy.compareCodes] at hcf
  have hci : InvS (compareCodes level code s1) :=
    ⟨by rw [compareCodes_noncheapG]; exact hvi.1, by rw [(reference_fields hcf).2]; exact hvi.2.1,
      leafI_compare hvi.2.2 level code⟩
  rw [compareCodes_twG]
  generalize compareCodes level code s1 = s2 at hcd hcf hcl hci ⊢
  -- target
  have ht : false = false → s2.eqlevFirst = level → t[level]! = s2.firsttc[level]! := by
    intro _ he
    rw [(reference_fields hcf).1, (reference_fields hvf).1]
    exact ha.2 level hlevel (by have := hcd.1; omega)
  rw [sparse_chooseTarget_twG t false _ tcLevel level nc s2 hL1 hL2 ht]
  have htd := D.target level nc s2 hcd
  have htf := F.target level nc s2
  have htl := hcl.ready.target_frame false tcLevel
  have htarget := hcl.ready.target hn0 hlevel false tcLevel
  have hk := sparse_chooseTarget_keeps false (.ofGraph G.graph) tcLevel level nc s2
  dsimp only [Sparse.policy, Generic.Policy.chooseTarget] at htd htf hk htarget
  have hti : InvS (Sparse.chooseTarget false (.ofGraph G.graph) tcLevel level nc s2).2.2.2 :=
    ⟨by rw [hk.1]; exact hci.1, by rw [hk.2.1]; exact hci.2.1,
      sparse_leafI_target hci.2.2 false _ tcLevel level nc⟩
  generalize Sparse.chooseTarget false (.ofGraph G.graph) tcLevel level nc s2 = c
    at htd htf htl htarget hti hk ⊢
  obtain ⟨tc, cell, size, s3⟩ := c
  dsimp only at htd htf htl htarget hti hk ⊢
  simp only [Bool.false_eq_true, ite_false]
  -- classification
  rw [sparse_classify_twG]
  have hcld := (D.classify level nc s3 htd).1
  have hclf := F.classify level nc s3
  have hclr := htl.ready.classify
  dsimp only [Sparse.policy, Generic.Policy.classify] at hcld hclf
  have hcli : InvS (Sparse.classify (.ofGraph G.graph) level nc s3).2 :=
    ⟨by rw [sparse_classify_noncheap]; exact hti.1, by rw [(reference_fields hclf).2]; exact hti.2.1,
      sparse_leafI_classify hti.2.2 _ level nc⟩
  generalize Sparse.classify (.ofGraph G.graph) level nc s3 = cl at hcld hclf hclr hcli ⊢
  obtain ⟨leaf, s4⟩ := cl
  dsimp only at hcld hclf hclr hcli ⊢
  -- leaf action
  rw [leafExit_twG t leaf level s4 (by have := hcli.1; omega) (by have := hcli.1; omega)]
  have hled := D.leaf leaf level s4 trivial hcld
  have hlef := F.leaf leaf level s4
  have hler := hclr.ready.leaf leaf
  dsimp only [Sparse.policy, Generic.Policy.leafExit] at hled hlef
  have hlei : InvS (leafExit leaf level s4).2 :=
    ⟨by rw [leafExit_noncheap]; exact hcli.1, by rw [(reference_fields hlef).2]; exact hcli.2.1,
      leafI_leafExit hcli.2.2 leaf level (sparse_labPerm hn0 hclr.ready)⟩
  generalize leafExit leaf level s4 = le at hled hlef hler hlei ⊢
  obtain ⟨exit, s5⟩ := le
  dsimp only at hled hlef hler hlei ⊢
  have hf5 : s5.firsttc = st.firsttc := by
    rw [(reference_fields hlef).1, (reference_fields hclf).1, (reference_fields htf).1,
      (reference_fields hcf).1, (reference_fields hvf).1]
  cases exit with
  | fuel => exact ⟨rfl, hled, hf5, hlei⟩
  | unwind target short => exact ⟨rfl, hled, hf5, hlei⟩
  | done =>
    simp only []
    rw [cheapCheck_twG t false level s5 hL1 hL2]
    have hchd := D.cheap false level s5 hled
    have hchf := F.cheap false level s5
    have hchr := hler.ready.cheap false
    dsimp only [Sparse.policy, Generic.Policy.cheapCheck] at hchd hchf
    have hchi : InvS (cheapCheck false level s5) := by
      refine ⟨?_, by rw [(reference_fields hchf).2]; exact hlei.2.1, leafI_cheap hlei.2.2 false level⟩
      unfold cheapCheck; split
      · show level + 1 ≤ n + 1; omega
      · exact hlei.1
    have htarget6 : Generic.Target Sparse.State.frame level tc.toNat cell (cheapCheck false level s5) :=
      ((htarget.of_out hclr.frame.effect).of_out hler.frame.effect).of_out hchr.frame.effect
    have hsw := hnext false level nc tc.toNat ((cell.nextElem none).getD 0) (cell.nextElem none) cell 0
      (cheapCheck false level s5) ⟨hlevel, hchr.ready, htarget6, fun v hv => VSet.nextElem_mem hv⟩
    obtain ⟨-, himp⟩ := hsw
    obtain ⟨hoff, -⟩ := himp hchi
    have ha6 : AgreeTo (last + 1) t (cheapCheck false level s5).firsttc := by
      rw [(reference_fields hchf).1, hf5]; exact ha
    obtain ⟨heq, hd7, hf7, hinv7⟩ := hoff (fun h => absurd h (by decide)) last t hchd ha6
    rw [heq]
    generalize next false level nc tc.toNat ((cell.nextElem none).getD 0) (cell.nextElem none) cell 0
      (cheapCheck false level s5) = r7 at hinv7 hd7 hf7 ⊢
    obtain ⟨exit7, index, s7⟩ := r7
    dsimp only at hinv7 hd7 hf7 ⊢
    have hf7' : s7.firsttc = st.firsttc := by rw [hf7, (reference_fields hchf).1, hf5]
    cases exit7 with
    | done =>
      simp only [Bool.false_eq_true, ite_false]
      rw [afterSweep_twG]
      refine ⟨rfl, ?_, ?_, ?_⟩
      · exact D.afterSweep level size index s7 hd7
      · unfold afterSweep; split <;> exact hf7'
      · unfold afterSweep; split <;> exact hinv7
    | fuel => exact ⟨rfl, hd7, hf7', hinv7⟩
    | unwind target short => exact ⟨rfl, hd7, hf7', hinv7⟩

theorem sparse_nodeStep_first (hn0 : 0 < n) (hB : n + 2 < B) (fuel : Nat)
    (next : Generic.SweepFn (SState n) n)
    (hnext : (sparseInfContract G tcLevel B).sweepValid fuel (n + 1) next)
    (level numcells : Nat) (st : SState n) (hlevel : 1 ≤ level) (h : Sparse.NodeInv G level numcells st)
    (hinv : InvS st) (t : Array Int) (horb : OrbIdS st) (ha : AgreeTo (level - 1) t st.firsttc) :
    ∃ t', Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel
        (fun first level numcells tc tv1 cursor cell index st =>
          Generic.sweep first (.ofGraph G.graph : Sparse.Graph n) B tcLevel fuel (n + 1) level numcells tc
            tv1 cursor cell index st)
        true level numcells (twG (phi (n + 2) B) t st) =
      ((Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel next true level numcells st).1,
        twG (phi (n + 2) B) t'
          (Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel next true level numcells st).2) ∧
      ((Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel next true level numcells st).1 = .fuel ∨
        ∃ last, Depth last
            (Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel next true level numcells st).2 ∧
          AgreeTo (last + 1) t'
            (Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel next true level numcells st).2.firsttc) ∧
      InvS (Generic.nodeStep (.ofGraph G.graph : Sparse.Graph n) tcLevel next true level numcells st).2 := by
  have hln := sparse_level_le' h
  have hL1 : level < n + 2 := by omega
  have hL2 : level < B := by omega
  have hv := h.visit_ready hn0 hlevel
  have hvi : InvS (Sparse.visit (.ofGraph G.graph) level numcells st).2.2 := hinv
  have hvo : OrbIdS (Sparse.visit (.ofGraph G.graph) level numcells st).2.2 := horb
  have hva : AgreeTo (level - 1) t (Sparse.visit (.ofGraph G.graph) level numcells st).2.2.firsttc := ha
  have hcode := (Sparse.depthPolicy (.ofGraph G.graph) (n + 2) tcLevel 0).code level numcells st
  unfold Generic.nodeStep
  dsimp only [Sparse.policy, Generic.Policy.visit, Generic.Policy.recordFirst,
    Generic.Policy.compareCodes, Generic.Policy.chooseTarget, Generic.Policy.firstterminal,
    Generic.Policy.classify, Generic.Policy.leafExit, Generic.Policy.cheapCheck,
    Generic.Policy.afterSweep] at hcode ⊢
  rw [sparse_visit_twG t _ level numcells st hL1 hL2]
  generalize Sparse.visit (.ofGraph G.graph) level numcells st = r at hv hvi hvo hva hcode ⊢
  obtain ⟨nc, code, s1⟩ := r
  dsimp only at hv hvi hvo hva hcode ⊢
  simp only [ite_true]
  -- the first-path code
  rw [recordFirst_twG]
  have hrl := hv.record code
  have hri : InvS (recordFirst level code s1) := ⟨hvi.1, by simp [recordFirst, hvi.2.1],
    leafI_record hvi.2.2 hcode⟩
  have hro : OrbIdS (recordFirst level code s1) := hvo
  have hra : AgreeTo (level - 1) t (recordFirst level code s1).firsttc := hva
  generalize recordFirst level code s1 = s2 at hrl hri hro hra ⊢
  -- target
  rw [sparse_chooseTarget_twG t true _ tcLevel level nc s2 hL1 hL2 (fun h => absurd h (by decide))]
  have htl := hrl.ready.target_frame true tcLevel
  have htarget := hrl.ready.target hn0 hlevel true tcLevel
  have hk := sparse_chooseTarget_keeps true (.ofGraph G.graph) tcLevel level nc s2
  have hcell := sparse_first_cell (tcLevel := tcLevel) hn0 hlevel hrl.ready
  have hl3 := sparse_leafI_target hri.2.2 true (.ofGraph G.graph) tcLevel level nc
  generalize Sparse.chooseTarget true (.ofGraph G.graph) tcLevel level nc s2 = c
    at htl htarget hk hcell hl3 ⊢
  obtain ⟨tc, cell, size, s3⟩ := c
  dsimp only at htl htarget hk hcell ⊢
  simp only [ite_true]
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hk
  simp only [ite_true] at hk4
  have hi3 : InvS s3 := ⟨by rw [hk1]; exact hri.1, by rw [hk2]; exact hri.2.1, hl3⟩
  have ho3 : OrbIdS s3 := fun v hv => by rw [hk3]; exact hro v hv
  have ha3 : AgreeTo level (t.set! level tc) s3.firsttc := by
    rw [hk4]
    have := hra.set tc
    rwa [Nat.sub_add_cancel hlevel] at this
  by_cases hleaf : (nc == n) = true
  · simp only [hleaf, ite_true]
    refine ⟨(t.set! level tc).set! (level + 1) (-1), by rw [firstterminal_twG]; rfl,
      .inr ⟨level, ?_, ?_⟩, ?_⟩
    · refine ⟨Nat.le_refl _, ?_⟩
      show (s3.firstcode.set! (level + 1) codeSentinel)[level + 1]! = codeSentinel
      exact Array.getElem!_set!_self _ _ _ (by rw [hi3.2.1]; omega)
    · exact ha3.set (-1)
    · exact ⟨hi3.1, by show (s3.firstcode.set! (level + 1) codeSentinel).size = n + 2; simp [hi3.2.1],
        leafI_firstterminal hi3.2.2 level (sparse_labPerm hn0 htl.ready)⟩
  · simp only [hleaf, Bool.false_eq_true, ite_false]
    obtain ⟨v, hv⟩ := hcell (by simpa using hleaf)
    rw [cheapCheck_twG (t.set! level tc) true level s3 hL1 hL2]
    have hchr := htl.ready.cheap true
    have hcheq : ∃ k', cheapCheck true level s3 = { s3 with noncheaplevel := k' } ∧ k' ≤ n + 1 := by
      unfold cheapCheck; split
      · exact ⟨level + 1, rfl, by omega⟩
      · exact ⟨s3.noncheaplevel, rfl, hi3.1⟩
    obtain ⟨k', hk', hk'le⟩ := hcheq
    have hchi : InvS (cheapCheck true level s3) := ⟨by rw [hk']; exact hk'le, by rw [hk']; exact hi3.2.1,
      leafI_cheap hi3.2.2 true level⟩
    have hcho : OrbIdS (cheapCheck true level s3) := by rw [hk']; exact ho3
    have hcha : AgreeTo level (t.set! level tc) (cheapCheck true level s3).firsttc := by
      rw [hk']; exact ha3
    have htarget6 : Generic.Target Sparse.State.frame level tc.toNat cell (cheapCheck true level s3) :=
      htarget.of_out hchr.frame.effect
    rw [hv]
    have hsw := hnext true level nc tc.toNat v (some v) cell 0
      (cheapCheck true level s3) ⟨hlevel, hchr.ready, htarget6, fun w hw => by
        cases hw; exact VSet.nextElem_mem hv⟩
    obtain ⟨-, himp⟩ := hsw
    obtain ⟨-, hfirst⟩ := himp hchi
    obtain ⟨t'', heq, hph, hinv7⟩ := hfirst rfl rfl (t.set! level tc) hcho hcha
    simp only [Option.getD_some] at heq ⊢
    rw [heq]
    generalize next true level nc tc.toNat v (some v) cell 0 (cheapCheck true level s3) = r7
      at hinv7 hph ⊢
    obtain ⟨exit7, index, s7⟩ := r7
    dsimp only at hinv7 hph ⊢
    refine ⟨t'', ?_⟩
    cases exit7 with
    | done =>
      simp only [ite_true]
      rw [show ({ afterSweep true level size index (twG (phi (n + 2) B) t'' s7) with
          order := (afterSweep true level size index (twG (phi (n + 2) B) t'' s7)).order * index } :
            SState n) = twG (phi (n + 2) B) t'' { afterSweep true level size index s7 with
          order := (afterSweep true level size index s7).order * index } by
        rw [afterSweep_twG]; rfl]
      refine ⟨rfl, .inr ?_, ?_⟩
      · rcases hph with h | ⟨last, hd7, ha7⟩
        · cases h
        · refine ⟨last, ?_, ?_⟩
          · show Depth last (afterSweep true level size index s7)
            unfold afterSweep; split <;> exact hd7
          · show AgreeTo (last + 1) t'' (afterSweep true level size index s7).firsttc
            unfold afterSweep; split <;> exact ha7
      · show InvS (afterSweep true level size index s7)
        unfold afterSweep; split <;> exact hinv7
    | fuel => exact ⟨rfl, .inl rfl, hinv7⟩
    | unwind target short =>
      refine ⟨rfl, ?_, hinv7⟩
      rcases hph with h | h
      · cases h
      · exact .inr h

/-- The continuation of a sparse sweep after a child returns: prune, recover, sweep on. -/
theorem sparse_resume_off (hn0 : 0 < n) (hB : n + 2 < B) (fuel cfuel : Nat)
    (next : Generic.SweepFn (SState n) n)
    (hnext : (sparseInfContract G tcLevel B).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv : Nat) (cell cell' : VSet n) (index : Nat)
    (base out : SState n) (hlevel : 1 ≤ level) (h : Sparse.Ready G level numcells base)
    (htarget : Generic.Target Sparse.State.frame level tc cell base)
    (hout : Sparse.FrameOut G level level base out) (hsub : ∀ v, cell'.mem v = true → cell.mem v = true)
    (hpast : first = true → tv1 ≤ tv) (hinv : InvS out) (last : Nat) (t : Array Int)
    (hd : Depth last out) (ha : AgreeTo (last + 1) t out.firsttc) :
    Generic.resume B (fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first (.ofGraph G.graph : Sparse.Graph n) B tcLevel fuel cfuel level numcells tc tv1
          cursor cell index st)
        first level numcells tc tv1 tv cell' index (twG (phi (n + 2) B) t out) =
      ((Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).1,
        (Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).2.1,
        twG (phi (n + 2) B) t (Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).2.2) ∧
      Depth last (Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).2.2 ∧
      (Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).2.2.firsttc =
        out.firsttc ∧
      InvS (Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).2.2 ∧
      Sparse.FrameOut G level level base
        (Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).2.2 := by
  have hln := sparse_level_le h
  have D := Sparse.depthPolicy (.ofGraph G.graph) (n + 2) tcLevel last
  have F := Sparse.referencePolicy (.ofGraph G.graph) (n + 2) tcLevel
  have hr := h.recover hn0 hlevel hout
  have hrd := D.recover level out hd
  have hrf := F.recover level out
  have hri : InvS ((Sparse.policy (n := n)).recover (n + 2) level out) := by
    refine ⟨?_, by rw [(reference_fields hrf).2]; exact hinv.2.1,
      (leafI_recover hinv.2.2 (n + 2) level).congr rfl rfl rfl rfl rfl rfl⟩
    show (Hex.GraphIso.Nauty.recover (n + 2) level out).noncheaplevel ≤ n + 1
    rw [recover_noncheap]; split <;> omega
  let cell'' := if (!first && tv == tv1) = true then longprune cell' out.fixedpts out.autos else cell'
  have hsub' : ∀ v, cell''.mem v = true → cell.mem v = true := by
    intro v hv
    simp only [cell''] at hv
    split at hv
    · exact hsub v (Hex.GraphIso.Nauty.longprune_subset hv)
    · exact hsub v hv
  have hsw := hnext first level numcells tc tv1 (cell''.nextElem (some tv)) cell''
    (if (first && ((Sparse.policy (n := n)).recover (n + 2) level out).orbits[tv]! == tv1) = true
      then index + 1 else index)
    ((Sparse.policy (n := n)).recover (n + 2) level out)
    ⟨hlevel, hr.1, (htarget.subset hsub').of_out hr.2.effect, fun v hv => VSet.nextElem_mem hv⟩
  obtain ⟨hsout, himp⟩ := hsw
  obtain ⟨hoff, -⟩ := himp hri
  have ha' : AgreeTo (last + 1) t ((Sparse.policy (n := n)).recover (n + 2) level out).firsttc := by
    rw [(reference_fields hrf).1]; exact ha
  have hP : Generic.Past first tv1 (cell''.nextElem (some tv)) := by
    intro hf v hv
    have := (VSet.nextElem_eq_some_iff.mp hv).2.1
    change tv + 1 ≤ v at this
    have := hpast hf
    omega
  obtain ⟨heq, hd', hf', hinv'⟩ := hoff hP last t hrd ha'
  have hf'' : (next first level numcells tc tv1 (cell''.nextElem (some tv)) cell''
      (if (first && ((Sparse.policy (n := n)).recover (n + 2) level out).orbits[tv]! == tv1) = true
        then index + 1 else index)
      ((Sparse.policy (n := n)).recover (n + 2) level out)).2.2.firsttc = out.firsttc := by
    rw [hf', (reference_fields hrf).1]
  unfold Generic.resume
  simp only [Id.run]
  rw [sparse_recover_twG t level out (by omega) (by omega)]
  dsimp only [Sparse.policy, Generic.Policy.longprune, Generic.Policy.recover, Generic.Policy.orbit]
    at heq hd' hf'' hinv' hsout ⊢
  by_cases hlp : (!first && tv == tv1) = true
  · simp only [cell'', hlp, ite_true] at heq hd' hf'' hinv' hsout ⊢
    exact ⟨heq, hd', hf'', hinv', hr.2.trans hsout⟩
  · simp only [cell'', hlp, Bool.false_eq_true, ite_false] at heq hd' hf'' hinv' hsout ⊢
    exact ⟨heq, hd', hf'', hinv', hr.2.trans hsout⟩

theorem sparse_sweepStep_off (hn0 : 0 < n) (hB : n + 2 < B) (fuel cfuel : Nat)
    (descend : Generic.NodeFn (SState n)) (next : Generic.SweepFn (SState n) n)
    (hdescend : (sparseInfContract G tcLevel B).nodeValid fuel descend)
    (hnext : (sparseInfContract G tcLevel B).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv : Nat) (cell : VSet n) (index : Nat) (st : SState n)
    (hlevel : 1 ≤ level) (h : Sparse.Ready G level numcells st)
    (htarget : Generic.Target Sparse.State.frame level tc cell st) (htv : cell.mem tv = true)
    (hpast : first = true → tv1 < tv) (hinv : InvS st) (last : Nat) (t : Array Int)
    (hd : Depth last st) (ha : AgreeTo (last + 1) t st.firsttc) :
    Generic.sweepStep B (fun first level numcells st =>
          Generic.node first (.ofGraph G.graph : Sparse.Graph n) B tcLevel fuel level numcells st)
        (fun first level numcells tc tv1 cursor cell index st =>
          Generic.sweep first (.ofGraph G.graph : Sparse.Graph n) B tcLevel fuel cfuel level numcells tc tv1
            cursor cell index st)
        first level numcells tc tv1 tv cell index (twG (phi (n + 2) B) t st) =
      ((Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).1,
        (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.1,
        twG (phi (n + 2) B) t
          (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.2) ∧
      Depth last (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.2 ∧
      (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.2.firsttc =
        st.firsttc ∧
      InvS (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.2 := by
  have hln := sparse_level_le h
  have D := Sparse.depthPolicy (.ofGraph G.graph) (n + 2) tcLevel last
  have F := Sparse.referencePolicy (.ofGraph G.graph) (n + 2) tcLevel
  have hft : (first && tv == tv1) = false := by
    cases first
    · rfl
    · simp only [Bool.true_and, beq_eq_false_iff_ne]; have := hpast rfl; omega
  unfold Generic.sweepStep
  dsimp only [Generic.Policy.orbit, Generic.Policy.afterChildFirst, Generic.Policy.leaveChild]
  simp only [Id.run]
  have e0 : (twG (phi (n + 2) B) t st).orbits = st.orbits := rfl
  by_cases hc : (!first || st.orbits[tv]! == tv) = true
  · have hc' : (!first || (twG (phi (n + 2) B) t st).orbits[tv]! == tv) = true := hc
    simp only [hc, hc', ite_true, hft, Bool.false_eq_true, ite_false]
    rw [sparse_child_twG t first level tc tv st (by omega)]
    have hch := h.child hn0 hlevel first htarget htv
    have hcd := D.child first level tc tv st hd
    have hcf := F.child first level tc tv st
    have hdn := hdescend false (level + 1) (numcells + 1) ((Sparse.policy (n := n)).child first level tc tv st)
      ⟨by omega, hch⟩
    obtain ⟨hdreach, hdimp⟩ := hdn
    obtain ⟨hoff, -⟩ := hdimp (by
      cases first <;> exact ⟨hinv.1, hinv.2.1,
        (leafI_child hinv.2.2 _ level tc tv (fun _ => VSet.mem_lt htv)).congr rfl rfl rfl rfl rfl rfl⟩)
    have hac : AgreeTo (last + 1) t ((Sparse.policy (n := n)).child first level tc tv st).firsttc := by
      rw [(reference_fields hcf).1]; exact ha
    obtain ⟨heq, hdd, hfd, hinvd⟩ := hoff rfl last t hcd hac
    rw [heq]
    generalize descend false (level + 1) (numcells + 1) ((Sparse.policy (n := n)).child first level tc tv st) = rd
      at hdreach hinvd hdd hfd ⊢
    obtain ⟨exit, s8⟩ := rd
    dsimp only at hdreach hinvd hdd hfd ⊢
    simp only [Nat.add_sub_cancel] at hdreach
    rw [leave_twG]
    have hout : Sparse.FrameOut G level level st { s8 with fixedpts := s8.fixedpts.erase tv } :=
      (h.child_frame hn0 hlevel first htarget htv hdreach).leave tv
    have hld : Depth last ({ s8 with fixedpts := s8.fixedpts.erase tv } : SState n) := hdd
    have hli : InvS ({ s8 with fixedpts := s8.fixedpts.erase tv } : SState n) := hinvd
    have hla : AgreeTo (last + 1) t ({ s8 with fixedpts := s8.fixedpts.erase tv } : SState n).firsttc := by
      show AgreeTo (last + 1) t s8.firsttc
      rw [hfd, (reference_fields hcf).1]; exact ha
    have hlf : ({ s8 with fixedpts := s8.fixedpts.erase tv } : SState n).firsttc = st.firsttc := by
      show s8.firsttc = st.firsttc
      rw [hfd, (reference_fields hcf).1]
    unfold Generic.advance
    simp only [Id.run]
    cases exit with
    | fuel => exact ⟨rfl, hld, hlf, hli⟩
    | done =>
      obtain ⟨h1, h2, h3, h4, -⟩ := sparse_resume_off (G := G) (tcLevel := tcLevel) hn0 hB fuel cfuel next
        hnext first level numcells tc tv1 tv cell cell index st _ hlevel h htarget hout
        (fun _ hv => hv) (fun h => Nat.le_of_lt (hpast h)) hli last t hld hla
      exact ⟨h1, h2, h3.trans hlf, h4⟩
    | unwind target short =>
      by_cases hlt : target < level
      · simp only [hlt, ite_true]; exact ⟨rfl, hld, hlf, hli⟩
      · simp only [hlt, ite_false]
        dsimp only [Sparse.policy, Generic.Policy.shortprune]
        have e4 : shortprune cell (twG (phi (n + 2) B) t { s8 with fixedpts := s8.fixedpts.erase tv }) =
            shortprune cell ({ s8 with fixedpts := s8.fixedpts.erase tv } : SState n) := rfl
        rw [e4]
        cases short with
        | true =>
          simp only [ite_true]
          obtain ⟨h1, h2, h3, h4, -⟩ := sparse_resume_off (G := G) (tcLevel := tcLevel) hn0 hB fuel cfuel
            next hnext first level numcells tc tv1 tv cell
            (shortprune cell ({ s8 with fixedpts := s8.fixedpts.erase tv } : SState n)) index st _ hlevel h
            htarget hout
            (fun v hv => Hex.GraphIso.Nauty.shortprune_subset
              (st := Sparse.State.frame ({ s8 with fixedpts := s8.fixedpts.erase tv } : SState n)) hv) (fun h => Nat.le_of_lt (hpast h)) hli last t hld hla
          exact ⟨h1, h2, h3.trans hlf, h4⟩
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          obtain ⟨h1, h2, h3, h4, -⟩ := sparse_resume_off (G := G) (tcLevel := tcLevel) hn0 hB fuel cfuel
            next hnext first level numcells tc tv1 tv cell cell index st _ hlevel h htarget hout
            (fun _ hv => hv) (fun h => Nat.le_of_lt (hpast h)) hli last t hld hla
          exact ⟨h1, h2, h3.trans hlf, h4⟩
  · have hc' : ¬ (!first || (twG (phi (n + 2) B) t st).orbits[tv]! == tv) = true := hc
    simp only [hc, hc', Bool.false_eq_true, ite_false]
    have hsw := hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell
      (if (first && st.orbits[tv]! == tv1) = true then index + 1 else index) st
      ⟨hlevel, h, htarget, fun v hv => VSet.nextElem_mem hv⟩
    obtain ⟨-, himp⟩ := hsw
    obtain ⟨hoff, -⟩ := himp hinv
    exact hoff (Generic.Past.next hpast) last t hd ha

theorem sparse_sweepStep_first (hn0 : 0 < n) (hB : n + 2 < B) (fuel cfuel : Nat)
    (descend : Generic.NodeFn (SState n)) (next : Generic.SweepFn (SState n) n)
    (hdescend : (sparseInfContract G tcLevel B).nodeValid fuel descend)
    (hnext : (sparseInfContract G tcLevel B).sweepValid fuel cfuel next)
    (level numcells tc tv1 : Nat) (cell : VSet n) (index : Nat) (st : SState n)
    (hlevel : 1 ≤ level) (h : Sparse.Ready G level numcells st)
    (htarget : Generic.Target Sparse.State.frame level tc cell st) (htv : cell.mem tv1 = true)
    (hinv : InvS st) (t : Array Int) (horb : OrbIdS st) (ha : AgreeTo level t st.firsttc) :
    ∃ t', Generic.sweepStep B (fun first level numcells st =>
          Generic.node first (.ofGraph G.graph : Sparse.Graph n) B tcLevel fuel level numcells st)
        (fun first level numcells tc tv1 cursor cell index st =>
          Generic.sweep first (.ofGraph G.graph : Sparse.Graph n) B tcLevel fuel cfuel level numcells tc tv1
            cursor cell index st)
        true level numcells tc tv1 tv1 cell index (twG (phi (n + 2) B) t st) =
      ((Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell index st).1,
        (Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell index st).2.1,
        twG (phi (n + 2) B) t'
          (Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell index st).2.2) ∧
      ((Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell index st).1 = .fuel ∨
        ∃ last, Depth last (Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell
            index st).2.2 ∧
          AgreeTo (last + 1) t' (Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell
            index st).2.2.firsttc) ∧
      InvS (Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell index st).2.2 := by
  have hln := sparse_level_le h
  have F := Sparse.referencePolicy (.ofGraph G.graph) (n + 2) tcLevel
  have horb1 : st.orbits[tv1]! = tv1 := horb tv1 (VSet.mem_lt htv)
  unfold Generic.sweepStep
  dsimp only [Sparse.policy, Generic.Policy.orbit, Generic.Policy.afterChildFirst,
    Generic.Policy.leaveChild]
  simp only [Id.run]
  have hc : (!true || st.orbits[tv1]! == tv1) = true := by simp [horb1]
  have hc' : (!true || (twG (phi (n + 2) B) t st).orbits[tv1]! == tv1) = true := hc
  simp only [hc, hc', ite_true, Bool.true_and, beq_self_eq_true]
  rw [sparse_child_twG t true level tc tv1 st (by omega)]
  have hch := h.child hn0 hlevel true htarget htv
  have hcf := F.child true level tc tv1 st
  have hdn := hdescend true (level + 1) (numcells + 1) ((Sparse.policy (n := n)).child true level tc tv1 st)
    ⟨by omega, hch⟩
  obtain ⟨hdreach, hdimp⟩ := hdn
  obtain ⟨-, hfirst⟩ := hdimp ⟨hinv.1, hinv.2.1,
    (leafI_child hinv.2.2 true level tc tv1 (fun _ => VSet.mem_lt htv)).congr rfl rfl rfl rfl rfl rfl⟩
  have hac : AgreeTo (level + 1 - 1) t ((Sparse.policy (n := n)).child true level tc tv1 st).firsttc := by
    rw [(reference_fields hcf).1, Nat.add_sub_cancel]; exact ha
  obtain ⟨t', heq, hph, hinvd⟩ := hfirst rfl t horb hac
  rw [heq]
  generalize descend true (level + 1) (numcells + 1) ((Sparse.policy (n := n)).child true level tc tv1 st) = rd
    at hdreach hinvd hph ⊢
  obtain ⟨exit, s8⟩ := rd
  dsimp only at hdreach hinvd hph ⊢
  simp only [Nat.add_sub_cancel] at hdreach
  rw [afterChildFirst_twG, leave_twG]
  let s9 : SState n := { afterChildFirst level tv1 s8 with
    fixedpts := (afterChildFirst level tv1 s8).fixedpts.erase tv1 }
  have hout : Sparse.FrameOut G level level st s9 :=
    ((h.child_frame hn0 hlevel true htarget htv hdreach).afterChild level tv1).leave tv1
  have hli : InvS s9 := hinvd
  refine ⟨t', ?_⟩
  unfold Generic.advance
  simp only [Id.run]
  cases exit with
  | fuel => exact ⟨rfl, .inl rfl, hli⟩
  | done =>
    obtain ⟨last, hd8, ha8⟩ := hph.resolve_left (by intro h; cases h)
    obtain ⟨h1, h2, h3, h4, -⟩ := sparse_resume_off (G := G) (tcLevel := tcLevel) hn0 hB fuel cfuel next
      hnext true level numcells tc tv1 tv1 cell cell index st s9 hlevel h htarget hout
      (fun _ hv => hv) (fun _ => Nat.le_refl _) hli last t' hd8 ha8
    have ha9 : AgreeTo (last + 1) t' s9.firsttc := ha8
    exact ⟨h1, .inr ⟨last, h2, by rw [← h3] at ha9; exact ha9⟩, h4⟩
  | unwind target short =>
    obtain ⟨last, hd8, ha8⟩ := hph.resolve_left (by intro h; cases h)
    have hd9 : Depth last s9 := hd8
    have ha9 : AgreeTo (last + 1) t' s9.firsttc := ha8
    by_cases hlt : target < level
    · simp only [hlt, ite_true]; exact ⟨rfl, .inr ⟨last, hd9, ha9⟩, hli⟩
    · simp only [hlt, ite_false]
      dsimp only [Sparse.policy, Generic.Policy.shortprune]
      have e4 : shortprune cell (twG (phi (n + 2) B) t' s9) = shortprune cell s9 := rfl
      rw [e4]
      cases short with
      | true =>
        simp only [ite_true]
        obtain ⟨h1, h2, h3, h4, -⟩ := sparse_resume_off (G := G) (tcLevel := tcLevel) hn0 hB fuel cfuel
          next hnext true level numcells tc tv1 tv1 cell (shortprune cell s9) index st s9 hlevel h htarget
          hout (fun v hv => Hex.GraphIso.Nauty.shortprune_subset (st := Sparse.State.frame s9) hv) (fun _ => Nat.le_refl _) hli last t' hd9 ha9
        exact ⟨h1, .inr ⟨last, h2, by rw [← h3] at ha9; exact ha9⟩, h4⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        obtain ⟨h1, h2, h3, h4, -⟩ := sparse_resume_off (G := G) (tcLevel := tcLevel) hn0 hB fuel cfuel
          next hnext true level numcells tc tv1 tv1 cell cell index st s9 hlevel h htarget hout
          (fun _ hv => hv) (fun _ => Nat.le_refl _) hli last t' hd9 ha9
        exact ⟨h1, .inr ⟨last, h2, by rw [← h3] at ha9; exact ha9⟩, h4⟩

/-- The two sparse runs' relation is a sound contract for HexGraphIso's sparse search. -/
theorem sparseInfPolicy (hn0 : 0 < n) (hB : n + 2 < B) :
    Generic.SoundPolicy (.ofGraph G.graph : Sparse.Graph n) (n + 2) tcLevel (sparseInfContract G tcLevel B) where
  node_zero := sparseInf_node_zero
  node_step := by
    intro fuel next hnext first level numcells st hin
    have hnextR : (Sparse.reachContract G).sweepValid fuel (n + 1) next :=
      fun first level numcells tc tv1 cursor cell index st hpre =>
        (hnext first level numcells tc tv1 cursor cell index st hpre).1
    refine ⟨Sparse.reach_node G hn0 tcLevel hnextR first level numcells st hin.1 hin.2,
      fun hinv => ⟨?_, ?_⟩⟩
    · intro hf last t hd ha
      subst hf
      rw [Generic.node]
      exact sparse_nodeStep_off hn0 hB fuel next hnext level numcells st hin.1 hin.2 hinv last t hd ha
    · intro hf t horb ha
      subst hf
      rw [Generic.node]
      exact sparse_nodeStep_first hn0 hB fuel next hnext level numcells st hin.1 hin.2 hinv t horb ha
  sweep_none := sparseInf_sweep_none
  sweep_zero := sparseInf_sweep_zero
  sweep_step := by
    intro fuel cfuel descend next hdescend hnext first level numcells tc tv1 tv cell index st hin
    obtain ⟨hlevel, h, htarget, hcur⟩ := hin
    have htv := hcur tv rfl
    have hdR : (Sparse.reachContract G).nodeValid fuel descend :=
      fun first level numcells st hpre => (hdescend first level numcells st hpre).1
    have hnR : (Sparse.reachContract G).sweepValid fuel cfuel next :=
      fun first level numcells tc tv1 cursor cell index st hpre =>
        (hnext first level numcells tc tv1 cursor cell index st hpre).1
    refine ⟨Sparse.reach_sweep G hn0 hdR hnR first level numcells tc tv1 tv index cell st hlevel h
      htarget htv, fun hinv => ⟨?_, ?_⟩⟩
    · intro hpast last t hd ha
      rw [Generic.sweep]
      exact sparse_sweepStep_off hn0 hB fuel cfuel descend next hdescend hnext first level numcells tc tv1
        tv cell index st hlevel h htarget htv (fun hf => hpast hf tv rfl) hinv last t hd ha
    · intro hf hc t horb ha
      subst hf
      cases hc
      rw [Generic.sweep]
      exact sparse_sweepStep_first hn0 hB fuel cfuel descend next hdescend hnext level numcells tc tv1 cell
        index st hlevel h htarget htv hinv t horb ha

end

/-! ## nauty's sparse root call -/

/-- The sparse search state nauty starts from: HexGraphIso's `Sparse.initial`
with `NAUTY_INFINITY` in `ptn` and the zero-filled `firsttc` of the allocator. -/
def sparseInitialC (g : Sparse.Graph n) (lab0 : Array Nat) (cellEnds : List Nat) : SState n :=
  { Sparse.initial g lab0 cellEnds with
    ptn := initPtn n nautyInfinity cellEnds
    firsttc := .replicate (n + 2) 0 }

theorem sparseInitialC_eq (g : Sparse.Graph n) (lab0 : Array Nat) (cellEnds : List Nat) :
    sparseInitialC g lab0 cellEnds =
      twG (phi (n + 2) nautyInfinity) (.replicate (n + 2) 0) (Sparse.initial g lab0 cellEnds) := by
  unfold sparseInitialC twG
  rw [show (Sparse.initial g lab0 cellEnds).ptn = initPtn n (n + 2) cellEnds from rfl,
    initPtn_map (by omega)]

theorem sparse_initial_invS (hn0 : 0 < n) (g : Sparse.Graph n) (lab0 : Array Nat) (cellEnds : List Nat) :
    InvS (Sparse.initial g lab0 cellEnds) :=
  ⟨by show 1 ≤ n + 1; omega, by simp [Sparse.initial], Nat.le_refl 1, hn0, fun ⟨i, hi⟩ => by
    change (Array.replicate (n + 2) 0)[i]! = codeSentinel at hi
    by_cases h : i < n + 2
    · rw [getElem!_pos _ i (by simpa using h)] at hi; simp [codeSentinel] at hi
    · rw [getElem!_neg _ i (by simpa using h)] at hi; simp [codeSentinel] at hi⟩

theorem sparse_initial_orbId (g : Sparse.Graph n) (lab0 : Array Nat) (cellEnds : List Nat) :
    OrbIdS (Sparse.initial g lab0 cellEnds) := by
  intro v hv
  show (Array.ofFn (n := n) fun i => i.val)[v]! = v
  rw [getElem!_pos _ v (by simpa using hv)]
  simp

/-- The refinement code nauty.c stores in a `short` is below `32768`. -/
theorem sparse_visit_code_lt (g : Sparse.Graph n) (level numcells : Nat) (st : SState n) :
    (Sparse.visit g level numcells st).2.1 < 32768 := by
  have h := Sparse.refineWith_code_lt g level st.lab st.ptn st.active numcells st.canong.scratch
  have : codeSentinel = 32767 := rfl
  show (Sparse.refineWith g level st.lab st.ptn st.active numcells st.canong.scratch).longcode < 32768
  omega

/-- nauty's sparse root call, with `NAUTY_INFINITY` and the zero-filled
`firsttc`, ends with HexGraphIso's exit and HexGraphIso's state up to the
infinity map and `firsttc`. -/
theorem sparse_node_inf (G : Hex.GraphIso.Sparse.Colored n k) (hn0 : 0 < n)
    (hn : n + 2 < nautyInfinity) :
    let p := Sparse.initialPartitionWith n k G.coloring.cells.toArray Fin.val
    ∃ t', Generic.node true (.ofGraph G.graph : Sparse.Graph n) nautyInfinity 100 (n + 2) 1 p.2.length
        (sparseInitialC (.ofGraph G.graph) p.1 p.2) =
      ((Generic.node true (.ofGraph G.graph : Sparse.Graph n) (n + 2) 100 (n + 2) 1 p.2.length
          (Sparse.initial (.ofGraph G.graph) p.1 p.2)).1,
        twG (phi (n + 2) nautyInfinity) t'
          (Generic.node true (.ofGraph G.graph : Sparse.Graph n) (n + 2) 100 (n + 2) 1 p.2.length
            (Sparse.initial (.ofGraph G.graph) p.1 p.2)).2) := by
  intro p
  have hpost := Generic.node_sound (sparseInfPolicy (G := G) (tcLevel := 100) (B := nautyInfinity) hn0 hn)
    true (n + 2) 1 p.2.length (Sparse.initial (.ofGraph G.graph) p.1 p.2)
    ⟨Nat.le_refl _, Sparse.NodeInv.initial G hn0⟩
  obtain ⟨-, himp⟩ := hpost
  obtain ⟨-, hfirst⟩ := himp (sparse_initial_invS hn0 _ _ _)
  have hag : AgreeTo (1 - 1) (.replicate (n + 2) 0) (Sparse.initial (.ofGraph G.graph) p.1 p.2).firsttc :=
    ⟨by simp [Sparse.initial], fun i h1 h2 => absurd h2 (by omega)⟩
  obtain ⟨t', heq, -, -⟩ := hfirst rfl _ (sparse_initial_orbId _ _ _) hag
  exact ⟨t', by rw [sparseInitialC_eq, heq]⟩

theorem sparse_finish_twG (g : Sparse.Graph n) (f : Nat → Nat) (t : Array Int) (st : SState n) :
    Sparse.finish g (twG f t st) = twG f t (Sparse.finish g st) := rfl

/-- The corollary for HexGraphIso's sparse run on a nonempty graph: nauty's
root call, finished, is `Sparse.run` up to the infinity map and `firsttc`. -/
theorem sparse_run_inf (G : Hex.GraphIso.Sparse.Colored n k) (hn0 : 0 < n)
    (hn : n + 2 < nautyInfinity) :
    let p := Sparse.initialPartitionWith n k G.coloring.cells.toArray Fin.val
    ∃ t', Sparse.finish (.ofGraph G.graph)
        (Generic.node true (.ofGraph G.graph : Sparse.Graph n) nautyInfinity 100 (n + 2) 1 p.2.length
          (sparseInitialC (.ofGraph G.graph) p.1 p.2)).2 =
      twG (phi (n + 2) nautyInfinity) t' (Sparse.run (.ofGraph G.graph) p.1 p.2) := by
  intro p
  obtain ⟨t', heq⟩ := sparse_node_inf G hn0 hn
  refine ⟨t', ?_⟩
  rw [heq]
  unfold Sparse.run Sparse.runState
  rw [ite_eq_right (by simp; omega)]
  rfl

/-! ## The node precondition of the sparse run -/

/-- The renamed-run part of the sparse node precondition: `st` is the image
under `twG (phi (n + 2) nautyInfinity) t` of a state `st₂` of HexGraphIso's
sparse run meeting the contract's node precondition, `InvS`, and on the first
path the identity orbits and the first-path hints so far, off it a first leaf
(`Depth`). The sparse counterpart of `NodeOk₀`. -/
def SparseNodeOk₀ (G : Hex.GraphIso.Sparse.Colored n k) (first : Bool) (level numcells : Nat)
    (st : SState n) : Prop :=
  ∃ t st₂, st = twG (phi (n + 2) nautyInfinity) t st₂ ∧ 1 ≤ level ∧
    Sparse.NodeInv G level numcells st₂ ∧ InvS st₂ ∧
    (first = true → OrbIdS st₂ ∧ AgreeTo (level - 1) t st₂.firsttc) ∧
    (first = false → ∃ last, Depth last st₂ ∧ AgreeTo (last + 1) t st₂.firsttc)

theorem SparseNodeOk₀.level_pos {G : Hex.GraphIso.Sparse.Colored n k} {first : Bool} {level numcells : Nat}
    {st : SState n} (h : SparseNodeOk₀ G first level numcells st) : 1 ≤ level := by
  obtain ⟨_, _, _, h1, _⟩ := h; exact h1

theorem SparseNodeOk₀.level_le {G : Hex.GraphIso.Sparse.Colored n k} {first : Bool} {level numcells : Nat}
    {st : SState n} (h : SparseNodeOk₀ G first level numcells st) : level ≤ n := by
  obtain ⟨_, _, _, _, h2, _⟩ := h; exact sparse_level_le' h2

/-- A node call satisfying `SparseNodeOk₀` is the renamed image of HexGraphIso's call. -/
theorem sparseNodeOk_run {G : Hex.GraphIso.Sparse.Colored n k} {first : Bool} {level numcells : Nat}
    {st : SState n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : SparseNodeOk₀ G first level numcells st)
    (tcLevel fuel : Nat) :
    ∃ t' st₂, Sparse.NodeInv G level numcells st₂ ∧
      Generic.node first (.ofGraph G.graph : Sparse.Graph n) nautyInfinity tcLevel fuel level numcells st =
        ((Generic.node first (.ofGraph G.graph : Sparse.Graph n) (n + 2) tcLevel fuel level numcells st₂).1,
          twG (phi (n + 2) nautyInfinity) t'
            (Generic.node first (.ofGraph G.graph : Sparse.Graph n) (n + 2) tcLevel fuel level numcells st₂).2) := by
  obtain ⟨t, st₂, rfl, hlevel, hok, hinv, hfirst, hoff⟩ := h
  have hpost := Generic.node_sound (sparseInfPolicy (G := G) (tcLevel := tcLevel) (B := nautyInfinity) hn0 hn)
    first fuel level numcells st₂ ⟨hlevel, hok⟩
  obtain ⟨-, himp⟩ := hpost
  obtain ⟨hoffP, hfirstP⟩ := himp hinv
  cases first with
  | true =>
    obtain ⟨horb, hag⟩ := hfirst rfl
    obtain ⟨t', heq, -, -⟩ := hfirstP rfl t horb hag
    exact ⟨t', st₂, hok, heq⟩
  | false =>
    obtain ⟨last, hd, hag⟩ := hoff rfl
    obtain ⟨heq, -, -, -⟩ := hoffP rfl last t hd hag
    exact ⟨t, st₂, hok, heq⟩

/-- With nauty's node fuel, a sparse node call satisfying `SparseNodeOk₀` never runs out of fuel. -/
theorem sparseNodeOk_noFuel {G : Hex.GraphIso.Sparse.Colored n k} {first : Bool} {level numcells : Nat}
    {st : SState n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : SparseNodeOk₀ G first level numcells st)
    (tcLevel : Nat) (hlev : level ≤ n) :
    (Generic.node first (.ofGraph G.graph : Sparse.Graph n) nautyInfinity tcLevel (n + 3 - level) level
      numcells st).1 ≠ .fuel := by
  have hlevel := h.level_pos
  obtain ⟨t', st₂, hok, heq⟩ := sparseNodeOk_run hn0 hn h tcLevel (n + 3 - level)
  rw [heq]
  exact Sparse.node_noFuel G hn0 first tcLevel _ level numcells st₂ hlevel hok (by omega)

/-- The root call of `nauty()` on a sparse graph satisfies `SparseNodeOk₀`. -/
theorem sparseNodeOk_root (G : Hex.GraphIso.Sparse.Colored n k) (hn0 : 0 < n) :
    let p := Sparse.initialPartitionWith n k G.coloring.cells.toArray Fin.val
    SparseNodeOk₀ G true 1 p.2.length (sparseInitialC (.ofGraph G.graph) p.1 p.2) := by
  intro p
  refine ⟨.replicate (n + 2) 0, Sparse.initial (.ofGraph G.graph) p.1 p.2, sparseInitialC_eq _ _ _,
    Nat.le_refl _, Sparse.NodeInv.initial G hn0, sparse_initial_invS hn0 _ _ _,
    fun _ => ⟨sparse_initial_orbId _ _ _, ?_⟩, fun h => absurd h (by decide)⟩
  exact ⟨by simp [Sparse.initial], fun i h1 h2 => absurd h2 (by omega)⟩

end NautyVerified.Spec.SearchInf
