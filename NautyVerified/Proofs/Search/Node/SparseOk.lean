import NautyVerified.Proofs.Search.Node.OtherHex
import NautyVerified.Proofs.Search.Node.FirstHex
import NautyVerified.Spec.SparseSweepOk

/-!
# The sparse sweeps keep their invariants

`sparse_sweepOff_next`: a child step of an off-path sweep of HexGraphIso's
sparse search run with `inf = nautyInfinity` (`otherChildG`) that does not end
the sweep leaves `SparseSweepOff` for the rest of it; `sparse_sweepFirst_next`
is the same for a first-path sweep (`firstChildG`). The first child of a
first-path sweep installs the native store (`sparse_first_store`).
-/

namespace NautyVerified.Proofs.Search

open Hex.GraphIso.Nauty
open NautyVerified.Spec.SearchInf

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {n k : Nat}

local notation "SState" => Hex.GraphIso.Nauty.Sparse.State

theorem sparse_recover_gcaFirst (inf level : Nat) (st : SState n) :
    ((Sparse.policy (n := n)).recover inf level st).gcaFirst = st.gcaFirst := by
  change (recoverLevels level (recoverPtn inf level st)).gcaFirst = st.gcaFirst
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.gcaFirst, ite_self]

theorem sparse_gcaSw_recover {inf level : Nat} {st : SState n} (h : st.gcaFirst ≤ level) :
    GcaSw level ((Sparse.policy (n := n)).recover inf level st) := by
  refine ⟨by rw [sparse_recover_gcaFirst]; exact h, recover_canon_le (inf := inf) level st, ?_⟩
  show (Hex.GraphIso.Nauty.recover inf level st).noncheaplevel ≤ level + 1
  rw [recover_noncheap]; split <;> omega

/-- The continuation of a sparse sweep after a child: the recovered state of a
pruned cell is in `SparseSweepOff₀`. -/
theorem sparse_recover_sweepOff₀ {G : Hex.GraphIso.Sparse.Colored n k} {level numcells tc tv : Nat}
    {cell cell' : VSet n} {st₀ s9 : SState n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (t : Array Int)
    (hlevel : 1 ≤ level) (hok : Sparse.Ready G level numcells st₀) (htarget : Generic.Target Sparse.State.frame level tc cell st₀)
    (hout : Sparse.FrameOut G level level st₀ s9) (hi9 : InvS s9) (last : Nat) (hd9 : Depth last s9)
    (ha9 : AgreeTo (last + 1) t s9.firsttc) (hsub : ∀ v, cell'.mem v = true → cell.mem v = true) :
    SparseSweepOff₀ G level numcells tc cell' (cell'.nextElem (some tv))
      ((Sparse.policy (n := n)).recover nautyInf level (twG (phi (n + 2) nautyInfinity) t s9)) := by
  have hln := sparse_level_le hok
  have D := Sparse.depthPolicy (.ofGraph G.graph) (n + 2) 100 last
  have F := Sparse.referencePolicy (.ofGraph G.graph) (n + 2) 100
  have hr := hok.recover hn0 hlevel hout
  have hrd := D.recover level s9 hd9
  have hrf := F.recover level s9
  have hri : InvS ((Sparse.policy (n := n)).recover (n + 2) level s9) := by
    refine ⟨?_, by rw [(reference_fields hrf).2]; exact hi9.2.1,
      (leafI_recover hi9.2.2 (n + 2) level).congr rfl rfl rfl rfl rfl rfl⟩
    show (Hex.GraphIso.Nauty.recover (n + 2) level s9).noncheaplevel ≤ n + 1
    rw [recover_noncheap]; split <;> omega
  rw [sparse_recover_twG t level s9 (by omega) (Nat.lt_trans (by omega : level < n + 2) hn)]
  exact ⟨t, _, rfl, hlevel, hr.1, (htarget.subset hsub).of_out hr.2.effect,
    fun v hv => VSet.nextElem_mem hv, hri, last, hrd, by rw [(reference_fields hrf).1]; exact ha9⟩

/-- A child step of an off-path sparse sweep that does not end it keeps `SparseSweepOff`. -/
theorem sparse_sweepOff_next {G : Hex.GraphIso.Sparse.Colored n k} {level numcells tc tv1 tv : Nat}
    {cell : VSet n} {st : SState n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity)
    (h : SparseSweepOff G level numcells tc cell (some tv) st) (fuel : Nat)
    (hdone : (otherChildG (.ofGraph G.graph : Sparse.Graph n) nautyInf 100 fuel level numcells tc tv1 tv
      cell st).1 = .done) :
    SparseSweepOff G level numcells tc
      (otherChildG (.ofGraph G.graph : Sparse.Graph n) nautyInf 100 fuel level numcells tc tv1 tv cell st).2.1
      ((otherChildG (.ofGraph G.graph : Sparse.Graph n) nautyInf 100 fuel level numcells tc tv1 tv cell
        st).2.1.nextElem (some tv))
      (otherChildG (.ofGraph G.graph : Sparse.Graph n) nautyInf 100 fuel level numcells tc tv1 tv cell st).2.2 := by
  obtain ⟨⟨t, st₀, rfl, hlevel, hok, htarget, hcur, hinv, last, hd, ha⟩, hs, hg⟩ := h
  have htv := hcur tv rfl
  have hln := sparse_level_le hok
  have D := Sparse.depthPolicy (.ofGraph G.graph) (n + 2) 100 last
  have F := Sparse.referencePolicy (.ofGraph G.graph) (n + 2) 100
  have hch := hok.child hn0 hlevel false htarget htv
  have hcd := D.child false level tc tv st₀ hd
  have hcf := F.child false level tc tv st₀
  have hci : InvS ((Sparse.policy (n := n)).child false level tc tv st₀) := ⟨hinv.1, hinv.2.1,
    (leafI_child hinv.2.2 false level tc tv (fun h => absurd h (by decide))).congr rfl rfl rfl rfl rfl rfl⟩
  have hpost := Generic.node_sound (sparseInfPolicy (G := G) (tcLevel := 100) (B := nautyInfinity) hn0 hn)
    false fuel (level + 1) (numcells + 1) ((Sparse.policy (n := n)).child false level tc tv st₀)
    ⟨by omega, hch⟩
  obtain ⟨hdreach, himp⟩ := hpost
  obtain ⟨hoff, -⟩ := himp hci
  have hac : AgreeTo (last + 1) t ((Sparse.policy (n := n)).child false level tc tv st₀).firsttc := by
    rw [(reference_fields hcf).1]; exact ha
  obtain ⟨heq, hdd, hfd, hinvd⟩ := hoff rfl last t hcd hac
  have hsc : Sparse.Store G.graph ((Sparse.policy (n := n)).child false level tc tv st₀) :=
    (hs.child false level tc tv).congr rfl rfl rfl
  have hsd := Sparse.node_store G hn0 false 100 fuel (level + 1) (numcells + 1) _ (by omega) hch hsc
  have hgd : (Generic.node false (.ofGraph G.graph : Sparse.Graph n) (n + 2) 100 fuel (level + 1)
      (numcells + 1) ((Sparse.policy (n := n)).child false level tc tv st₀)).2.gcaFirst ≤ level := by
    rw [Sparse.node_gca]; exact hg.1
  unfold otherChildG at hdone ⊢
  rw [sparse_child_twG t false level tc tv st₀ (by omega), heq] at hdone ⊢
  generalize Generic.node false (.ofGraph G.graph : Sparse.Graph n) (n + 2) 100 fuel (level + 1)
    (numcells + 1) ((Sparse.policy (n := n)).child false level tc tv st₀) = rd
    at hdreach hdd hfd hinvd hsd hgd hdone ⊢
  obtain ⟨exit, s8⟩ := rd
  dsimp only at hdreach hdd hfd hinvd hsd hgd hdone ⊢
  simp only [Nat.add_sub_cancel] at hdreach
  let s9 : SState n := { s8 with fixedpts := s8.fixedpts.erase tv }
  have e9 : (Generic.Policy.leaveChild (n := n) tv (twG (phi (n + 2) nautyInfinity) t s8) : SState n) =
      twG (phi (n + 2) nautyInfinity) t s9 := rfl
  have hout : Sparse.FrameOut G level level st₀ s9 :=
    (hok.child_frame hn0 hlevel false htarget htv hdreach).leave tv
  have ha9 : AgreeTo (last + 1) t s9.firsttc := by
    show AgreeTo (last + 1) t s8.firsttc
    rw [hfd, (reference_fields hcf).1]; exact ha
  have hres : ∀ cell' : VSet n, (∀ v, cell'.mem v = true → cell.mem v = true) →
      SparseSweepOff G level numcells tc cell' (cell'.nextElem (some tv))
        ((Sparse.policy (n := n)).recover nautyInf level (twG (phi (n + 2) nautyInfinity) t s9)) :=
    fun cell' hsub => ⟨sparse_recover_sweepOff₀ hn0 hn t hlevel hok htarget hout hinvd last hdd ha9 hsub,
      (show Sparse.Store G.graph (twG (phi (n + 2) nautyInfinity) t s9) from
        (hsd.leave tv).congr rfl rfl rfl).recover nautyInf level, sparse_gcaSw_recover hgd⟩
  have hlong : ∀ cell' : VSet n, (∀ v, cell'.mem v = true → cell.mem v = true) →
      ∀ v, (if (tv == tv1) = true then Generic.Policy.longprune (n := n) cell'
        (twG (phi (n + 2) nautyInfinity) t s9) else cell').mem v = true → cell.mem v = true := by
    intro cell' hsub v hv
    split at hv
    · exact hsub v (Hex.GraphIso.Nauty.longprune_subset hv)
    · exact hsub v hv
  cases exit with
  | fuel => cases hdone
  | done =>
    simp only [e9] at hdone ⊢
    exact hres _ (hlong cell fun _ hv => hv)
  | unwind target short =>
    by_cases hlt : target < level
    · simp only [hlt, ite_true] at hdone; cases hdone
    · simp only [hlt, ite_false, e9] at hdone ⊢
      cases short with
      | true =>
        simp only [ite_true]
        exact hres _ (hlong _ fun v hv => Hex.GraphIso.Nauty.shortprune_subset
          (st := Sparse.State.frame (twG (phi (n + 2) nautyInfinity) t s9)) hv)
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        exact hres _ (hlong cell fun _ hv => hv)

/-- The continuation of a first-path sparse sweep after a child: the recovered
state of a pruned cell is in `SparseSweepFirst`, past its first vertex. -/
theorem sparse_recover_sweepFirst {G : Hex.GraphIso.Sparse.Colored n k}
    {level numcells tc tv1 tv : Nat} {cell cell' : VSet n} {st₀ s9 : SState n} (hn0 : 0 < n)
    (hn : n + 2 < nautyInfinity) (t : Array Int) (hlevel : 1 ≤ level) (hle : tv1 ≤ tv)
    (hok : Sparse.Ready G level numcells st₀) (htarget : Generic.Target Sparse.State.frame level tc cell st₀)
    (hout : Sparse.FrameOut G level level st₀ s9) (hi9 : InvS s9) (last : Nat) (hd9 : Depth last s9)
    (ha9 : AgreeTo (last + 1) t s9.firsttc) (hsub : ∀ v, cell'.mem v = true → cell.mem v = true)
    (hs9 : Sparse.Store G.graph s9) (hg9 : s9.gcaFirst ≤ level) :
    SparseSweepFirst G level numcells tc tv1 cell' (cell'.nextElem (some tv))
      ((Sparse.policy (n := n)).recover nautyInf level (twG (phi (n + 2) nautyInfinity) t s9)) := by
  have hpast : ∀ v, cell'.nextElem (some tv) = some v → tv1 < v := by
    intro v hv
    have := (VSet.nextElem_eq_some_iff.mp hv).2.1
    change tv + 1 ≤ v at this
    omega
  obtain ⟨t₁, st₁, e, h1, h2, h3, h4, h5, l, h6, h7⟩ :=
    sparse_recover_sweepOff₀ (tv := tv) hn0 hn t hlevel hok htarget hout hi9 last hd9 ha9 hsub
  refine ⟨⟨t₁, st₁, e, h1, h2, h3, h4, h5, .inr ⟨fun _ v hv => hpast v hv, l, h6, h7⟩⟩,
    fun hc => absurd (hpast tv1 hc) (Nat.lt_irrefl _), fun _ _ _ => ⟨?_, ?_⟩⟩
  · exact (show Sparse.Store G.graph (twG (phi (n + 2) nautyInfinity) t s9) from
      hs9.congr rfl rfl rfl).recover nautyInf level
  · exact sparse_gcaSw_recover hg9

/-- A child step of a first-path sparse sweep that does not end it keeps `SparseSweepFirst`. -/
theorem sparse_sweepFirst_next {G : Hex.GraphIso.Sparse.Colored n k} {level numcells tc tv1 tv : Nat}
    {cell : VSet n} {st : SState n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity)
    (h : SparseSweepFirst G level numcells tc tv1 cell (some tv) st) (fuel : Nat)
    (hdone : (firstChildG (.ofGraph G.graph : Sparse.Graph n) nautyInf 100 fuel level numcells tc tv1 tv
      cell st).1 = .done) :
    SparseSweepFirst G level numcells tc tv1
      (firstChildG (.ofGraph G.graph : Sparse.Graph n) nautyInf 100 fuel level numcells tc tv1 tv cell st).2.1
      ((firstChildG (.ofGraph G.graph : Sparse.Graph n) nautyInf 100 fuel level numcells tc tv1 tv cell
        st).2.1.nextElem (some tv))
      (firstChildG (.ofGraph G.graph : Sparse.Graph n) nautyInf 100 fuel level numcells tc tv1 tv cell st).2.2 := by
  obtain ⟨⟨t, st₀, rfl, hlevel, hok, htarget, hcur, hinv, hph⟩, hb, hsg⟩ := h
  have htv := hcur tv rfl
  have hln := sparse_level_le hok
  have F := Sparse.referencePolicy (.ofGraph G.graph) (n + 2) 100
  have hle : tv1 ≤ tv := by
    rcases hph with ⟨hc, -⟩ | ⟨hpast, -⟩
    · exact Nat.le_of_eq (Option.some.inj hc).symm
    · exact Nat.le_of_lt (hpast rfl tv rfl)
  unfold firstChildG at hdone ⊢
  have eo : (Generic.Policy.orbit (n := n) (twG (phi (n + 2) nautyInfinity) t st₀) tv) = st₀.orbits[tv]! := rfl
  by_cases ho : (st₀.orbits[tv]! == tv) = true
  · simp only [eo, ho, ite_true] at hdone ⊢
    have hch := hok.child hn0 hlevel true htarget htv
    have hcf := F.child true level tc tv st₀
    have hci : InvS ((Sparse.policy (n := n)).child true level tc tv st₀) := ⟨hinv.1, hinv.2.1,
      (leafI_child hinv.2.2 true level tc tv (fun _ => VSet.mem_lt htv)).congr rfl rfl rfl rfl rfl rfl⟩
    rw [sparse_child_twG t true level tc tv st₀ (by omega)] at hdone ⊢
    have hpost := Generic.node_sound (sparseInfPolicy (G := G) (tcLevel := 100) (B := nautyInfinity) hn0 hn)
      (tv == tv1) fuel (level + 1) (numcells + 1) ((Sparse.policy (n := n)).child true level tc tv st₀)
      ⟨by omega, hch⟩
    obtain ⟨hdreach, himp⟩ := hpost
    obtain ⟨hoffP, hfirstP⟩ := himp hci
    rcases hph with ⟨hc, horb, ha⟩ | ⟨hpast, last, hd, ha⟩
    · -- the first child, on the first path
      have htv1 : tv = tv1 := Option.some.inj hc
      subst htv1
      simp only [beq_self_eq_true, ite_true] at hdone hoffP hfirstP hdreach ⊢
      have horbc : OrbIdS ((Sparse.policy (n := n)).child true level tc tv st₀) := fun v hv => horb v hv
      have hac : AgreeTo (level + 1 - 1) t ((Sparse.policy (n := n)).child true level tc tv st₀).firsttc := by
        rw [(reference_fields hcf).1, Nat.add_sub_cancel]; exact ha
      obtain ⟨t', heq, hph', hinvd⟩ := hfirstP trivial t horbc hac
      have hbc : ((Sparse.policy (n := n)).child true level tc tv st₀).canong.toRows =
          (Sparse.Graph.ofGraph G.graph).blank := hb rfl
      have hstore := fun hne => sparse_first_store hn0 (fuel := fuel) (tcLevel := 100) (by omega) hch horbc hbc hne
      rw [heq] at hdone ⊢
      generalize Generic.node true (.ofGraph G.graph : Sparse.Graph n) (n + 2) 100 fuel (level + 1)
        (numcells + 1) ((Sparse.policy (n := n)).child true level tc tv st₀) = rd
        at hdreach hph' hinvd hstore hdone ⊢
      obtain ⟨exit, s8⟩ := rd
      dsimp only at hdreach hph' hinvd hstore hdone ⊢
      simp only [Nat.add_sub_cancel] at hdreach
      let s9 : SState n := { afterChildFirst level tv s8 with
        fixedpts := (afterChildFirst level tv s8).fixedpts.erase tv }
      have e9 : (Generic.Policy.leaveChild (n := n) tv (Generic.Policy.afterChildFirst (n := n) level tv
          (twG (phi (n + 2) nautyInfinity) t' s8)) : SState n) = twG (phi (n + 2) nautyInfinity) t' s9 := rfl
      have hout : Sparse.FrameOut G level level st₀ s9 :=
        ((hok.child_frame hn0 hlevel true htarget htv hdreach).afterChild level tv).leave tv
      have hne : exit ≠ .fuel := by rintro rfl; cases hdone
      have hs9 : Sparse.Store G.graph s9 := ((hstore hne).afterChild level tv).leave tv
      have hg9 : s9.gcaFirst ≤ level := Nat.le_refl _
      obtain ⟨last, hd8, ha8⟩ := hph'.resolve_left hne
      cases exit with
      | fuel => cases hdone
      | done =>
        simp only [e9]
        exact sparse_recover_sweepFirst hn0 hn t' hlevel hle hok htarget hout hinvd last hd8 ha8
          (fun _ hv => hv) hs9 hg9
      | unwind target short =>
        by_cases hlt : target < level
        · simp only [hlt, ite_true] at hdone; cases hdone
        · simp only [hlt, ite_false, e9]
          cases short with
          | true =>
            simp only [ite_true]
            exact sparse_recover_sweepFirst hn0 hn t' hlevel hle hok htarget hout hinvd last hd8 ha8
              (fun v hv => Hex.GraphIso.Nauty.shortprune_subset
                (st := Sparse.State.frame (twG (phi (n + 2) nautyInfinity) t' s9)) hv) hs9 hg9
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            exact sparse_recover_sweepFirst hn0 hn t' hlevel hle hok htarget hout hinvd last hd8 ha8
              (fun _ hv => hv) hs9 hg9
    · -- a later child, off the first path
      have hlt := hpast rfl tv rfl
      have hne : (tv == tv1) = false := by simp; omega
      have hne' : tv ≠ tv1 := by omega
      obtain ⟨hs, hg⟩ := hsg tv rfl hne'
      simp only [hne, Bool.false_eq_true, ite_false] at hdone hoffP hfirstP hdreach ⊢
      have D := Sparse.depthPolicy (.ofGraph G.graph) (n + 2) 100 last
      have hcd := D.child true level tc tv st₀ hd
      have hac : AgreeTo (last + 1) t ((Sparse.policy (n := n)).child true level tc tv st₀).firsttc := by
        rw [(reference_fields hcf).1]; exact ha
      obtain ⟨heq, hdd, hfd, hinvd⟩ := hoffP trivial last t hcd hac
      have hsc : Sparse.Store G.graph ((Sparse.policy (n := n)).child true level tc tv st₀) :=
        (hs.child true level tc tv).congr rfl rfl rfl
      have hsd := Sparse.node_store G hn0 false 100 fuel (level + 1) (numcells + 1) _ (by omega) hch hsc
      have hgd : (Generic.node false (.ofGraph G.graph : Sparse.Graph n) (n + 2) 100 fuel (level + 1)
          (numcells + 1) ((Sparse.policy (n := n)).child true level tc tv st₀)).2.gcaFirst ≤ level := by
        rw [Sparse.node_gca]; exact hg.1
      rw [heq] at hdone ⊢
      generalize Generic.node false (.ofGraph G.graph : Sparse.Graph n) (n + 2) 100 fuel (level + 1)
        (numcells + 1) ((Sparse.policy (n := n)).child true level tc tv st₀) = rd
        at hdreach hdd hfd hinvd hsd hgd hdone ⊢
      obtain ⟨exit, s8⟩ := rd
      dsimp only at hdreach hdd hfd hinvd hsd hgd hdone ⊢
      simp only [Nat.add_sub_cancel] at hdreach
      let s9 : SState n := { s8 with fixedpts := s8.fixedpts.erase tv }
      have e9 : (Generic.Policy.leaveChild (n := n) tv (twG (phi (n + 2) nautyInfinity) t s8) : SState n) =
          twG (phi (n + 2) nautyInfinity) t s9 := rfl
      have hout : Sparse.FrameOut G level level st₀ s9 :=
        (hok.child_frame hn0 hlevel true htarget htv hdreach).leave tv
      have ha9 : AgreeTo (last + 1) t s9.firsttc := by
        show AgreeTo (last + 1) t s8.firsttc
        rw [hfd, (reference_fields hcf).1]; exact ha
      have hs9 : Sparse.Store G.graph s9 := hsd.leave tv
      cases exit with
      | fuel => cases hdone
      | done =>
        simp only [e9]
        exact sparse_recover_sweepFirst hn0 hn t hlevel hle hok htarget hout hinvd last hdd ha9
          (fun _ hv => hv) hs9 hgd
      | unwind target short =>
        by_cases hlt' : target < level
        · simp only [hlt', ite_true] at hdone; cases hdone
        · simp only [hlt', ite_false, e9]
          cases short with
          | true =>
            simp only [ite_true]
            exact sparse_recover_sweepFirst hn0 hn t hlevel hle hok htarget hout hinvd last hdd ha9
              (fun v hv => Hex.GraphIso.Nauty.shortprune_subset
                (st := Sparse.State.frame (twG (phi (n + 2) nautyInfinity) t s9)) hv) hs9 hgd
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            exact sparse_recover_sweepFirst hn0 hn t hlevel hle hok htarget hout hinvd last hdd ha9
              (fun _ hv => hv) hs9 hgd
  · -- a vertex in an earlier child's orbit: skipped
    simp only [eo, ho, Bool.false_eq_true, ite_false] at hdone ⊢
    rcases hph with ⟨hc, horb, -⟩ | ⟨hpast, last, hd, ha⟩
    · have htv1 : tv = tv1 := Option.some.inj hc
      subst htv1
      exact absurd (by simp [horb tv (VSet.mem_lt htv)]) ho
    · have hlt := hpast rfl tv rfl
      have hnx : ∀ v, cell.nextElem (some tv) = some v → tv < v := by
        intro v hv
        have := (VSet.nextElem_eq_some_iff.mp hv).2.1
        change tv + 1 ≤ v at this
        omega
      refine ⟨⟨t, st₀, rfl, hlevel, hok, htarget, fun v hv => VSet.nextElem_mem hv, hinv,
        .inr ⟨Generic.Past.next (fun _ => hpast rfl tv rfl), last, hd, ha⟩⟩,
        fun hc => absurd (hnx tv1 hc) (by omega), fun _ _ _ => hsg tv rfl (by omega)⟩

end NautyVerified.Proofs.Search
