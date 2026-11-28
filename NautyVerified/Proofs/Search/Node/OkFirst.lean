import NautyVerified.Proofs.Search.Node.FirstHex
import NautyVerified.Proofs.Search.Node.OkOff
import NautyVerified.Spec.PartOk
import NautyVerified.Proofs.Search.Node.GcaSteps

/-!
# `NodeOk` along a first-path node

`SweepOkFirst G level numcells tc tv1 cell cursor st`: the state of a
first-path sweep is the renamed image of an `(n + 2)`-run state meeting the
inf contract's sweep precondition: before the first child (the cursor at
`tv1`) with the identity orbits and the first-path codes so far, after it
(the cursor past `tv1`) with a first leaf found.

`nodeOk_sweepFirst`: a first-path node that is not a leaf starts its sweep in
`SweepOkFirst` at its first target vertex. `sweepOkFirst_child`: each child
call satisfies `NodeOk` (on the first path for the first vertex, off it for
the others). `sweepOkFirst_next`: a child step (`firstChild`) that does not end
the sweep leaves `SweepOkFirst` for the rest.
-/

namespace NautyVerified.Proofs.Search

open Hex.GraphIso Hex.GraphIso.Nauty
open NautyVerified.Spec.SearchInf

set_option linter.unusedSimpArgs false

variable {n k : Nat}

/-- The renamed-run part of `SweepOkFirst`. -/
def SweepOkFirst₀ (G : Colored n k) (level numcells tc tv1 : Nat) (cell : VSet n)
    (cursor : Option Nat) (st : Search n) : Prop :=
  ∃ t st₂, st = tw (phi (n + 2) nautyInfinity) t st₂ ∧ 1 ≤ level ∧ SearchOk G level numcells st₂ ∧
    Generic.Target (fun st => st) level tc cell st₂ ∧ (∀ v, cursor = some v → cell.mem v = true) ∧
    Inv st₂ ∧
    ((cursor = some tv1 ∧ OrbId st₂ ∧ AgreeTo level t st₂.firsttc) ∨
      (Generic.Past true tv1 cursor ∧ ∃ last, Depth last st₂ ∧ AgreeTo (last + 1) t st₂.firsttc))

/-- The sweep invariant of a first-path node: the renamed-run part, and the level
counters (`GcaSw`) whenever the cursor is past the first child. -/
def SweepOkFirst (G : Colored n k) (level numcells tc tv1 : Nat) (cell : VSet n)
    (cursor : Option Nat) (st : Search n) : Prop :=
  SweepOkFirst₀ G level numcells tc tv1 cell cursor st ∧
    ∀ v, cursor = some v → v ≠ tv1 → GcaSw level st

/-- The renamed-run part of `nodeOk_sweepFirst`. -/
theorem nodeOk_sweepFirst₀ {G : Colored n k} {level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : NodeOk₀ G true level numcells st)
    (ctx : Ctx n) (tcLevel : Nat) :
    let v := visit ctx level numcells st
    let st₁ := recordFirst level v.2.1 v.2.2
    let ct := chooseTarget true ctx tcLevel level v.1 st₁
    v.1 ≠ n → ∃ tv1, ct.2.1.nextElem none = some tv1 ∧
      SweepOkFirst₀ G level v.1 ct.1.toNat tv1 ct.2.1 (some tv1) (cheapCheck true level ct.2.2.2) := by
  obtain ⟨t, st₀, rfl, hlevel, hok, hinv, hfirst, -⟩ := h
  obtain ⟨horb, ha⟩ := hfirst rfl
  have hln := level_le_of_ok hok
  have hL1 : level < n + 2 := by omega
  have hL2 : level < nautyInfinity := by omega
  have R := reachPolicy G ctx tcLevel hn0
  have hv := R.visit level numcells st₀ hlevel hok
  have hvi : Inv (visit ctx level numcells st₀).2.2 := hinv
  have hvo : OrbId (visit ctx level numcells st₀).2.2 := horb
  have hva : AgreeTo (level - 1) t (visit ctx level numcells st₀).2.2.firsttc := ha
  dsimp only [policy, Generic.Policy.visit] at hv ⊢
  rw [visit_tw t ctx level numcells st₀ hL1 hL2]
  generalize visit ctx level numcells st₀ = r at hv hvi hvo hva ⊢
  obtain ⟨nc, code, s1⟩ := r
  obtain ⟨hok1, -⟩ := hv
  dsimp only at hok1 hvi hvo hva ⊢
  rw [recordFirst_tw]
  have hrl := R.record level code nc s1 hok1
  dsimp only [policy, Generic.Policy.recordFirst] at hrl
  have hri : Inv (recordFirst level code s1) := ⟨hvi.1, by simp [recordFirst, hvi.2]⟩
  have hro : OrbId (recordFirst level code s1) := hvo
  have hra : AgreeTo (level - 1) t (recordFirst level code s1).firsttc := hva
  generalize recordFirst level code s1 = s2 at hrl hri hro hra ⊢
  rw [chooseTarget_tw t true ctx tcLevel level nc s2 hL1 hL2 (fun h => absurd h (by decide))]
  have htr := R.target true level nc s2 hlevel hrl.ok
  dsimp only [policy, Generic.Policy.chooseTarget] at htr
  have hcs := chooseFirst_fields ctx tcLevel level nc s2
  have hcell := first_cell_some (ctx := ctx) (tcLevel := tcLevel) hn0 hlevel hrl.ok
  generalize chooseTarget true ctx tcLevel level nc s2 = c at htr hcs hcell ⊢
  obtain ⟨tc, cell, size, s3⟩ := c
  obtain ⟨htl, htarget⟩ := htr
  dsimp only at htl htarget hcs hcell ⊢
  simp only [ite_true]
  intro hnc
  have hi3 : Inv s3 := by rw [hcs]; exact hri
  have ho3 : OrbId s3 := by rw [hcs]; exact hro
  have ha3 : AgreeTo level (t.set! level tc) s3.firsttc := by
    rw [hcs]
    have := hra.set tc
    rwa [Nat.sub_add_cancel hlevel] at this
  obtain ⟨v, hv⟩ := hcell hnc
  rw [cheapCheck_tw (t.set! level tc) true level s3 hL1 hL2]
  have hchr := R.cheap true level nc s3 htl.ok
  dsimp only [policy, Generic.Policy.cheapCheck] at hchr
  have hcheq : ∃ k', cheapCheck true level s3 = { s3 with noncheaplevel := k' } ∧ k' ≤ n + 1 := by
    unfold cheapCheck; split
    · exact ⟨level + 1, rfl, by omega⟩
    · exact ⟨s3.noncheaplevel, rfl, hi3.1⟩
  obtain ⟨k', hk', hk'le⟩ := hcheq
  refine ⟨v, hv, t.set! level tc, cheapCheck true level s3, rfl, hlevel, hchr.ok,
    htarget.of_out hchr.effect, fun w hw => by cases hw; exact VSet.nextElem_mem hv,
    by rw [hk']; exact ⟨hk'le, hi3.2⟩, .inl ⟨rfl, by rw [hk']; exact ho3, by rw [hk']; exact ha3⟩⟩

/-- A first-path node that is not a leaf starts its sweep in `SweepOkFirst`. -/
theorem nodeOk_sweepFirst {G : Colored n k} {level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : NodeOk G true level numcells st)
    (ctx : Ctx n) (tcLevel : Nat) :
    let v := visit ctx level numcells st
    let st₁ := recordFirst level v.2.1 v.2.2
    let ct := chooseTarget true ctx tcLevel level v.1 st₁
    v.1 ≠ n → ∃ tv1, ct.2.1.nextElem none = some tv1 ∧
      SweepOkFirst G level v.1 ct.1.toNat tv1 ct.2.1 (some tv1) (cheapCheck true level ct.2.2.2) :=
  fun hv => by
    obtain ⟨tv1, he, hs⟩ := nodeOk_sweepFirst₀ hn0 hn h.1 ctx tcLevel hv
    exact ⟨tv1, he, hs, fun v hc hne => absurd (Option.some.inj hc).symm hne⟩

/-- The renamed-run part of `sweepOkFirst_child`. -/
theorem sweepOkFirst_child₀ {G : Colored n k} {level numcells tc tv1 tv : Nat} {cell : VSet n}
    {st : Search n} (hn0 : 0 < n) (h : SweepOkFirst₀ G level numcells tc tv1 cell (some tv) st)
    (ctx : Ctx n) (tcLevel : Nat) :
    NodeOk₀ G (tv == tv1) (level + 1) (numcells + 1) (child true level tc tv st) := by
  obtain ⟨t, st₀, rfl, hlevel, hok, htarget, hcur, hinv, hph⟩ := h
  have hln := level_le_of_ok hok
  have R := reachPolicy G ctx tcLevel hn0
  have F := referencePolicy ctx (n + 2) tcLevel
  have hch := R.child true level numcells tc tv cell st₀ hlevel hok htarget (hcur tv rfl)
  have hcf := F.child true level tc tv st₀
  dsimp only [policy, Generic.Policy.child] at hch hcf
  rw [child_tw t true level tc tv st₀ (by omega)]
  rcases hph with ⟨hc, horb, ha⟩ | ⟨hpast, last, hd, ha⟩
  · have htv : tv = tv1 := Option.some.inj hc
    subst htv
    simp only [beq_self_eq_true]
    refine ⟨t, child true level tc tv st₀, rfl, by omega, hch.1, child_inv hinv,
      fun _ => ⟨child_orbId horb, ?_⟩, fun h => absurd h (by decide)⟩
    rw [(ref_fields hcf).1, Nat.add_sub_cancel]; exact ha
  · have hlt := hpast rfl tv rfl
    have hne : (tv == tv1) = false := by simp; omega
    rw [hne]
    have D := depthPolicy ctx (n + 2) tcLevel last
    have hcd := D.child true level tc tv st₀ hd
    dsimp only [policy, Generic.Policy.child] at hcd
    refine ⟨t, child true level tc tv st₀, rfl, by omega, hch.1, child_inv hinv,
      fun h => absurd h (by decide), fun _ => ⟨last, hcd, ?_⟩⟩
    rw [(ref_fields hcf).1]; exact ha

/-- Each child of a first-path sweep is called in `NodeOk`. -/
theorem sweepOkFirst_child {G : Colored n k} {level numcells tc tv1 tv : Nat} {cell : VSet n}
    {st : Search n} (hn0 : 0 < n) (h : SweepOkFirst G level numcells tc tv1 cell (some tv) st)
    (ctx : Ctx n) (tcLevel : Nat) :
    NodeOk G (tv == tv1) (level + 1) (numcells + 1) (child true level tc tv st) :=
  ⟨sweepOkFirst_child₀ hn0 h.1 ctx tcLevel, fun hf =>
    gcaOk_child (h.2 tv rfl (by simpa using hf)) true tc tv⟩

/-- The renamed-run part of `sweepOkFirst_next`. -/
theorem sweepOkFirst_next₀ {G : Colored n k} {level numcells tc tv1 tv : Nat} {cell : VSet n}
    {st : Search n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity)
    (h : SweepOkFirst₀ G level numcells tc tv1 cell (some tv) st) (ctx : Ctx n) (tcLevel fuel : Nat)
    (hdone : (firstChild ctx nautyInfinity tcLevel fuel level numcells tc tv1 tv cell st).1 = .done) :
    SweepOkFirst₀ G level numcells tc tv1
      (firstChild ctx nautyInfinity tcLevel fuel level numcells tc tv1 tv cell st).2.1
      ((firstChild ctx nautyInfinity tcLevel fuel level numcells tc tv1 tv cell st).2.1.nextElem (some tv))
      (firstChild ctx nautyInfinity tcLevel fuel level numcells tc tv1 tv cell st).2.2 := by
  obtain ⟨t, st₀, rfl, hlevel, hok, htarget, hcur, hinv, hph⟩ := h
  have htv := hcur tv rfl
  have hln := level_le_of_ok hok
  have R := reachPolicy G ctx tcLevel hn0
  have F := referencePolicy ctx (n + 2) tcLevel
  have hle : tv1 ≤ tv := by
    rcases hph with ⟨hc, -⟩ | ⟨hpast, -⟩
    · exact Nat.le_of_eq (Option.some.inj hc).symm
    · exact Nat.le_of_lt (hpast rfl tv rfl)
  -- the continuation after the child: prune, recover, sweep on
  have hres : ∀ (t' : Array Int) (last : Nat) (s9 : Search n) (cell' : VSet n),
      SearchOut G level level st₀ s9 → Depth last s9 → Inv s9 → AgreeTo (last + 1) t' s9.firsttc →
      (∀ v, cell'.mem v = true → cell.mem v = true) →
      SweepOkFirst₀ G level numcells tc tv1 cell' (cell'.nextElem (some tv))
        (recover nautyInfinity level (tw (phi (n + 2) nautyInfinity) t' s9)) := by
    intro t' last s9 cell' hout hd9 hi9 ha9 hsub
    have D := depthPolicy ctx (n + 2) tcLevel last
    have hr := R.recover level numcells st₀ s9 hlevel hok hout
    have hrd := D.recover level s9 hd9
    have hrf := F.recover level s9
    dsimp only [policy, Generic.Policy.recover] at hr hrd hrf
    have hri : Inv (recover (n + 2) level s9) := by
      refine ⟨?_, by rw [(ref_fields hrf).2]; exact hi9.2⟩
      rw [recover_noncheap]; split <;> omega
    rw [recover_tw t' level s9 (by omega) (by omega)]
    refine ⟨t', recover (n + 2) level s9, rfl, hlevel, hr.ok, (htarget.subset hsub).of_out hr.effect,
      fun v hv => VSet.nextElem_mem hv, hri, .inr ⟨?_, last, hrd, ?_⟩⟩
    · intro _ v hv
      have := (VSet.nextElem_eq_some_iff.mp hv).2.1
      change tv + 1 ≤ v at this
      omega
    · rw [(ref_fields hrf).1]; exact ha9
  unfold firstChild at hdone ⊢
  have eo : (tw (phi (n + 2) nautyInfinity) t st₀).orbits = st₀.orbits := rfl
  by_cases ho : (st₀.orbits[tv]! == tv) = true
  · simp only [eo, ho, ite_true] at hdone ⊢
    have hch := R.child true level numcells tc tv cell st₀ hlevel hok htarget htv
    have hcf := F.child true level tc tv st₀
    dsimp only [policy, Generic.Policy.child] at hch hcf
    obtain ⟨hokc, hceff⟩ := hch
    rw [child_tw t true level tc tv st₀ (by omega)] at hdone ⊢
    have hpost := Generic.node_sound (infPolicy (G := G) (ctx := ctx) (tcLevel := tcLevel)
      (B := nautyInfinity) hn0 hn) (tv == tv1) fuel (level + 1) (numcells + 1)
      (child true level tc tv st₀) ⟨by omega, hokc⟩
    obtain ⟨hdreach, himp⟩ := hpost
    obtain ⟨hoffP, hfirstP⟩ := himp (child_inv hinv)
    rcases hph with ⟨hc, horb, ha⟩ | ⟨hpast, last, hd, ha⟩
    · -- the first child, on the first path
      have htv1 : tv = tv1 := Option.some.inj hc
      subst htv1
      simp only [beq_self_eq_true, ite_true] at hdone hoffP hfirstP hdreach ⊢
      have hac : AgreeTo (level + 1 - 1) t (child true level tc tv st₀).firsttc := by
        rw [(ref_fields hcf).1, Nat.add_sub_cancel]; exact ha
      obtain ⟨t', heq, hph', hinvd⟩ := hfirstP trivial t (child_orbId horb) hac
      rw [← node_eq_generic, ← node_eq_generic] at heq
      rw [← node_eq_generic] at hph' hinvd hdreach
      rw [heq] at hdone ⊢
      generalize node true ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
        (child true level tc tv st₀) = rd at hdreach hph' hinvd hdone ⊢
      obtain ⟨exit, s8⟩ := rd
      dsimp only at hdreach hph' hinvd hdone ⊢
      simp only [Nat.add_sub_cancel] at hdreach
      let s9 : Search n := { afterChildFirst level tv s8 with
        fixedpts := (afterChildFirst level tv s8).fixedpts.erase tv }
      have e9 : ({ afterChildFirst level tv (tw (phi (n + 2) nautyInfinity) t' s8) with
          fixedpts := (afterChildFirst level tv (tw (phi (n + 2) nautyInfinity) t' s8)).fixedpts.erase tv } :
          Search n) = tw (phi (n + 2) nautyInfinity) t' s9 := rfl
      have hout : SearchOut G level level st₀ s9 :=
        (R.leave tv _).out ((R.afterChild level tv s8).out (hceff s8 hdreach))
      cases exit with
      | fuel => cases hdone
      | done =>
        obtain ⟨last, hd8, ha8⟩ := hph'.resolve_left (by intro h; cases h)
        simp only [e9]
        exact hres t' last s9 cell hout hd8 hinvd ha8 fun _ hv => hv
      | unwind target short =>
        obtain ⟨last, hd8, ha8⟩ := hph'.resolve_left (by intro h; cases h)
        by_cases hlt : target < level
        · simp only [hlt, ite_true] at hdone; cases hdone
        · simp only [hlt, ite_false, e9]
          cases short with
          | true =>
            simp only [ite_true]
            exact hres t' last s9 (shortprune cell s9) hout hd8 hinvd ha8 fun v hv => R.short cell s9 v hv
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            exact hres t' last s9 cell hout hd8 hinvd ha8 fun _ hv => hv
    · -- a later child, off the first path
      have hlt := hpast rfl tv rfl
      have hne : (tv == tv1) = false := by simp; omega
      simp only [hne, Bool.false_eq_true, ite_false] at hdone hoffP hfirstP hdreach ⊢
      have D := depthPolicy ctx (n + 2) tcLevel last
      have hcd := D.child true level tc tv st₀ hd
      dsimp only [policy, Generic.Policy.child] at hcd
      have hac : AgreeTo (last + 1) t (child true level tc tv st₀).firsttc := by
        rw [(ref_fields hcf).1]; exact ha
      obtain ⟨heq, hdd, hfd, hinvd⟩ := hoffP trivial last t hcd hac
      rw [← node_eq_generic, ← node_eq_generic] at heq
      rw [← node_eq_generic] at hdd hfd hinvd hdreach
      rw [heq] at hdone ⊢
      generalize node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
        (child true level tc tv st₀) = rd at hdreach hdd hfd hinvd hdone ⊢
      obtain ⟨exit, s8⟩ := rd
      dsimp only at hdreach hdd hfd hinvd hdone ⊢
      simp only [Nat.add_sub_cancel] at hdreach
      let s9 : Search n := { s8 with fixedpts := s8.fixedpts.erase tv }
      have e9 : ({ tw (phi (n + 2) nautyInfinity) t s8 with
          fixedpts := (tw (phi (n + 2) nautyInfinity) t s8).fixedpts.erase tv } : Search n) =
          tw (phi (n + 2) nautyInfinity) t s9 := rfl
      have hout : SearchOut G level level st₀ s9 := (R.leave tv s8).out (hceff s8 hdreach)
      have ha9 : AgreeTo (last + 1) t s9.firsttc := by
        show AgreeTo (last + 1) t s8.firsttc
        rw [hfd, (ref_fields hcf).1]; exact ha
      cases exit with
      | fuel => cases hdone
      | done =>
        simp only [e9]
        exact hres t last s9 cell hout hdd hinvd ha9 fun _ hv => hv
      | unwind target short =>
        by_cases hlt' : target < level
        · simp only [hlt', ite_true] at hdone; cases hdone
        · simp only [hlt', ite_false, e9]
          cases short with
          | true =>
            simp only [ite_true]
            exact hres t last s9 (shortprune cell s9) hout hdd hinvd ha9 fun v hv => R.short cell s9 v hv
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            exact hres t last s9 cell hout hdd hinvd ha9 fun _ hv => hv
  · -- a vertex in an earlier child's orbit: skipped
    simp only [eo, ho, Bool.false_eq_true, ite_false] at hdone ⊢
    rcases hph with ⟨hc, horb, -⟩ | ⟨hpast, last, hd, ha⟩
    · have htv1 : tv = tv1 := Option.some.inj hc
      subst htv1
      exact absurd (by simp [horb tv (VSet.mem_lt htv)]) ho
    · refine ⟨t, st₀, rfl, hlevel, hok, htarget, fun v hv => VSet.nextElem_mem hv, hinv,
        .inr ⟨Generic.Past.next (fun _ => hpast rfl tv rfl), last, hd, ha⟩⟩

/-- A child step of a first-path sweep that does not end it leaves `SweepOkFirst`. -/
theorem sweepOkFirst_next {G : Colored n k} {level numcells tc tv1 tv : Nat} {cell : VSet n}
    {st : Search n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity)
    (h : SweepOkFirst G level numcells tc tv1 cell (some tv) st) (ctx : Ctx n) (tcLevel fuel : Nat)
    (hdone : (firstChild ctx nautyInfinity tcLevel fuel level numcells tc tv1 tv cell st).1 = .done) :
    SweepOkFirst G level numcells tc tv1
      (firstChild ctx nautyInfinity tcLevel fuel level numcells tc tv1 tv cell st).2.1
      ((firstChild ctx nautyInfinity tcLevel fuel level numcells tc tv1 tv cell st).2.1.nextElem (some tv))
      (firstChild ctx nautyInfinity tcLevel fuel level numcells tc tv1 tv cell st).2.2 := by
  refine ⟨sweepOkFirst_next₀ hn0 hn h.1 ctx tcLevel fuel hdone, fun _ _ _ => ?_⟩
  refine gcaSw_firstChild (fun hne => h.2 tv rfl hne) hdone fun hf heq => ?_
  obtain ⟨⟨t, st₀, rfl, -, -, -, hcur, -, hph⟩, -⟩ := h
  rcases hph with ⟨-, horb, -⟩ | ⟨hpast, -⟩
  · have h1 := horb tv (VSet.mem_lt (hcur tv rfl))
    have : ((tw (phi (n + 2) nautyInfinity) t st₀).orbits[tv]! == tv) = true := by
      show (st₀.orbits[tv]! == tv) = true
      simp [h1]
    rw [hf] at this; cases this
  · have := hpast rfl tv rfl
    omega

/-- The state of an off-path sweep satisfies `PartOk`. -/
theorem SweepOkOff.part {G : Colored n k} {level numcells tc : Nat} {cell : VSet n}
    {cursor : Option Nat} {st : Search n} (hn : n + 2 < nautyInfinity)
    (h : SweepOkOff G level numcells tc cell cursor st) : PartOk G level numcells st := by
  obtain ⟨⟨t, st₂, rfl, -, hok, -⟩, -⟩ := h
  exact PartOk.of_tw hn hok t

/-- The state of a first-path sweep satisfies `PartOk`. -/
theorem SweepOkFirst.part {G : Colored n k} {level numcells tc tv1 : Nat} {cell : VSet n}
    {cursor : Option Nat} {st : Search n} (hn : n + 2 < nautyInfinity)
    (h : SweepOkFirst G level numcells tc tv1 cell cursor st) : PartOk G level numcells st := by
  obtain ⟨⟨t, st₂, rfl, -, hok, -⟩, -⟩ := h
  exact PartOk.of_tw hn hok t

/-- The target cell of a sweep is a cell of the partition: its members are in
range and it starts at `tc`. -/
theorem SweepOkOff.target {G : Colored n k} {level numcells tc : Nat} {cell : VSet n}
    {cursor : Option Nat} {st : Search n} (h : SweepOkOff G level numcells tc cell cursor st) :
    ∃ st₂, Generic.Target (fun st => st) level tc cell st₂ ∧ st₂.lab = st.lab := by
  obtain ⟨⟨t, st₂, rfl, -, -, htarget, -⟩, -⟩ := h
  exact ⟨st₂, htarget, rfl⟩

theorem SweepOkFirst.target {G : Colored n k} {level numcells tc tv1 : Nat} {cell : VSet n}
    {cursor : Option Nat} {st : Search n} (h : SweepOkFirst G level numcells tc tv1 cell cursor st) :
    ∃ st₂, Generic.Target (fun st => st) level tc cell st₂ ∧ st₂.lab = st.lab := by
  obtain ⟨⟨t, st₂, rfl, -, -, htarget, -⟩, -⟩ := h
  exact ⟨st₂, htarget, rfl⟩

end NautyVerified.Proofs.Search
