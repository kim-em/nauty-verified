import NautyVerified.Proofs.Search.Node.OtherHex
import NautyVerified.Spec.NodeOkOff
import NautyVerified.Proofs.Search.Node.GcaSteps

/-!
# The off-path sweep keeps `SweepOkOff`

`sweepOkOff_next`: a child step of an off-path sweep (`otherChild`, run with
`inf = nautyInfinity`) that does not end the sweep leaves the pruned cell and
the recovered state in `SweepOkOff`, ready for the next vertex.
-/

namespace NautyVerified.Proofs.Search

open Hex.GraphIso Hex.GraphIso.Nauty
open NautyVerified.Spec.SearchInf

set_option linter.unusedSimpArgs false

variable {n k : Nat}

theorem sweepOkOff_next {G : Colored n k} {level numcells tc tv1 tv : Nat} {cell : VSet n}
    {st : Search n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity)
    (h : SweepOkOff G level numcells tc cell (some tv) st) (ctx : Ctx n) (tcLevel fuel : Nat)
    (hdone : (otherChild ctx nautyInfinity tcLevel fuel level numcells tc tv1 tv cell st).1 = .done) :
    SweepOkOff G level numcells tc
      (otherChild ctx nautyInfinity tcLevel fuel level numcells tc tv1 tv cell st).2.1
      ((otherChild ctx nautyInfinity tcLevel fuel level numcells tc tv1 tv cell st).2.1.nextElem (some tv))
      (otherChild ctx nautyInfinity tcLevel fuel level numcells tc tv1 tv cell st).2.2 := by
  obtain ⟨h, hg⟩ := h
  refine ⟨?_, gcaSw_otherChild hg hdone⟩
  obtain ⟨t, st₀, rfl, hlevel, hok, htarget, hcur, hinv, last, hd, ha⟩ := h
  have htv := hcur tv rfl
  have hln := level_le_of_ok hok
  have R := reachPolicy G ctx tcLevel hn0
  have D := depthPolicy ctx (n + 2) tcLevel last
  have F := referencePolicy ctx (n + 2) tcLevel
  have hch := R.child false level numcells tc tv cell st₀ hlevel hok htarget htv
  have hcd := D.child false level tc tv st₀ hd
  have hcf := F.child false level tc tv st₀
  dsimp only [policy, Generic.Policy.child] at hch hcd hcf
  obtain ⟨hokc, hceff⟩ := hch
  -- the child call
  have hpost := Generic.node_sound (infPolicy (G := G) (ctx := ctx) (tcLevel := tcLevel)
    (B := nautyInfinity) hn0 hn) false fuel (level + 1) (numcells + 1) (child false level tc tv st₀)
    ⟨by omega, hokc⟩
  obtain ⟨hdreach, himp⟩ := hpost
  obtain ⟨hoff, -⟩ := himp (child_inv hinv fun h => absurd h (by decide))
  have hac : AgreeTo (last + 1) t (child false level tc tv st₀).firsttc := by
    rw [(ref_fields hcf).1]; exact ha
  obtain ⟨heq, hdd, hfd, hinvd⟩ := hoff rfl last t hcd hac
  rw [← node_eq_generic, ← node_eq_generic] at heq
  rw [← node_eq_generic] at hdreach hdd hfd hinvd
  unfold otherChild at hdone ⊢
  rw [child_tw t false level tc tv st₀ (by omega), heq] at hdone ⊢
  generalize node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
    (child false level tc tv st₀) = rd at hdreach hdd hfd hinvd hdone ⊢
  obtain ⟨exit, s8⟩ := rd
  dsimp only at hdreach hdd hfd hinvd hdone ⊢
  simp only [Nat.add_sub_cancel] at hdreach
  let s9 : Search n := { s8 with fixedpts := s8.fixedpts.erase tv }
  have e9 : ({ tw (phi (n + 2) nautyInfinity) t s8 with
      fixedpts := (tw (phi (n + 2) nautyInfinity) t s8).fixedpts.erase tv } : Search n) =
      tw (phi (n + 2) nautyInfinity) t s9 := rfl
  have hout : SearchOut G level level st₀ s9 := (R.leave tv s8).out (hceff s8 hdreach)
  have hd9 : Depth last s9 := hdd
  have hi9 : Inv s9 := hinvd
  have ha9 : AgreeTo (last + 1) t s9.firsttc := by
    show AgreeTo (last + 1) t s8.firsttc
    rw [hfd, (ref_fields hcf).1]; exact ha
  -- the continuation, for a pruned cell `cell'`
  have hres : ∀ cell' : VSet n, (∀ v, cell'.mem v = true → cell.mem v = true) →
      SweepOkOff₀ G level numcells tc (if (tv == tv1) = true then longprune cell' s9.fixedpts s9.autos else cell')
        ((if (tv == tv1) = true then longprune cell' s9.fixedpts s9.autos else cell').nextElem (some tv))
        (recover nautyInfinity level (tw (phi (n + 2) nautyInfinity) t s9)) := by
    intro cell' hsub
    have hr := R.recover level numcells st₀ s9 hlevel hok hout
    have hrd := D.recover level s9 hd9
    have hrf := F.recover level s9
    dsimp only [policy, Generic.Policy.recover] at hr hrd hrf
    have hri : Inv (recover (n + 2) level s9) := by
      refine ⟨?_, by rw [(ref_fields hrf).2]; exact hi9.2.1, leafI_recover hi9.2.2 (n + 2) level⟩
      rw [recover_noncheap]; split <;> omega
    have hsub' : ∀ v, (if (tv == tv1) = true then longprune cell' s9.fixedpts s9.autos else cell').mem v = true →
        cell.mem v = true := by
      intro v hv
      split at hv
      · exact hsub v (R.long cell' s9 v hv)
      · exact hsub v hv
    rw [recover_tw t level s9 (by omega) (by omega)]
    refine ⟨t, recover (n + 2) level s9, rfl, hlevel, hr.ok, (htarget.subset hsub').of_out hr.effect,
      fun v hv => VSet.nextElem_mem hv, hri, last, hrd, ?_⟩
    rw [(ref_fields hrf).1]; exact ha9
  cases exit with
  | fuel => cases hdone
  | done =>
    simp only [e9] at hdone ⊢
    exact hres cell fun _ hv => hv
  | unwind target short =>
    by_cases hlt : target < level
    · simp only [hlt, ite_true] at hdone; cases hdone
    · simp only [hlt, ite_false, e9] at hdone ⊢
      have e4 : shortprune cell (tw (phi (n + 2) nautyInfinity) t s9) = shortprune cell s9 := rfl
      cases short with
      | true =>
        simp only [ite_true, e4]
        exact hres (shortprune cell s9) fun v hv => R.short cell s9 v hv
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        exact hres cell fun _ hv => hv

end NautyVerified.Proofs.Search
