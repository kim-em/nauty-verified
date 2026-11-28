import NautyVerified.Spec.NodeProc
import NautyVerified.Proofs.Search.Spec
import NautyVerified.Proofs.Search.Node.Breakout
import NautyVerified.Proofs.Search.Node.InvSteps
import NautyVerified.Proofs.Search.Node.OkFirst
import NautyVerified.Proofs.Search.Node.Visit
import HexGraphIso.Nauty.Policy.ReturnOrigin

/-!
# What an off-path node's `processnode` and `breakout` calls need

`proc_leafOk`: the state an off-path node passes to `processnode` meets
`processnodeSpec`'s `LeafOk` (`Spec/NodeProc.lean`).

`SInv.brokenSt`, `SInv.brokenStFirst`: `breakout` of a sweep's current vertex,
in an off-path or a first-path sweep, keeps `SInv`. Only `lab`, `ptn` and
`active` change, and they are those of HexGraphIso's `child`, whose partition
facts come from the sweep invariant's `SearchOk` and target cell.

`SInv.visitSt`: the refinement of a node keeps `SInv`.

`node_short_autos`, `leafExit_short_autos`: a short-prune return carries a
nonempty workspace, since the leaf that requested it pushed a pair.
-/

namespace NautyVerified.Proofs.Search

open Hex.GraphIso Hex.GraphIso.Nauty NautyVerified.Spec NautyVerified.Spec.SearchInf

variable {n k : Nat}

theorem proc_leafOk {G : Colored n k} {level nc : Nat} {st : Search n}
    (h : NodeOk G false level nc st) (ctx : Ctx n) (tcLevel : Nat) :
    let v := visit ctx level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := chooseTarget false ctx tcLevel level v.1 st₁
    LeafOk ct.2.2.2 := by
  intro v st₁ ct
  obtain ⟨hl, hs⟩ := proc_leafI h ctx tcLevel
  obtain ⟨h1, h2, h3⟩ := hl
  obtain ⟨⟨f1, f2⟩, ⟨c1, c2⟩, e⟩ := h3 hs
  exact ⟨f1, f2, c1, c2, e, h1, h2⟩

/-- `breakout` of a vertex of the target cell, from a renamed `SearchOk` state,
gives `SInv` back. -/
theorem SInv.broken {G : Colored n k} {level numcells tc tv : Nat} {cell : VSet n}
    {st st₂ : Search n} {t : Array Int} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (ctx : Ctx n)
    (tcLevel : Nat) (hs : SInv st) (e : st = tw (phi (n + 2) nautyInfinity) t st₂)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st₂)
    (htarget : Generic.Target (fun st => st) level tc cell st₂) (htv : cell.mem tv = true) :
    SInv (brokenSt level tc tv st) := by
  subst e
  have hln := level_le_of_ok hok
  have R := reachPolicy G ctx tcLevel hn0
  have hch := R.child false level numcells tc tv cell st₂ hlevel hok htarget htv
  dsimp only [policy, Generic.Policy.child] at hch
  have hp : PartOk G (level + 1) (numcells + 1)
      (tw (phi (n + 2) nautyInfinity) t (child false level tc tv st₂)) :=
    PartOk.of_tw hn hch.1 t
  rw [← child_tw t false level tc tv st₂ (by omega)] at hp
  have hp' : PartOk G (level + 1) (numcells + 1) (brokenSt level tc tv (tw (phi (n + 2) nautyInfinity) t st₂)) :=
    hp.frame rfl rfl (.inl rfl)
  exact SInv.of (hp'.facts hn0 hn)
    (hs.rest.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

/-- `breakout` of an off-path sweep's current vertex keeps `SInv`. -/
theorem SInv.brokenSt {G : Colored n k} {level numcells tc tv : Nat} {cell : VSet n}
    {st : Search n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (ctx : Ctx n) (tcLevel : Nat)
    (hs : SInv st) (h : SweepOkOff₀ G level numcells tc cell (some tv) st) :
    SInv (Search.brokenSt level tc tv st) := by
  obtain ⟨t, st₂, e, hlevel, hok, htarget, hcur, -⟩ := h
  exact SInv.broken hn0 hn ctx tcLevel hs e hlevel hok htarget (hcur tv rfl)

/-- `breakout` of a first-path sweep's current vertex keeps `SInv`. -/
theorem SInv.brokenStFirst {G : Colored n k} {level numcells tc tv1 tv : Nat} {cell : VSet n}
    {st : Search n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (ctx : Ctx n) (tcLevel : Nat)
    (hs : SInv st) (h : SweepOkFirst₀ G level numcells tc tv1 cell (some tv) st) :
    SInv (Search.brokenSt level tc tv st) := by
  obtain ⟨t, st₂, e, hlevel, hok, htarget, hcur, -⟩ := h
  exact SInv.broken hn0 hn ctx tcLevel hs e hlevel hok htarget (hcur tv rfl)

/-- The refinement of a node satisfying `NodeOk` keeps `SInv`. -/
theorem SInv.visitSt {G : Colored n k} {first : Bool} {level nc : Nat} {st : Search n}
    (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (hs : SInv st) (h : NodeOk G first level nc st)
    (ctx : Ctx n) : SInv (Search.visitSt ctx level nc st) := by
  have hlevel : 1 ≤ level := by obtain ⟨⟨_, _, _, h1, _⟩, _⟩ := h; exact h1
  have hp := PartOk.visit hn0 hn hlevel (PartOk.of_nodeOk hn h) ctx
  have hp' : PartOk G level (visit ctx level nc st).1 (Search.visitSt ctx level nc st) :=
    hp.frame rfl rfl (.inl rfl)
  exact SInv.of (hp'.facts hn0 hn)
    (hs.rest.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem autos_pos_of_back {out : Search n} {p : VSet n × VSet n} (h : out.autos.back? = some p) :
    0 < out.autos.size := by
  rcases Nat.eq_zero_or_pos out.autos.size with h0 | h0
  · rw [Array.size_eq_zero_iff] at h0
    rw [h0] at h
    simp at h
  · exact h0

/-- A node call returning a short prune leaves a nonempty workspace. -/
theorem node_short_autos (first : Bool) (ctx : Ctx n) (inf tcLevel fuel level nc : Nat)
    (st : Search n) {target : Nat}
    (hcap : 0 < (node first ctx inf tcLevel fuel level nc st).2.wsCap)
    (he : (node first ctx inf tcLevel fuel level nc st).1 = .unwind target true) :
    0 < (node first ctx inf tcLevel fuel level nc st).2.autos.size := by
  rcases (node_origin first ctx inf tcLevel fuel level nc st he).admission hcap with h | h
  · exact autos_pos_of_back h.1
  · exact autos_pos_of_back h.1

/-- A leaf action requesting a short prune leaves a nonempty workspace. -/
theorem leafExit_short_autos {st : Search n} (hcap : 0 < st.wsCap) {leaf : Leaf}
    {level target : Nat} (he : (leafExit leaf level st).1 = .unwind target true) :
    0 < (leafExit leaf level st).2.autos.size := by
  rcases leafExit_short_pair hcap he with h | h
  · exact autos_pos_of_back h.2
  · exact autos_pos_of_back h.2

end NautyVerified.Proofs.Search
