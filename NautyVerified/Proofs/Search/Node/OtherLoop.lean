import NautyVerified.Proofs.Search.Node.OtherIter
import NautyVerified.Proofs.Search.Node.FirstMisc
import NautyVerified.Proofs.Search.Processnode.Cmp

/-!
# `othernode0`'s child loop is `sweep false`

`wp_otherLoopG`: the loop `while (tv >= 0) { … tv = nextelement(tcell, M, tv); }`
runs the policy's off-path sweep `SW = Generic.sweep false … cfuel cursor cell 0 st`
(`oSweepG`; `sweep_false_someG`, one child per iteration by `wp_otherIterG`),
emitting `sweepEmG`. The invariant `OInvG`: `OAtG` for the cursor (`curVal`,
`-1` for none), `NodeLaws.SweepOff` (threaded by `NodeLaws.off_next`), the
rest of the run equal to `SW`, and the words so far followed by the rest's
`sweepEmG` equal to the total. The variant is the sweep's remaining fuel.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk longs)
open Hex.GraphIso Hex.GraphIso.Nauty
open NautyVerified.Spec.SearchInf (SweepOkOff)

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

/-- The cursor as nauty.c's `tv` holds it. -/
def curVal : Option Nat → Int
  | none => -1
  | some v => v

theorem curVal_in {cur : Option Nat} (h : ∀ v, cur = some v → v < n) (hn : n < 1073741824) :
    InInt (curVal cur) := by
  rcases cur with _ | v
  · exact ⟨by decide, by decide⟩
  · have := h v rfl; simp only [curVal]; exact ⟨by omega, by omega⟩

/-! ### For any dispatch representation and search policy -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

/-- `OAtG` with a new value of `tv`. -/
theorem OAtG.setTv {m₀ m : mem} {le le' : temp_env} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {cell : VSet n} {chain₀ chain : List (block × block)} {level nc tc tv1 : Nat} {tvv : Int}
    {nd bt : block} {L : OLocs}
    (h : OAtG D m₀ m le S gl cl G st cell chain₀ chain level nc tc tv1 tvv nd bt L)
    (ht : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.tcnode_this, dense.id.tcell,
      dense.id.tv1], PTree.get x le' = PTree.get x le) {r : Int}
    (htv : PTree.get dense.id.tv le' = some (.Vint (ir r))) :
    OAtG D m₀ m le' S gl cl G st cell chain₀ chain level nc tc tv1 r nd bt L := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ht
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := ht
  exact ⟨h.search, t1 ▸ h.lab, t2 ▸ h.ptn, t3 ▸ h.lev, t4 ▸ h.this, t5 ▸ h.tcell, t6 ▸ h.tv1,
    htv, h.cellA, h.carry⟩

variable [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]

/-- The sweep run with nauty's node fuel, for the policy `P`. -/
abbrev oSweepG (G : O.Gr n) (level nc tc tv1 cfuel : Nat) (cur : Option Nat)
    (cell : VSet n) (st : SearchState n (O.Canon n)) :
    Exit × Nat × SearchState n (O.Canon n) :=
  Generic.sweep false G nautyInf 100 (nodeFuel n (level + 1)) cfuel level nc tc tv1 cur cell 0 st

/-- The loop invariant, for `D` and the policy `P`. -/
def OInvG (D : DispatchRep ge O) {K : PolicyLink O n} {G : O.Gr n} (Lw : NodeLaws K G)
    (Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int)
    (m₀ : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) (chain₀ : List (block × block))
    (level nc tc tv1 : Nat) (nd bt : block) (L : OLocs)
    (SW : Exit × Nat × SearchState n (O.Canon n)) (Total : List Int) (e : env) (cfuel : Nat)
    (t : trace) : Assn := fun e' le m => e' = e ∧
  ∃ st cell cur chain,
    OAtG D m₀ m le S gl cl G st cell chain₀ chain level nc tc tv1 (curVal cur) nd bt L ∧
    Lw.SweepOff level nc tc cell cur st ∧ oSweepG G level nc tc tv1 cfuel cur cell st = SW ∧
    ∃ W, Emits t W ∧ W ++ sweepEmG Em G level nc tc tv1 cfuel cur cell st = Total

/-- Between the body and the increment, for `D` and the policy `P`. -/
def OMidG (D : DispatchRep ge O) {K : PolicyLink O n} {G : O.Gr n} (Lw : NodeLaws K G)
    (Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int)
    (m₀ : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) (chain₀ : List (block × block))
    (level nc tc tv1 : Nat) (nd bt : block) (L : OLocs)
    (SW : Exit × Nat × SearchState n (O.Canon n)) (Total : List Int) (e : env) (cfuel : Nat)
    (t : trace) : Assn := fun e' le m => e' = e ∧
  ∃ st cell tv chain c, cfuel = c + 1 ∧ tv < n ∧
    OAtG D m₀ m le S gl cl G st cell chain₀ chain level nc tc tv1 tv nd bt L ∧
    Lw.SweepOff level nc tc cell (cell.nextElem (some tv)) st ∧
    oSweepG G level nc tc tv1 c (cell.nextElem (some tv)) cell st = SW ∧
    ∃ W, Emits t W ∧ W ++ sweepEmG Em G level nc tc tv1 c (cell.nextElem (some tv)) cell st = Total

set_option maxHeartbeats 8000000 in
/-- The child loop, for the policy `P` with link `K` and laws `Lw`. -/
theorem wp_otherLoopG (K : PolicyLink O n) {G : O.Gr n} (Lw : NodeLaws K G)
    {Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int}
    {f : function} {Q : Post} {e : env} {m₀ : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {chain₀ : List (block × block)}
    {level nc tc tv1 : Nat} {nd bt : block} {L : OLocs} {SW : Exit × Nat × SearchState n (O.Canon n)}
    {Total : List Int}
    (hE : OEnvG D e S gl cl m₀ L) (hfr : f.fn_return = tint) (hnc : nc < n) (htv1 : tv1 < n)
    (hcb : AutomCb xi S.bUA)
    (hRec : ∀ s ch, Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (nodeSpecG D xi Lw.NodeOk Em false S gl cl G s (level + 1) (nc + 1) ch))
    (hSWf : SW.1 ≠ .fuel)
    (hQn : ∀ t le' m' cell chain', SW.1 = .done → Emits t Total →
      OAtG D m₀ m' le' S gl cl G SW.2.2 cell chain₀ chain' level nc tc tv1 (-1) nd bt L →
      Q.normal t e le' m')
    (hQr : ∀ t m' tg s chain', SW.1 = .unwind tg s → tg < level →
      SearchAtG D m' S gl cl G SW.2.2 false s → (s = true → 0 < SW.2.2.autos.size) →
      Emits t Total →
      CarryG D m₀ m' S gl cl chain₀ chain' level (.Vint (ir nc)) (.Vint (ir tc)) nd bt L →
      match Mem.free_list m' (blocks_of_env ge e) with
      | some m'' => Q.ret t (.Vint (ir tg)) m''
      | none => False)
    {cfuel : Nat} {le : temp_env} {m : mem}
    (hI : OInvG D Lw Em m₀ S gl cl chain₀ level nc tc tv1 nd bt L SW Total e cfuel E0 e le m) :
    Wp xi ge f Othernode.childLoop Q e le m := by
  rw [childLoop_eq]
  refine wp_loop (I := fun c t => OInvG D Lw Em m₀ S gl cl chain₀ level nc tc tv1 nd bt L SW Total e c t)
    (J := fun c t => OMidG D Lw Em m₀ S gl cl chain₀ level nc tc tv1 nd bt L SW Total e c t) ?_ ?_ hI
  · -- the body
    intro c t e' le' m' ⟨rfl, st, cell, cur, chain, hO, hsw, hsweep, W, hW, htot⟩
    have hnl := hO.search.nlt
    have hcurlt : ∀ v, cur = some v → v < n := fun v hv => by
      subst hv; exact (Lw.off_args hsw).1
    wp_step; wp_step; wp_step
    refine Processnode.wp_ifB (Processnode.eval_geI (x := curVal cur) (y := 0) hO.tv rfl rfl rfl
      (curVal_in hcurlt (by omega)) ⟨by decide, by decide⟩) rfl ?_
    rcases cur with _ | tv
    · -- no vertex left: leave the loop
      simp only [curVal, show ¬ (0 : Int) ≤ -1 by decide, decide_false, Bool.false_eq_true, ite_false]
      apply wp_break
      have hsw0 : SW = (.done, 0, st) := by
        rw [← hsweep]; exact sweep_false_noneG _ _ _ _ _ _ _ _ _ _ _ _
      simp only [sweepEmG, List.append_nil] at htot
      subst htot
      rw [hsw0] at hQn
      simpa using hQn _ _ _ cell chain rfl hW hO
    · simp only [curVal, show (0 : Int) ≤ tv by omega, decide_true, ite_true]
      apply wp_skip
      simp only [seqPost, Post.after, E0_append]
      rcases c with _ | c
      · exact absurd (by rw [← hsweep, oSweepG, Generic.sweep]) hSWf
      refine wp_otherIterG (Em := Em) K Lw hE hfr hO hsw hnc htv1 hcb hRec ?_ ?_
      · intro t' le'' m'' chain' hd hEm hO'
        have hsw' := Lw.off_next (tv1 := tv1) (nodeFuel n (level + 1)) hsw hd
        have hstep := sweep_false_someG G nautyInf 100 (nodeFuel n (level + 1)) c level nc tc
          tv1 tv 0 cell st
        rw [show otherChildG G nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv cell st =
          ((oChildG G level nc tc tv1 tv cell st).1, (oChildG G level nc tc tv1 tv cell st).2.1,
            (oChildG G level nc tc tv1 tv cell st).2.2) from rfl, hd] at hstep
        refine ⟨rfl, _, _, tv, chain', c, rfl, hcurlt tv rfl, hO', hsw', ?_,
          W ++ Em false (level + 1) (nc + 1) (P.child false level tc tv st), ?_, ?_⟩
        · rw [← hsweep]; exact hstep.symm
        · exact hW.append hEm
        · rw [← htot]
          simp only [sweepEmG, List.append_assoc]
          congr 2
          rw [show otherChildG G nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv cell st =
            ((oChildG G level nc tc tv1 tv cell st).1, (oChildG G level nc tc tv1 tv cell st).2.1,
              (oChildG G level nc tc tv1 tv cell st).2.2) from rfl, hd]
      · intro t' m'' tg s chain' hu htg hS' hau hEm hC
        have hstep := sweep_false_someG G nautyInf 100 (nodeFuel n (level + 1)) c level nc tc
          tv1 tv 0 cell st
        rw [show otherChildG G nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv cell st =
          ((oChildG G level nc tc tv1 tv cell st).1, (oChildG G level nc tc tv1 tv cell st).2.1,
            (oChildG G level nc tc tv1 tv cell st).2.2) from rfl, hu] at hstep
        have hSW : SW = (.unwind tg s, 0, (oChildG G level nc tc tv1 tv cell st).2.2) := by
          rw [← hsweep]; exact hstep
        have htot' : W ++ Em false (level + 1) (nc + 1) (P.child false level tc tv st) = Total := by
          rw [← htot]
          simp only [sweepEmG]
          rw [show otherChildG G nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv cell st =
            ((oChildG G level nc tc tv1 tv cell st).1, (oChildG G level nc tc tv1 tv cell st).2.1,
              (oChildG G level nc tc tv1 tv cell st).2.2) from rfl, hu]
          simp
        have := hQr (t ++ t') m'' tg s chain' (by rw [hSW]) htg (by rw [hSW]; exact hS')
          (by rw [hSW]; exact hau) (htot' ▸ hW.append hEm) hC
        exact this
  · -- the increment
    intro c t e' le' m' ⟨rfl, st, cell, tv, chain, c', hc, htv, hO, hsw, hsweep, W, hW, htot⟩
    obtain ⟨tw, htw, hrep⟩ := hO.cellA
    refine wp_nodeNextG hO.search (hE.gl _) hO.tcell htw hrep hO.tv htv ?_
    intro r hr
    refine ⟨c', by omega, ?_⟩
    have hrv : r = curVal (cell.nextElem (some tv)) := by
      rcases hr with ⟨h1, h2⟩ | ⟨v, h1, h2⟩ <;> rw [h1, h2] <;> rfl
    refine ⟨rfl, st, cell, cell.nextElem (some tv), chain,
      hO.setTv (fun x hx => ?_) (by rw [← hrv]; exact temps_gss _ _ _),
      hsw, hsweep, W, by simpa using hW, htot⟩
    rw [temps_gso _ _ (by revert x; decide), temps_gso _ _ (by revert x; decide)]

end Generic

end NautyVerified.Proofs.Search
