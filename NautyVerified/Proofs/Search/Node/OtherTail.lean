import NautyVerified.Proofs.Search.Node.OtherEntry
import NautyVerified.Proofs.Search.Node.OtherRest
import NautyVerified.Proofs.Search.Node.OtherBodySteps

/-!
# `othernode0` after `processnode`

`wp_otherTailG`: from a node that continues after `processnode` (the
short-prune flag clear, the target cell chosen), `Othernode.tail` runs
`cheapCheck false` and the sweep `oSweepG … (n + 1) (cell.nextElem none) cell`,
then returns `level - 1`, or returns the target of an unwind below `level`.
`wp_loopEmptyG`: the child loop with the cursor at `-1` does nothing;
`wp_retLevelG`: `return level - 1;`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (Keep)
open NautyVerified.Proofs.Set (sk longs)
open Hex.GraphIso Hex.GraphIso.Nauty
open NautyVerified.Spec.SearchInf (SweepOkOff)

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

/-! ### For any dispatch and search policy -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}

omit E in
/-- The child loop with the cursor at `-1` does nothing. -/
theorem wp_loopEmptyG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    (htv : PTree.get dense.id.tv le = some (.Vint (ir (-1)))) (hQ : Q.normal E0 e le m) :
    Wp xi ge f Othernode.childLoop Q e le m := by
  rw [childLoop_eq]
  refine wp_loop (I := fun k t e' le' m' => k = 0 ∧ t = E0 ∧ e' = e ∧ le' = le ∧ m' = m)
    (J := fun _ _ _ _ _ => False) ?_ ?_ (n := 0) ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rintro k t e' le' m' ⟨-, rfl, rfl, rfl, rfl⟩
    wp_step; wp_step; wp_step
    refine Processnode.wp_ifB (Processnode.eval_geI (x := -1) (y := 0) htv rfl rfl rfl
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩) rfl ?_
    simp only [show ¬ (0 : Int) ≤ -1 by decide, decide_false, Bool.false_eq_true, ite_false]
    apply wp_break
    simpa using hQ
  · intro _ _ _ _ _ h; exact h.elim

omit E in
/-- `return level - 1;` after the loop. -/
theorem wp_retLevelG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {level : Nat}
    (hfr : f.fn_return = tint) (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hQ : match Mem.free_list m (blocks_of_env ge e) with
      | some m' => Q.ret E0 (.Vint (ir ((level : Int) - 1))) m'
      | none => False) :
    Wp xi ge f (sk (.Sreturn (some (.Ebinop .Osub (Refine.tv dense.id.level) (ci 1 tint) tint))))
      Q e le m := by
  wp_step; wp_step
  apply wp_return_some_eval
  simp only [Exec.evalExpr, hlev, Refine.tv, typeof, hfr, cop, ir_sub]
  exact hQ

variable [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]

set_option maxHeartbeats 8000000 in
/-- `othernode0` after `processnode`, for the policy `P` with link `K` and laws `Lw`. -/
theorem wp_otherTailG (D : DispatchC ge O) (K : PolicyLink O n) {G : O.Gr n} (Lw : NodeLaws K G)
    {Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int}
    {f : function} {Q : Post} {L : OLocs} {m₀ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {chain₀ chain : List (block × block)} {level nc tc : Nat} {nd bt : block} {le : temp_env}
    {st : SearchState n (O.Canon n)} {cell : VSet n}
    (hE : OEnvG D.toDispatchRep (oEnv L) S gl cl m₀ L) (hfr : f.fn_return = tint)
    (hS : SearchAtG D.toDispatchRep m S gl cl G st false false)
    (c : CarryG D.toDispatchRep m₀ m S gl cl chain₀ chain level (.Vint (ir nc)) (.Vint (ir tc))
      nd bt L)
    (hcell : ∃ tw, ArrayAt m .Mint64 bt 0 (longs tw) S.M ∧ SetRep (fun w => bv64 (tw w)) S.M cell)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.ptn le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hthis : PTree.get dense.id.tcnode_this le = some (.Vptr nd Ptrofs.zero))
    (htcl : PTree.get dense.id.tcell le = some (.Vptr bt Ptrofs.zero))
    (hln : level ≤ n) (hnc : nc < n) (hcb : AutomCb xi S.bUA)
    (hRec : ∀ s ch, Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (nodeSpecG D.toDispatchRep xi Lw.NodeOk Em false S gl cl G s (level + 1) (nc + 1) ch))
    (hsw : Lw.SweepOff level nc tc cell (cell.nextElem none) (cheapCheck false level st))
    (hSWf : (oSweepG G level nc tc ((cell.nextElem none).getD 0) (n + 1) (cell.nextElem none) cell
      (cheapCheck false level st)).1 ≠ .fuel)
    (hDone : ∀ t m' chain',
      (oSweepG G level nc tc ((cell.nextElem none).getD 0) (n + 1) (cell.nextElem none) cell
        (cheapCheck false level st)).1 = .done →
      Emits t (sweepEmG Em G level nc tc ((cell.nextElem none).getD 0) (n + 1)
        (cell.nextElem none) cell (cheapCheck false level st)) →
      SearchAtG D.toDispatchRep m' S gl cl G (oSweepG G level nc tc ((cell.nextElem none).getD 0)
        (n + 1) (cell.nextElem none) cell (cheapCheck false level st)).2.2 false false →
      CarryG D.toDispatchRep m₀ m' S gl cl chain₀ chain' level (.Vint (ir nc)) (.Vint (ir tc))
        nd bt L →
      match Mem.free_list m' (blocks_of_env ge (oEnv L)) with
      | some m'' => Q.ret t (.Vint (ir ((level : Int) - 1))) m''
      | none => False)
    (hUnw : ∀ t m' tg s chain',
      (oSweepG G level nc tc ((cell.nextElem none).getD 0) (n + 1) (cell.nextElem none) cell
        (cheapCheck false level st)).1 = .unwind tg s → tg < level →
      SearchAtG D.toDispatchRep m' S gl cl G (oSweepG G level nc tc ((cell.nextElem none).getD 0)
        (n + 1) (cell.nextElem none) cell (cheapCheck false level st)).2.2 false s →
      (s = true → 0 < (oSweepG G level nc tc ((cell.nextElem none).getD 0) (n + 1)
        (cell.nextElem none) cell (cheapCheck false level st)).2.2.autos.size) →
      Emits t (sweepEmG Em G level nc tc ((cell.nextElem none).getD 0) (n + 1)
        (cell.nextElem none) cell (cheapCheck false level st)) →
      CarryG D.toDispatchRep m₀ m' S gl cl chain₀ chain' level (.Vint (ir nc)) (.Vint (ir tc))
        nd bt L →
      match Mem.free_list m' (blocks_of_env ge (oEnv L)) with
      | some m'' => Q.ret t (.Vint (ir tg)) m''
      | none => False) :
    Wp xi ge f Othernode.tail Q (oEnv L) le m := by
  have hLS := hE.notS
  have hLF := hE.fresh
  have hl := hS.lit
  have hl1 := c.l1
  obtain ⟨btS, btW, -, -, -⟩ := c.ntc
  obtain ⟨tw, htw, hrep⟩ := hcell
  -- `if (needshortprune) …`: the flag is clear
  wp_step; wp_step; wp_step
  refine wp_prune0G hS (hE.glob _ (by decide)) (hE.glob _ (by decide)) (hE.glob _ (by decide))
    (hE.glob _ (by decide)) htcl htw hrep btS btW (fun h => absurd h (by decide)) ?_
  intro m1 tw1 h1 htw1 hrep1 hu1 hg1 hk1
  simp only [Bool.false_eq_true, ite_false] at hrep1
  have wrN : ∀ z ∈ [E.needshortprune], z ∈ wrEnv ∨ z ∈ S.wrVG ∨
      z ∈ D.toDispatchRep.canonBlocks cl S.bc :=
    fun z hz => .inl (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; simp [hz])
  obtain ⟨c1, -⟩ := c.cell hLS hLF hS (hu1.mono fun z hz => by
    rcases hz with rfl | rfl
    · exact .inl (by simp)
    · exact .inr rfl) wrN hg1 ⟨_, htw1⟩ hk1
  simp only [seqPost, Post.after, E0_append]
  -- the cheap test
  wp_step
  refine wp_cheapG h1 c1.uaV (TcChain.headValid c1.tcc) (K.cheapautom_eq st.ptn level)
    (hE.glob _ (by decide)) (hE.glob _ (by decide)) (hE.glob _ (by decide))
    (hE.glob _ (by decide)) hptn hlev hl1 hln ?_
  intro le2 m2 h2 hu2 hg2 hwm2 hle2
  have wrC : ∀ z ∈ [E.noncheaplevel], z ∈ wrEnv ∨ z ∈ S.wrVG ∨
      z ∈ D.toDispatchRep.canonBlocks cl S.bc :=
    fun z hz => .inl (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; simp [hz])
  obtain ⟨c2, nbt2⟩ := c1.chg hLS hLF h1 hu2 hg2 hwm2 (fun z hz => by
    rcases hz with rfl | hz | hz | hz
    · exact .inl (h1.chgL wrC (by simp))
    · have hg : z ∈ D.globs := D.wglobs_sub z hz
      exact .inl ⟨SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inr hg))))),
        h1.globs_ne hg (.inr (.inr (.inr (.inl (by simp))))),
        h1.globs_ne hg (.inr (.inr (.inr (.inr (by simp)))))⟩
    · exact .inr (.inr (.inl hz))
    · exact .inr (.inl hz)) ⟨_, htw1⟩
  have htw2 := htw1.unch hu2 nbt2
  have t2 : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.tcnode_this, dense.id.tcell],
      PTree.get x le2 = PTree.get x le := fun x hx => hle2 x (by revert x; decide)
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at t2
  obtain ⟨t2a, t2b, t2c, t2d, t2e⟩ := t2
  simp only [seqPost, Post.after, E0_append]
  -- the first cursor
  wp_step; wp_step
  refine wp_firstNextG h2 (hE.gl _) (t2e.trans htcl) htw2 hrep1 ?_
  intro r hr
  simp only [seqPost, Post.after, E0_append]
  have hT : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.tcnode_this, dense.id.tcell],
      PTree.get x (PTree.set dense.id.tv1 (.Vint (ir r)) (PTree.set dense.id.tv (.Vint (ir r))
        (PTree.set (idOf 715) (.Vint (ir r)) (PTree.set (idOf 714) (.Vint (ir r)) le2)))) =
      PTree.get x le2 := fun x hx => by
    rw [temps_gso _ _ (by revert x; decide), temps_gso _ _ (by revert x; decide),
      temps_gso _ _ (by revert x; decide), temps_gso _ _ (by revert x; decide)]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hT
  obtain ⟨T1, T2, T3, T4, T5⟩ := hT
  rcases hr with ⟨hnone, rfl⟩ | ⟨v, hsome, rfl⟩
  · -- an empty cell: the loop does nothing
    have hsw0 : oSweepG G level nc tc ((cell.nextElem none).getD 0) (n + 1) (cell.nextElem none)
        cell (cheapCheck false level st) = (.done, 0, cheapCheck false level st) := by
      rw [hnone]; exact sweep_false_noneG _ _ _ _ _ _ _ _ _ _ _ _
    refine wp_loopEmptyG (by rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _) ?_
    refine wp_retLevelG hfr (T3.trans (t2c.trans hlev)) ?_
    exact hDone _ m2 chain (by rw [hsw0]) (by rw [hnone]; simp only [sweepEmG]; exact Emits.nil)
      (by rw [hsw0]; exact h2) c2
  · -- the sweep
    have hvn : v < n := VSet.mem_lt (VSet.nextElem_mem hsome)
    simp only [hsome, Option.getD_some] at hsw hSWf hDone hUnw ⊢
    refine wp_otherLoopG (Em := Em) (chain₀ := chain₀) (tc := tc) (nd := nd) (bt := bt) K Lw
      (SW := oSweepG G level nc tc v (n + 1) (some v) cell (cheapCheck false level st))
      (Total := sweepEmG Em G level nc tc v (n + 1) (some v) cell (cheapCheck false level st))
      hE hfr hnc hvn hcb hRec hSWf ?_ ?_ (cfuel := n + 1) ?_
    · intro t le' m' cell' chain' hd' hEm hO
      simp only [seqPost, Post.after]
      refine wp_retLevelG hfr hO.lev ?_
      have := hDone t m' chain' hd' hEm hO.search hO.carry
      revert this
      cases Mem.free_list m' (blocks_of_env ge (oEnv L)) <;> simp [append_E0]
    · intro t m' tg s chain' hu' htg hS' hau hEm hC
      have := hUnw t m' tg s chain' hu' htg hS' hau hEm hC
      revert this
      cases Mem.free_list m' (blocks_of_env ge (oEnv L)) <;> exact id
    · refine ⟨rfl, _, cell, some v, chain, ⟨h2, T1.trans (t2a.trans hlab),
        T2.trans (t2b.trans hptn), T3.trans (t2c.trans hlev), T4.trans (t2d.trans hthis),
        T5.trans (t2e.trans htcl), temps_gss _ _ _,
        by rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _, ⟨tw1, htw2, hrep1⟩, c2⟩,
        hsw, rfl, [], Emits.nil, rfl⟩

end Generic

end NautyVerified.Proofs.Search
