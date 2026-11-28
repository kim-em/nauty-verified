import NautyVerified.Proofs.Search.Node.FirstInit
import NautyVerified.Proofs.Search.Node.FirstBodySteps
import NautyVerified.Proofs.Search.Node.ProcFacts
import NautyVerified.Proofs.Refine1.Nontrivial
import NautyVerified.Proofs.Search.Node.OtherBody

/-!
# `firstpathnode0` meets its specification

`firstpathnode_body`: nauty.c's `firstpathnode0` satisfies
`firstpathnodeSpecG` at `level`, given `firstpathnode0`'s and `othernode0`'s
specifications at `level + 1` for its children, the emission law
`EmLawFirst`, and `refine`'s specification.

The body: the locals are allocated on entry (`fpn_entry`), the prologue finds
this level's target-cell entry (`wp_nodePrologue`), then the node count, the
refinement (`wp_nodeVisit`), the first-path code (`wp_recordFirst`), the
target cell (`wp_fpnTarget`, `wp_firsttcStore`), the first leaf
(`wp_fpnLeaf`), the kill check, the cheap-automorphism test, the child loop
(`wp_fpnLoop`) and the end of the sweep (`wp_fpnGrp`, `wp_fpnLast`);
HexGraphIso's side is `node_true_succ`. Memory is carried in `HeadAt` before the
loop and `LoopAt` during it; `HeadAt.post` gives the postcondition at each
return.
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

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

/-- The specification's postcondition at a return, once the locals are freed. -/
theorem fPost {k : Nat} {G : Colored n k} {Em : Bool → Nat → Nat → Search n → List Int}
    {L : LCtx n} {O : OLocs} {st : Search n} {nc : Nat} {args : List val} {m : mem}
    {ch : List (block × block)} {s : Search n} {ns : Bool} {v : Int} {t : trace}
    (H : HeadAt L m s false ns ch) (hfresh : ∀ z ∈ L.locals, ¬ Mem.valid_block L.m₀ z)
    (hLO : ∀ z ∈ [O.bq, O.bnc, O.bc, O.bz, O.bk], z ∈ L.locals)
    (hnd : [O.bq, O.bnc, O.bc, O.bz, O.bk].Nodup) (hctx : L.ctx = ⟨rowsOf G⟩)
    (hr2 : (hexNode true ⟨rowsOf G⟩ L.level nc st).2 = s)
    (hrv : exitValue L.level (hexNode true ⟨rowsOf G⟩ L.level nc st).1 = (v, ns))
    (hEm : Emits t (Em true L.level nc st))
    (hlt : ∀ tg sh, (hexNode true ⟨rowsOf G⟩ L.level nc st).1 = .unwind tg sh → tg < L.level) :
    match Mem.free_list m (blocks_of_env ge (fEnv O)) with
    | some m'' => (firstpathnodeSpecG xi G Em L.S st L.level nc L.chain₀).post args L.m₀ t
        (.Vint (ir v)) m''
    | none => False := by
  obtain ⟨mf, hfree, hS, hC, hF, hW⟩ := H.post hfresh (blocks_fEnv O) hnd hLO
  rw [hfree]
  refine ⟨by rw [hrv], by rw [hr2, hrv]; rw [hctx] at hS; exact hS, hEm, hC, hF, hW, hlt⟩

set_option maxHeartbeats 16000000 in
theorem firstpathnode_body {k : Nat} (G : Colored n k) (Em : Bool → Nat → Nat → Search n → List Int)
    (hLaw : EmLawFirst Em ⟨rowsOf G⟩) (S : SLoc) (level : Nat)
    (hRef : Refine.RefineFn xi S.M (.Vptr S.refineBlock Ptrofs.zero))
    (hRecF : ∀ s nc' ch, Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (firstpathnodeSpecG xi G Em S s (level + 1) nc' ch))
    (hRecO : ∀ s nc' ch, Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (othernodeSpecG xi G Em S s (level + 1) nc' ch)) :
    ∀ st nc chain, Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (firstpathnodeSpecG xi G Em S st level nc chain) := by
  intro st nc chain
  refine satisfies_internal (Entry := fun args m₀ e le m => ∃ O : OLocs, e = fEnv O ∧
      le = fTemps S.bl S.lofs S.bp S.pofs level nc (tcParent chain level) ∧
      (∀ z ∈ O.list, ¬ Mem.valid_block m₀ z ∧ Mem.valid_block m z ∧
        Mem.valid_access m .Mint32 z (zOfInt 0) .Freeable) ∧
      O.list.Pairwise (· ≠ ·) ∧ Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z) ∧
      (∀ z, Mem.valid_block m₀ z → Mem.valid_block m z)) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    obtain ⟨e, le, m', hfe, O, h1, h2, h3⟩ :=
      fpn_entry S.bl S.lofs S.bp S.pofs level nc (tcParent chain level) m
    exact ⟨e, le, m', hfe, O, h1, h2, h3⟩
  rintro args m₀ ⟨rfl, h0, hTc0, hTo0, hlen, hcb, hl1, hln, hncn, hok, huaV, huaP⟩
  rw [triple_iff_wp]
  rintro e le mA ⟨O, rfl, rfl, hLA, hLd, huA, hgA⟩
  have hLF : ∀ z ∈ O.list, ¬ Mem.valid_block m₀ z := fun z hz => (hLA z hz).1
  have haccA : ∀ z ∈ O.list, Mem.valid_access mA .Mint32 z (zOfInt 0) .Freeable :=
    fun z hz => (hLA z hz).2.2
  have hn0 := h0.n0
  have hnl := h0.nlt
  have hnI : n + 2 < SearchInf.nautyInfinity := by show n + 2 < 2000000002; omega
  obtain ⟨hSA, hTcA, hToA, hbackA, hwmA, hLS, hwkA, hcA⟩ :=
    oAlloc (L := O) h0 huaV hTc0 hTo0 huA hgA hLF
  have hgl : ∀ x, x ∉ [dense.id.numcells, dense.id.refcode, dense.id.tcellsize, dense.id.tc,
      dense.id.qinvar] → PTree.get x (fEnv O) = none := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := hx
    rw [PTree.gso _ _ h2, PTree.gso _ _ h5, PTree.gso _ _ h4, PTree.gso _ _ h3, PTree.gso _ _ h1]
    rfl
  have gl : ∀ l : List ident, (∀ x ∈ l, x ∉ [dense.id.numcells, dense.id.refcode,
      dense.id.tcellsize, dense.id.tc, dense.id.qinvar]) → ∀ x ∈ l, PTree.get x (fEnv O) = none :=
    fun l hl x hx => hgl x (hl x hx)
  have enc : PTree.get dense.id.numcells (fEnv O) = some (O.bnc, tint) := by
    (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
  have ez : PTree.get dense.id.tcellsize (fEnv O) = some (O.bz, tint) := by
    (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
  have ec : PTree.get dense.id.tc (fEnv O) = some (O.bc, tint) := by
    (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
  have eq : PTree.get dense.id.qinvar (fEnv O) = some (O.bq, tint) := by
    (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
  have ek : PTree.get dense.id.refcode (fEnv O) = some (O.bk, tint) := PTree.gss _ _ _
  have hfr : dense.fn.«nauty:firstpathnode0».fn_return = tint := rfl
  have hd := h0.distinct
  have hT0 : ∀ x, PTree.get x (fTemps S.bl S.lofs S.bp S.pofs level nc (tcParent chain level)) =
      PTree.get x (fTemps S.bl S.lofs S.bp S.pofs level nc (tcParent chain level)) := fun _ => rfl
  clear hT0
  rw [dense.fn.«nauty:firstpathnode0».fn_body_eq, Firstpathnode.body_eq]
  obtain ⟨_, -, bncA⟩ := arrayAt_of_access (haccA O.bnc (by simp))
  refine wp_nodePrologue (nc := nc) hSA (hgA _ huaV) hTcA hToA hlen hl1 enc bncA
    (hLS _ (by simp)) (hwkA _ (by simp)) (hcA _ (by simp)) (gl _ (by decide))
    (by simp (config := {decide := true}) only [fTemps, temps_gso, temps_gss])
    (by simp (config := {decide := true}) only [fTemps, temps_gso, temps_gss]) ?_
  intro le1 m1 chain' nd bt hS1 hA1 hTc1 hTo1 hown htake hold hcellE hU1 hg1 hwm1 hK1 hthis1
    htcl1 hle1
  have hlab1 : PTree.get dense.id.lab le1 = some (.Vptr S.bl S.lofs) := by
    rw [hle1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [fTemps, temps_gso, temps_gss]
  have hptn1 : PTree.get dense.id.ptn le1 = some (.Vptr S.bp S.pofs) := by
    rw [hle1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [fTemps, temps_gso, temps_gss]
  have hlev1 : PTree.get dense.id.level le1 = some (.Vint (ir level)) := by
    rw [hle1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [fTemps, temps_gso, temps_gss]
  -- the fixed context of the node
  let ctx : Ctx n := ⟨rowsOf G⟩
  let v := visit ctx level nc st
  let ct := chooseTarget true ctx 100 level v.1 (recordFirst level v.2.1 v.2.2)
  let L : LCtx n := ⟨S, ctx, m₀, chain, level, v.1, ct.1.toNat, ct.2.2.1, O.bnc, O.bq, O.bk,
    O.bc, O.bz, nd, bt⟩
  have hLL : ∀ z ∈ L.locals, z ∈ O.list := by
    intro z hz
    simp only [L, LCtx.locals, OLocs.list, List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢
    rcases hz with h | h | h | h | h <;> simp [h]
  have hfresh : ∀ z ∈ L.locals, ¬ Mem.valid_block L.m₀ z := fun z hz => hLF z (hLL z hz)
  have H1 : HeadAt L m1 st true false chain' :=
    HeadAt.init (L := L) h0 hTo0 hl1 hlen huaV huaP hfresh (fun z hz => hLS z (hLL z hz)) huA hgA
      hwmA (fun z hz => haccA z (hLL z hz)) (fun z hz => hwkA z (hLL z hz))
      (fun z hz => hcA z (hLL z hz)) hS1 hTc1 hTo1 hown htake hold hcellE hU1 hg1 hwm1 hK1
  -- the node count
  wp_step; wp_step; wp_step
  refine wp_numnodes hS1 (hgl _ (by decide)) ?_
  intro m2 h2 hu2 hg2
  have hbst : S.bst ∈ S.vars := by simp [SLoc.vars]
  have H2 : HeadAt L m2 { st with numnodes := st.numnodes + 1 } true false chain' :=
    H1.stepS hfresh h2 hu2 (fun z hz => by subst hz; exact .inl (vars_chg hd hbst (by sep_ne hd)))
      hg2 (WorkMono.of_unch hS1.work hu2 (fun z hz e => vars_notWork hd hbst (e ▸ hz))
        (fun z hz e => hS1.work_not hz (e ▸ SLoc.vars_blocks hbst)))
  simp only [seqPost, Post.after, E0_append]
  -- the refinement
  have hLd' := hLd
  simp only [OLocs.list, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true] at hLd'
  obtain ⟨⟨d12, d13, d14, d15⟩, ⟨d23, d24, d25⟩, ⟨d34, d35⟩, d45⟩ := hLd'
  have hloc2 : ∀ z ∈ L.locals, z ∉ S.blocks ∧ Mem.valid_block m2 z ∧ ¬ IsWork m2 z := fun z hz =>
    ⟨(H2.locals z hz).2.1, (H2.locals z hz).1, (H2.locals z hz).2.2⟩
  have hbncS : O.bnc ∉ S.blocks := hLS _ (by simp)
  have hA2 := hA1.unch hu2 (fun e => hbncS (e ▸ SLoc.vars_blocks hbst))
  obtain ⟨_, hqA⟩ := H2.locA O.bq (by simp [L, LCtx.locals])
  obtain ⟨_, hkA⟩ := H2.locA O.bk (by simp [L, LCtx.locals])
  have hbtL : ∀ z ∈ L.locals, L.btc ≠ z := fun z hz e =>
    (H2.chain.apart _ (List.mem_of_getElem? H2.chain.own)).2 (e ▸ hz)
  wp_step; wp_step; wp_step
  refine wp_nodeVisit (st := { st with numnodes := st.numnodes + 1 }) h2 H2.vU
    (TcChain.head_valid H2.chain.chain) hRef (bnc := O.bnc) (bq := O.bq) (bk := O.bk)
    (by
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_singleton _ _⟩⟩
      · intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl
        · exact d15
        · exact d12
      · intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        subst hz; exact fun e => d25 e.symm)
    (fun z hz => hloc2 z (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> simp [L, LCtx.locals]))
    enc eq ek (gl _ (by decide)) hA2 ⟨_, hqA⟩ ⟨_, hkA⟩ hlab1 hptn1 hlev1 hl1 hln hncn
    { SInv.visitSt hn0 hnI hS1.inv hok ⟨rowsOf G⟩ with } ?_
  intro m3 h3 hnc3 hk3 hq3 hU3 hg3 hwm3 hK3
  have hv := visit_eq ctx level nc st
  obtain ⟨hv1, hv2, hv3⟩ := hv
  have H3 : HeadAt L m3 v.2.2 true false chain' := by
    refine H2.stepL (Ls := [O.bnc, O.bq, O.bk]) hfresh (by rw [hv1]; exact h3) (hU3.mono fun z hz => ?_)
      (fun z hz => .inr (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> simp [L, LCtx.locals])) hg3 hwm3 hK3 (fun z hz _ => ?_)
      (fun hb => ?_)
    · rcases hz with h' | h' | h' | h' | h' | h'
      · exact .inl h'
      · exact .inr (.inl h')
      · exact .inr (.inr (.inl h'))
      all_goals (subst h'; exact .inr (.inr (.inr (by simp))))
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨_, hnc3⟩
      · exact ⟨_, hq3⟩
      · exact ⟨_, hk3⟩
    · exfalso
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with e | e | e
      · exact hbtL O.bnc (by simp [L, LCtx.locals]) e
      · exact hbtL O.bq (by simp [L, LCtx.locals]) e
      · exact hbtL O.bk (by simp [L, LCtx.locals]) e
  have ld : ∀ {mm : mem} {b : block} {w : val}, ArrayAt mm .Mint32 b 0 (fun _ => w) 1 →
      Mem.load .Mint32 mm b (zOfInt 0) = some w := fun hA => by
    simpa [elemOfs] using hA.load 0 (by decide)
  have hc := visit_code_lt ctx level nc st
  simp only [seqPost, Post.after, E0_append]
  -- `firstcode[level] = refcode`
  wp_step; wp_step; wp_step
  refine wp_recordFirst H3.search (hgl _ (by decide)) ek (ld hk3) hlev1 (Nat.lt_of_lt_of_le hc (by decide)) hln ?_
  intro m4 h4 hu4 hg4
  have hbFC : S.bFC ∈ S.vars := by simp [SLoc.vars]
  have H4 : HeadAt L m4 (recordFirst level v.2.1 v.2.2) true false chain' :=
    H3.stepS hfresh h4 hu4 (fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        subst hz; exact .inl (vars_chg hd hbFC (by sep_ne hd))) hg4
      (WorkMono.of_unch H3.search.work hu4 (fun z hz e => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
          exact vars_notWork hd hbFC (e ▸ hz))
        (fun z hz e => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
          exact H3.search.work_not hz (e ▸ SLoc.vars_blocks hbFC)))
  have hq4 : Mem.load .Mint32 m4 O.bq (zOfInt 0) = some (.Vint (ir 0)) := by
    rw [hu4.load _ _ _ (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      exact fun e => hLS O.bq (by simp) (e ▸ SLoc.vars_blocks hbFC))]
    exact ld hq3
  simp only [seqPost, Post.after, E0_append]
  -- the invariant statistics
  wp_step
  refine wp_fpnInvstat0 eq hq4 ?_
  simp only [seqPost, Post.after, E0_append]
  -- HexGraphIso's node, unfolded
  have hN : hexNode true ctx level nc st =
      node true ctx nautyInf 100 (n + 2 - level + 1) level nc st := by
    show node _ _ _ _ (n + 3 - level) _ _ _ = _
    rw [show n + 3 - level = n + 2 - level + 1 by omega]
  rw [node_true_succ] at hN
  have hEmL := hLaw level nc st hl1 hln
  have hpf := (SearchInf.PartOk.visit hn0 hnI hl1 (SearchInf.PartOk.of_nodeOk hnI hok) ctx).facts
    hn0 hnI
  have hncv : v.1 ≤ n := hpf.numcellsLe
  have hLO : ∀ z ∈ [O.bq, O.bnc, O.bc, O.bz, O.bk], z ∈ L.locals := by
    intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with h | h | h | h | h <;> simp [L, LCtx.locals, h]
  have hnd : [O.bq, O.bnc, O.bc, O.bz, O.bk].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or]
    and_intros <;> first | exact List.nodup_nil | trivial | intro e <;> first | exact absurd e d12 | exact absurd e.symm d12 | exact absurd e d13 | exact absurd e.symm d13 | exact absurd e d14 | exact absurd e.symm d14 | exact absurd e d15 | exact absurd e.symm d15 | exact absurd e d23 | exact absurd e.symm d23 | exact absurd e d24 | exact absurd e.symm d24 | exact absurd e d25 | exact absurd e.symm d25 | exact absurd e d34 | exact absurd e.symm d34 | exact absurd e d35 | exact absurd e.symm d35 | exact absurd e d45 | exact absurd e.symm d45
  -- `tc = -1`
  obtain ⟨_, hbcA⟩ := H4.locA O.bc (by simp [L, LCtx.locals])
  have hbcS : O.bc ∉ S.blocks := hLS _ (by simp)
  wp_step; wp_step; wp_step
  refine wp_localStore ec ⟨_, hbcA⟩ (rhs := .Eunop .Oneg (ci 1 tint) tint) (w := -1)
    (by simp [Exec.evalExpr, typeof, cop]) rfl ?_
  intro m5 hA5 hu5 hK5 hg5
  have h5 := H4.search.unch hu5 (fun z hz e => hbcS (e ▸ hz))
    (fun z hz e => (H4.locals O.bc (by simp [L, LCtx.locals])).2.2 (e ▸ hz))
  have H5 : HeadAt L m5 (recordFirst level v.2.1 v.2.2) true false chain' :=
    H4.stepL (Ls := [O.bc]) hfresh h5 (hu5.mono fun z hz => .inr (.inr (.inr (by simp [hz]))))
      (fun z hz => .inr (by simp at hz; simp [hz, L, LCtx.locals])) hg5
      (WorkMono.of_unch H4.search.work hu5
        (fun z hz e => hbcS (e ▸ by revert z; simp [workG, SLoc.blocks]))
        (fun z hz e => (H4.locals O.bc (by simp [L, LCtx.locals])).2.2 (e ▸ hz)))
      (fun z _ => hK5 z) (fun z hz _ => by simp at hz; subst hz; exact ⟨_, hA5⟩)
      (fun hb => by simp at hb; exact absurd hb (hbtL O.bc (by simp [L, LCtx.locals])))
  simp only [seqPost, Post.after, E0_append]
  -- the target cell
  have hncL : Mem.load .Mint32 m5 O.bnc (zOfInt 0) = some (.Vint (ir (v.1 : Int))) := by
    rw [hu5.load _ _ _ (fun e => d14 e), hu4.load _ _ _ (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      exact fun e => hbncS (e ▸ SLoc.vars_blocks hbFC))]
    exact ld hnc3
  have hloc5 : ∀ z ∈ L.locals, z ∉ S.blocks ∧ Mem.valid_block m5 z ∧ ¬ IsWork m5 z := fun z hz =>
    ⟨(H5.locals z hz).2.1, (H5.locals z hz).1, (H5.locals z hz).2.2⟩
  have hmem5 := List.mem_of_getElem? H5.chain.own
  obtain ⟨-, btS, -, btW⟩ := H5.chain.ok.apart _ hmem5
  have btV : Mem.valid_block m5 bt := (H5.chain.ok.valid _ hmem5).2
  obtain ⟨_, hbzA⟩ := H5.locA O.bz (by simp [L, LCtx.locals])
  obtain ⟨_, hbcA5⟩ := H5.locA O.bc (by simp [L, LCtx.locals])
  wp_step; wp_step; wp_step
  refine wp_fpnTarget (nc := v.1) H5.search H5.vU (TcChain.head_valid H5.chain.chain)
    (bt := bt) (bz := O.bz) (bc := O.bc) (bnc := O.bnc)
    (by
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_singleton _ _⟩⟩
      · intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl
        · exact hbtL _ (by simp [L, LCtx.locals])
        · exact hbtL _ (by simp [L, LCtx.locals])
      · intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        subst hz; exact d34)
    (fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨btS, btV, btW⟩
      · exact hloc5 _ (by simp [L, LCtx.locals])
      · exact hloc5 _ (by simp [L, LCtx.locals]))
    htcl1 ez ec (gl _ (by decide)) (hgl _ (by decide)) H5.cellv ⟨_, hbzA⟩ ⟨_, hbcA5⟩ enc hncL
    hncv hlab1 hptn1 hlev1 hl1 hln
    (fun hne => exists_gt_of_bcount (n := n) (ptn := v.2.2.ptn) (by rw [← hpf.count]; exact Nat.lt_of_le_of_ne hncv hne))
    ?_ ?_
  · intro hne m6 h6 hws hz6 hc6 hU6 hg6 hwm6 hK6
    have hlt : v.1 < n := Nat.lt_of_le_of_ne hncv hne
    have hpos := PartFacts.target_lt (ctx := ctx) (tcLevel := 100) hpf hl1 hlt (-1) (by omega)
    have hct : ct = (((maketargetcell ctx v.2.2.lab v.2.2.ptn level 100 (-1)).1 : Int),
        (maketargetcell ctx v.2.2.lab v.2.2.ptn level 100 (-1)).2.1,
        (maketargetcell ctx v.2.2.lab v.2.2.ptn level 100 (-1)).2.2,
        { { recordFirst level v.2.1 v.2.2 with
            tctotal := (recordFirst level v.2.1 v.2.2).tctotal +
              (maketargetcell ctx v.2.2.lab v.2.2.ptn level 100 (-1)).2.2 } with
          firsttc := (recordFirst level v.2.1 v.2.2).firsttc.set! level
            ((maketargetcell ctx v.2.2.lab v.2.2.ptn level 100 (-1)).1 : Int) }) := by
      show chooseTarget true ctx 100 level v.1 _ = _
      rw [chooseTarget_true_eq, ite_eq_left hne]; rfl
    have hbtnL : bt ∉ L.locals := fun hz => hbtL bt hz rfl
    have H6 : HeadAt L m6 { recordFirst level v.2.1 v.2.2 with
        tctotal := (recordFirst level v.2.1 v.2.2).tctotal +
          (maketargetcell ctx v.2.2.lab v.2.2.ptn level 100 (-1)).2.2 } true false chain' := by
      refine H5.stepL (Ls := [bt, O.bz, O.bc]) hfresh h6 (hU6.mono fun z hz => ?_)
        (fun z hz => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          rcases hz with rfl | rfl | rfl
          · exact .inl rfl
          · exact .inr (by simp [L, LCtx.locals])
          · exact .inr (by simp [L, LCtx.locals])) hg6 hwm6 hK6 (fun z hz hzl => ?_)
        (fun _ => by obtain ⟨ws, hwa, -⟩ := hws; exact ⟨_, hwa⟩)
      · rcases hz with h' | h' | h' | h' | h' | h'
        · exact .inl h'
        · exact .inr (.inl h')
        · exact .inr (.inr (.inl h'))
        all_goals (subst h'; exact .inr (.inr (.inr (by simp))))
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl
        · exact absurd hzl hbtnL
        · exact ⟨_, hz6⟩
        · exact ⟨_, hc6⟩
    have hbTC : S.bTC ∈ S.vars := by simp [SLoc.vars]
    simp only [seqPost, Post.after, E0_append]
    -- `firsttc[level] = tc`
    wp_step; wp_step; wp_step
    refine wp_firsttcStore h6 (hgl _ (by decide)) ec (ld hc6) hlev1 (by omega)
      (Int.ofNat_lt.mpr hpos) hln ?_
    intro m7 h7 hu7 hg7
    have H7 : HeadAt L m7 ct.2.2.2 true false chain' := by
      rw [hct]
      exact H6.stepS hfresh h7 hu7 (fun z hz => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          subst hz; exact .inl (vars_chg hd hbTC (by sep_ne hd))) hg7
        (WorkMono.of_unch H6.search.work hu7 (fun z hz e => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
            exact vars_notWork hd hbTC (e ▸ hz))
          (fun z hz e => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
            exact H6.search.work_not hz (e ▸ SLoc.vars_blocks hbTC)))
    have nloc7 : ∀ z ∈ L.locals, ¬ z ∈ [S.bTC] := fun z hz e => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
      exact (H6.locals z hz).2.1 (e ▸ SLoc.vars_blocks hbTC)
    have hncL7 : Mem.load .Mint32 m7 O.bnc (zOfInt 0) = some (.Vint (ir (v.1 : Int))) := by
      rw [hu7.load _ _ _ (nloc7 _ (by simp [L, LCtx.locals])), hU6.load _ _ _ (by
        rintro (h' | h' | h' | h' | h' | h')
        · exact hbncS h'.1
        · exact h' (hloc5 _ (by simp [L, LCtx.locals])).2.1
        · exact (hloc5 _ (by simp [L, LCtx.locals])).2.2 h'
        · exact hbtL _ (by simp [L, LCtx.locals]) h'.symm
        · exact d13 h'
        · exact d14 h')]
      exact hncL
    simp only [seqPost, Post.after, E0_append]
    -- no node callback, not a leaf
    wp_step
    refine wp_userNode H7.search (hgl _ (by decide)) ?_
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine wp_fpnLeaf H7.search (gl _ (by decide)) hfr enc hncL7 hncv hlab1 hlev1 hl1 hln
      (fun h => absurd h hne) (fun _ => ?_)
    simp only [seqPost, Post.after, E0_append]
    -- the kill check
    have k710 : ∀ x, x ≠ idOf 710 → PTree.get x (PTree.set (idOf 710) (.Vint Int.zero) le1) =
        PTree.get x le1 := fun x h => temps_gso _ _ h
    wp_step
    refine wp_fpnKill (hgl _ (by decide)) ?_
    simp only [seqPost, Post.after]
    -- the cheap-automorphism test
    wp_step
    refine wp_fpnCheap H7.search (hgl _ (by decide)) (hgl _ (by decide)) (hgl _ (by decide))
      (hgl _ (by decide)) (by rw [k710 _ (by decide)]; exact hptn1)
      (by rw [k710 _ (by decide)]; exact hlev1) hl1 hln ?_
    intro le8 m8 h8 hu8 hg8 hle8
    have H8 : HeadAt L m8 (cheapCheck true level ct.2.2.2) true false chain' :=
      H7.stepS hfresh h8 hu8 (fun z hz => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          subst hz; exact .inl ⟨by simp [SLoc.blocks], by sep_ne hd, by decide⟩) hg8
        (WorkMono.of_unch H7.search.work hu8 (fun z hz e => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
            subst e; revert hz; decide)
          (fun z hz e => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
            exact H7.search.work_not hz (e ▸ by simp [SLoc.blocks])))
    simp only [seqPost, Post.after, E0_append]
    -- `index = 0; childcount = 0;`
    wp_step; wp_step; wp_step; wp_step
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step; wp_step
    simp only [seqPost, Post.after, E0_append]
    generalize hle9 : PTree.set dense.id.childcount _ (PTree.set dense.id.index _ le8) = le9
    have k9 : ∀ x, x ≠ dense.id.childcount → x ≠ dense.id.index → x ≠ idOf 710 → x ≠ idOf 711 →
        x ≠ idOf 712 → PTree.get x le9 = PTree.get x le1 := fun x h1 h2 h3 h4 h5 => by
      rw [← hle9, temps_gso _ _ h1, temps_gso _ _ h2, hle8 x h4 h5, k710 x h3]
    have hidx9 : PTree.get dense.id.index le9 = some (.Vint (ir ((0 : Nat) : Int))) := by
      rw [← hle9, temps_gso _ _ (by decide), temps_gss]; rfl
    have hcc9 : ∃ c, PTree.get dense.id.childcount le9 = some (.Vint c) := by
      rw [← hle9, temps_gss]; exact ⟨_, rfl⟩
    -- the first vertex of the target cell
    have hsw0 := nodeOk_sweepFirst hn0 hnI hok ctx 100 hne
    obtain ⟨tv1, htv1, hok1⟩ := hsw0
    have nb7 : ¬ bt ∈ [S.bTC] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      intro hw; apply btS; show bt ∈ S.blocks; rw [hw]; exact SLoc.vars_blocks hbTC
    have nb8 : ¬ bt ∈ [Block.noncheaplevel] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      intro hw; apply btS; show bt ∈ S.blocks; rw [hw]; simp [SLoc.blocks]
    obtain ⟨ws, hwa, hwr⟩ := hws
    have hwa8 : ArrayAt m8 .Mint64 bt 0 (longs ws) S.M := (hwa.unch hu7 nb7).unch hu8 nb8
    wp_step; wp_step
    refine wp_fpnFirst H8.search (gl _ (by decide))
      (by rw [k9 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact htcl1)
      hwa8 hwr ?_
    intro r hr
    have htv1' : (maketargetcell ctx v.2.2.lab v.2.2.ptn level 100 (-1)).2.1.nextElem none =
        some tv1 := by
      have h' : ct.2.1.nextElem none = some tv1 := htv1
      rw [hct] at h'; exact h'
    have hr' : r = tv1 := by
      rcases hr with ⟨h1, -⟩ | ⟨w, h1, h2⟩
      · exact absurd (htv1'.symm.trans h1) (by simp)
      · rw [h2, Option.some.inj (htv1'.symm.trans h1)]
    subst hr'
    simp only [seqPost, Post.after, E0_append]
    -- the child loop
    have hle10 : ∀ x, x ≠ dense.id.tv1 → x ≠ dense.id.tv → x ≠ idOf 714 → x ≠ idOf 713 →
        PTree.get x (PTree.set dense.id.tv1 (.Vint (ir (tv1 : Int))) (PTree.set dense.id.tv
          (.Vint (ir (tv1 : Int))) (PTree.set (idOf 714) (.Vint (ir (tv1 : Int)))
            (PTree.set (idOf 713) (.Vint (ir (tv1 : Int))) le9)))) = PTree.get x le9 :=
      fun x h1 h2 h3 h4 => by rw [temps_gso _ _ h1, temps_gso _ _ h2, temps_gso _ _ h3, temps_gso _ _ h4]
    have k10 : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.tcell,
        dense.id.tcnode_this], PTree.get x (PTree.set dense.id.tv1 (.Vint (ir (tv1 : Int)))
          (PTree.set dense.id.tv (.Vint (ir (tv1 : Int))) (PTree.set (idOf 714) (.Vint (ir (tv1 : Int)))
            (PTree.set (idOf 713) (.Vint (ir (tv1 : Int))) le9)))) = PTree.get x le1 := by
      intro x hx
      rw [hle10 x (by revert x; decide) (by revert x; decide) (by revert x; decide)
        (by revert x; decide), k9 x (by revert x; decide) (by revert x; decide) (by revert x; decide)
        (by revert x; decide) (by revert x; decide)]
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at k10
    obtain ⟨ka, kb, kc, kd, ke⟩ := k10
    have hE : FEnv (fEnv O) L := ⟨enc, ek, ez, ec, eq, hgl⟩
    have hT10 : FTemps (PTree.set dense.id.tv1 (.Vint (ir (tv1 : Int))) (PTree.set dense.id.tv
        (.Vint (ir (tv1 : Int))) (PTree.set (idOf 714) (.Vint (ir (tv1 : Int)))
          (PTree.set (idOf 713) (.Vint (ir (tv1 : Int))) le9)))) L tv1 :=
      ⟨ka.trans hlab1, kb.trans hptn1, kc.trans hlev1, kd.trans htcl1, ke.trans hthis1,
        temps_gss _ _ _, by rw [hle10 _ (by decide) (by decide) (by decide) (by decide)]; exact hcc9⟩
    -- the locals' values at the loop
    have arr1 : ∀ {mm : mem} {b : block} {w : val}, Mem.load .Mint32 mm b (zOfInt 0) = some w →
        Mem.valid_access mm .Mint32 b (zOfInt 0) .Freeable → ArrayAt mm .Mint32 b 0 (fun _ => w) 1 :=
      fun {mm b w} hl ha => by
        refine ⟨Int.le_refl _, by decide, fun i hi => ?_, fun i hi => ?_⟩
        · obtain rfl : i = 0 := by omega
          exact hl
        · obtain rfl : i = 0 := by omega
          exact Mem.valid_access_implies _ _ _ _ _ _ ha (.perm_F_any _)
    have nl78 : ∀ z ∈ L.locals, ¬ z ∈ [S.bTC] ∧ ¬ z ∈ [Block.noncheaplevel] := fun z hz =>
      ⟨nloc7 z hz, by
        simp only [List.mem_cons, List.mem_nil_iff, or_false]
        intro e; exact (H7.locals z hz).2.1 (by rw [e]; simp [SLoc.blocks])⟩
    have ld8 : ∀ z ∈ L.locals, Mem.load .Mint32 m8 z (zOfInt 0) = Mem.load .Mint32 m6 z (zOfInt 0) :=
      fun z hz => by rw [hu8.load _ _ _ (nl78 z hz).2, hu7.load _ _ _ (nl78 z hz).1]
    have hnc8 : ArrayAt m8 .Mint32 O.bnc 0 (fun _ => .Vint (ir (L.nc : Int))) 1 :=
      arr1 (by rw [hu8.load _ _ _ (nl78 _ (by simp [L, LCtx.locals])).2]; exact hncL7)
        (H8.fre _ (by simp [L, LCtx.locals]))
    have hct1 : ((ct.1.toNat : Nat) : Int) =
        ((maketargetcell ctx v.2.2.lab v.2.2.ptn level 100 (-1)).1 : Int) := by
      rw [hct]; simp
    have lbc : Mem.load .Mint32 m8 O.bc (zOfInt 0) =
        some (.Vint (ir ((ct.1.toNat : Nat) : Int))) := by
      rw [ld8 O.bc (by simp [L, LCtx.locals]), hct1]; exact ld hc6
    have lbz : Mem.load .Mint32 m8 O.bz (zOfInt 0) = some (.Vint (ir ((ct.2.2.1 : Nat) : Int))) := by
      rw [ld8 O.bz (by simp [L, LCtx.locals]), hct]; exact ld hz6
    have htc8 : ArrayAt m8 .Mint32 O.bc 0 (fun _ => .Vint (ir (L.tc : Int))) 1 :=
      arr1 lbc (H8.fre _ (by simp [L, LCtx.locals]))
    have htz8 : ArrayAt m8 .Mint32 O.bz 0 (fun _ => .Vint (ir (L.tcsize : Int))) 1 :=
      arr1 lbz (H8.fre _ (by simp [L, LCtx.locals]))
    have hcell8 : ∃ tw, ArrayAt m8 .Mint64 bt 0 (longs tw) S.M ∧
        SetRep (fun w => bv64 (tw w)) S.M ct.2.1 := ⟨ws, hwa8, by rw [hct]; exact hwr⟩
    have HL := H8.loop hcell8 hnc8 htc8 htz8
    have hlevn : level + 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hpf.levelLe hlt)
    have htv1n : tv1 < n := hok1.pos.1
    -- HexGraphIso's sweep
    have hsw : sweep true ctx nautyInf 100 (n + 2 - level) (n + 1) level v.1 ct.1.toNat
        ((ct.2.1.nextElem none).getD 0) (ct.2.1.nextElem none) ct.2.1 0
        (cheapCheck true level ct.2.2.2) =
        fSweep L tv1 (n + 1) (some tv1) ct.2.1 0 (cheapCheck true level ct.2.2.2) := by
      have h' : ct.2.1.nextElem none = some tv1 := htv1
      rw [h']
      show sweep _ _ _ _ (n + 2 - level) _ _ _ _ _ _ _ _ _ =
        sweep _ _ _ _ (n + 3 - (level + 1)) _ _ _ _ _ _ _ _ _
      rw [show n + 3 - (level + 1) = n + 2 - level by omega]
      rfl
    have hNR : hexNode true ctx level nc st =
        match (fSweep L tv1 (n + 1) (some tv1) ct.2.1 0 (cheapCheck true level ct.2.2.2)).1 with
        | .done => (.unwind (level - 1) false, afterSweep true level ct.2.2.1
            (fSweep L tv1 (n + 1) (some tv1) ct.2.1 0 (cheapCheck true level ct.2.2.2)).2.1
            (fSweep L tv1 (n + 1) (some tv1) ct.2.1 0 (cheapCheck true level ct.2.2.2)).2.2)
        | _ => ((fSweep L tv1 (n + 1) (some tv1) ct.2.1 0 (cheapCheck true level ct.2.2.2)).1,
            (fSweep L tv1 (n + 1) (some tv1) ct.2.1 0 (cheapCheck true level ct.2.2.2)).2.2) := by
      rw [hN]; dsimp only; rw [ite_eq_right hne, hsw]; rfl
    have hnf0 := SearchInf.nodeOk_noFuel hn0 hnI hok ctx 100 hln
    have hEmS : Em true level nc st =
        fSweepEm Em L tv1 (n + 1) (some tv1) ct.2.1 (cheapCheck true level ct.2.2.2) := by
      rw [hEmL]; dsimp only; rw [ite_eq_right hne]
      have h' : ct.2.1.nextElem none = some tv1 := htv1
      show sweepEmFirst _ _ _ _ _ _ _ (ct.2.1.nextElem none) _ _ = _
      rw [h']; rfl
    refine wp_fpnLoop (Em := Em) (G := G) L hE hfr hn0 hnI (fun s ch => hRecF s (v.1 + 1) ch)
      (fun s ch => hRecO s (v.1 + 1) ch) hcb hlevn (show v.1 + 1 ≤ n from hlt) htv1n ?_ ?_ ?_
      (k := n + 1)
      ⟨some tv1, ct.2.1, cheapCheck true level ct.2.2.2, 0, true, chain', HL, hT10,
        by rw [temps_gso _ _ (by decide), temps_gss]; rfl,
        by rw [hle10 _ (by decide) (by decide) (by decide) (by decide)]; exact hidx9, by omega,
        fun _ => rfl, hok1, rfl, [], Emits.nil, rfl⟩
    · intro hf
      apply hnf0
      show (hexNode true ctx level nc st).1 = .fuel
      rw [hNR]
      revert hf
      generalize fSweep L tv1 (n + 1) (some tv1) ct.2.1 0 (cheapCheck true level ct.2.2.2) = R
      intro hf
      rw [hf]
    · intro t le' m' cl ch hdn hEm hL' hT hidx hidxle
      obtain ⟨x, hx, hgt⟩ := exists_gt_of_bcount (n := n) (ptn := v.2.2.ptn)
        (by rw [← hpf.count]; exact hlt)
      have hmb := mtc_bounds ctx v.2.2.lab v.2.2.ptn level 100 (-1) hpf.ptnSize
        (Nat.le_trans hpf.ptnLast hl1) (by omega) hx hgt
      have hsz : ct.2.2.1 ≤ n := by rw [hct]; exact hmb.2
      -- MULTIPLY
      wp_step
      refine wp_fpnGrp hL'.search (hgl _ (by decide)) hidx ?_
      intro le'' m'' h'' hu'' hg'' hle''
      have H' := hL'.head.stepS hfresh h'' hu'' (fun z hz => by
          subst hz; exact .inl (vars_chg hd hbst (by sep_ne hd))) hg''
        (WorkMono.of_unch hL'.search.work hu'' (fun z hz e => vars_notWork hd hbst (e ▸ hz))
          (fun z hz e => hL'.search.work_not hz (e ▸ SLoc.vars_blocks hbst)))
      have hbzS : O.bz ∉ S.blocks := hLS _ (by simp)
      have hzv : Mem.load .Mint32 m'' O.bz (zOfInt 0) = some (.Vint (ir (L.tcsize : Int))) := by
        rw [hu''.load _ _ _ (fun e => hbzS (by rw [e]; exact SLoc.vars_blocks hbst))]; exact ld hL'.tz
      simp only [seqPost, Post.after, E0_append]
      refine wp_fpnLast h'' (gl _ (by decide)) hfr ez hzv
        (by rw [hle'' _ (by decide)]; exact hidx) (by rw [hle'' _ (by decide)]; exact hT.lev)
        hsz hidxle hln ?_
      intro m3 h3 hu3 hg3
      have H'' := H'.stepS hfresh h3 hu3 (fun z hz => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          subst hz; exact .inl ⟨by simp [SLoc.blocks], by sep_ne hd, by decide⟩) hg3
        (WorkMono.of_unch h''.work hu3 (fun z hz e => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
            subst e; revert hz; decide)
          (fun z hz e => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
            exact h''.work_not hz (e ▸ by simp [SLoc.blocks])))
      have hr : hexNode true ctx level nc st = (.unwind (level - 1) false, afterSweep true level
          ct.2.2.1 (fSweep L tv1 (n + 1) (some tv1) ct.2.1 0 (cheapCheck true level ct.2.2.2)).2.1
          (fSweep L tv1 (n + 1) (some tv1) ct.2.1 0 (cheapCheck true level ct.2.2.2)).2.2) := by
        rw [hNR, hdn]
      have hEm' := emits_killEv.append hEm
      rw [List.nil_append, ← hEmS] at hEm'
      have := fPost (xi := xi) (G := G) (Em := Em) (O := O)
        (args := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level), .Vint (ir nc),
          .Vptr (tcParent chain level) Ptrofs.zero])
        (v := ((level - 1 : Nat) : Int)) H'' hfresh hLO hnd rfl
        (by rw [hr]) (by rw [hr]; rfl)
        hEm'
        (fun tg sh h => by rw [hr] at h; cases h; exact Nat.sub_lt hl1 Nat.one_pos)
      rw [Int.ofNat_sub hl1] at this
      revert this
      cases Mem.free_list m3 (blocks_of_env ge (fEnv O)) <;> simp only [Post.after, E0_append, append_E0] <;> exact fun h => h
    · intro t m' cl ch tg sh hu htg hL' hEm
      have hr : hexNode true ctx level nc st = (.unwind tg sh,
          (fSweep L tv1 (n + 1) (some tv1) ct.2.1 0 (cheapCheck true level ct.2.2.2)).2.2) := by
        rw [hNR, hu]
      have hEm' := emits_killEv.append hEm
      rw [List.nil_append, ← hEmS] at hEm'
      have := fPost (xi := xi) (G := G) (Em := Em) (O := O)
        (args := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level), .Vint (ir nc),
          .Vptr (tcParent chain level) Ptrofs.zero])
        (v := (tg : Int)) hL'.head hfresh hLO hnd rfl
        (by rw [hr]) (by rw [hr]; rfl)
        hEm'
        (fun tg' sh' h => by rw [hr] at h; cases h; exact htg)
      revert this
      cases Mem.free_list m' (blocks_of_env ge (fEnv O)) <;> simp only [Post.after, E0_append, append_E0] <;> exact fun h => h
  · intro hv1n
    have hvn : (visit ctx level nc st).1 = n := hv1n
    have hct : ct = ((-1 : Int), VSet.empty, 0, { recordFirst level v.2.1 v.2.2 with
        firsttc := (recordFirst level v.2.1 v.2.2).firsttc.set! level (-1) }) := by
      show chooseTarget true ctx 100 level v.1 _ = _
      rw [chooseTarget_true_eq, ite_eq_right (fun h => h hv1n)]
    have hbTC : S.bTC ∈ S.vars := by simp [SLoc.vars]
    wp_step; wp_step; wp_step
    refine wp_firsttcStore H5.search (hgl _ (by decide)) ec (ld hA5) hlev1 (by omega) (by omega) hln ?_
    intro m6 h6 hu6 hg6
    have H6 := H5.stepS hfresh h6 hu6 (fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        subst hz; exact .inl (vars_chg hd hbTC (by sep_ne hd))) hg6
      (WorkMono.of_unch H5.search.work hu6 (fun z hz e => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
          exact vars_notWork hd hbTC (e ▸ hz))
        (fun z hz e => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
          exact H5.search.work_not hz (e ▸ SLoc.vars_blocks hbTC)))
    have hncL6 : Mem.load .Mint32 m6 O.bnc (zOfInt 0) = some (.Vint (ir (v.1 : Int))) := by
      rw [hu6.load _ _ _ (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false]
        exact fun e => hbncS (e ▸ SLoc.vars_blocks hbTC))]
      exact hncL
    simp only [seqPost, Post.after, E0_append]
    wp_step
    refine wp_userNode h6 (hgl _ (by decide)) ?_
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine wp_fpnLeaf h6 (gl _ (by decide)) hfr enc hncL6 hncv hlab1 hlev1 hl1 hln ?_
      (fun h => absurd hv1n h)
    intro _ m7 h7 hF hW
    have H7 := H6.stepS hfresh h7 hF.1 (fun z hz => hz) hF.2 hW
    have hr : hexNode true ctx level nc st = (.unwind (level - 1) false, firstterminal level ct.2.2.2) := by
      rw [hN]; dsimp only; rw [ite_eq_left hvn]
    have := fPost (xi := xi) (G := G) (Em := Em) (O := O) (t := E0)
      (args := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level), .Vint (ir nc),
        .Vptr (tcParent chain level) Ptrofs.zero])
      (v := ((level - 1 : Nat) : Int)) H7 hfresh hLO hnd rfl
      (by rw [hr, hct]) (by rw [hr]; rfl)
      (by rw [hEmL]; dsimp only; rw [ite_eq_left hvn]; exact Emits.nil)
      (fun tg sh h => by rw [hr] at h; cases h; show level - 1 < level; omega)
    rw [show ((level - 1 : Nat) : Int) = (level : Int) - 1 by omega] at this
    revert this
    cases Mem.free_list m7 (blocks_of_env ge (fEnv O)) <;> simp only [Post.after] <;> exact fun h => h

end NautyVerified.Proofs.Search
