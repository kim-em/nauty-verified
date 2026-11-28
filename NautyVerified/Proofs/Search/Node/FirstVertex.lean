import NautyVerified.Proofs.Search.Node.FirstTail

/-!
# One vertex of `firstpathnode0`'s sweep

`FEnv e L`: the node's five `int` locals are bound in `e` to `L`'s blocks, and
no other name is. `FTemps le L tv tv1 index`: the temporaries the loop reads.

`wp_fpnChild`: `if (orbits[tv] == tv) { breakout(…); ADDELEMENT(fixedpts, tv);
cosetindex = tv; <the recursive call>; … }` is HexGraphIso's `firstChild`. A
vertex that continues the sweep ends in `LoopAt` for the new cell and state; one
that unwinds below `level` returns its target.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso Hex.GraphIso.Nauty
open NautyVerified.Spec.SearchInf (NodeOk nautyInfinity)

variable {xi : ExternalCalls} {n : Nat}

/-- The node's locals in `e`. -/
structure FEnv (e : env) (L : LCtx n) : Prop where
  enc : PTree.get dense.id.numcells e = some (L.bnc, tint)
  ek : PTree.get dense.id.refcode e = some (L.bk, tint)
  ez : PTree.get dense.id.tcellsize e = some (L.bz, tint)
  ec : PTree.get dense.id.tc e = some (L.bc, tint)
  eq : PTree.get dense.id.qinvar e = some (L.bq, tint)
  glob : ∀ x, x ∉ [dense.id.numcells, dense.id.refcode, dense.id.tcellsize, dense.id.tc,
    dense.id.qinvar] → PTree.get x e = none

theorem FEnv.gl {e : env} {L : LCtx n} (hE : FEnv e L) (l : List ident)
    (h : ∀ x ∈ l, x ∉ [dense.id.numcells, dense.id.refcode, dense.id.tcellsize, dense.id.tc,
      dense.id.qinvar] := by decide) : ∀ x ∈ l, PTree.get x e = none :=
  fun x hx => hE.glob x (h x hx)

/-- The temporaries of the loop. -/
structure FTemps (le : temp_env) (L : LCtx n) (tv1 : Nat) : Prop where
  lab : PTree.get dense.id.«lab» le = some (.Vptr L.S.bl L.S.lofs)
  ptn : PTree.get dense.id.«ptn» le = some (.Vptr L.S.bp L.S.pofs)
  lev : PTree.get dense.id.«level» le = some (.Vint (ir L.level))
  tcell : PTree.get dense.id.tcell le = some (.Vptr L.btc Ptrofs.zero)
  this : PTree.get dense.id.«tcnode_this» le = some (.Vptr L.bnd Ptrofs.zero)
  tv1 : PTree.get dense.id.«tv1» le = some (.Vint (ir tv1))
  cc : ∃ c, PTree.get dense.id.«childcount» le = some (.Vint c)

theorem FTemps.of {le le' : temp_env} {L : LCtx n} {tv1 : Nat} (h : FTemps le L tv1)
    (he : ∀ x ∈ [dense.id.«lab», dense.id.«ptn», dense.id.«level», dense.id.tcell,
      dense.id.«tcnode_this», dense.id.«tv1»], PTree.get x le' = PTree.get x le)
    (hc : ∃ c, PTree.get dense.id.«childcount» le' = some (.Vint c)) : FTemps le' L tv1 := by
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at he
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := he
  exact ⟨e1 ▸ h.lab, e2 ▸ h.ptn, e3 ▸ h.lev, e4 ▸ h.tcell, e5 ▸ h.this, e6 ▸ h.tv1, hc⟩

/-- Before the first child, the orbit test at `tv1` passes. -/
theorem SweepOkFirst.orb_tv1 {k : Nat} {G : Colored n k} {level nc tc tv1 : Nat} {cell : VSet n}
    {st : Search n} (h : SweepOkFirst G level nc tc tv1 cell (some tv1) st) :
    (st.orbits[tv1]! == tv1) = true := by
  obtain ⟨⟨t, st₀, rfl, -, -, -, hcur, -, hph⟩, -⟩ := h
  rcases hph with ⟨-, horb, -⟩ | ⟨hpast, -⟩
  · have h1 := horb tv1 (VSet.mem_lt (hcur tv1 rfl))
    show (st₀.orbits[tv1]! == tv1) = true
    simp [h1]
  · have := hpast rfl tv1 rfl
    omega

/-- The current vertex is in the target cell, which is a cell of `lab` from `tc`. -/
theorem SweepOkFirst.pos {k : Nat} {G : Colored n k} {level nc tc tv1 tv : Nat} {cell : VSet n}
    {st : Search n} (h : SweepOkFirst G level nc tc tv1 cell (some tv) st) :
    tv < n ∧ tc < n ∧ ∃ j, tc ≤ j ∧ j < n ∧ st.lab[j]! = tv := by
  obtain ⟨⟨t, st₀, rfl, -, -, htarget, hcur, -⟩, -⟩ := h
  have hm := hcur tv rfl
  obtain ⟨len, hcell, hmem⟩ := htarget
  obtain ⟨-, h2, h3⟩ := hcell (mem_ne_empty hm)
  obtain ⟨o, ho, hlo⟩ := mem_segN_iff.1 (hmem tv hm)
  exact ⟨VSet.mem_lt hm, by omega, tc + o, by omega, by omega, hlo⟩

theorem child_true_eq (level tc tv : Nat) (st : Search n) :
    child true level tc tv st =
      { { brokenSt level tc tv st with fixedpts := st.fixedpts.insert tv } with cosetindex := tv } := by
  simp [child]

/-- What the vertex emits. -/
abbrev vertexEm {k : Nat} (Em : Bool → Nat → Nat → Search n → List Int) (level nc tc tv1 tv : Nat)
    (st : Search n) : List Int :=
  if st.orbits[tv]! == tv then Em (tv == tv1) (level + 1) (nc + 1) (child true level tc tv st) else []

/-- `firstChild` at the vertex, with nauty's pinned constants. -/
abbrev fChild (L : LCtx n) (tv1 tv : Nat) (cell : VSet n) (st : Search n) : Exit × VSet n × Search n :=
  firstChild L.ctx nautyInf 100 (nodeFuel n (L.level + 1)) L.level L.nc L.tc tv1 tv cell st

set_option maxHeartbeats 8000000 in
theorem wp_fpnChild {k : Nat} {G : Colored n k} {Em : Bool → Nat → Nat → Search n → List Int}
    {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    (L : LCtx n) {st : Search n} {pre : Bool} {cell : VSet n} {ch : List (block × block)}
    {tv tv1 : Nat} (hE : FEnv e L) (hT : FTemps le L tv1)
    (htv : PTree.get dense.id.«tv» le = some (.Vint (ir tv)))
    (h : LoopAt L m st pre false cell ch)
    (hpre : pre = true → tv = tv1) (hok : SweepOkFirst G L.level L.nc L.tc tv1 cell (some tv) st)
    (hn0 : 0 < n) (hn : n + 2 < nautyInfinity)
    (hRecF : ∀ st' ch', Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (firstpathnodeSpec xi (NodeOk G) Em L.S L.ctx st' (L.level + 1) (L.nc + 1) ch'))
    (hRecO : ∀ st' ch', Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (othernodeSpec xi (NodeOk G) Em L.S L.ctx st' (L.level + 1) (L.nc + 1) ch'))
    (hcb : AutomCb xi L.S.bUA) (hln : L.level + 1 ≤ n) (hncl : L.nc + 1 ≤ n) (htv1n : tv1 < n)
    (hfr : f.fn_return = tint)
    (hQd : ∀ t le' m' ch', (fChild L tv1 tv cell st).1 = .done →
      LoopAt L m' (fChild L tv1 tv cell st).2.2 false false (fChild L tv1 tv cell st).2.1 ch' →
      Emits t (vertexEm (k := k) Em L.level L.nc L.tc tv1 tv st) → FTemps le' L tv1 →
      PTree.get dense.id.«tv» le' = some (.Vint (ir tv)) →
      PTree.get dense.id.«index» le' = PTree.get dense.id.«index» le →
      Q.normal t e le' m')
    (hQr : ∀ t m' ch' target short, (fChild L tv1 tv cell st).1 = .unwind target short →
      target < L.level →
      LoopAt L m' (fChild L tv1 tv cell st).2.2 false short (fChild L tv1 tv cell st).2.1 ch' →
      Emits t (vertexEm (k := k) Em L.level L.nc L.tc tv1 tv st) →
      match Mem.free_list m' (blocks_of_env ge e) with
      | some m'' => Q.ret t (.Vint (ir target)) m''
      | none => False) :
    Wp xi ge f fpnChild Q e le m := by
  have hnl := h.search.nlt
  have hd := h.search.distinct
  have hl1 := h.chain.lvl
  obtain ⟨htvn, htcn, hj⟩ := hok.pos
  apply wp_if_eval
  rw [Processnode.eval_eqI (x := (st.orbits[tv]! : Int)) (y := (tv : Int))
    (eval_orbAt h.search (hE.glob _ (by decide)) htv htvn)
    (by simp [Exec.evalExpr, Refine.tv, htv]) rfl rfl
    ⟨by omega, by have := h.search.inv.orbitsSmall tv htvn; omega⟩ ⟨by omega, by omega⟩]
  by_cases ho : st.orbits[tv]! = tv
  · have hb : (st.orbits[tv]! == tv) = true := by simpa using ho
    rw [decide_eq_true (by omega)]
    simp only [show Cfrontend.Cop.bool_val (Val.of_bool true) tint m = some true from rfl, ite_true]
    have chg : ∀ b ∈ [L.S.bl, L.S.bp, L.S.bA, L.S.bF, Block.cosetindex], L.S.Chg b := by
      intro b hb
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by simp [SLoc.blocks], by sep_ne hd, by sep_ne hd⟩
    have hk : ∀ b ∈ [L.S.bl, L.S.bp, L.S.bA, L.S.bF, Block.cosetindex], ∀ z ∈ workG8, z ≠ b := by
      intro b hb z hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      simp only [workG8, List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hb with rfl | rfl | rfl | rfl | rfl <;>
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> sep_ne hd
    -- breakout
    wp_step
    refine wp_nodeBreakout h.search hE.ec (h.tc.load 0 (by decide)) (hE.gl _) hT.lab hT.ptn hT.lev
      htv (by omega) htcn hj (SInv.brokenStFirst hn0 hn L.ctx 100 h.search.inv hok.1) ?_
    intro m₁ hS₁ hu₁ hg₁
    have h₁ := h.small hS₁ hu₁ hg₁ (fun z hz => by
        rcases hz with rfl | rfl | rfl
        · exact chg _ (by simp)
        · exact chg _ (by simp)
        · exact chg _ (by simp))
      (fun z hz hW => by
        rcases hW with rfl | rfl | rfl
        · exact hk _ (by simp) _ hz rfl
        · exact hk _ (by simp) _ hz rfl
        · exact hk _ (by simp) _ hz rfl)
    simp only [seqPost, Post.after, E0_append]
    -- ADDELEMENT
    wp_step
    refine wp_fixAdd hS₁ (hE.glob _ (by decide)) (hE.glob _ (by decide)) htv htvn ?_
    intro m₂ hS₂ hu₂ hg₂
    have h₂ := h₁.small hS₂ hu₂ hg₂ (fun z hz => by subst hz; exact chg _ (by simp))
      (fun z hz hW => hk _ (by simp) _ hz hW)
    simp only [seqPost, Post.after, E0_append]
    -- cosetindex
    wp_step; wp_step; wp_step
    refine wp_setCoset hS₂ (hE.glob _ (by decide)) htv htvn ?_
    intro m₃ hS₃ hu₃ hg₃
    have h₃ := h₂.small hS₃ hu₃ hg₃ (fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; subst hz; exact chg _ (by simp))
      (fun z hz hW => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hW; exact hk _ (by simp) _ hz hW)
    have h₃' : LoopAt L m₃ (child true L.level L.tc tv st) pre false cell ch := by
      rw [child_true_eq]; exact h₃
    simp only [seqPost, Post.after, E0_append]
    have hNok := sweepOkFirst_child hn0 hok L.ctx 100
    have hpre' : tv ≠ tv1 → pre = false := fun hne => by
      cases pre
      · rfl
      · exact absurd (hpre rfl) hne
    -- the recursive call
    wp_step
    obtain ⟨cc, hcc⟩ := hT.cc
    refine wp_fpnCallIf L h₃' (hRecF _ _) (hRecO _ _) hNok hpre' hcb hln hncl htv1n htvn hE.enc
      (hE.gl _) hT.lab hT.ptn hT.lev htv hT.tv1 hT.this hcc ?_
    intro t le₄ m₄ ch₄ h₄ hEm hrt hle hcc4 htg
    simp only [seqPost, Post.after]
    have hle4 : ∀ x ∈ [dense.id.«lab», dense.id.«ptn», dense.id.«level», dense.id.tcell,
        dense.id.«tcnode_this», dense.id.«tv1», dense.id.«tv», dense.id.«index»],
        PTree.get x le₄ = PTree.get x le := fun x hx =>
      hle x (by revert x; decide) (by revert x; decide) (by revert x; decide) (by revert x; decide)
    simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at hle4
    obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := hle4
    have hT4 : FTemps le₄ L tv1 := hT.of (by
      simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
      exact ⟨l1, l2, l3, l4, l5, l6⟩) hcc4
    have hnf := SearchInf.nodeOk_noFuel hn0 hn hNok L.ctx 100 (by omega)
    have hcap : 0 < (childRes L.ctx L.level L.nc L.tc tv tv1 st).2.wsCap := by
      have := h₄.search.inv.wsCap
      have e1 : (childAfter L.ctx L.level L.nc L.tc tv tv1 st).wsCap =
          (childRes L.ctx L.level L.nc L.tc tv tv1 st).2.wsCap := by
        unfold childAfter; split <;> rfl
      rw [← e1, this]; decide
    have hnz : (exitValue (L.level + 1) (childRes L.ctx L.level L.nc L.tc tv tv1 st).1).2 = true →
        0 < (childAfter L.ctx L.level L.nc L.tc tv tv1 st).autos.size := by
      intro hs
      have e1 : (childAfter L.ctx L.level L.nc L.tc tv tv1 st).autos =
          (childRes L.ctx L.level L.nc L.tc tv tv1 st).2.autos := by
        unfold childAfter; split <;> rfl
      rw [e1]
      generalize hr : (childRes L.ctx L.level L.nc L.tc tv tv1 st).1 = r at hs
      rcases r with _ | ⟨tg, sh⟩ | _
      · simp [exitValue] at hs
      · simp only [exitValue] at hs
        subst hs
        exact node_short_autos _ _ _ _ _ _ _ _ hcap hr
      · simp [exitValue] at hs
    have hfc : fChild L tv1 tv cell st = tailRes L.level (childRes L.ctx L.level L.nc L.tc tv tv1 st).1
        cell { childAfter L.ctx L.level L.nc L.tc tv tv1 st with
          fixedpts := (childAfter L.ctx L.level L.nc L.tc tv tv1 st).fixedpts.erase tv } :=
      firstChild_orb _ _ _ _ _ _ _ _ _ _ hb
    have hEm' : Emits t (vertexEm (k := k) Em L.level L.nc L.tc tv1 tv st) := by
      simp only [vertexEm, hb, ite_true]; exact hEm
    refine wp_fpnTail L h₄ hnf htg hnz hfr (hE.gl _) (by rw [l7]; exact htv) htvn hrt hT4.tcell
      hT4.ptn hT4.lev (by omega) ?_ ?_
    · intro m' hd' h'
      rw [← hfc] at hd' h'
      simp only [append_E0]
      exact hQd t le₄ m' ch₄ hd' h' hEm' hT4 (by rw [l7]; exact htv) l8
    · intro m' target short hr hlt h'
      have hfr' : (fChild L tv1 tv cell st).1 = .unwind target short := by
        rw [hfc, hr]; simp [tailRes, hlt]
      have hst : (fChild L tv1 tv cell st).2 = (cell, { childAfter L.ctx L.level L.nc L.tc tv tv1 st with
          fixedpts := (childAfter L.ctx L.level L.nc L.tc tv tv1 st).fixedpts.erase tv }) := by
        rw [hfc, hr]; simp [tailRes, hlt]
      have := hQr t m' ch₄ target short hfr' hlt (by rw [hst]; exact h') hEm'
      revert this
      cases Mem.free_list m' (blocks_of_env ge e) <;> simp [append_E0]
  · -- the vertex is skipped
    have hb : (st.orbits[tv]! == tv) = false := by simpa using ho
    rw [decide_eq_false (by omega)]
    simp only [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m = some false from rfl,
      Bool.false_eq_true, ite_false]
    apply wp_skip
    have hfc : fChild L tv1 tv cell st = (.done, cell, st) := by simp [fChild, firstChild, hb]
    have hp : pre = false := by
      cases pre
      · rfl
      · have := hpre rfl; subst this; rw [hok.orb_tv1] at hb; cases hb
    subst hp
    refine hQd E0 le m ch (by rw [hfc]) (by rw [hfc]; exact h) ?_ hT htv rfl
    simp only [vertexEm, hb, Bool.false_eq_true, ite_false]
    exact Emits.nil

end NautyVerified.Proofs.Search
