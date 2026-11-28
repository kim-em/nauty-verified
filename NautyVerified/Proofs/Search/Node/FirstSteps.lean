import NautyVerified.Proofs.Search.Node.Compare
import NautyVerified.Proofs.Search.Node.OtherSteps
import NautyVerified.Proofs.Search.Node.Target
import NautyVerified.Proofs.Search.Node.Choose
import NautyVerified.Proofs.Search.Node.Firstpathnode

/-!
# Straight-line steps of `firstpathnode0`

`wp_recordFirst`: `firstcode[level] = (short)refcode` is HexGraphIso's
`recordFirst level code`, for the `refcode` local holding `code`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Refine (tv)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

theorem Arrays.setFirstcode {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    (h : Arrays m S ctx st) (hu : Unch m m' (· = S.bFC)) (hd : S.blocks.Pairwise (· ≠ ·))
    {fc : Array Nat} (hfc : ArrayAt m' .Mint16signed S.bFC 0 (shorts fc) (n + 2)) :
    Arrays m' S ctx { st with firstcode := fc } := by
  obtain ⟨aw, ha, har⟩ := h.active
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  obtain ⟨wv, hwv⟩ := h.workperm
  exact ⟨h.lab.unch hu (by sep_ne hd), h.ptn.unch hu (by sep_ne hd),
    h.orbits.unch hu (by sep_ne hd), ⟨aw, ha.unch hu (by sep_ne hd), har⟩,
    ⟨fw, hf.unch hu (by sep_ne hd), hfr⟩, ⟨wv, hwv.unch hu (by sep_ne hd)⟩,
    h.firstlab.unch hu (by sep_ne hd), h.canonlab.unch hu (by sep_ne hd), hfc,
    h.canoncode.unch hu (by sep_ne hd), h.firsttc.unch hu (by sep_ne hd),
    h.canong.unch hu (by sep_ne hd), h.autos.unch hu (by sep_ne hd) (by sep_ne hd),
    ⟨h.graph.arr.unch hu (by sep_ne hd), h.graph.rep⟩⟩

/-- `firstcode[level] = (short)refcode;` -/
theorem wp_recordFirst {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level code : Nat} {bk : block}
    (h : SearchAt m S ctx st pre nsp)
    (hE : PTree.get dense.id.«nauty:firstcode» e = none)
    (hek : PTree.get dense.id.«refcode» e = some (bk, tint))
    (hkv : Mem.load .Mint32 m bk (zOfInt 0) = some (.Vint (ir code)))
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hc : code < 32768) (hn : level ≤ n)
    (hQ : ∀ m', SearchAt m' S ctx (recordFirst level code st) pre nsp → Unch m m' (· ∈ [S.bFC]) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (gats dense.id.«nauty:firstcode» (tv dense.id.level))
      (.Ecast (.Evar dense.id.«refcode» tint) tshort)) Q e le m := by
  have hnl := h.nlt
  have hd := h.distinct
  have hrhs : Exec.evalExpr ge e le m (.Ecast (.Evar dense.id.«refcode» tint) tshort) =
      some (.Vint (ir (code : Int))) := by
    rw [Exec.evalExpr, eval_local hek hkv]
    simp only [typeof, Cfrontend.Cop.sem_cast, Cfrontend.Cop.classify_cast, Cfrontend.Cop.cast_int_int]
    exact congrArg (fun x => some (val.Vint x)) (sign_ext16_ir (a := code) (by omega) (by omega))
  refine wp_gstoreS hE Program.find_nautyFirstcode
    (h.dyns.firstcode.ptr (by have := h.dyns.capFC; omega)) h.arrays.firstcode (by omega)
    (tv dense.id.level) level (by omega) hlev rfl _ code hc hrhs (.inr rfl) ?_
  intro m' harr hu hk hv
  have hU : Unch m m' (· ∈ [S.bFC]) := hu.mono fun z hz => by simp [hz]
  have hfs := h.inv.firstcodeSize
  refine hQ m' ?_ hU hv
  refine h.rebuild hU (fun z hz => by simp at hz; subst hz; simp [SLoc.wr, SLoc.wrV])
    (fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hk | exact Keep.unch hu (by sep_ne hd))
    { h.scalars.unch hu (by sep_all hd) with } { h.stats.unch hu (by sep_ne hd) with }
    (h.arrays.setFirstcode hu hd (by rw [shorts_set (by omega)]; exact harr)) ?_
  have i := h.inv
  exact { i with
    codesSmall := fun j hj => by
      refine ⟨?_, (i.codesSmall j hj).2⟩
      show (st.firstcode.set! level code)[j]! < 32768
      by_cases hjl : j = level
      · subst hjl; rw [Array.getElem!_set!_self _ _ _ (by omega)]; omega
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hjl)]; exact (i.codesSmall j hj).1
    firstcodeSize := by show (st.firstcode.set! level code).size = n + 2; simp [hfs] }

set_option maxHeartbeats 2000000 in
/-- The first path's target cell: `if (numcells != n) { maketargetcell(…, -1, …);
stats->tctotal += tcellsize; }`. -/
theorem wp_fpnTarget {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level nc : Nat}
    (h : SearchAt m S ctx st pre nsp) (hvU : Mem.valid_block m S.bUA)
    (hvT : Mem.valid_block m Block.tcnode0)
    {bt bz bc bnc : block}
    (hloc : [bt, bz, bc].Pairwise (· ≠ ·))
    (hlocS : ∀ z ∈ [bt, bz, bc], z ∉ S.blocks ∧ Mem.valid_block m z ∧ ¬ IsWork m z)
    (htc : PTree.get dense.id.«tcell» le = some (.Vptr bt Ptrofs.zero))
    (hez : PTree.get dense.id.«tcellsize» e = some (bz, tint))
    (hec : PTree.get dense.id.«tc» e = some (bc, tint))
    (hge : ∀ x ∈ [dense.id.«maketargetcell», dense.id.«nauty:g», dense.id.«nauty:tc_level»,
      dense.id.«nauty:digraph», dense.id.«nauty:dispatch», dense.id.«nauty:m», dense.id.«nauty:n»],
      PTree.get x e = none)
    (hEs : PTree.get dense.id.«nauty:stats» e = none)
    (ht : ∃ v, ArrayAt m .Mint64 bt 0 v S.M) (hz : ∃ v, ArrayAt m .Mint32 bz 0 v 1)
    (hc : ∃ v, ArrayAt m .Mint32 bc 0 v 1)
    (hnc : PTree.get dense.id.numcells e = some (bnc, tint))
    (hncv : Mem.load .Mint32 m bnc (zOfInt 0) = some (.Vint (ir nc))) (hncl : nc ≤ n)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hl1 : 1 ≤ level) (hln : level ≤ n)
    (hnt : nc ≠ n → ∃ x < n, level < st.ptn[x]!)
    (hQy : nc ≠ n → ∀ m', SearchAt m' S ctx
        { st with tctotal := st.tctotal + (maketargetcell ctx st.lab st.ptn level 100 (-1)).2.2 }
        pre nsp →
      (∃ ws, ArrayAt m' .Mint64 bt 0 (Set.longs ws) S.M ∧ SetRep (fun w => bv64 (ws w)) S.M
        (maketargetcell ctx st.lab st.ptn level 100 (-1)).2.1) →
      ArrayAt m' .Mint32 bz 0
        (fun _ => .Vint (ir ((maketargetcell ctx st.lab st.ptn level 100 (-1)).2.2 : Int))) 1 →
      ArrayAt m' .Mint32 bc 0
        (fun _ => .Vint (ir ((maketargetcell ctx st.lab st.ptn level 100 (-1)).1 : Int))) 1 →
      Unch m m' (fun z => S.Chg z ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨ z = bt ∨ z = bz ∨
        z = bc) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → WorkMono m m' →
      (∀ z ∈ [bt, bz, bc], Keep m m' z) → Q.normal E0 e le m')
    (hQn : nc = n → Q.normal E0 e le m) :
    Wp xi ge f Firstpathnode.target Q e le m := by
  have hnl := h.nlt
  have hncE : Exec.evalExpr ge e le m (.Evar dense.id.numcells tint) = some (.Vint (ir nc)) :=
    eval_local hnc hncv
  have hEn : PTree.get dense.id.«nauty:n» e = none := hge _ (by simp)
  simp only [Firstpathnode.target, Set.sk]
  apply wp_if_eval
  rw [Exec.evalExpr, hncE, eval_gint hEn find_n h.fixed.nn]
  simp only [typeof, cop]
  rw [ir_eq (a := (nc : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hne : nc = n
  · rw [ite_eq_right (by simp [hne])]
    exact wp_skip (hQn hne)
  rw [ite_eq_left (by simp; omega)]
  obtain ⟨x, hx, hgt⟩ := hnt hne
  have hsz := h.inv.ptnSize
  have hlast : st.ptn[n - 1]! ≤ level := Nat.le_trans h.inv.ptnLast hl1
  obtain ⟨-, hsz2⟩ := mtc_bounds ctx st.lab st.ptn level 100 (-1) hsz hlast (by omega) hx hgt
  wp_step; wp_step; wp_step
  refine wp_nodeTarget h hvU hvT hloc hlocS htc hez hec hge ht hz hc hlab hptn hlev hl1 hln
    (hintE := .Eunop .Oneg (ci 1 tint) tint) (hint := -1) rfl rfl (by decide) (by omega)
    ⟨x, hx, hgt⟩ ?_
  intro m₁ h₁ hws hzv hcv hu₁ hg₁ hw₁ hK₁
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step
  have hzl : Mem.load .Mint32 m₁ bz (zOfInt 0) = some (.Vint (ir
      ((maketargetcell ctx st.lab st.ptn level 100 (-1)).2.2 : Int))) := hzv.load 0 (by decide)
  refine wp_tctotal h₁ hEs hez hzl (by omega) ?_
  intro m' h' hu' hg'
  have hb : ∀ z ∈ [bt, bz, bc], z ≠ S.bst := fun z hz e => (hlocS z hz).1 (e ▸ by simp [SLoc.blocks])
  obtain ⟨ws, hwa, hwr⟩ := hws
  exact hQy hne m' h' ⟨ws, hwa.unch hu' (hb bt (by simp)), hwr⟩ (hzv.unch hu' (hb bz (by simp)))
    (hcv.unch hu' (hb bc (by simp)))
    (hu₁.trans (hu'.mono fun z hz => .inl (by subst hz; exact ⟨by simp [SLoc.blocks], by sep_ne h.distinct, by sep_ne h.distinct⟩))) (fun z hz => hg' z (hg₁ z hz))
    (hw₁.trans hg₁ (WorkMono.of_unch h₁.work hu' (by simp only [workG]; sep_all h.distinct)
      fun z hz e => h₁.work_not hz (e ▸ by simp [SLoc.blocks])))
    (fun z hz => (hK₁ z hz).trans (Alloc.Keep.unch hu' (hb z hz)))

end NautyVerified.Proofs.Search
