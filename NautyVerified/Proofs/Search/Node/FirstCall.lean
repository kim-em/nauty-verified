import NautyVerified.Proofs.Search.Node.FirstLoopAt
import NautyVerified.Proofs.Search.Node.ProcFacts
import NautyVerified.Proofs.Search.Processnode.Cmp
import NautyVerified.Proofs.Search.Node.UaFrame
import NautyVerified.Proofs.Search.Node.Child
import NautyVerified.Proofs.Search.Node.Policy

/-!
# The recursive calls of `firstpathnode0`'s child loop

- `wp_fpnCall`: `rtnlevel = firstpathnode0(lab, ptn, level + 1, numcells + 1,
  tcnode_this);` passes `firstpathnode0`'s specification at the child on, as
  `wp_nodeChild` does for `othernode0`;
- `LoopAt.small`: a step changing only blocks of `S` other than
  `userautomproc`'s, `tcnode0` and the work globals keeps `LoopAt`;
- `eval_orbAt`: reading `orbits[x]`;
- `SearchAt.afterChildFirst`: `gca_first = level; stabvertex = tv1;` is
  HexGraphIso's `afterChildFirst`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

theorem wp_fpnCall {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {NodeOk : Bool → Nat → Nat → Search n → Prop} {Em : Bool → Nat → Nat → Search n → List Int}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {level nc : Nat} {chain : List (block × block)}
    (hRec : Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (firstpathnodeSpec xi NodeOk Em S ctx st (level + 1) (nc + 1) chain))
    (h : SearchAt m S ctx st true false) (hTc : TcChain m S.M Block.tcnode0 chain)
    (hTo : TcOk m S chain) (hlen : level ≤ chain.length) (hcb : AutomCb xi S.bUA)
    (hln : level + 1 ≤ n) (hncl : nc + 1 ≤ n) (hok : NodeOk true (level + 1) (nc + 1) st)
    (hvU : Mem.valid_block m S.bUA) (hpU : Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty)
    {bnc : block} (hen : PTree.get dense.id.numcells e = some (bnc, tint))
    (hncv : Mem.load .Mint32 m bnc (zOfInt 0) = some (.Vint (ir nc)))
    (hge : PTree.get dense.id.«nauty:firstpathnode0» e = none)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (htcn : PTree.get dense.id.«tcnode_this» le =
      some (.Vptr (tcParent chain (level + 1)) Ptrofs.zero))
    (hQ : ∀ t m',
      SearchAt m' S ctx (hexNode true ctx (level + 1) (nc + 1) st).2 false
        (exitValue (level + 1) (hexNode true ctx (level + 1) (nc + 1) st).1).2 →
      Emits t (Em true (level + 1) (nc + 1) st) →
      (∃ chain', TcChain m' S.M Block.tcnode0 chain' ∧ TcOk m' S chain' ∧
        level + 1 ≤ chain'.length ∧ chain'.take level = chain.take level ∧
        ∀ p ∈ chain', p ∈ chain ∨ (¬ Mem.valid_block m p.1 ∧ ¬ Mem.valid_block m p.2)) →
      NodeFrame m m' S chain (level + 1) →
      (∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z) →
      (∀ tg sh, (hexNode true ctx (level + 1) (nc + 1) st).1 = .unwind tg sh → tg < level + 1) →
      Q.normal t e (PTree.set dense.id.«rtnlevel»
        (.Vint (ir (exitValue (level + 1) (hexNode true ctx (level + 1) (nc + 1) st).1).1))
        (PTree.set (idOf 716)
          (.Vint (ir (exitValue (level + 1) (hexNode true ctx (level + 1) (nc + 1) st).1).1)) le))
        m') :
    Wp xi ge f fpnCall Q e le m := by
  have hnl := h.nlt
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.firstpathnodeFn Ptrofs.zero)
    (targs := [tptr tint, tptr tint, tint, tint, tptr tcStruct]) (tres := tint)
    (cc := Common.AST.cc_default)
    (vargs := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir ((level + 1 : Nat) : Int)),
      .Vint (ir ((nc + 1 : Nat) : Int)), .Vptr (tcParent chain (level + 1)) Ptrofs.zero])
    (.Internal dense.fn.«nauty:firstpathnode0») _ hRec rfl ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_firstpathnodeFn]) rfl
    ⟨rfl, h, hTc, hTo, by omega, hcb, by omega, hln, hncl, hok, hvU, hpU⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, hge, find_firstpathnodeFn, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode]
  · simp only [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, hen, hlab, hptn, hlev, htcn,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hncv, ite_true, Refine.tv, typeof, cop,
      ir_add]
    push_cast
    rfl
  · rintro t v m' ⟨hv, hS', hE, hC, hF, hW, hT⟩
    subst hv
    simp only [set_opttemp]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, Refine.tv, append_E0]
    refine hQ t m' hS' hE ?_ hF hW hT
    obtain ⟨c', h1, h2, h3, h4, h5⟩ := hC
    exact ⟨c', h1, h2, h3, by simpa using h4, h5⟩

/-- The naugraph.c and nautil.c work globals. -/
abbrev workG8 : List block :=
  [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
    Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
    Block.nautilWorkperm, Block.nautilWorkpermSz]

/-- A step changing only blocks of `S` other than `userautomproc`'s, `tcnode0`
and the work globals keeps `LoopAt`. -/
theorem LoopAt.small {n : Nat} {L : LCtx n} {m : mem} {st : Search n} {pre nsp : Bool}
    {cell : VSet n} {ch : List (block × block)} (h : LoopAt L m st pre nsp cell ch)
    {m' : mem} {st' : Search n} {pre' nsp' : Bool} {W : block → Prop}
    (hS : SearchAt m' L.S L.ctx st' pre' nsp') (hu : Unch m m' W)
    (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hWS : ∀ z, W z → z ∈ L.S.blocks ∧ z ≠ L.S.bUA ∧ z ≠ Block.tcnode0)
    (hWw : ∀ z ∈ workG8, ¬ W z) : LoopAt L m' st' pre' nsp' cell ch := by
  obtain ⟨tw, hta, htr⟩ := h.cell
  have hmem := List.mem_of_getElem? h.chain.own
  have hbt : ¬ W L.btc := fun hw => (h.chain.ok.apart _ hmem).2.1 (hWS _ hw).1
  exact h.step hS (hu.mono fun z hz => .inl (hWS z hz)) hg
    (fun z hz => .inl (IsWork.back h.search hu hWw hz)) ⟨tw, hta.unch hu hbt, htr⟩
    (Alloc.Keep.unch hu hbt)

/-- `orbits[x]` for `x` holding `c < n`. -/
theorem eval_orbAt {n : Nat} {e : env} {le : temp_env} {m : mem} {S : SLoc} {ctx : Ctx n}
    {st : Search n} {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    (hge : PTree.get dense.id.«nauty:orbits» e = none) {x : ident} {c : Nat}
    (hx : PTree.get x le = some (.Vint (ir c))) (hc : c < n) :
    Exec.evalExpr ge e le m (orbAt x) = some (.Vint (ir (st.orbits[c]! : Int))) := by
  have hnl := h.nlt
  have harr := h.arrays.orbits
  simp only [orbAt, Exec.evalExpr, Exec.lvalOfVar, hge, find_orbits, Exec.derefLoc,
    Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h.fixed.orbits.load, Refine.tv, hx,
    typeof, cop]
  apply load_array harr hc
  apply addr_elem S.oofs _ .Mint32 rfl rfl (by omega)
  have hf := harr.fits
  have h4 : csize .Mint32 = 4 := rfl
  have hob : S.ob = intOfZ (Ptrofs.unsigned S.oofs) := rfl
  rw [h4] at hf ⊢
  omega

/-- `cosetindex = tv;` -/
theorem wp_setCoset {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {v : Nat}
    (h : SearchAt m S ctx st pre nsp) (hge : PTree.get dense.id.«nauty:cosetindex» e = none)
    (htv : PTree.get dense.id.«tv» le = some (.Vint (ir v))) (hv : v < n)
    (hQ : ∀ m', SearchAt m' S ctx { st with cosetindex := v } pre nsp →
      Unch m m' (· ∈ [Block.cosetindex]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar dense.id.«nauty:cosetindex» tint) (Refine.tv dense.id.«tv»)) Q e le m := by
  have hnl := h.nlt
  refine wp_gint hge find_cosetindex h.scalars.cosetindex.writable (x := (v : Int))
    (by simp only [Exec.evalExpr, Refine.tv, htv]) rfl ?_
  intro m' iC hu hg
  have hU : Unch m m' (· ∈ [Block.cosetindex]) := hu.mono fun z hz => by simp [hz]
  refine hQ m' ?_ hU hg
  have sc := h.scalars
  refine h.setScalars hU (fun z hz => by simp at hz; subst hz; decide)
    ⟨sc.gcaFirst.unch hU (by decide), sc.gcaCanon.unch hU (by decide),
      sc.noncheaplevel.unch hU (by decide), sc.allsamelevel.unch hU (by decide),
      sc.eqlevFirst.unch hU (by decide), sc.eqlevCanon.unch hU (by decide),
      sc.compCanon.unch hU (by decide), sc.samerows.unch hU (by decide),
      sc.canonlevel.unch hU (by decide), sc.stabvertex.unch hU (by decide), iC,
      sc.needshortprune.unch hU (by decide)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, -⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, by show v < _; omega⟩ }

/-- `gca_first = level;` -/
theorem wp_setGcaFirst {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level : Nat}
    (h : SearchAt m S ctx st pre nsp) (hge : PTree.get dense.id.«nauty:gca_first» e = none)
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level))) (hl : level ≤ n)
    (hQ : ∀ m', SearchAt m' S ctx { st with gcaFirst := level } pre nsp →
      Unch m m' (· ∈ [Block.gcaFirst]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar dense.id.«nauty:gca_first» tint) (Refine.tv dense.id.«level»)) Q e le m := by
  have hnl := h.nlt
  refine wp_gint hge find_gcaFirst h.scalars.gcaFirst.writable (x := (level : Int))
    (by simp only [Exec.evalExpr, Refine.tv, hlev]) rfl ?_
  intro m' iG hu hg
  have hU : Unch m m' (· ∈ [Block.gcaFirst]) := hu.mono fun z hz => by simp [hz]
  refine hQ m' ?_ hU hg
  have sc := h.scalars
  refine h.setScalars hU (fun z hz => by simp at hz; subst hz; decide)
    ⟨iG, sc.gcaCanon.unch hU (by decide),
      sc.noncheaplevel.unch hU (by decide), sc.allsamelevel.unch hU (by decide),
      sc.eqlevFirst.unch hU (by decide), sc.eqlevCanon.unch hU (by decide),
      sc.compCanon.unch hU (by decide), sc.samerows.unch hU (by decide),
      sc.canonlevel.unch hU (by decide), sc.stabvertex.unch hU (by decide),
      sc.cosetindex.unch hU (by decide), sc.needshortprune.unch hU (by decide)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨-, s2⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨by show level < _; omega, s2⟩ }

/-- `stabvertex = tv1;` -/
theorem wp_setStab {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {v : Nat}
    (h : SearchAt m S ctx st pre nsp) (hge : PTree.get dense.id.«nauty:stabvertex» e = none)
    (htv : PTree.get dense.id.«tv1» le = some (.Vint (ir v))) (hv : v < n)
    (hQ : ∀ m', SearchAt m' S ctx { st with stabvertex := v } pre nsp →
      Unch m m' (· ∈ [Block.stabvertex]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar dense.id.«nauty:stabvertex» tint) (Refine.tv dense.id.«tv1»)) Q e le m := by
  have hnl := h.nlt
  refine wp_gint hge find_stabvertex h.scalars.stabvertex.writable (x := (v : Int))
    (by simp only [Exec.evalExpr, Refine.tv, htv]) rfl ?_
  intro m' iS hu hg
  have hU : Unch m m' (· ∈ [Block.stabvertex]) := hu.mono fun z hz => by simp [hz]
  refine hQ m' ?_ hU hg
  have sc := h.scalars
  refine h.setScalars hU (fun z hz => by simp at hz; subst hz; decide)
    ⟨sc.gcaFirst.unch hU (by decide), sc.gcaCanon.unch hU (by decide),
      sc.noncheaplevel.unch hU (by decide), sc.allsamelevel.unch hU (by decide),
      sc.eqlevFirst.unch hU (by decide), sc.eqlevCanon.unch hU (by decide),
      sc.compCanon.unch hU (by decide), sc.samerows.unch hU (by decide),
      sc.canonlevel.unch hU (by decide), iS,
      sc.cosetindex.unch hU (by decide), sc.needshortprune.unch hU (by decide)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, -, s12⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, by show v < _; omega, s12⟩ }

/-- Before the first leaf, `maxlevel` is not tracked. -/
theorem SearchAt.preTrue {n : Nat} {m : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) : SearchAt m S ctx st true nsp :=
  { h with stats := { h.stats with maxlevel := fun e => absurd e (by decide) } }

theorem tcParent_own {n : Nat} {L : LCtx n} {m : mem} {ch : List (block × block)}
    (h : ChainAt L m ch) : tcParent ch (L.level + 1) = L.bnd := by
  have := h.lvl
  unfold tcParent
  rw [ite_eq_right (by omega), show L.level + 1 - 2 = L.level - 1 by omega, h.own]
  rfl

/-- The node's child result and the state after it: `afterChildFirst` on the first path. -/
abbrev childRes {n : Nat} (ctx : Ctx n) (level nc tc tv tv1 : Nat) (st : Search n) :
    Exit × Search n :=
  hexNode (tv == tv1) ctx (level + 1) (nc + 1) (child true level tc tv st)

abbrev childAfter {n : Nat} (ctx : Ctx n) (level nc tc tv tv1 : Nat) (st : Search n) : Search n :=
  if tv == tv1 then afterChildFirst level tv1 (childRes ctx level nc tc tv tv1 st).2
  else (childRes ctx level nc tc tv tv1 st).2

set_option maxHeartbeats 4000000 in
/-- `if (tv == tv1) { rtnlevel = firstpathnode0(…); childcount = 1; gca_first = level;
stabvertex = tv1; } else { rtnlevel = othernode0(…); ++childcount; }` -/
theorem wp_fpnCallIf {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {NodeOk : Bool → Nat → Nat → Search n → Prop} {Em : Bool → Nat → Nat → Search n → List Int}
    (L : LCtx n) {st : Search n} {pre : Bool} {cell : VSet n} {ch : List (block × block)}
    {tv tv1 : Nat}
    (h : LoopAt L m (child true L.level L.tc tv st) pre false cell ch)
    (hRecF : Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (firstpathnodeSpec xi NodeOk Em L.S L.ctx (child true L.level L.tc tv st) (L.level + 1)
        (L.nc + 1) ch))
    (hRecO : Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (othernodeSpec xi NodeOk Em L.S L.ctx (child true L.level L.tc tv st) (L.level + 1)
        (L.nc + 1) ch))
    (hNok : NodeOk (tv == tv1) (L.level + 1) (L.nc + 1) (child true L.level L.tc tv st))
    (hpre : tv ≠ tv1 → pre = false) (hcb : AutomCb xi L.S.bUA)
    (hln : L.level + 1 ≤ n) (hncl : L.nc + 1 ≤ n) (htv1n : tv1 < n) (htvn : tv < n)
    (hen : PTree.get dense.id.numcells e = some (L.bnc, tint))
    (hge : ∀ x ∈ [dense.id.«nauty:firstpathnode0», dense.id.«nauty:othernode0»,
      dense.id.«nauty:gca_first», dense.id.«nauty:stabvertex»], PTree.get x e = none)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr L.S.bl L.S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr L.S.bp L.S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir L.level)))
    (htv : PTree.get dense.id.«tv» le = some (.Vint (ir tv)))
    (htv1 : PTree.get dense.id.«tv1» le = some (.Vint (ir tv1)))
    (htcn : PTree.get dense.id.«tcnode_this» le = some (.Vptr L.bnd Ptrofs.zero))
    {cc : Lib.Integers.int} (hcc : PTree.get dense.id.«childcount» le = some (.Vint cc))
    (hQ : ∀ t le' m' ch', LoopAt L m' (childAfter L.ctx L.level L.nc L.tc tv tv1 st) false
        (exitValue (L.level + 1) (childRes L.ctx L.level L.nc L.tc tv tv1 st).1).2 cell ch' →
      Emits t (Em (tv == tv1) (L.level + 1) (L.nc + 1) (child true L.level L.tc tv st)) →
      PTree.get dense.id.«rtnlevel» le' =
        some (.Vint (ir (exitValue (L.level + 1) (childRes L.ctx L.level L.nc L.tc tv tv1 st).1).1)) →
      (∀ x, x ≠ dense.id.«rtnlevel» → x ≠ idOf 716 → x ≠ idOf 717 → x ≠ dense.id.«childcount» →
        PTree.get x le' = PTree.get x le) →
      (∃ c, PTree.get dense.id.«childcount» le' = some (.Vint c)) →
      (∀ tg sh, (childRes L.ctx L.level L.nc L.tc tv tv1 st).1 = .unwind tg sh → tg < L.level + 1) →
      Q.normal t e le' m') :
    Wp xi ge f (Set.sk callIf) Q e le m := by
  have hc := h.chain
  have hl1 := hc.lvl
  have hnl := h.search.nlt
  simp only [List.forall_mem_cons] at hge
  obtain ⟨g1, g2, g3, g4, -⟩ := hge
  have hncv : Mem.load .Mint32 m L.bnc (zOfInt 0) = some (.Vint (ir L.nc)) := h.nc.load 0 (by decide)
  have htcn' : PTree.get dense.id.«tcnode_this» le =
      some (.Vptr (tcParent ch (L.level + 1)) Ptrofs.zero) := by rw [tcParent_own hc]; exact htcn
  wp_step; wp_step
  simp only [callIf]
  apply wp_if_eval
  rw [Processnode.eval_eqI (x := (tv : Int)) (y := (tv1 : Int)) (by simp [Exec.evalExpr, Refine.tv, htv])
    (by simp [Exec.evalExpr, Refine.tv, htv1]) rfl rfl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases heq : tv = tv1
  · subst heq
    rw [decide_eq_true (rfl : (tv : Int) = tv)]
    simp only [show Cfrontend.Cop.bool_val (Val.of_bool true) tint m = some true from rfl, ite_true]
    have hb : (tv == tv) = true := beq_self_eq_true tv
    rw [hb] at hNok
    simp only [childAfter, childRes, hb, ite_true] at hQ
    wp_step
    refine wp_fpnCall hRecF h.search.preTrue hc.chain hc.ok hc.len hcb hln hncl hNok h.vU h.pU
      hen hncv g1 hlab hptn hlev htcn' ?_
    intro t m₁ hS₁ hE₁ hC₁ hF₁ hW₁ hT₁
    obtain ⟨ch', c1, c2, c3, c4, c5⟩ := hC₁
    have h₁ := h.call hS₁ c1 c2 c3 c4 c5 hF₁ hW₁ (hF₁.2 _ h.vU) (NodeFrame.perm_bUA h.search hc.ok hF₁ h.vU h.pU) hl1
    simp only [seqPost, Post.after, firstAfter]
    have hd := h.search.distinct
    have scal : ∀ b ∈ [Block.gcaFirst, Block.stabvertex], L.S.Chg b := by
      intro b hb
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl
      · exact ⟨by simp [SLoc.blocks], by sep_ne hd, by decide⟩
      · exact ⟨by simp [SLoc.blocks], by sep_ne hd, by decide⟩
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr]
    wp_step; wp_step; wp_step
    refine wp_setGcaFirst (level := L.level) h₁.search g3
      (by simp (config := {decide := true}) only [temps_gso, temps_gss, hlev]) (by omega) ?_
    intro m₂ hS₂ hu₂ hg₂
    have h₂ := h₁.small hS₂ hu₂ hg₂ (fun z hz => scal z (by simp at hz; simp [hz]))
      (fun z hz hz' => by simp at hz'; subst hz'; revert hz; decide)
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    refine wp_setStab (v := tv) hS₂ g4
      (by simp (config := {decide := true}) only [temps_gso, temps_gss, htv1]) htv1n ?_
    intro m₃ hS₃ hu₃ hg₃
    have h₃ := h₂.small hS₃ hu₃ hg₃ (fun z hz => scal z (by simp at hz; simp [hz]))
      (fun z hz hz' => by simp at hz'; subst hz'; revert hz; decide)
    simp only [append_E0]
    refine hQ t _ m₃ ch' h₃ hE₁
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (fun x h1 h2 h3 h4 => by simp only [temps_gso _ _ h4, temps_gso _ _ h1, temps_gso _ _ h2])
      ⟨_, temps_gss _ _ _⟩ hT₁
  · have hb : (tv == tv1) = false := by simpa using heq
    rw [decide_eq_false (by omega)]
    simp only [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m = some false from rfl,
      Bool.false_eq_true, ite_false]
    rw [hb] at hNok
    simp only [childAfter, childRes, hb, Bool.false_eq_true, ite_false] at hQ
    have hp := hpre heq
    subst hp
    wp_step
    refine wp_nodeChild hRecO h.search hc.chain hc.ok hc.len hcb hln hncl hNok h.vU h.pU
      hen hncv g2 hlab hptn hlev htcn' ?_
    intro t m₁ hS₁ hE₁ hC₁ hF₁ hW₁ hT₁
    obtain ⟨ch', c1, c2, c3, c4, c5⟩ := hC₁
    have h₁ := h.call hS₁ c1 c2 c3 c4 c5 hF₁ hW₁ (hF₁.2 _ h.vU) (NodeFrame.perm_bUA h.search hc.ok hF₁ h.vU h.pU) hl1
    simp only [seqPost, Post.after]
    wp_step; wp_step
    apply wp_set_eval
    simp (config := {decide := true}) only [Exec.evalExpr, Refine.tv, temps_gso, hcc]
    simp only [typeof, cop, append_E0]
    refine hQ t _ m₁ ch' h₁ (by simpa using hE₁)
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (fun x h1 h2 h3 h4 => by simp only [temps_gso _ _ h4, temps_gso _ _ h1, temps_gso _ _ h3])
      ⟨_, temps_gss _ _ _⟩ hT₁

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

/-- `wp_fpnCall` for `D` and the policy `P`. -/
theorem wp_fpnCallG {n : Nat} [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]
    {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {NodeOk : Bool → Nat → Nat → SearchState n (O.Canon n) → Prop}
    {Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {level nc : Nat} {chain : List (block × block)}
    (hRec : Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (nodeSpecG D xi NodeOk Em true S gl cl G st (level + 1) (nc + 1) chain))
    (h : SearchAtG D m S gl cl G st true false) (hTc : TcChain m S.M E.tcnode0 chain)
    (hTo : TcOkG D m S gl cl chain) (hlen : level ≤ chain.length) (hcb : AutomCb xi S.bUA)
    (hln : level + 1 ≤ n) (hncl : nc + 1 ≤ n) (hok : NodeOk true (level + 1) (nc + 1) st)
    (hvU : Mem.valid_block m S.bUA) (hpU : Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty)
    {bnc : block} (hen : PTree.get dense.id.numcells e = some (bnc, tint))
    (hncv : Mem.load .Mint32 m bnc (zOfInt 0) = some (.Vint (ir nc)))
    (hge : PTree.get dense.id.«nauty:firstpathnode0» e = none)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (htcn : PTree.get dense.id.«tcnode_this» le =
      some (.Vptr (tcParent chain (level + 1)) Ptrofs.zero))
    (hQ : ∀ t m',
      SearchAtG D m' S gl cl G (hexNodeG true G (level + 1) (nc + 1) st).2 false
        (exitValue (level + 1) (hexNodeG true G (level + 1) (nc + 1) st).1).2 →
      Emits t (Em true (level + 1) (nc + 1) st) →
      (∃ chain', TcChain m' S.M E.tcnode0 chain' ∧ TcOkG D m' S gl cl chain' ∧
        level + 1 ≤ chain'.length ∧ chain'.take level = chain.take level ∧
        ∀ p ∈ chain', p ∈ chain ∨ (¬ Mem.valid_block m p.1 ∧ ¬ Mem.valid_block m p.2)) →
      NodeFrameG D m m' S gl cl chain (level + 1) →
      (∀ z, IsWorkG D m' z → IsWorkG D m z ∨ ¬ Mem.valid_block m z) →
      (∀ tg sh, (hexNodeG true G (level + 1) (nc + 1) st).1 = .unwind tg sh → tg < level + 1) →
      Q.normal t e (PTree.set dense.id.«rtnlevel»
        (.Vint (ir (exitValue (level + 1) (hexNodeG true G (level + 1) (nc + 1) st).1).1))
        (PTree.set (idOf 716)
          (.Vint (ir (exitValue (level + 1) (hexNodeG true G (level + 1) (nc + 1) st).1).1)) le))
        m') :
    Wp xi ge f fpnCall Q e le m := by
  have hnl := h.nlt
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr E.firstpathnodeFn Ptrofs.zero)
    (targs := [tptr tint, tptr tint, tint, tint, tptr tcStruct]) (tres := tint)
    (cc := Common.AST.cc_default)
    (vargs := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir ((level + 1 : Nat) : Int)),
      .Vint (ir ((nc + 1 : Nat) : Int)), .Vptr (tcParent chain (level + 1)) Ptrofs.zero])
    (.Internal dense.fn.«nauty:firstpathnode0») _ hRec rfl ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, E.funct_firstpathnodeFn]) rfl
    ⟨rfl, h, hTc, hTo, by omega, hcb, by omega, hln, hncl, hok, hvU, hpU⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, hge, E.find_firstpathnodeFn, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode]
  · simp only [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, hen, hlab, hptn, hlev, htcn,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hncv, ite_true, Refine.tv, typeof, cop,
      ir_add]
    push_cast
    rfl
  · rintro t v m' ⟨hv, hS', hE, hC, hF, hW, hT⟩
    subst hv
    simp only [set_opttemp]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, Refine.tv, append_E0]
    refine hQ t m' hS' hE ?_ hF hW hT
    obtain ⟨c', h1, h2, h3, h4, h5⟩ := hC
    exact ⟨c', h1, h2, h3, by simpa using h4, h5⟩

/-- `LoopAt.small` for `D`: a step changing only blocks of `S` other than
`userautomproc`'s, `tcnode0`, `D`'s written globals and nautil.c's `workperm`
pair keeps `LoopAtG`. -/
theorem LoopAtG.small {n : Nat} {L : LCtxG D n} {m : mem} {st : SearchState n (O.Canon n)}
    {pre nsp : Bool} {cell : VSet n} {ch : List (block × block)}
    (h : LoopAtG L m st pre nsp cell ch)
    {m' : mem} {st' : SearchState n (O.Canon n)} {pre' nsp' : Bool} {W : block → Prop}
    (hS : SearchAtG D m' L.S L.gl L.cl L.G st' pre' nsp') (hu : Unch m m' W)
    (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hWS : ∀ z, W z → L.S.ChgG D L.gl L.cl z)
    (hWg : ∀ z ∈ D.wglobs, ¬ W z) (hWn : ¬ W E.nautilWorkperm ∧ ¬ W E.nautilWorkpermSz) :
    LoopAtG L m' st' pre' nsp' cell ch := by
  obtain ⟨tw, hta, htr⟩ := h.cell
  have hmem := List.mem_of_getElem? h.chain.own
  have hbt : ¬ W L.btc := fun hw => (h.chain.ok.apart _ hmem).2.1 (hWS _ hw).1
  have hwk : ∀ z, IsWorkG D m z → ¬ W z := fun z hz hw => h.search.work_not hz (hWS z hw).1
  exact h.step hS (hu.mono fun z hz => .inl (hWS z hz)) hg
    (fun z hz => .inl ((h.search.work.unch hu hWg hWn hwk hg).2 z hz)) ⟨tw, hta.unch hu hbt, htr⟩
    (Alloc.Keep.unch hu hbt)

/-- `orbits[x]` for `x` holding `c < n`, for `D`. -/
theorem eval_orbAtG {n : Nat} {e : env} {le : temp_env} {m : mem} {S : SLoc} {gl : D.GLoc}
    {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (hge : PTree.get dense.id.«nauty:orbits» e = none) {x : ident} {c : Nat}
    (hx : PTree.get x le = some (.Vint (ir c))) (hc : c < n) :
    Exec.evalExpr ge e le m (orbAt x) = some (.Vint (ir (st.orbits[c]! : Int))) := by
  have hnl := h.nlt
  have harr := h.arrays.orbits
  simp only [orbAt, Exec.evalExpr, Exec.lvalOfVar, hge, E.find_orbits, Exec.derefLoc,
    Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h.fixed.orbits.load, Refine.tv, hx,
    typeof, cop]
  apply load_array harr hc
  apply addr_elem S.oofs _ .Mint32 rfl rfl (by omega)
  have hf := harr.fits
  have h4 : csize .Mint32 = 4 := rfl
  have hob : S.ob = intOfZ (Ptrofs.unsigned S.oofs) := rfl
  rw [h4] at hf ⊢
  omega

/-- `cosetindex = tv;`, for `D`. -/
theorem wp_setCosetG {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {pre nsp : Bool} {v : Nat}
    (h : SearchAtG D m S gl cl G st pre nsp) (hge : PTree.get dense.id.«nauty:cosetindex» e = none)
    (htv : PTree.get dense.id.«tv» le = some (.Vint (ir v))) (hv : v < n)
    (hQ : ∀ m', SearchAtG D m' S gl cl G { st with cosetindex := v } pre nsp →
      Unch m m' (· ∈ [E.cosetindex]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar dense.id.«nauty:cosetindex» tint) (Refine.tv dense.id.«tv»)) Q e le m := by
  have hnl := h.nlt
  refine wp_gint hge E.find_cosetindex h.scalars.cosetindex.writable (x := (v : Int))
    (by simp only [Exec.evalExpr, Refine.tv, htv]) rfl ?_
  intro m' iC hu hg
  have hU : Unch m m' (· ∈ [E.cosetindex]) := hu.mono fun z hz => by simp [hz]
  refine hQ m' ?_ hU hg
  have sc := h.scalars
  refine h.setScalars hU (fun z hz => by simp at hz; subst hz; simp) hg
    ⟨sc.gcaFirst.unch hU (by sep_notin h.lit), sc.gcaCanon.unch hU (by sep_notin h.lit),
      sc.noncheaplevel.unch hU (by sep_notin h.lit), sc.allsamelevel.unch hU (by sep_notin h.lit),
      sc.eqlevFirst.unch hU (by sep_notin h.lit), sc.eqlevCanon.unch hU (by sep_notin h.lit),
      sc.compCanon.unch hU (by sep_notin h.lit), sc.samerows.unch hU (by sep_notin h.lit),
      sc.canonlevel.unch hU (by sep_notin h.lit), sc.stabvertex.unch hU (by sep_notin h.lit), iC,
      sc.needshortprune.unch hU (by sep_notin h.lit)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, -⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, by show v < _; omega⟩ }

/-- `gca_first = level;`, for `D`. -/
theorem wp_setGcaFirstG {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {pre nsp : Bool} {level : Nat}
    (h : SearchAtG D m S gl cl G st pre nsp) (hge : PTree.get dense.id.«nauty:gca_first» e = none)
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level))) (hl : level ≤ n)
    (hQ : ∀ m', SearchAtG D m' S gl cl G { st with gcaFirst := level } pre nsp →
      Unch m m' (· ∈ [E.gcaFirst]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar dense.id.«nauty:gca_first» tint) (Refine.tv dense.id.«level»)) Q e le m := by
  have hnl := h.nlt
  refine wp_gint hge E.find_gcaFirst h.scalars.gcaFirst.writable (x := (level : Int))
    (by simp only [Exec.evalExpr, Refine.tv, hlev]) rfl ?_
  intro m' iG hu hg
  have hU : Unch m m' (· ∈ [E.gcaFirst]) := hu.mono fun z hz => by simp [hz]
  refine hQ m' ?_ hU hg
  have sc := h.scalars
  refine h.setScalars hU (fun z hz => by simp at hz; subst hz; simp) hg
    ⟨iG, sc.gcaCanon.unch hU (by sep_notin h.lit),
      sc.noncheaplevel.unch hU (by sep_notin h.lit), sc.allsamelevel.unch hU (by sep_notin h.lit),
      sc.eqlevFirst.unch hU (by sep_notin h.lit), sc.eqlevCanon.unch hU (by sep_notin h.lit),
      sc.compCanon.unch hU (by sep_notin h.lit), sc.samerows.unch hU (by sep_notin h.lit),
      sc.canonlevel.unch hU (by sep_notin h.lit), sc.stabvertex.unch hU (by sep_notin h.lit),
      sc.cosetindex.unch hU (by sep_notin h.lit), sc.needshortprune.unch hU (by sep_notin h.lit)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨-, s2⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨by show level < _; omega, s2⟩ }

/-- `stabvertex = tv1;`, for `D`. -/
theorem wp_setStabG {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {pre nsp : Bool} {v : Nat}
    (h : SearchAtG D m S gl cl G st pre nsp) (hge : PTree.get dense.id.«nauty:stabvertex» e = none)
    (htv : PTree.get dense.id.«tv1» le = some (.Vint (ir v))) (hv : v < n)
    (hQ : ∀ m', SearchAtG D m' S gl cl G { st with stabvertex := v } pre nsp →
      Unch m m' (· ∈ [E.stabvertex]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar dense.id.«nauty:stabvertex» tint) (Refine.tv dense.id.«tv1»)) Q e le m := by
  have hnl := h.nlt
  refine wp_gint hge E.find_stabvertex h.scalars.stabvertex.writable (x := (v : Int))
    (by simp only [Exec.evalExpr, Refine.tv, htv]) rfl ?_
  intro m' iS hu hg
  have hU : Unch m m' (· ∈ [E.stabvertex]) := hu.mono fun z hz => by simp [hz]
  refine hQ m' ?_ hU hg
  have sc := h.scalars
  refine h.setScalars hU (fun z hz => by simp at hz; subst hz; simp) hg
    ⟨sc.gcaFirst.unch hU (by sep_notin h.lit), sc.gcaCanon.unch hU (by sep_notin h.lit),
      sc.noncheaplevel.unch hU (by sep_notin h.lit), sc.allsamelevel.unch hU (by sep_notin h.lit),
      sc.eqlevFirst.unch hU (by sep_notin h.lit), sc.eqlevCanon.unch hU (by sep_notin h.lit),
      sc.compCanon.unch hU (by sep_notin h.lit), sc.samerows.unch hU (by sep_notin h.lit),
      sc.canonlevel.unch hU (by sep_notin h.lit), iS,
      sc.cosetindex.unch hU (by sep_notin h.lit), sc.needshortprune.unch hU (by sep_notin h.lit)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, -, s12⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, by show v < _; omega, s12⟩ }

/-- Before the first leaf, `maxlevel` is not tracked. -/
theorem SearchAtG.preTrue {n : Nat} {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) : SearchAtG D m S gl cl G st true nsp :=
  { h with stats := { h.stats with maxlevel := fun e => absurd e (by decide) } }

theorem tcParent_ownG {n : Nat} {L : LCtxG D n} {m : mem} {ch : List (block × block)}
    (h : ChainAtG L m ch) : tcParent ch (L.level + 1) = L.bnd := by
  have := h.lvl
  unfold tcParent
  rw [ite_eq_right (by omega), show L.level + 1 - 2 = L.level - 1 by omega, h.own]
  rfl

/-- `childRes` for the policy `P`. -/
abbrev childResG {n : Nat} [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]
    (G : O.Gr n) (level nc tc tv tv1 : Nat) (st : SearchState n (O.Canon n)) :
    Exit × SearchState n (O.Canon n) :=
  hexNodeG (tv == tv1) G (level + 1) (nc + 1) (P.child true level tc tv st)

/-- `childAfter` for the policy `P`. -/
abbrev childAfterG {n : Nat} [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]
    (G : O.Gr n) (level nc tc tv tv1 : Nat) (st : SearchState n (O.Canon n)) :
    SearchState n (O.Canon n) :=
  if tv == tv1 then P.afterChildFirst level tv1 (childResG G level nc tc tv tv1 st).2
  else (childResG G level nc tc tv tv1 st).2

set_option maxHeartbeats 4000000 in
/-- `wp_fpnCallIf` for `D` and the policy `P`, linked to `O` by `Lk`. -/
theorem wp_fpnCallIfG {n : Nat} [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]
    (Lk : PolicyLink O n) {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {NodeOk : Bool → Nat → Nat → SearchState n (O.Canon n) → Prop}
    {Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int}
    (L : LCtxG D n) {st : SearchState n (O.Canon n)} {pre : Bool} {cell : VSet n}
    {ch : List (block × block)} {tv tv1 : Nat}
    (h : LoopAtG L m (P.child true L.level L.tc tv st) pre false cell ch)
    (hRecF : Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (nodeSpecG D xi NodeOk Em true L.S L.gl L.cl L.G (P.child true L.level L.tc tv st)
        (L.level + 1) (L.nc + 1) ch))
    (hRecO : Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (nodeSpecG D xi NodeOk Em false L.S L.gl L.cl L.G (P.child true L.level L.tc tv st)
        (L.level + 1) (L.nc + 1) ch))
    (hNok : NodeOk (tv == tv1) (L.level + 1) (L.nc + 1) (P.child true L.level L.tc tv st))
    (hpre : tv ≠ tv1 → pre = false) (hcb : AutomCb xi L.S.bUA)
    (hln : L.level + 1 ≤ n) (hncl : L.nc + 1 ≤ n) (htv1n : tv1 < n) (htvn : tv < n)
    (hen : PTree.get dense.id.numcells e = some (L.bnc, tint))
    (hge : ∀ x ∈ [dense.id.«nauty:firstpathnode0», dense.id.«nauty:othernode0»,
      dense.id.«nauty:gca_first», dense.id.«nauty:stabvertex»], PTree.get x e = none)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr L.S.bl L.S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr L.S.bp L.S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir L.level)))
    (htv : PTree.get dense.id.«tv» le = some (.Vint (ir tv)))
    (htv1 : PTree.get dense.id.«tv1» le = some (.Vint (ir tv1)))
    (htcn : PTree.get dense.id.«tcnode_this» le = some (.Vptr L.bnd Ptrofs.zero))
    {cc : Lib.Integers.int} (hcc : PTree.get dense.id.«childcount» le = some (.Vint cc))
    (hQ : ∀ t le' m' ch', LoopAtG L m' (childAfterG L.G L.level L.nc L.tc tv tv1 st) false
        (exitValue (L.level + 1) (childResG L.G L.level L.nc L.tc tv tv1 st).1).2 cell ch' →
      Emits t (Em (tv == tv1) (L.level + 1) (L.nc + 1) (P.child true L.level L.tc tv st)) →
      PTree.get dense.id.«rtnlevel» le' =
        some (.Vint (ir (exitValue (L.level + 1) (childResG L.G L.level L.nc L.tc tv tv1 st).1).1)) →
      (∀ x, x ≠ dense.id.«rtnlevel» → x ≠ idOf 716 → x ≠ idOf 717 → x ≠ dense.id.«childcount» →
        PTree.get x le' = PTree.get x le) →
      (∃ c, PTree.get dense.id.«childcount» le' = some (.Vint c)) →
      (∀ tg sh, (childResG L.G L.level L.nc L.tc tv tv1 st).1 = .unwind tg sh → tg < L.level + 1) →
      Q.normal t e le' m') :
    Wp xi ge f (Set.sk callIf) Q e le m := by
  have hc := h.chain
  have hl1 := hc.lvl
  have hnl := h.search.nlt
  simp only [List.forall_mem_cons] at hge
  obtain ⟨g1, g2, g3, g4, -⟩ := hge
  have hncv : Mem.load .Mint32 m L.bnc (zOfInt 0) = some (.Vint (ir L.nc)) := h.nc.load 0 (by decide)
  have htcn' : PTree.get dense.id.«tcnode_this» le =
      some (.Vptr (tcParent ch (L.level + 1)) Ptrofs.zero) := by rw [tcParent_ownG hc]; exact htcn
  wp_step; wp_step
  simp only [callIf]
  apply wp_if_eval
  rw [Processnode.eval_eqI (x := (tv : Int)) (y := (tv1 : Int)) (by simp [Exec.evalExpr, Refine.tv, htv])
    (by simp [Exec.evalExpr, Refine.tv, htv1]) rfl rfl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases heq : tv = tv1
  · subst heq
    rw [decide_eq_true (rfl : (tv : Int) = tv)]
    simp only [show Cfrontend.Cop.bool_val (Val.of_bool true) tint m = some true from rfl, ite_true]
    have hb : (tv == tv) = true := beq_self_eq_true tv
    rw [hb] at hNok
    simp only [childAfterG, childResG, hb, ite_true, Lk.afterChildFirst_eq] at hQ
    wp_step
    refine wp_fpnCallG hRecF h.search.preTrue hc.chain hc.ok hc.len hcb hln hncl hNok h.vU h.pU
      hen hncv g1 hlab hptn hlev htcn' ?_
    intro t m₁ hS₁ hE₁ hC₁ hF₁ hW₁ hT₁
    obtain ⟨ch', c1, c2, c3, c4, c5⟩ := hC₁
    have h₁ := h.call hS₁ c1 c2 c3 c4 c5 hF₁ hW₁ (hF₁.2 _ h.vU)
      (NodeFrameG.perm_bUA h.search hc.ok hF₁ h.vU h.pU) hl1
    simp only [seqPost, Post.after, firstAfter]
    have hd := h.search.lit
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr]
    wp_step; wp_step; wp_step
    refine wp_setGcaFirstG (level := L.level) h₁.search g3
      (by simp (config := {decide := true}) only [temps_gso, temps_gss, hlev]) (by omega) ?_
    intro m₂ hS₂ hu₂ hg₂
    have h₂ := h₁.small hS₂ hu₂ hg₂
      (fun z hz => by
        simp at hz; subst hz
        exact ⟨SLoc.mem_litG (by simp [SLoc.litG]), by sep_ne hd, by sep_ne hd⟩)
      (fun z hz e => by
        simp at e; subst e
        exact h₁.search.lit_globs _ (by simp [SLoc.litG]) (D.wglobs_sub _ hz))
      ⟨by simp only [List.mem_cons, List.mem_nil_iff, or_false]; sep_ne hd,
        by simp only [List.mem_cons, List.mem_nil_iff, or_false]; sep_ne hd⟩
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    refine wp_setStabG (v := tv) hS₂ g4
      (by simp (config := {decide := true}) only [temps_gso, temps_gss, htv1]) htv1n ?_
    intro m₃ hS₃ hu₃ hg₃
    have h₃ := h₂.small hS₃ hu₃ hg₃
      (fun z hz => by
        simp at hz; subst hz
        exact ⟨SLoc.mem_litG (by simp [SLoc.litG]), by sep_ne hd, by sep_ne hd⟩)
      (fun z hz e => by
        simp at e; subst e
        exact h₁.search.lit_globs _ (by simp [SLoc.litG]) (D.wglobs_sub _ hz))
      ⟨by simp only [List.mem_cons, List.mem_nil_iff, or_false]; sep_ne hd,
        by simp only [List.mem_cons, List.mem_nil_iff, or_false]; sep_ne hd⟩
    simp only [append_E0]
    refine hQ t _ m₃ ch' h₃ hE₁
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (fun x h1 h2 h3 h4 => by simp only [temps_gso _ _ h4, temps_gso _ _ h1, temps_gso _ _ h2])
      ⟨_, temps_gss _ _ _⟩ hT₁
  · have hb : (tv == tv1) = false := by simpa using heq
    rw [decide_eq_false (by omega)]
    simp only [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m = some false from rfl,
      Bool.false_eq_true, ite_false]
    rw [hb] at hNok
    simp only [childAfterG, childResG, hb, Bool.false_eq_true, ite_false] at hQ
    have hp := hpre heq
    subst hp
    wp_step
    refine wp_nodeChildG hRecO h.search hc.chain hc.ok hc.len hcb hln hncl hNok h.vU h.pU
      hen hncv g2 hlab hptn hlev htcn' ?_
    intro t m₁ hS₁ hE₁ hC₁ hF₁ hW₁ hT₁
    obtain ⟨ch', c1, c2, c3, c4, c5⟩ := hC₁
    have h₁ := h.call hS₁ c1 c2 c3 c4 c5 hF₁ hW₁ (hF₁.2 _ h.vU)
      (NodeFrameG.perm_bUA h.search hc.ok hF₁ h.vU h.pU) hl1
    simp only [seqPost, Post.after]
    wp_step; wp_step
    apply wp_set_eval
    simp (config := {decide := true}) only [Exec.evalExpr, Refine.tv, temps_gso, hcc]
    simp only [typeof, cop, append_E0]
    refine hQ t _ m₁ ch' h₁ (by simpa using hE₁)
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (fun x h1 h2 h3 h4 => by simp only [temps_gso _ _ h4, temps_gso _ _ h1, temps_gso _ _ h3])
      ⟨_, temps_gss _ _ _⟩ hT₁

end Generic

end NautyVerified.Proofs.Search
