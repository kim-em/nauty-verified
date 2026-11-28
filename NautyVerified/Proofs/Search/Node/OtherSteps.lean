import NautyVerified.Proofs.Search.Node.Steps
import NautyVerified.Proofs.Search.Node.Compare
import NautyVerified.Proofs.Search.Node.Fields
import NautyVerified.Proofs.Cheapautom.Satisfies
import NautyVerified.Proofs.Search.Valid

/-!
# More straight-line steps of `othernode0`

- `wp_tctotal`: `stats->tctotal += tcellsize` (`chooseTarget` adds the target
  cell's size);
- `wp_hint`: `t710 = !getcanon || comp_canon < 0` (the target is hinted);
- `wp_tcReset`: after a hinted target, `if (tc != firsttc[level])
  eqlev_first = level - 1`;
- `wp_cheap`: `cheapautom`, then `noncheaplevel = level + 1` unless it succeeded.

Each has a form over `SearchAtG D` (`…G`); the dense `wp_cheap` keeps its own
proof, since the dispatch call's frame is weaker than the dense one.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

theorem lr_add_small (a s : Nat) (hs : s < 2147483648) :
    Lib.Integers.Int64.add (lr a) (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir s))) =
      lr ((a + s : Nat) : Int) := by
  apply bv64_inj.1
  rw [bv64_add, bv64_repr, bv64_repr, bv64_repr, intOfZ_zOfInt, intOfZ_zOfInt,
    show intOfZ (Lib.Integers.Int.signed (ir s)) = ((s : Nat) : Int) from Refine.signed_ir hs,
    ← BitVec.ofInt_add]
  push_cast; rfl

/-- An `int` local holds `v`. -/
theorem eval_local {ge : genv} {e : env} {le : temp_env} {m : mem} {x : ident} {b : block} {v : Int}
    (hx : PTree.get x e = some (b, tint)) (hv : Mem.load .Mint32 m b (zOfInt 0) = some (.Vint (ir v))) :
    Exec.evalExpr ge e le m (.Evar x tint) = some (.Vint (ir v)) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hx, Exec.derefLoc, Cfrontend.Ctypes.access_mode,
    Mem.loadv, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hv]
  simp [hv, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

theorem SearchAtG.setEqlevFirst {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) (hu : Unch m m' (· ∈ [E.eqlevFirst]))
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    {v : Nat} (iEF : IntAt m' E.eqlevFirst v) (hv2 : v < 2147483648) :
    SearchAtG D m' S gl cl G { st with eqlevFirst := v } pre nsp := by
  have sc := h.scalars
  refine h.setScalars hu (fun z hz => by simp at hz; subst hz; simp) hv
    ⟨sc.gcaFirst.unch hu (by sep_notin h.lit), sc.gcaCanon.unch hu (by sep_notin h.lit),
      sc.noncheaplevel.unch hu (by sep_notin h.lit), sc.allsamelevel.unch hu (by sep_notin h.lit),
      iEF, sc.eqlevCanon.unch hu (by sep_notin h.lit), sc.compCanon.unch hu (by sep_notin h.lit),
      sc.samerows.unch hu (by sep_notin h.lit), sc.canonlevel.unch hu (by sep_notin h.lit),
      sc.stabvertex.unch hu (by sep_notin h.lit), sc.cosetindex.unch hu (by sep_notin h.lit),
      sc.needshortprune.unch hu (by sep_notin h.lit)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, s3, s4, -, s6⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, s3, s4, hv2, s6⟩ }

theorem SearchAtG.setNoncheap {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) (hu : Unch m m' (· ∈ [E.noncheaplevel]))
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    {v : Nat} (iNC : IntAt m' E.noncheaplevel v) (hv2 : v < 2147483648) :
    SearchAtG D m' S gl cl G { st with noncheaplevel := v } pre nsp := by
  have sc := h.scalars
  refine h.setScalars hu (fun z hz => by simp at hz; subst hz; simp) hv
    ⟨sc.gcaFirst.unch hu (by sep_notin h.lit), sc.gcaCanon.unch hu (by sep_notin h.lit),
      iNC, sc.allsamelevel.unch hu (by sep_notin h.lit),
      sc.eqlevFirst.unch hu (by sep_notin h.lit), sc.eqlevCanon.unch hu (by sep_notin h.lit),
      sc.compCanon.unch hu (by sep_notin h.lit),
      sc.samerows.unch hu (by sep_notin h.lit), sc.canonlevel.unch hu (by sep_notin h.lit),
      sc.stabvertex.unch hu (by sep_notin h.lit), sc.cosetindex.unch hu (by sep_notin h.lit),
      sc.needshortprune.unch hu (by sep_notin h.lit)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, -, s4⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, hv2, s4⟩ }

/-- `stats->tctotal += tcellsize`, for `D`. -/
theorem wp_tctotalG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {pre nsp : Bool} (h : SearchAtG D m S gl cl G st pre nsp)
    (hge : PTree.get dense.id.«nauty:stats» e = none) {bsz : block} {sz : Nat}
    (hsz : PTree.get dense.id.tcellsize e = some (bsz, tint))
    (hszv : Mem.load .Mint32 m bsz (zOfInt 0) = some (.Vint (ir sz))) (hsz2 : sz < 2147483648)
    (hQ : ∀ m', SearchAtG D m' S gl cl G { st with tctotal := st.tctotal + sz } pre nsp →
      Unch m m' (· = S.bst) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (statsF dense.id.tctotal tulong)
      (.Ebinop .Oadd (statsF dense.id.tctotal tulong) (.Evar dense.id.tcellsize tint) tulong))
      Q e le m := by
  have hfit := h.stats.fits
  refine wp_statsStore (off := 48) (chunk := .Mint64) hge fld_tctotal rfl h.fixed.stats
    (by decide) (by omega) h.stats.tctotal.writable
    (w := .Vlong (lr ((st.tctotal + sz : Nat) : Int)))
    (w' := .Vlong (lr ((st.tctotal + sz : Nat) : Int))) ?_ rfl ?_
  · have hv := eval_statsF (le := le) (ty := tulong) hge fld_tctotal rfl h.fixed.stats
      (by decide) (by omega) h.stats.tctotal
    rw [Exec.evalExpr, hv, eval_local hsz hszv]
    simp only [Exec.evalExpr, typeof, cop, lr_add_small _ _ hsz2]
  intro m' hst
  have hu : Unch m m' (· = S.bst) := Unch.store hst rfl
  have hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z :=
    fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz
  refine hQ m' ?_ hu hv
  have hd := h.lit
  have hs := h.stats
  refine h.rebuild (L := [S.bst]) (hu.mono fun z hz => by simp [hz]) (by simp)
    (fun z hz => Keep.unch hu (by revert z hz; sep_all hd)) hv
    { h.scalars.unch hu (by sep_all hd) with }
    { (hs.fix.store hst (by first | omega | (simp only [csize32, csize64]; omega))) with
      numorbits := hs.numorbits.store_other hst (by simp only [csize32, csize64]; omega)
      numgenerators := hs.numgenerators.store_other hst (by simp only [csize32, csize64]; omega)
      numnodes := hs.numnodes.store_other hst (by simp only [csize32, csize64]; omega)
      numbadleaves := hs.numbadleaves.store_other hst (by simp only [csize32, csize64]; omega)
      maxlevel := fun hp => (hs.maxlevel hp).store_other hst (by simp only [csize32, csize64]; omega)
      maxlevelW := Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ hs.maxlevelW
      tctotal := FieldAt.store_same hst hs.tctotal.writable
      canupdates := hs.canupdates.store_other hst (by simp only [csize32, csize64]; omega)
      fits := hs.fits }
    { h.arrays.unch hu (by sep_all hd) (fun z hz e => h.graph_ne hz (.inl (by simp)) e)
      (fun z hz e => h.canon_ne hz (.inr (.inl (by simp))) e) with }
    { h.inv with }

/-- `t710 = !getcanon ? 1 : comp_canon < 0`, for `D`. -/
theorem wp_hintG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (hE0 : PTree.get dense.id.«nauty:getcanon» e = none)
    (hE1 : PTree.get dense.id.«nauty:comp_canon» e = none)
    (hQ : ∀ le', PTree.get (idOf 710) le' = some (Val.of_bool (decide (st.compCanon < 0))) →
      (∀ x, x ≠ idOf 710 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m) :
    Wp xi ge f (.Sifthenelse (.Eunop .Onotbool (.Evar dense.id.«nauty:getcanon» tint) tint)
      (.Sset (idOf 710) (ci 1 tint))
      (sk (.Sset (idOf 710) (.Ecast (.Ebinop .Olt (.Evar dense.id.«nauty:comp_canon» tint)
        (ci 0 tint) tint) tbool)))) Q e le m := by
  obtain ⟨-, -, -, -, -, -, -, hc1, hc2, -⟩ := h.inv.scalars
  have hcast : ∀ b : Bool, Cfrontend.Cop.sem_cast (Val.of_bool b) tint tbool m =
      some (Val.of_bool b) := fun b => by cases b <;> rfl
  apply wp_if_eval
  rw [Exec.evalExpr, eval_gint hE0 E.find_getcanon h.fixed.getcanon]
  simp only [typeof, cop]
  rw [ite_eq_right (by decide)]
  wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, Exec.evalExpr, eval_gint hE1 E.find_compCanon h.scalars.compCanon]
  simp only [Exec.evalExpr, typeof, cop]
  rw [ir_lt (a := st.compCanon) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩, hcast]
  exact hQ _ (temps_gss _ _ _) fun x hx => temps_gso _ _ hx

/-- After a hinted target: `if (tc != firsttc[level]) eqlev_first = level - 1`, for `D`. -/
theorem wp_tcResetG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {level : Nat} {btc : block} {tc : Int}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (hE1 : PTree.get dense.id.«nauty:eqlev_first» e = none)
    (hE2 : PTree.get dense.id.«nauty:firsttc» e = none)
    (htc : PTree.get dense.id.tc e = some (btc, tint))
    (htcv : Mem.load .Mint32 m btc (zOfInt 0) = some (.Vint (ir tc)))
    (htc1 : -1 ≤ tc) (htc2 : tc < 2147483648)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (h1 : 1 ≤ level) (hn : level ≤ n)
    (hQ : ∀ m', SearchAtG D m' S gl cl G
        (if tc ≠ st.firsttc[level]! then { st with eqlevFirst := level - 1 } else st) pre nsp →
      Unch m m' (· ∈ [E.eqlevFirst]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sifthenelse (.Ebinop .One (.Evar dense.id.tc tint)
        (Alloc.gat dense.id.«nauty:firsttc» (tv dense.id.level)) tint)
      (sk (.Sassign (.Evar dense.id.«nauty:eqlev_first» tint)
        (.Ebinop .Osub (tv dense.id.level) (ci 1 tint) tint))) .Sskip) Q e le m := by
  have hnl := h.nlt
  have hft := h.inv.firsttcRange level (by omega)
  have hFT : Exec.evalExpr ge e le m (Alloc.gat dense.id.«nauty:firsttc» (tv dense.id.level)) =
      some (.Vint (ir st.firsttc[level]!)) :=
    Alloc.eval_gat hE2 E.find_nautyFirsttc (h.dyns.firsttc.ptr (by have := h.dyns.capTC; omega))
      h.arrays.firsttc (by omega) (tv dense.id.level) level (by omega) hlev rfl
  apply wp_if_eval
  rw [Exec.evalExpr, eval_local htc htcv, hFT]
  simp only [typeof, cop]
  rw [ir_eq (a := tc) (b := st.firsttc[level]!) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hne : tc = st.firsttc[level]!
  · rw [ite_eq_right (by simp [hne])]
    apply wp_skip
    exact hQ m (by rw [if_neg (by simpa using hne)]; exact h) (Unch.refl _ _) fun _ h => h
  · rw [ite_eq_left (by simp [hne])]
    wp_step; wp_step
    refine wp_gint hE1 E.find_eqlevFirst h.scalars.eqlevFirst.writable (x := (level : Int) - 1)
      (by simp [Exec.evalExpr, tv, hlev, typeof, cop]) rfl ?_
    intro m' iEF hu hv
    have hU : Unch m m' (· ∈ [E.eqlevFirst]) := hu.mono fun z hz => by simp [hz]
    refine hQ m' ?_ hU hv
    rw [if_pos hne]
    exact h.setEqlevFirst hU hv (v := level - 1)
      (show IntAt m' E.eqlevFirst (((level - 1 : Nat)) : Int) by
        rw [show (((level - 1 : Nat)) : Int) = (level : Int) - 1 by omega]; exact iEF) (by omega)

/-- `t713 = (*dispatch.cheapautom)(ptn, level, digraph, n); if (!t713) noncheaplevel = level + 1;`,
for `D`: `cheapCheck false` when `O.cheapautom` is HexGraphIso's. The dispatch call may
change `D`'s written globals, its scratch blocks in use and new blocks. -/
theorem wp_cheapG {D : DispatchC ge O} {f : function} {Q : Post} {e : env} {le : temp_env}
    {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {pre nsp : Bool} {level : Nat} (h : SearchAtG D.toDispatchRep m S gl cl G st pre nsp)
    (hvU : Mem.valid_block m S.bUA) (hvT : Mem.valid_block m E.tcnode0)
    (hO : O.cheapautom st.ptn level n = Hex.GraphIso.Nauty.cheapautom st.ptn level n)
    (hE1 : PTree.get dense.id.«nauty:dispatch» e = none)
    (hE2 : PTree.get dense.id.«nauty:digraph» e = none)
    (hE3 : PTree.get dense.id.«nauty:n» e = none)
    (hE4 : PTree.get dense.id.«nauty:noncheaplevel» e = none)
    (hptn : PTree.get dense.id.ptn le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (h1 : 1 ≤ level) (hn : level ≤ n)
    (hQ : ∀ le' m', SearchAtG D.toDispatchRep m' S gl cl G (cheapCheck false level st) pre nsp →
      Unch m m' (fun z => z = E.noncheaplevel ∨ z ∈ D.wglobs ∨ D.IsWork m z ∨
        ¬ Mem.valid_block m z) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → WorkMonoG D.toDispatchRep m m' →
      (∀ x, x ≠ idOf 713 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f (.Ssequence (sk (.Scall (some (idOf 713))
      (.Ederef (.Efield (.Evar dense.id.«nauty:dispatch» (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr))
        dense.id.«cheapautom» (tptr (tfun [tptr tint, tint, tint, tint] tint)))
        (tfun [tptr tint, tint, tint, tint] tint))
      [.Etempvar dense.id.ptn (tptr tint), tv dense.id.level, .Evar dense.id.«nauty:digraph» tint,
       .Evar dense.id.«nauty:n» tint])) Othernode.cheap) Q e le m := by
  have hnl := h.nlt
  have hI := h.inv
  obtain ⟨fd, hfd, hty, hsat⟩ := D.cheapautom_fn xi
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr D.cheapautom Ptrofs.zero) (targs := [tptr tint, tint, tint, tint])
    (tres := tint) (cc := Common.AST.cc_default) fd _ (hsat S.bp S.pofs st.ptn level n) ?_ ?_ ?_
    hfd hty
    ⟨rfl, h.work.disp, h.arrays.ptn, hI.ptnSize, fun x hx => by
        rcases hI.ptnVals x hx with hv | hv
        · omega
        · rw [hv]; decide,
      by have := hI.ptnLast; omega, hnl, by omega⟩ ?_
  · rfl
  · simp only [Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar, hE1, E.find_dispatch, typeof,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode, field_dCheapautom, Mem.loadv, Alloc.Mptr_eq]
    rw [show Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 40))) = zOfInt 40 from rfl,
      h.fixed.dCheapautom.load]
  · simp only [Exec.evalExprlist, Exec.evalExpr, hptn, hlev, tv, Exec.lvalOfVar, hE2, hE3,
      E.find_digraph, E.find_n, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h.fixed.digraph.load, h.fixed.nn.load,
      typeof, cop]
  rintro t v m₁ ⟨rfl, rfl, hstep⟩
  obtain ⟨h₁, hw₁⟩ := h.dstep hvU hvT hstep (fun _ hz => hz.elim)
  have hv₁ := hstep.valid
  have hu₁ : Unch m m₁ (fun z => z = E.noncheaplevel ∨ z ∈ D.wglobs ∨ D.IsWork m z ∨
      ¬ Mem.valid_block m z) :=
    hstep.unch.mono fun z hz => by
      rcases hz with hz | hz
      · exact hz.elim
      · exact .inr hz
  rw [hO]
  simp only [set_opttemp, seqPost, Post.after, E0_append]
  simp only [Othernode.cheap, sk]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, tv, typeof, cop]
  by_cases hc : Hex.GraphIso.Nauty.cheapautom st.ptn level n = true
  · simp only [hc, ite_true]
    rw [ite_eq_right (by decide)]
    apply wp_skip
    have : cheapCheck false level st = st := by unfold cheapCheck; simp [hc]
    exact hQ _ m₁ (by rw [this]; exact h₁) hu₁ hv₁ hw₁ fun x hx => temps_gso _ _ hx
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [ite_eq_left (by decide)]
    wp_step; wp_step
    refine wp_gint hE4 E.find_noncheaplevel h₁.scalars.noncheaplevel.writable
      (x := (level : Int) + 1)
      (by rw [show Exec.evalExpr ge e (PTree.set (idOf 713) (.Vint (ir 0)) le) m₁
          (.Ebinop .Oadd (tv dense.id.level) (ci 1 tint) tint) = some (.Vint (ir ((level : Int) + 1))) by
            simp only [Exec.evalExpr, tv]; rw [temps_gso _ _ (by decide), hlev]; simp [typeof, cop]]) rfl ?_
    intro m' iNC hu hv
    have hU : Unch m₁ m' (· ∈ [E.noncheaplevel]) := hu.mono fun z hz => by simp [hz]
    have hcc : cheapCheck false level st = { st with noncheaplevel := level + 1 } := by
      unfold cheapCheck; simp [hc]
    have mNC : E.noncheaplevel ∈ S.blocksG D.toDispatchRep gl cl :=
      SLoc.mem_blocksG_of D.toDispatchRep (.inr (.inr (.inr (.inr (.inl (by simp))))))
    have hw₂ : WorkMonoG D.toDispatchRep m₁ m' := fun z hz => .inl ((h₁.work.unch hu
      (fun y hy e => h₁.globs_ne (D.wglobs_sub _ hy) (.inr (.inr (.inr (.inr (by simp))))) e)
      ⟨by sep_ne h₁.lit, by sep_ne h₁.lit⟩ (fun y hy e => h₁.work_not hy (e ▸ mNC)) hv).2 z hz)
    refine hQ _ m' ?_ (hu₁.trans (hu.mono fun z hz => .inl hz)) (fun z hz => hv _ (hv₁ _ hz))
      (hw₁.trans hv₁ hw₂) fun x hx => temps_gso _ _ hx
    rw [hcc]
    exact h₁.setNoncheap hU hv (v := level + 1) (by push_cast; exact iNC) (by omega)

end Generic

/-- `stats->tctotal += tcellsize`. -/
theorem wp_tctotal {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    (hge : PTree.get dense.id.«nauty:stats» e = none) {bsz : block} {sz : Nat}
    (hsz : PTree.get dense.id.tcellsize e = some (bsz, tint))
    (hszv : Mem.load .Mint32 m bsz (zOfInt 0) = some (.Vint (ir sz))) (hsz2 : sz < 2147483648)
    (hQ : ∀ m', SearchAt m' S ctx { st with tctotal := st.tctotal + sz } pre nsp →
      Unch m m' (· = S.bst) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (statsF dense.id.tctotal tulong)
      (.Ebinop .Oadd (statsF dense.id.tctotal tulong) (.Evar dense.id.tcellsize tint) tulong))
      Q e le m :=
  wp_tctotalG h.toG hge hsz hszv hsz2 fun m' h' hu hv => hQ m' (h'.dense h.gw) hu hv

/-- `t710 = !getcanon ? 1 : comp_canon < 0`: whether the target is hinted. -/
theorem wp_hint {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    (hE0 : PTree.get dense.id.«nauty:getcanon» e = none)
    (hE1 : PTree.get dense.id.«nauty:comp_canon» e = none)
    (hQ : ∀ le', PTree.get (idOf 710) le' = some (Val.of_bool (decide (st.compCanon < 0))) →
      (∀ x, x ≠ idOf 710 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m) :
    Wp xi ge f (.Sifthenelse (.Eunop .Onotbool (.Evar dense.id.«nauty:getcanon» tint) tint)
      (.Sset (idOf 710) (ci 1 tint))
      (sk (.Sset (idOf 710) (.Ecast (.Ebinop .Olt (.Evar dense.id.«nauty:comp_canon» tint)
        (ci 0 tint) tint) tbool)))) Q e le m :=
  wp_hintG h.toG hE0 hE1 hQ

/-- After a hinted target: `if (tc != firsttc[level]) eqlev_first = level - 1`. -/
theorem wp_tcReset {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level : Nat} {btc : block} {tc : Int}
    (h : SearchAt m S ctx st pre nsp)
    (hE1 : PTree.get dense.id.«nauty:eqlev_first» e = none)
    (hE2 : PTree.get dense.id.«nauty:firsttc» e = none)
    (htc : PTree.get dense.id.tc e = some (btc, tint))
    (htcv : Mem.load .Mint32 m btc (zOfInt 0) = some (.Vint (ir tc)))
    (htc1 : -1 ≤ tc) (htc2 : tc < 2147483648)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (h1 : 1 ≤ level) (hn : level ≤ n)
    (hQ : ∀ m', SearchAt m' S ctx
        (if tc ≠ st.firsttc[level]! then { st with eqlevFirst := level - 1 } else st) pre nsp →
      Unch m m' (· ∈ [Block.eqlevFirst]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sifthenelse (.Ebinop .One (.Evar dense.id.tc tint)
        (Alloc.gat dense.id.«nauty:firsttc» (tv dense.id.level)) tint)
      (sk (.Sassign (.Evar dense.id.«nauty:eqlev_first» tint)
        (.Ebinop .Osub (tv dense.id.level) (ci 1 tint) tint))) .Sskip) Q e le m :=
  wp_tcResetG h.toG hE1 hE2 htc htcv htc1 htc2 hlev h1 hn fun m' h' hu hv =>
    hQ m' (h'.dense h.gw) hu hv

/-- `t713 = (*dispatch.cheapautom)(ptn, level, digraph, n); if (!t713) noncheaplevel = level + 1;`:
HexGraphIso's `cheapCheck false`. -/
theorem wp_cheap {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level : Nat} (h : SearchAt m S ctx st pre nsp)
    (hE1 : PTree.get dense.id.«nauty:dispatch» e = none)
    (hE2 : PTree.get dense.id.«nauty:digraph» e = none)
    (hE3 : PTree.get dense.id.«nauty:n» e = none)
    (hE4 : PTree.get dense.id.«nauty:noncheaplevel» e = none)
    (hptn : PTree.get dense.id.ptn le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (h1 : 1 ≤ level) (hn : level ≤ n)
    (hQ : ∀ le' m', SearchAt m' S ctx (cheapCheck false level st) pre nsp →
      Unch m m' (· ∈ [Block.noncheaplevel]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 713 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f (.Ssequence (sk (.Scall (some (idOf 713))
      (.Ederef (.Efield (.Evar dense.id.«nauty:dispatch» (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr))
        dense.id.«cheapautom» (tptr (tfun [tptr tint, tint, tint, tint] tint)))
        (tfun [tptr tint, tint, tint, tint] tint))
      [.Etempvar dense.id.ptn (tptr tint), tv dense.id.level, .Evar dense.id.«nauty:digraph» tint,
       .Evar dense.id.«nauty:n» tint])) Othernode.cheap) Q e le m := by
  have hnl := h.nlt
  have hI := h.inv
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.cheapautomFn Ptrofs.zero) (targs := [tptr tint, tint, tint, tint])
    (tres := tint) (cc := Common.AST.cc_default) (.Internal dense.fn.cheapautom) _
    (Cheapautom.cheapautom_satisfies S.bp S.pofs st.ptn level n) ?_ ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_cheapautomFn]) rfl
    ⟨rfl, h.arrays.ptn, hI.ptnSize, fun x hx => by
        rcases hI.ptnVals x hx with hv | hv
        · omega
        · rw [hv]; decide,
      by have := hI.ptnLast; omega, hnl, by omega⟩ ?_
  · rfl
  · simp only [Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar, hE1, find_dispatch, typeof,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode, field_dCheapautom, Mem.loadv, Alloc.Mptr_eq]
    rw [show Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 40))) = zOfInt 40 from rfl,
      h.fixed.dCheapautom.load]
  · simp only [Exec.evalExprlist, Exec.evalExpr, hptn, hlev, tv, Exec.lvalOfVar, hE2, hE3,
      find_digraph, find_n, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h.fixed.digraph.load, h.fixed.nn.load,
      typeof, cop]
  rintro t v m'' ⟨rfl, hmm, rfl⟩
  rw [hmm]
  simp only [set_opttemp, seqPost, Post.after, E0_append]
  simp only [Othernode.cheap, sk]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, tv, typeof, cop]
  by_cases hc : Hex.GraphIso.Nauty.cheapautom st.ptn level n = true
  · simp only [hc, ite_true]
    rw [ite_eq_right (by decide)]
    apply wp_skip
    have : cheapCheck false level st = st := by unfold cheapCheck; simp [hc]
    exact hQ _ m (by rw [this]; exact h) (Unch.refl _ _) (fun _ h => h)
      fun x hx => temps_gso _ _ hx
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [ite_eq_left (by decide)]
    wp_step; wp_step
    refine wp_gint hE4 find_noncheaplevel h.scalars.noncheaplevel.writable
      (x := (level : Int) + 1)
      (by rw [show Exec.evalExpr ge e (PTree.set (idOf 713) (.Vint (ir 0)) le) m
          (.Ebinop .Oadd (tv dense.id.level) (ci 1 tint) tint) = some (.Vint (ir ((level : Int) + 1))) by
            simp only [Exec.evalExpr, tv]; rw [temps_gso _ _ (by decide), hlev]; simp [typeof, cop]]) rfl ?_
    intro m' iNC hu hv
    have hU : Unch m m' (· ∈ [Block.noncheaplevel]) := hu.mono fun z hz => by simp [hz]
    have hcc : cheapCheck false level st = { st with noncheaplevel := level + 1 } := by
      unfold cheapCheck; simp [hc]
    refine hQ _ m' ?_ hU hv fun x hx => temps_gso _ _ hx
    rw [hcc]
    have sc := h.scalars
    refine h.setScalars hU (fun z hz => by simp at hz; subst hz; decide)
      ⟨sc.gcaFirst.unch hU (by decide), sc.gcaCanon.unch hU (by decide),
        show IntAt m' Block.noncheaplevel (((level + 1 : Nat)) : Int) by push_cast; exact iNC,
        sc.allsamelevel.unch hU (by decide), sc.eqlevFirst.unch hU (by decide),
        sc.eqlevCanon.unch hU (by decide), sc.compCanon.unch hU (by decide),
        sc.samerows.unch hU (by decide), sc.canonlevel.unch hU (by decide),
        sc.stabvertex.unch hU (by decide), sc.cosetindex.unch hU (by decide),
        sc.needshortprune.unch hU (by decide)⟩
      { h.arrays with } { h.stats with } ?_
    obtain ⟨s1, s2, -, s4⟩ := h.inv.scalars
    exact { h.inv with scalars := ⟨s1, s2, show level + 1 < 2147483648 by omega, s4⟩ }


end NautyVerified.Proofs.Search
