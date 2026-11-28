import NautyVerified.Proofs.Top.NautyRoot
import NautyVerified.Proofs.Search.Processnode.Canon
import NautyVerified.Proofs.Search.Processnode.Classifier
import NautyVerified.Proofs.Search.Processnode.Set
import NautyVerified.Proofs.Search.Node.Rebuild
import NautyVerified.Proofs.Dispatch.Dense
import NautyVerified.Logic.Grow

/-!
# `nauty()` after the search (`tPost` up to `tFree`)

The root call returns a level (0 or 1), so neither error branch
(`NAUTY_ABORTED`, `NAUTY_KILLED`) is taken. With `getcanon` set,
`(*dispatch.updatecan)(g, canong, canonlab, samerows, m, n)` fills every row
of `canong` from the best labelling (`wp_topUpdatecanG`, through the dispatch
procedures' `updatecanSpec`), the loop copies `canonlab` into `lab`, and
`stats->invarsuclevel`, `invapplics` and `invsuccesses` are stored
(`wp_statsTailG`).

`wp_tPostG D C` states this over `SearchAtG D` for any dispatch procedures
`D : DispatchC ge O` and store update `C : Classifier O`: afterwards memory
holds the search state with the store updated and `lab = canonlab`
(`postStateG`), and the store's representation holds all `n` rows of
`O.updatecan`. The dense `wp_tPost` (state `postState`, `canong` holding the
rows as a `GraphAt`) is its instance at `Dispatch.dense` and `denseClassifier`.
-/

namespace NautyVerified.Proofs.Top

variable {bI : CompCert4Lean.Common.Values.block}

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (Keep DynAt)
open NautyVerified.Proofs.Search
open NautyVerified.Proofs.Graph (GraphAt)
open NautyVerified.Proofs.Search.Processnode (Keep.access' eval_gptr)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

variable {n : Nat} {S : SLoc} {ctx : Ctx n}

/-- `lab` with its first `k` entries replaced by `canonlab`'s. -/
def copyFrom (v w : Nat → val) (k : Nat) : Nat → val := fun j => if j < k then w j else v j

theorem copyFrom_succ (v w : Nat → val) (k : Nat) :
    upd (copyFrom v w k) k (w k) = copyFrom v w (k + 1) := by
  funext j
  simp only [upd, copyFrom]
  by_cases h : j = k
  · subst h; simp
  · by_cases h2 : j < k
    · simp [h, h2, show j < k + 1 by omega]
    · simp [h, h2, show ¬ j < k + 1 by omega]


open NautyVerified.Proofs.Set (sk) in
open NautyVerified.Proofs.Refine (tv) in
/-- `stats->invarsuclevel = …; stats->invapplics = invapplics; stats->invsuccesses = invsuccesses;` -/
abbrev statsTail : statement :=
          (.Ssequence
            (.Ssequence
              (sk
                (.Sifthenelse
                  (.Ebinop .Oeq (.Evar dense.id.«nauty:invarsuclevel» tint) (ci 2000000002 tint) tint)
                  (sk (.Sset (idOf 736) (.Ecast (ci 0 tint) tint)))
                  (sk (.Sset (idOf 736) (.Ecast (.Evar dense.id.«nauty:invarsuclevel» tint) tint)))))
              (.Sassign
                (.Efield
                  (.Ederef
                    (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                    (.Tstruct dense.id.«_1024» noattr))
                  dense.id.«invarsuclevel»
                  tint)
                (tv (idOf 736))))
            (.Ssequence
              (sk
                (.Sassign
                  (.Efield
                    (.Ederef
                      (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                      (.Tstruct dense.id.«_1024» noattr))
                    dense.id.«invapplics»
                    tulong)
                  (.Evar dense.id.«nauty:invapplics» tulong)))
              (sk
                (.Sassign
                  (.Efield
                    (.Ederef
                      (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                      (.Tstruct dense.id.«_1024» noattr))
                    dense.id.«invsuccesses»
                    tulong)
                  (.Evar dense.id.«nauty:invsuccesses» tulong)))))


section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)
open NautyVerified.Proofs.Search.Processnode (lab_inj)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}

/-- The search state after `updatecan`, the store updated by `C`. -/
abbrev canonStateG (C : Classifier O) (G : O.Gr n) (st : SearchState n (O.Canon n)) :
    SearchState n (O.Canon n) :=
  { st with canong := C.update G st.canong st.canonlab st.samerows }

/-- The search state after `postIf`: the store updated and `lab = canonlab`. -/
abbrev postStateG (C : Classifier O) (G : O.Gr n) (st : SearchState n (O.Canon n)) :
    SearchState n (O.Canon n) :=
  { canonStateG C G st with lab := st.canonlab }

section Frame

variable {D : DispatchRep ge O} {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
  {st : SearchState n (O.Canon n)} {pre nsp : Bool}

/-- A block of `S` outside the store's representation and `D`'s written globals is
none of the blocks a call writing only the store may change. -/
theorem _root_.NautyVerified.Proofs.Search.SearchAtG.stepNotC (h : SearchAtG D m S gl cl G st pre nsp) (hv : SValidG D m S gl cl)
    {out : block → Prop} (hout : ∀ z, out z → z ∈ D.canonBlocks cl S.bc) {y : block}
    (hy : y ∈ S.blocksG D gl cl) (hyc : y ∉ D.canonBlocks cl S.bc) (hyw : y ∉ D.wglobs) :
    ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) := by
  rintro (h1 | h1 | h1 | h1)
  · exact hyc (hout y h1)
  · exact hyw h1
  · exact h.work.notin y h1 hy
  · exact h1 (hv y hy)

/-- The graph's and the store's blocks and `canonlab`, as `updatecan` needs them. -/
theorem _root_.NautyVerified.Proofs.Search.SearchAtG.sepCL (h : SearchAtG D m S gl cl G st pre nsp) (hv : SValidG D m S gl cl) :
    D.Sep m (D.graphBlocks gl S.bg ++ D.canonBlocks cl S.bc ++ [S.bCL]) := by
  have hg : (D.graphBlocks gl S.bg).Pairwise (· ≠ ·) :=
    h.distinct.sublist (by
      simp only [SLoc.blocksG, List.append_assoc]; exact List.sublist_append_left _ _)
  have hc : (D.canonBlocks cl S.bc).Pairwise (· ≠ ·) :=
    h.distinct.sublist (by
      simp only [SLoc.blocksG, List.append_assoc]
      exact ((List.sublist_append_left _ _).trans (List.sublist_append_right _ _)).trans
        (List.sublist_append_right _ _))
  have hCL : S.bCL ∈ S.litG := by simp [SLoc.litG]
  have hmem : ∀ z ∈ D.graphBlocks gl S.bg ++ D.canonBlocks cl S.bc ++ [S.bCL],
      z ∈ S.blocksG D gl cl ∧ z ∉ D.globs ∧ z ≠ E.nautyBit ∧ z ≠ E.nautilBit ∧
        z ≠ E.leftbit := by
    intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with (hz | hz) | rfl
    · exact ⟨SLoc.mem_blocksG_of D (.inl hz),
        fun hg => h.graph_ne hz (.inr (.inr (.inr (.inr hg)))) rfl,
        h.graph_ne hz (.inr (.inr (.inr (.inl (by simp))))),
        h.graph_ne hz (.inr (.inr (.inr (.inl (by simp))))),
        h.graph_ne hz (.inr (.inr (.inr (.inl (by simp)))))⟩
    · exact ⟨SLoc.mem_blocksG_of D (.inr (.inr (.inl hz))),
        fun hg => h.canon_ne hz (.inr (.inr (.inr (.inr hg)))) rfl,
        h.canon_ne hz (.inr (.inr (.inr (.inl (by simp))))),
        h.canon_ne hz (.inr (.inr (.inr (.inl (by simp))))),
        h.canon_ne hz (.inr (.inr (.inr (.inl (by simp)))))⟩
    · exact ⟨(S.litG_sub D gl cl).subset hCL, h.lit_globs _ hCL, by sep_ne h.lit,
        by sep_ne h.lit, by sep_ne h.lit⟩
  refine ⟨List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨hg, hc,
      fun z hz y hy => h.graph_ne hz (.inr (.inl hy))⟩, List.pairwise_singleton _ _,
      fun z hz y hy => ?_⟩, fun z hz => hv z (hmem z hz).1,
    fun z hz hw => h.work.notin z hw (hmem z hz).1, fun z hz => (hmem z hz).2.1,
    fun z hz => (hmem z hz).2.2⟩
  rw [List.mem_singleton] at hy
  subst hy
  rcases List.mem_append.1 hz with hz | hz
  · exact h.graph_ne hz (.inr (.inr (.inl (by simp))))
  · exact h.canon_ne hz (.inr (.inr (.inl (by simp))))

/-- Across a call of one of `D`'s procedures whose outputs are the store's blocks,
leaving the store `c`. -/
theorem _root_.NautyVerified.Proofs.Search.SearchAtG.callCanon (h : SearchAtG D m S gl cl G st pre nsp) (hv : SValidG D m S gl cl)
    {out : block → Prop} (hstep : D.Step m m' out) (hout : ∀ z, out z → z ∈ D.canonBlocks cl S.bc)
    {c : O.Canon n} (hc : D.CanonRep m' cl S.bc S.cofs S.M (O.rows c) st.samerows)
    (hinv : SInvG O G { st with canong := c }) :
    SearchAtG D m' S gl cl G { st with canong := c } pre nsp ∧ SStepG D m m' S gl cl := by
  have hu := hstep.unch
  have nL : ∀ y ∈ S.litG, y ∉ D.canonBlocks cl S.bc →
      ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) := fun y hy hyc =>
    h.stepNotC hv hout ((S.litG_sub D gl cl).subset hy) hyc
      fun hw => h.lit_globs y hy (D.wglobs_sub _ hw)
  have nE : ∀ y ∈ envSearch, ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) :=
    fun y hy => nL y (by unfold SLoc.litG; exact List.mem_append_right _ hy)
      fun hc => h.canon_ne hc (.inr (.inr (.inr (.inl hy)))) rfl
  have nV : ∀ y ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA],
      ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) :=
    fun y hy => nL y (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
        rcases hy with h | h | h | h | h | h | h | h | h | h <;> simp [SLoc.litG, h])
      fun hc => h.canon_ne hc (.inr (.inr (.inl hy))) rfl
  have nV4 : ∀ y ∈ [S.bl, S.bp, S.bo, S.bst],
      ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) :=
    fun y hy => nL y (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
        rcases hy with h | h | h | h <;> simp [SLoc.litG, h])
      fun hc => h.canon_ne hc (.inr (.inl hy)) rfl
  have nGr : ∀ y ∈ D.graphBlocks gl S.bg,
      ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) :=
    fun y hy => h.stepNotC hv hout (SLoc.mem_blocksG_of D (.inl hy))
      (fun hc => h.canon_ne hc (.inl hy) rfl)
      fun hw => h.globs_ne (D.wglobs_sub _ hw) (.inl hy) rfl
  have nG : ∀ y ∈ D.globs, y ∉ D.wglobs →
      ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) :=
    fun y hy hyw => h.stepNotC hv hout (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inr hy))))))
      (fun hc => h.canon_ne hc (.inr (.inr (.inr (.inr hy)))) rfl) hyw
  have hN : ∀ z, out z → z ≠ E.nautilWorkperm ∧ z ≠ E.nautilWorkpermSz ∧
      ∀ c' b, DynAt m E.nautilWorkperm E.nautilWorkpermSz 4 c' b → 0 < c' → z ≠ b := by
    intro z hz
    have h1 := hout z hz
    refine ⟨h.canon_ne h1 (.inr (.inr (.inr (.inl (by simp))))),
      h.canon_ne h1 (.inr (.inr (.inr (.inl (by simp))))), fun c' b d hc e => ?_⟩
    exact h.work_not (.inr ⟨c', hc, e ▸ d⟩) (SLoc.mem_blocksG_of D (.inr (.inr (.inl h1))))
  obtain ⟨hwk, hwm⟩ := h.work.step hstep hv
    (fun z hz => SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inr hz))))))
    hN ⟨SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl (by simp)))))),
      SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl (by simp))))))⟩
  have hW : ∀ z ∈ [S.bl, S.bp, S.bo, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws,
      E.fmptr], ¬ (out z ∨ z ∈ D.wglobs ∨ D.IsWork m z ∨ ¬ Mem.valid_block m z) := by
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    iterate 3 exact nV4 _ (by simp)
    iterate 9 exact nV _ (by simp)
    exact nE _ (by simp)
  refine ⟨{ h with
      fixed := h.fixed.unch hu fun z hz => nE z (by revert z; simp)
      scalars := { h.scalars.unch hu (fun z hz => nE z (by revert z; simp)) with }
      stats := { h.stats.unch hu (nV4 _ (by simp)) with }
      arrays := h.arrays.setCanong hu hW nGr hc
      dyns := h.dyns.unch hu fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        iterate 16 exact nE _ (by simp)
        iterate 8 exact nV _ (by simp)
        exact nG _ D.wsP_mem D.wsP_nw
        exact nG _ D.wsS_mem D.wsS_nw
        exact nV _ (by simp)
      work := hwk
      tables := h.tables.unch hu (nE _ (by simp)) (nE _ (by simp)) (nE _ (by simp))
        fun z hz hzw => nG z hz hzw
      inv := hinv }, ⟨hu.mono fun z hz => ?_, hstep.valid⟩, hwm⟩
  rcases hz with h1 | h1 | h1 | h1
  · exact .inl (h.chg_wr (.inr (.inr (hout z h1))))
  · exact .inl (h.chg_globs (D.wglobs_sub _ h1))
  · exact .inr (.inr (.inl h1))
  · exact .inr (.inl h1)

/-- A block outside `S` that is valid and not a work block survives a search step. -/
theorem _root_.NautyVerified.Proofs.Search.SStepG.keepOut (h : SStepG D m m' S gl cl) {z : block} (hz : z ∉ S.blocksG D gl cl)
    (hv : Mem.valid_block m z) (hw : ¬ IsWorkG D m z) {chunk : memory_chunk} {o : Z} :
    Mem.load chunk m' z o = Mem.load chunk m z o :=
  h.1.1.load _ _ _ (by rintro (h1 | h1 | h1); exact hz h1.1; exact h1 hv; exact hw h1)

end Frame

variable {xi : ExternalCalls}

/-- `(*dispatch.updatecan)(g, canong, canonlab, samerows, m, n)` in `nauty()`. -/
theorem wp_topUpdatecanG (D : DispatchC ge O) (C : Classifier O) {Q : Post} {le : temp_env}
    {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {nsp : Bool}
    (hs : SearchAtG D.toDispatchRep m S gl cl G st false nsp)
    (hvm : SValidG D.toDispatchRep m S gl cl)
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ v < n, ∃ i < n, st.canonlab[i]! = v)
    (hfit : O.Fits G (O.rows st.canong) st.canonlab st.samerows)
    (hQ : ∀ m', SearchAtG D.toDispatchRep m' S gl cl G (canonStateG C G st) false nsp →
      D.CanonRep m' cl S.bc S.cofs S.M (O.updatecan G (O.rows st.canong) st.canonlab st.samerows) n →
      SStepG D.toDispatchRep m m' S gl cl → Q.normal E0 (nEnv bI) le m') :
    Wp xi ge dense.fn.nauty Processnode.updatecanCall Q (nEnv bI) le m := by
  have hinv := hs.inv
  have hcCL : 0 < S.capCL := by have := hs.dyns.capCL; have := hs.n0; omega
  obtain ⟨fd, hfd, hty, hsat⟩ := D.updatecan_fn xi
  refine wp_call (vf := .Vptr D.updatecan Ptrofs.zero)
    (targs := [tptr tulong, tptr tulong, tptr tint, tint, tint, tint]) (tres := .Tvoid)
    (cc := cc_default) (vargs := [.Vptr S.bg S.gofs, .Vptr S.bc S.cofs, .Vptr S.bCL Ptrofs.zero,
      .Vint (ir st.samerows), .Vint (ir S.M), .Vint (ir n)]) fd _
    (hsat G gl S.bg S.gofs (O.rows st.canong) cl S.bc S.cofs S.bCL Ptrofs.zero st.canonlab
      st.samerows S.M) rfl
    (Processnode.eval_dispatch (e := nEnv bI) rfl E.field_dUpdatecan rfl (by decide) (by decide)
      hs.fixed.dUpdatecan)
    ?_ hfd hty ?_ ?_
  · simp only [Exec.evalExprlist,
      eval_gptr (ty := tptr tulong) (e := nEnv bI) rfl E.find_g rfl hs.fixed.g,
      eval_gptr (ty := tptr tulong) (e := nEnv bI) rfl E.find_canong rfl hs.fixed.canong,
      eval_gptr (ty := tptr tint) (e := nEnv bI) rfl E.find_nautyCanonlab rfl
        ⟨hs.dyns.canonlab.ptr hcCL, hs.dyns.canonlab.bpW⟩,
      Search.eval_gint (e := nEnv bI) rfl E.find_samerows hs.scalars.samerows,
      Search.eval_gint (e := nEnv bI) rfl E.find_m hs.fixed.mm,
      Search.eval_gint (e := nEnv bI) rfl E.find_n hs.fixed.nn, typeof, cop]
  · exact ⟨rfl, hs.ctx, hs.arrays.graph, hs.graphOk, hs.arrays.canong, hinv.canong,
      hs.arrays.canonlab, hinv.canonlabSize, hcl, hcs, lab_inj hcl hcs, hinv.samerows,
      hs.sepCL hvm, hfit⟩
  · rintro t r m' ⟨rfl, hcr, hok, hstep⟩
    have hrows := C.rows_update G st.canong st.canonlab st.samerows
    have hcr' : D.CanonRep m' cl S.bc S.cofs S.M
        (O.rows (C.update G st.canong st.canonlab st.samerows)) n := by
      rw [hrows]; exact hcr
    obtain ⟨hS', hst'⟩ := hs.callCanon hvm hstep (fun z hz => hz) (D.canon_le hcr' hinv.samerows)
      { hinv with canong := by show O.StoreOk G (O.rows _); rw [hrows]; exact hok }
    exact hQ m' hS' hcr hst'

/-- A store to `statsblk` at offset 64 or beyond keeps `StatsG`. -/
theorem StatsG.storeHi {m m' : mem} {S : SLoc} {κ : Type} {st : SearchState n κ} {pre : Bool}
    (h : StatsG m S st pre) {c : memory_chunk} {off : Int} {w : val}
    (hst : Mem.store c m S.bst (zOfInt (S.sb + off)) w = some m') (hoff : 64 ≤ off) :
    StatsG m' S st pre :=
  have c4 : csize .Mint32 = 4 := rfl
  have c8 : csize .Mint64 = 8 := rfl
  { (h.fix.store hst (by omega)) with
    numorbits := h.numorbits.store_other hst (by omega)
    numgenerators := h.numgenerators.store_other hst (by omega)
    numnodes := h.numnodes.store_other hst (by omega)
    numbadleaves := h.numbadleaves.store_other hst (by omega)
    maxlevel := fun hp => (h.maxlevel hp).store_other hst (by omega)
    maxlevelW := Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ h.maxlevelW
    tctotal := h.tctotal.store_other hst (by omega)
    canupdates := h.canupdates.store_other hst (by omega)
    fits := h.fits }

/-- `canonlab[x]` for `x` holding `c < n`. -/
theorem eval_canonlabAtG {e : env} {le : temp_env} {m : mem} {bC : block} {cl : Array Nat}
    (hge : PTree.get dense.id.«nauty:canonlab» e = none)
    (hp : Mem.load .Mint64 m E.nautyCanonlab (zOfInt 0) = some (.Vptr bC Ptrofs.zero))
    (harr : ArrayAt m .Mint32 bC 0 (ints cl) n) (hnl : n < 1073741824)
    {x : ident} {c : Nat} (hx : PTree.get x le = some (.Vint (ir c))) (hc : c < n) :
    Exec.evalExpr ge e le m (.Ederef (.Ebinop .Oadd (.Evar dense.id.«nauty:canonlab» (tptr tint))
      (Refine.tv x) (tptr tint)) tint) = some (.Vint (ir (cl[c]! : Int))) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, E.find_nautyCanonlab, Exec.derefLoc,
    Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp, Refine.tv, hx, typeof, cop]
  apply load_array harr hc
  apply addr_elem Ptrofs.zero _ .Mint32 rfl rfl (by omega)
  have hf := harr.fits
  have h4 : csize .Mint32 = 4 := rfl
  have h0 : intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 := rfl
  rw [h4] at hf ⊢
  rw [h0]
  omega

/-- The three `statsblk` stores after the canonical labelling. -/
theorem wp_statsTailG [T : TopEnv ge] {Q : Post} {le : temp_env} {m : mem} {S : SLoc}
    (hso : S.sofs = Ptrofs.zero) (hP : PtrAt m E.stats (.Vptr S.bst S.sofs))
    (hR : Mem.range_perm m S.bst (zOfInt 0) (zOfInt 88) .Cur .Freeable)
    (nA : E.invapplics ≠ S.bst) (nS' : E.invsuccesses ≠ S.bst)
    (nSt : S.bst ≠ E.stats)
    (hIL : ∃ w, Mem.load .Mint32 m E.invarsuclevel (zOfInt 0) = some (.Vint w))
    (hIA : ∃ w, Mem.load .Mint64 m E.invapplics (zOfInt 0) = some (.Vlong w))
    (hIS : ∃ w, Mem.load .Mint64 m E.invsuccesses (zOfInt 0) = some (.Vlong w))
    (hQ : ∀ le' m', Unch m m' (· = S.bst) →
      (∀ {k : Nat} {κ : Type} {st : SearchState k κ} {pre : Bool}, StatsG m S st pre →
        StatsG m' S st pre) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 736 → PTree.get x le' = PTree.get x le) → Q.normal E0 (nEnv bI) le' m') :
    Wp xi ge dense.fn.nauty statsTail Q (nEnv bI) le m := by
  have hsb : S.sb = 0 := by simp [SLoc.sb, hso]
  have hva2 : ∀ (c : memory_chunk) (off : Int), 0 ≤ off → off + csize c ≤ 88 →
      ZArith.BinInt.Z.divide (Common.Memdata.align_chunk c) (zOfInt off) →
      Mem.valid_access m c S.bst (zOfInt (S.sb + off)) .Writable := fun c off h0 h1 hal => by
    rw [hsb, Int.zero_add]; exact va88 hR c off h0 h1 hal
  obtain ⟨wL, hL2⟩ := hIL
  obtain ⟨wA, hA2⟩ := hIA
  obtain ⟨wS, hS2⟩ := hIS
  wp_step; wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar,
    show PTree.get dense.id.«nauty:invarsuclevel» (nEnv bI) = none from rfl, E.find_invarsuclevel,
    Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hL2, typeof, cop]
  split <;> (wp_step; wp_step; apply wp_set_eval; simp only [Exec.evalExpr, Exec.lvalOfVar,
    show PTree.get dense.id.«nauty:invarsuclevel» (nEnv bI) = none from rfl, E.find_invarsuclevel,
    Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hL2, typeof, cop])
  all_goals
    refine Search.wp_statsStore (S := S) (ty := tint) (chunk := .Mint32) (off := 80) rfl
      T.field_statsInvarsuclevel rfl hP (by decide) (by rw [hsb]; decide)
      (hva2 .Mint32 80 (by decide) (by decide) ⟨zOfInt 20, rfl⟩)
      (by simp only [Exec.evalExpr, temps_gss]; rfl) rfl ?_
    intro m3 hs3
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine Search.wp_statsStore (S := S) (ty := tulong) (chunk := .Mint64) (off := 64) rfl
      T.field_statsInvapplics rfl (hP.unch (Unch.store hs3 rfl) nSt) (by decide)
      (by rw [hsb]; decide)
      (Mem.store_valid_access_1 _ _ _ _ _ _ hs3 _ _ _ _
        (hva2 .Mint64 64 (by decide) (by decide) ⟨zOfInt 8, rfl⟩))
      (by simp only [Exec.evalExpr, Exec.lvalOfVar,
            show PTree.get dense.id.«nauty:invapplics» (nEnv bI) = none from rfl, E.find_invapplics,
            Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
            show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
            Mem.load_store_other _ _ _ _ _ _ hs3 _ _ _ (.inl nA), hA2]; rfl) rfl ?_
    intro m4 hs4
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    refine Search.wp_statsStore (S := S) (ty := tulong) (chunk := .Mint64) (off := 72) rfl
      T.field_statsInvsuccesses rfl
      ((hP.unch (Unch.store hs3 rfl) nSt).unch (Unch.store hs4 rfl) nSt)
      (by decide) (by rw [hsb]; decide)
      (Mem.store_valid_access_1 _ _ _ _ _ _ hs4 _ _ _ _ (Mem.store_valid_access_1 _ _ _ _ _ _ hs3 _ _ _ _
        (hva2 .Mint64 72 (by decide) (by decide) ⟨zOfInt 9, rfl⟩)))
      (by simp only [Exec.evalExpr, Exec.lvalOfVar,
            show PTree.get dense.id.«nauty:invsuccesses» (nEnv bI) = none from rfl,
            E.find_invsuccesses,
            Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
            show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
            Mem.load_store_other _ _ _ _ _ _ hs4 _ _ _ (.inl nS'),
            Mem.load_store_other _ _ _ _ _ _ hs3 _ _ _ (.inl nS'), hS2]; rfl) rfl ?_
    intro m5 hs5
    simp only [seqPost, Post.after, E0_append]
    refine hQ _ m5 ((((Unch.store hs3 rfl).trans (Unch.store hs4 rfl)).trans (Unch.store hs5 rfl)).mono
      fun z hz => hz.symm)
      (fun h => StatsG.storeHi (StatsG.storeHi (StatsG.storeHi h hs3 (by decide)) hs4 (by decide))
        hs5 (by decide))
      (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hs5 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hs4 _
          (Mem.store_valid_block_1 _ _ _ _ _ _ hs3 _ hz)))
      (fun x hx => temps_gso _ _ hx)

/-- `SearchAtG` after the copy of `canonlab` into `lab` and the `statsblk` stores. -/
theorem SearchAtG.postLabG {D : DispatchRep ge O} (C : Classifier O) {m1 m5 : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {nsp : Bool}
    (hS1 : SearchAtG D m1 S gl cl G (canonStateG C G st) false nsp)
    (hu3 : Unch m1 m5 (· ∈ [S.bl, S.bst]))
    (hv : ∀ z, Mem.valid_block m1 z → Mem.valid_block m5 z)
    (hlabF : ArrayAt m5 .Mint32 S.bl S.lb (ints st.canonlab) n)
    (hst5 : StatsG m5 S (postStateG C G st) false)
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ u < n, ∃ i < n, st.canonlab[i]! = u) :
    SearchAtG D m5 S gl cl G (postStateG C G st) false nsp ∧ SStepG D m1 m5 S gl cl := by
  have hd := hS1.lit
  have hsc3 : ∀ z ∈ (scalarBlocks : List block), ¬ z ∈ [S.bl, S.bst] := by
    simp only [scalarBlocks]; sep_all hd
  have hL : ∀ z ∈ [S.bl, S.bst], z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc := by
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl <;> simp [SLoc.wrVG]
  have hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws], Keep m1 m5 z := by
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Keep.unch hu3 (by sep_notin hd)
  have ha := hS1.arrays
  have hcg : ∀ z ∈ D.canonBlocks cl S.bc, ¬ z ∈ [S.bl, S.bst] := by
    intro z hz hzL
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzL
    rcases hzL with rfl | rfl
    · exact hS1.canon_ne hz (.inr (.inl (by simp))) rfl
    · exact hS1.canon_ne hz (.inr (.inl (by simp))) rfl
  have hgg : ∀ z ∈ D.graphBlocks gl S.bg, ¬ z ∈ [S.bl, S.bst] := by
    intro z hz hzL
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzL
    rcases hzL with rfl | rfl
    · exact hS1.graph_ne hz (.inl (by simp)) rfl
    · exact hS1.graph_ne hz (.inl (by simp)) rfl
  obtain ⟨aw, haw, har⟩ := ha.active
  obtain ⟨fw, hfw, hfr⟩ := ha.fixedpts
  obtain ⟨wv, hwv⟩ := ha.workperm
  have har5 : ArraysG D m5 S gl cl G (postStateG C G st) :=
    ⟨hlabF, ha.ptn.unch hu3 (by sep_notin hd), ha.orbits.unch hu3 (by sep_notin hd),
      ⟨aw, haw.unch hu3 (by sep_notin hd), har⟩, ⟨fw, hfw.unch hu3 (by sep_notin hd), hfr⟩,
      ⟨wv, hwv.unch hu3 (by sep_notin hd)⟩, ha.firstlab.unch hu3 (by sep_notin hd),
      ha.canonlab.unch hu3 (by sep_notin hd), ha.firstcode.unch hu3 (by sep_notin hd),
      ha.canoncode.unch hu3 (by sep_notin hd), ha.firsttc.unch hu3 (by sep_notin hd),
      D.canon_unch ha.canong hu3 hcg,
      ha.autos.unch hu3 (by sep_notin hd) (by sep_notin hd), D.graph_unch ha.graph hu3 hgg⟩
  refine ⟨hS1.rebuild hu3 hL hK hv { hS1.scalars.unch hu3 hsc3 with } hst5 har5
    { hS1.inv with labSize := hS1.inv.canonlabSize, labSmall := hcl, labSurj := hcs }, ?_⟩
  refine SStepG.of_unch hS1 hu3 hv (fun z hz => .inl (hS1.chg_wr (.inr (.inl ?_)))) ?_
    ⟨by sep_notin hd, by sep_notin hd⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl <;> simp [SLoc.wrVG]
  · intro z hz hzL
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzL
    rcases hzL with rfl | rfl <;>
      exact hS1.lit_globs _ (by simp [SLoc.litG]) (D.wglobs_sub _ hz)

/-- `nauty()` after the search returned, up to the release (`tPost` up to `tFree`),
for any dispatch procedures `D` and store update `C`. -/
theorem wp_tPostG [T : TopEnv ge] (D : DispatchC ge O) (C : Classifier O) {Q : Post}
    {le : temp_env} {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {nsp : Bool} {v : Nat}
    (hs : SearchAtG D.toDispatchRep m S gl cl G st false nsp)
    (hvm : SValidG D.toDispatchRep m S gl cl) (hso : S.sofs = Ptrofs.zero)
    (hret : PTree.get dense.id.«retval» le = some (.Vint (ir v))) (hv : v ≤ 1)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ u < n, ∃ i < n, st.canonlab[i]! = u)
    (hfit : O.Fits G (O.rows st.canong) st.canonlab st.samerows)
    (hout : ∀ z ∈ [E.invarsuclevel, E.invapplics, E.invsuccesses],
      z ∉ S.blocksG D.toDispatchRep gl cl ∧ Mem.valid_block m z ∧ ¬ IsWorkG D.toDispatchRep m z)
    (hIL : ∃ w, Mem.load .Mint32 m E.invarsuclevel (zOfInt 0) = some (.Vint w))
    (hIA : ∃ w, Mem.load .Mint64 m E.invapplics (zOfInt 0) = some (.Vlong w))
    (hIS : ∃ w, Mem.load .Mint64 m E.invsuccesses (zOfInt 0) = some (.Vlong w))
    (hQ : ∀ le' m', SearchAtG D.toDispatchRep m' S gl cl G (postStateG C G st) false nsp →
      D.CanonRep m' cl S.bc S.cofs S.M (O.updatecan G (O.rows st.canong) st.canonlab st.samerows) n →
      SStepG D.toDispatchRep m m' S gl cl →
      (∀ x, x ≠ dense.id.«i» → x ≠ idOf 736 → PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tFree Q (nEnv bI) le' m') :
    Wp xi ge dense.fn.nauty Nauty.tPost Q (nEnv bI) le m := by
  have hn0 := hs.n0
  have hnl := hs.nlt
  simp only [Nauty.tPost, Nauty.postIf, Set.sk]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Refine.tv, hret, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 11) = ir 11 from rfl, ir_neg,
    ir_eq ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  simp only [show ((v : Int) = -11) = False from propext ⟨fun h => by omega, False.elim⟩,
    decide_false, Bool.false_eq_true, ite_false]
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Refine.tv, hret, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 12) = ir 12 from rfl, ir_neg,
    ir_eq ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  simp only [show ((v : Int) = -12) = False from propext ⟨fun h => by omega, False.elim⟩,
    decide_false, Bool.false_eq_true, ite_false]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Search.eval_gint (e := nEnv bI) rfl E.find_getcanon hs.fixed.getcanon]
  simp only [typeof, cop]
  rw [ite_eq_left (by decide)]
  wp_step; wp_step; wp_step
  refine wp_topUpdatecanG D C hs hvm hcl hcs hfit ?_
  intro m1 hS1 hG1 hstep1
  simp only [seqPost, Post.after, E0_append]
  have hd1 := hS1.lit
  have hcap : 0 < S.capCL := by have := hS1.dyns.capCL; omega
  have hpCL := hS1.dyns.canonlab.ptr hcap
  have harrCL := hS1.arrays.canonlab
  have hN1 := hS1.fixed.nn
  have hlab1 := hS1.arrays.lab
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k ≤ n ∧ PTree.get dense.id.«i» le' = some (.Vint (ir k)) ∧
    ArrayAt m' .Mint32 S.bl S.lb (copyFrom (ints st.lab) (ints st.canonlab) k) n ∧
    Unch m1 m' (· = S.bl) ∧ (∀ z, Mem.valid_block m1 z → Mem.valid_block m' z) ∧
    (∀ x, x ≠ dense.id.«i» → PTree.get x le' = PTree.get x le)
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) => k < n ∧
    PTree.get dense.id.«i» le' = some (.Vint (ir k)) ∧
    ArrayAt m' .Mint32 S.bl S.lb (copyFrom (ints st.lab) (ints st.canonlab) (k + 1)) n ∧
    Unch m1 m' (· = S.bl) ∧ (∀ z, Mem.valid_block m1 z → Mem.valid_block m' z) ∧
    (∀ x, x ≠ dense.id.«i» → PTree.get x le' = PTree.get x le)
  have nN : E.n ≠ S.bl := by sep_ne hd1
  have nC : E.nautyCanonlab ≠ S.bl := by sep_ne hd1
  have nCL : S.bCL ≠ S.bl := by sep_ne hd1
  refine wp_forLoopC (Inv := Inv) (Mid := Mid) dense.id.«i» _ rfl _ n (by omega) ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, -, hu, -, -⟩
    refine ⟨hk, hi, ?_⟩
    rw [Exec.evalExpr, show Exec.evalExpr ge (nEnv bI) le' m' (Refine.tv dense.id.«i») = _ from hi,
      Search.eval_gint (e := nEnv bI) rfl E.find_n (hN1.unch hu nN)]
    simp only [typeof, cop]
    rw [ir_lt (a := k) (b := n) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    simp
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, ?_, Unch.refl _ _, fun _ h => h,
      fun x hx => temps_gso _ _ hx⟩
    have : copyFrom (ints st.lab) (ints st.canonlab) 0 = ints st.lab :=
      funext fun j => by simp [copyFrom]
    rw [this]; exact hlab1
  · rintro k le' m' hk ⟨-, hi, harr', hu, hg, ho⟩
    wp_step; wp_step
    refine wp_storeE harr' (by omega) (Refine.pi dense.id.«lab»)
      (by simp only [Exec.evalExpr, Refine.pi, ho dense.id.«lab» (by decide), hlab]) rfl
      (Refine.tv dense.id.«i») k hk hi rfl _ (st.canonlab[k]! : Int)
      (eval_canonlabAtG (e := nEnv bI) rfl (by rw [hu.load _ _ _ nC]; exact hpCL)
        (harrCL.unch hu nCL) hS1.nlt hi hk) rfl ?_
    intro m'' harr'' hu'' hg''
    rw [show (Vint (ir (st.canonlab[k]! : Int))) = ints st.canonlab k from rfl, copyFrom_succ]
      at harr''
    exact ⟨rfl, hk, hi, harr'', hu.trans hu'', fun z hz => hg'' _ (hg z hz), ho⟩
  · rintro k le' m' ⟨hk, hi, harr', hu, hg, ho⟩
    refine ⟨hi, by omega, temps_gss _ _ _, harr', hu, hg, fun x hx => ?_⟩
    rw [temps_gso _ _ hx, ho x hx]
  · rintro le2 m2 ⟨-, hi2, harr2, hu2, hg2, ho2⟩
    simp only [seqPost, Post.after, E0_append]
    have hsb : S.sb = 0 := by simp [SLoc.sb, hso]
    have hblS : S.bl ∈ S.blocksG D.toDispatchRep gl cl :=
      SLoc.mem_blocksG_of D.toDispatchRep (.inr (.inl (by simp)))
    have hbstS : S.bst ∈ S.blocksG D.toDispatchRep gl cl :=
      SLoc.mem_blocksG_of D.toDispatchRep (.inr (.inl (by simp)))
    have ld : ∀ z ∈ [E.invarsuclevel, E.invapplics, E.invsuccesses], ∀ chunk o,
        Mem.load chunk m2 z o = Mem.load chunk m z o := fun z hz chunk o => by
      obtain ⟨h1, h2, h3⟩ := hout z hz
      rw [hu2.load _ _ _ (fun e => h1 (by rw [e]; exact hblS)), hstep1.keepOut h1 h2 h3]
    have hout' := hout
    simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
      and_true] at hout'
    obtain ⟨-, ⟨oA, -, -⟩, ⟨oS, -, -⟩⟩ := hout'
    have nStats : E.stats ≠ S.bl := by sep_ne hd1
    have nbst : S.bst ≠ S.bl := by sep_ne hd1
    have hR2 : Mem.range_perm m2 S.bst (zOfInt 0) (zOfInt 88) .Cur .Freeable := by
      have := (hS1.stats.unch hu2 nbst).perm; rw [hsb] at this; simpa using this
    refine wp_statsTailG hso (hS1.fixed.stats.unch hu2 nStats) hR2
      (fun e => oA (e ▸ hbstS)) (fun e => oS (e ▸ hbstS)) (by sep_ne hd1)
      (let ⟨w, hw⟩ := hIL; ⟨w, ((ld _ (by simp) .Mint32 (zOfInt 0)).trans hw)⟩)
      (let ⟨w, hw⟩ := hIA; ⟨w, ((ld _ (by simp) .Mint64 (zOfInt 0)).trans hw)⟩)
      (let ⟨w, hw⟩ := hIS; ⟨w, ((ld _ (by simp) .Mint64 (zOfInt 0)).trans hw)⟩) ?_
    intro le5 m5 hu5 hsT hg5 ho5
    have hu3 : Unch m1 m5 (· ∈ [S.bl, S.bst]) :=
      (hu2.mono fun z hz => by simp [hz]).trans (hu5.mono fun z hz => by simp [hz])
    have hlabF : ArrayAt m5 .Mint32 S.bl S.lb (ints st.canonlab) n := by
      have h5 := harr2.unch hu5 nbst.symm
      refine ⟨h5.base_nonneg, h5.fits, fun j hj => ?_, h5.writable⟩
      have := h5.load j hj
      simpa [copyFrom, hj] using this
    obtain ⟨hS5, hst5⟩ := SearchAtG.postLabG C hS1 hu3 (fun z hz => hg5 _ (hg2 _ hz)) hlabF
      { hsT (hS1.stats.unch hu2 nbst) with } hcl hcs
    have hbc : ∀ z ∈ D.canonBlocks cl S.bc, ¬ z ∈ [S.bl, S.bst] := by
      intro z hz hzL
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzL
      rcases hzL with rfl | rfl
      · exact hS1.canon_ne hz (.inr (.inl (by simp))) rfl
      · exact hS1.canon_ne hz (.inr (.inl (by simp))) rfl
    refine hQ _ m5 hS5 (D.canon_unch hG1 hu3 hbc) (hstep1.trans hst5) ?_
    intro x h1 h2
    rw [ho5 x h2, ho2 x h1]

end Generic


/-! ### Dense nauty -/

/-- The search state after `updatecan`. -/
abbrev canonState (ctx : Ctx n) (st : Search n) : Search n :=
  { st with canong := updatecan ctx st.canong st.canonlab st.samerows }

/-- The search state after `postIf`: `canong` updated and `lab = canonlab`. -/
abbrev postState (ctx : Ctx n) (st : Search n) : Search n :=
  { canonState ctx st with lab := st.canonlab }

/-- `nauty()` after the search returned, up to the release (`tPost` up to `tFree`). -/
theorem wp_tPost {Q : Post} {le : temp_env} {m : mem} {st : Search n} {nsp : Bool} {v : Nat}
    (hs : SearchAt m S ctx st false nsp) (hvm : ∀ z ∈ S.blocks, Mem.valid_block m z)
    (hso : S.sofs = Ptrofs.zero)
    (hret : PTree.get dense.id.«retval» le = some (.Vint (ir v))) (hv : v ≤ 1)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ u < n, ∃ i < n, st.canonlab[i]! = u)
    (hout : ∀ z ∈ [Block.invarsuclevel, Block.invapplics, Block.invsuccesses],
      z ∉ S.blocks ∧ Mem.valid_block m z ∧ ¬ IsWork m z)
    (hIL : ∃ w, Mem.load .Mint32 m Block.invarsuclevel (zOfInt 0) = some (.Vint w))
    (hIA : ∃ w, Mem.load .Mint64 m Block.invapplics (zOfInt 0) = some (.Vlong w))
    (hIS : ∃ w, Mem.load .Mint64 m Block.invsuccesses (zOfInt 0) = some (.Vlong w))
    (hQ : ∀ le' m', SearchAt m' S ctx (postState ctx st) false nsp →
      (∃ cw, GraphAt m' S.bc S.cofs cw (updatecan ctx st.canong st.canonlab st.samerows) S.M) →
      SStep m m' S →
      (∀ x, x ≠ dense.id.«i» → x ≠ idOf 736 → PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tFree Q (nEnv bI) le' m') :
    Wp xi ge dense.fn.nauty Nauty.tPost Q (nEnv bI) le m := by
  have hgw := hs.gw
  refine wp_tPostG NautyVerified.Proofs.Dispatch.dense denseClassifier hs.toG
    (fun z hz => hvm z (SLoc.mem_blocksG.1 hz)) hso hret hv hlab hcl hcs trivial
    (fun z hz => let ⟨h1, h2, h3⟩ := hout z hz
      ⟨fun h => h1 (SLoc.mem_blocksG.1 h), h2, fun h => h3 (isWork_dense.1 h)⟩) hIL hIA hIS ?_
  intro le' m' hS' hC' hSt' hle'
  obtain ⟨cw, hrows⟩ := hC'
  exact hQ le' m' (hS'.dense hgw) ⟨cw, ⟨hrows.arr, hrows.rep⟩⟩
    ⟨SFrameG.dense hSt'.1, workMonoG_dense hSt'.2⟩ hle'

end NautyVerified.Proofs.Top
