import NautyVerified.Proofs.Top.NautyRoot
import NautyVerified.Proofs.Search.Processnode.Canon
import NautyVerified.Logic.Grow

/-!
# `nauty()` after the search (`tPost` up to `tFree`)

The root call returns a level (0 or 1), so neither error branch
(`NAUTY_ABORTED`, `NAUTY_KILLED`) is taken. With `getcanon` set,
`(*dispatch.updatecan)(g, canong, canonlab, samerows, m, n)` fills every row
of `canong` from the best labelling (`wp_topUpdatecan`), `lab` receives
`canonlab` (`wp_copyLab`), and `stats->invarsuclevel`, `invapplics` and
`invsuccesses` are stored.

Afterwards memory holds the search state with `lab = canonlab` and `canong`
updated (`postState`), and `canong` holds all `n` rows of HexGraphIso's
`updatecan`.
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

kernel_rfl field_statsInvapplics : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«invapplics» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 64)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_statsInvsuccesses : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«invsuccesses» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 72)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_statsInvarsuclevel : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«invarsuclevel» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 80)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

variable {xi : ExternalCalls}

variable {n : Nat} {S : SLoc} {ctx : Ctx n}

/-- The search state after `updatecan`. -/
abbrev canonState (ctx : Ctx n) (st : Search n) : Search n :=
  { st with canong := updatecan ctx st.canong st.canonlab st.samerows }

/-- `(*dispatch.updatecan)(g, canong, canonlab, samerows, m, n)` in `nauty()`. -/
theorem wp_topUpdatecan {Q : Post} {le : temp_env} {m : mem} {st : Search n} {nsp : Bool}
    (hs : SearchAt m S ctx st false nsp) (hvm : ∀ z ∈ S.blocks, Mem.valid_block m z)
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ v < n, ∃ i < n, st.canonlab[i]! = v)
    (hQ : ∀ m', SearchAt m' S ctx (canonState ctx st) false nsp →
      (∃ cw, GraphAt m' S.bc S.cofs cw (updatecan ctx st.canong st.canonlab st.samerows) S.M) →
      SStep m m' S → Keep m m' S.bc → Q.normal E0 (nEnv bI) le m') :
    Wp xi ge dense.fn.nauty Processnode.updatecanCall Q (nEnv bI) le m := by
  have hd := hs.distinct
  have hinv := hs.inv
  have hn0 := hs.n0
  have hnlt := hs.nlt
  obtain ⟨cw, hca, hcr⟩ := hs.arrays.canong.arr
  obtain ⟨cW, bW, cS, bS, cB, bB, cN, bN, dW, dS, dB, dN, nW, nS, nB, nN, pWS, pWB, pSB, pNW,
    pNS, pNB⟩ := hs.work.arr
  have hcCL : 0 < S.capCL := by have := hs.dyns.capCL; omega
  refine wp_call (vf := .Vptr Block.updatecanFn Ptrofs.zero)
    (targs := [tptr tulong, tptr tulong, tptr tint, tint, tint, tint]) (tres := .Tvoid)
    (cc := cc_default) (vargs := [.Vptr S.bg S.gofs, .Vptr S.bc S.cofs, .Vptr S.bCL Ptrofs.zero,
      .Vint (ir st.samerows), .Vint (ir S.M), .Vint (ir n)]) _ _
    (Satisfies.grow (Updatecan.updatecan_satisfies S.bg S.gofs S.gw ctx.g S.bc S.cofs cw st.canong
      S.bCL Ptrofs.zero st.canonlab st.samerows S.M cW bW)) rfl
    (Processnode.eval_dispatch rfl field_dUpdatecan rfl (by decide) (by decide)
      hs.fixed.dUpdatecan)
    ?_ (by simp [Genv.find_funct, funct_updatecanFn]) Processnode.type_updatecan ?_ ?_
  · simp only [Exec.evalExprlist,
      eval_gptr (ty := tptr tulong) (e := nEnv bI) rfl find_g rfl hs.fixed.g,
      eval_gptr (ty := tptr tulong) (e := nEnv bI) rfl find_canong rfl hs.fixed.canong,
      eval_gptr (ty := tptr tint) (e := nEnv bI) rfl find_nautyCanonlab rfl
        ⟨hs.dyns.canonlab.ptr hcCL, hs.dyns.canonlab.bpW⟩,
      Search.eval_gint (e := nEnv bI) rfl find_samerows hs.scalars.samerows,
      Search.eval_gint (e := nEnv bI) rfl find_m hs.fixed.mm,
      Search.eval_gint (e := nEnv bI) rfl find_n hs.fixed.nn, typeof, cop]
  · have vbg : Mem.valid_block m S.bg := hvm _ (by simp [SLoc.blocks])
    have vbc : Mem.valid_block m S.bc := hvm _ (by simp [SLoc.blocks])
    have vbl : Mem.valid_block m S.bCL := hvm _ (by simp [SLoc.blocks])
    refine ⟨rfl, hs.arrays.graph, ⟨hca, hcr⟩, hinv.canongSize, hs.arrays.canonlab,
      hinv.canonlabSize, hcl, hcs, dW, hs.tables.left, hs.tables.nautilBit, vbg, vbc, vbl,
      by sep_ne hd, by sep_ne hd, ?_, ?_, hinv.samerows, hs.M1, hs.Mlt, hs.nM⟩
    · rintro z (rfl | rfl | rfl | rfl) <;> exact ⟨by sep_ne hd, by sep_ne hd, by sep_ne hd⟩
    · intro hc
      have hb := nW hc
      refine ⟨fun e => hb (e ▸ ?_), fun e => hb (e ▸ ?_), fun e => hb (e ▸ ?_), fun e => hb (e ▸ ?_),
        fun e => hb (e ▸ ?_)⟩ <;> simp [SLoc.blocks]
  · rintro t r m' ⟨⟨rfl, cw', cap', b', hg', hD', hcap, hrel, hu, hkc⟩, hv⟩
    let W := fun z => z = S.bc ∨ z = Block.naugraphWorkpermSz ∨ z = Block.naugraphWorkperm ∨
      (0 < cW ∧ z = bW) ∨ (¬ Mem.valid_block m b' ∧ z = b')
    have notW : ∀ z ∈ S.blocks, z ≠ S.bc → z ≠ Block.naugraphWorkpermSz →
        z ≠ Block.naugraphWorkperm → ¬ W z := by
      rintro z hz h1 h2 h3 (e | e | e | ⟨hc, e⟩ | ⟨hnv, e⟩)
      · exact h1 e
      · exact h2 e
      · exact h3 e
      · exact nW hc (e ▸ hz)
      · exact hnv (e ▸ hvm z hz)
    have hWa : ∀ z, W z → (z ∈ S.blocks ∧ z ∉ [Block.naugraphWorkset, Block.naugraphWorksetSz,
        Block.naugraphBucket, Block.naugraphBucketSz, Block.nautilWorkperm,
        Block.nautilWorkpermSz]) ∨ (0 < cW ∧ z = bW) ∨ (z ∉ S.blocks ∧ ¬ IsWork m z) := by
      rintro z (rfl | rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩)
      · exact .inl ⟨by simp [SLoc.blocks], by sep_notin hd⟩
      · exact .inl ⟨by simp [SLoc.blocks], by decide⟩
      · exact .inl ⟨by simp [SLoc.blocks], by decide⟩
      · exact .inr (.inl ⟨hc, rfl⟩)
      · exact .inr (.inr ⟨fun hz => hnv (hvm _ hz), fun hw => hnv hw.valid⟩)
    obtain ⟨hwm, hwk⟩ := SearchAt.afterWP hs hvm dW hu hWa hD' hrel
    have hS : ∀ z ∈ S.blocks, W z → z ∈ S.wr ∨ z ∈ workG := by
      rintro z hz (rfl | rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩)
      · exact .inl (by simp [SLoc.wr, wrG, SLoc.wrV])
      · exact .inr (by decide)
      · exact .inr (by decide)
      · exact absurd hz (nW hc)
      · exact absurd (hvm _ hz) hnv
    have nw := fun z (hz : z ∈ S.blocks) h1 h2 h3 => notW z hz h1 h2 h3
    have hS' : SearchAt m' S ctx (canonState ctx st) false nsp := by
      refine hs.rebuildW hu hS ?_ ((hs.scalars.unch hu (by all_notW hd, notW)).cast rfl)
        ((hs.stats.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd)
          (by sep_ne hd))).cast rfl) ?_ { hinv with canongSize := by rw [updatecan_size]; exact hinv.canongSize }
        hwk
      · intro z hz
        exact Keep.unch hu (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
      · exact hs.arrays.set hu
          (hs.arrays.lab.unch hu (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
          (hs.arrays.ptn.unch hu (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
          (hs.arrays.orbits.unch hu (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
          (hs.arrays.active' hu (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
          (hs.arrays.fixedpts' hu (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
          (hs.arrays.workperm' hu (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
          (hs.arrays.firstlab.unch hu (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
          (hs.arrays.canonlab.unch hu (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
          (hs.arrays.firstcode.unch hu (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
          (hs.arrays.canoncode.unch hu (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
          (hs.arrays.firsttc.unch hu (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
          ⟨⟨cw', hg'.arr, fun v hv => hg'.rep v (Nat.lt_of_lt_of_le hv hinv.samerows)⟩⟩
          (hs.arrays.autos.unch hu (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
            (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
          (nw _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
    refine hQ m' hS' ⟨cw', hg'⟩ ⟨⟨hu.mono fun z hz => ?_, hv⟩, hwm⟩ hkc
    rcases hz with rfl | rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩
    · exact .inl (Processnode.SLoc.wr_chg hd (by simp [SLoc.wr, wrG, SLoc.wrV]))
    · exact .inl ⟨by simp [SLoc.blocks], by sep_ne hd, by sep_ne hd⟩
    · exact .inl ⟨by simp [SLoc.blocks], by sep_ne hd, by sep_ne hd⟩
    · exact .inr (.inr (.inl ⟨cW, hc, dW⟩))
    · exact .inr (.inl hnv)

/-- A store to `statsblk` at offset 64 or beyond keeps `Stats`. -/
theorem Stats.storeHi {m m' : mem} {st : Search n} {pre : Bool} (h : Stats m S st pre)
    {c : memory_chunk} {off : Int} {w : val}
    (hst : Mem.store c m S.bst (zOfInt (S.sb + off)) w = some m') (hoff : 64 ≤ off) :
    Stats m' S st pre :=
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

/-- `canonlab[x]` for `x` holding `c < n`. -/
theorem eval_canonlabAt {e : env} {le : temp_env} {m : mem} {bC : block} {cl : Array Nat}
    (hge : PTree.get dense.id.«nauty:canonlab» e = none)
    (hp : Mem.load .Mint64 m Block.nautyCanonlab (zOfInt 0) = some (.Vptr bC Ptrofs.zero))
    (harr : ArrayAt m .Mint32 bC 0 (ints cl) n) (hnl : n < 1073741824)
    {x : ident} {c : Nat} (hx : PTree.get x le = some (.Vint (ir c))) (hc : c < n) :
    Exec.evalExpr ge e le m (.Ederef (.Ebinop .Oadd (.Evar dense.id.«nauty:canonlab» (tptr tint))
      (Refine.tv x) (tptr tint)) tint) = some (.Vint (ir (cl[c]! : Int))) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, find_nautyCanonlab, Exec.derefLoc,
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

/-- The search state after `postIf`: `canong` updated and `lab = canonlab`. -/
abbrev postState (ctx : Ctx n) (st : Search n) : Search n :=
  { canonState ctx st with lab := st.canonlab }

/-- A block outside `S` that is valid and not a work block survives a search step. -/
theorem SStep.keepOut {m m' : mem} (h : SStep m m' S) {z : block} (hz : z ∉ S.blocks)
    (hv : Mem.valid_block m z) (hw : ¬ IsWork m z) {chunk : memory_chunk} {o : Z} :
    Mem.load chunk m' z o = Mem.load chunk m z o :=
  h.1.1.load _ _ _ (by rintro (h1 | h1 | h1); exact hz h1.1; exact h1 hv; exact hw h1)

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

/-- The three `statsblk` stores after the canonical labelling. -/
theorem wp_statsTail {Q : Post} {le : temp_env} {m : mem}
    (hso : S.sofs = Ptrofs.zero) (hP : PtrAt m Search.Block.stats (.Vptr S.bst S.sofs))
    (hR : Mem.range_perm m S.bst (zOfInt 0) (zOfInt 88) .Cur .Freeable)
    (nA : Block.invapplics ≠ S.bst) (nS' : Block.invsuccesses ≠ S.bst)
    (nSt : S.bst ≠ Search.Block.stats)
    (hIL : ∃ w, Mem.load .Mint32 m Block.invarsuclevel (zOfInt 0) = some (.Vint w))
    (hIA : ∃ w, Mem.load .Mint64 m Block.invapplics (zOfInt 0) = some (.Vlong w))
    (hIS : ∃ w, Mem.load .Mint64 m Block.invsuccesses (zOfInt 0) = some (.Vlong w))
    (hQ : ∀ le' m', Unch m m' (· = S.bst) →
      (∀ {k : Nat} {st : Search k} {pre : Bool}, Stats m S st pre → Stats m' S st pre) →
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
    show PTree.get dense.id.«nauty:invarsuclevel» (nEnv bI) = none from rfl, find_invarsuclevel,
    Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hL2, typeof, cop]
  split <;> (wp_step; wp_step; apply wp_set_eval; simp only [Exec.evalExpr, Exec.lvalOfVar,
    show PTree.get dense.id.«nauty:invarsuclevel» (nEnv bI) = none from rfl, find_invarsuclevel,
    Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hL2, typeof, cop])
  all_goals
    refine Search.wp_statsStore (S := S) (ty := tint) (chunk := .Mint32) (off := 80) rfl
      field_statsInvarsuclevel rfl hP (by decide) (by rw [hsb]; decide)
      (hva2 .Mint32 80 (by decide) (by decide) ⟨zOfInt 20, rfl⟩)
      (by simp only [Exec.evalExpr, temps_gss]; rfl) rfl ?_
    intro m3 hs3
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine Search.wp_statsStore (S := S) (ty := tulong) (chunk := .Mint64) (off := 64) rfl
      field_statsInvapplics rfl (hP.unch (Unch.store hs3 rfl) nSt) (by decide)
      (by rw [hsb]; decide)
      (Mem.store_valid_access_1 _ _ _ _ _ _ hs3 _ _ _ _
        (hva2 .Mint64 64 (by decide) (by decide) ⟨zOfInt 8, rfl⟩))
      (by simp only [Exec.evalExpr, Exec.lvalOfVar,
            show PTree.get dense.id.«nauty:invapplics» (nEnv bI) = none from rfl, find_invapplics,
            Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
            show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
            Mem.load_store_other _ _ _ _ _ _ hs3 _ _ _ (.inl nA), hA2]; rfl) rfl ?_
    intro m4 hs4
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    refine Search.wp_statsStore (S := S) (ty := tulong) (chunk := .Mint64) (off := 72) rfl
      field_statsInvsuccesses rfl
      ((hP.unch (Unch.store hs3 rfl) nSt).unch (Unch.store hs4 rfl) nSt)
      (by decide) (by rw [hsb]; decide)
      (Mem.store_valid_access_1 _ _ _ _ _ _ hs4 _ _ _ _ (Mem.store_valid_access_1 _ _ _ _ _ _ hs3 _ _ _ _
        (hva2 .Mint64 72 (by decide) (by decide) ⟨zOfInt 9, rfl⟩)))
      (by simp only [Exec.evalExpr, Exec.lvalOfVar,
            show PTree.get dense.id.«nauty:invsuccesses» (nEnv bI) = none from rfl, find_invsuccesses,
            Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
            show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
            Mem.load_store_other _ _ _ _ _ _ hs4 _ _ _ (.inl nS'),
            Mem.load_store_other _ _ _ _ _ _ hs3 _ _ _ (.inl nS'), hS2]; rfl) rfl ?_
    intro m5 hs5
    simp only [seqPost, Post.after, E0_append]
    refine hQ _ m5 ((((Unch.store hs3 rfl).trans (Unch.store hs4 rfl)).trans (Unch.store hs5 rfl)).mono
      fun z hz => hz.symm)
      (fun h => Stats.storeHi (Stats.storeHi (Stats.storeHi h hs3 (by decide)) hs4 (by decide)) hs5
        (by decide))
      (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hs5 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hs4 _
          (Mem.store_valid_block_1 _ _ _ _ _ _ hs3 _ hz)))
      (fun x hx => temps_gso _ _ hx)

/-- `SearchAt` after the copy of `canonlab` into `lab` and the `statsblk` stores. -/
theorem SearchAt.postLab {m1 m5 : mem} {st : Search n} {nsp : Bool}
    (hS1 : SearchAt m1 S ctx (canonState ctx st) false nsp) (hu3 : Unch m1 m5 (· ∈ [S.bl, S.bst]))
    (hlabF : ArrayAt m5 .Mint32 S.bl S.lb (ints st.canonlab) n)
    (hst5 : Stats m5 S (postState ctx st) false)
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ u < n, ∃ i < n, st.canonlab[i]! = u) :
    SearchAt m5 S ctx (postState ctx st) false nsp := by
  have hd1 := hS1.distinct
  have nL : ∀ z ∈ S.blocks, z ≠ S.bl → z ≠ S.bst → ¬ z ∈ [S.bl, S.bst] := by
    intro z _ h1 h2 h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with h | h; exact h1 h; exact h2 h
  have hsc3 : ∀ z ∈ [Block.gcaFirst, Block.gcaCanon, Block.noncheaplevel, Block.allsamelevel,
      Block.eqlevFirst, Block.eqlevCanon, Block.compCanon, Block.samerows, Block.canonlevel,
      Block.stabvertex, Block.cosetindex, Block.needshortprune], ¬ z ∈ [S.bl, S.bst] := by
    intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with h|h|h|h|h|h|h|h|h|h|h|h <;>
      (subst h; exact nL _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1))
  have hLw : ∀ z ∈ [S.bl, S.bst], z ∈ S.wr := by
    intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl <;> simp [SLoc.wr, SLoc.wrV]
  refine hS1.rebuild hu3 hLw ?_ ((hS1.scalars.unch hu3 hsc3).cast rfl) hst5 ?_
    { hS1.inv with labSize := hS1.inv.canonlabSize, labSmall := hcl, labSurj := hcs }
  · intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Alloc.Keep.unch hu3 (nL _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1))
  · have ha := hS1.arrays
    have nw := fun z (hz : z ∈ S.blocks) h1 h2 => nL z hz h1 h2
    exact ha.set hu3 hlabF
      (ha.ptn.unch hu3 (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)))
      (ha.orbits.unch hu3 (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)))
      (ha.active' hu3 (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)))
      (ha.fixedpts' hu3 (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)))
      (ha.workperm' hu3 (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)))
      (ha.firstlab.unch hu3 (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)))
      (ha.canonlab.unch hu3 (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)))
      (ha.firstcode.unch hu3 (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)))
      (ha.canoncode.unch hu3 (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)))
      (ha.firsttc.unch hu3 (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)))
      (ha.canong.unch hu3 (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)))
      (ha.autos.unch hu3 (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1))
        (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)))
      (nw _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1))

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
  have hd := hs.distinct
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
  rw [Search.eval_gint (e := nEnv bI) rfl find_getcanon hs.fixed.getcanon]
  simp only [typeof, cop]
  rw [ite_eq_left (by decide)]
  wp_step; wp_step; wp_step
  refine wp_topUpdatecan hs hvm hcl hcs ?_
  intro m1 hS1 hG1 hstep1 hk1
  simp only [seqPost, Post.after, E0_append]
  have hd1 := hS1.distinct
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
  have nN : Search.Block.n ≠ S.bl := by sep_ne hd1
  have nC : Block.nautyCanonlab ≠ S.bl := by sep_ne hd1
  have nCL : S.bCL ≠ S.bl := by sep_ne hd1
  refine wp_forLoopC (Inv := Inv) (Mid := Mid) dense.id.«i» _ rfl _ n (by omega) ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, -, hu, -, -⟩
    refine ⟨hk, hi, ?_⟩
    rw [Exec.evalExpr, show Exec.evalExpr ge (nEnv bI) le' m' (Refine.tv dense.id.«i») = _ from hi,
      Search.eval_gint (e := nEnv bI) rfl Search.find_n (hN1.unch hu nN)]
    simp only [typeof, cop]
    rw [ir_lt (a := k) (b := n) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    simp
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, ?_, Unch.refl _ _, fun _ h => h,
      fun x hx => temps_gso _ _ hx⟩
    have : copyFrom (ints st.lab) (ints st.canonlab) 0 = ints st.lab := funext fun j => by simp [copyFrom]
    rw [this]; exact hlab1
  · rintro k le' m' hk ⟨-, hi, harr', hu, hg, ho⟩
    wp_step; wp_step
    refine wp_storeE harr' (by omega) (Refine.pi dense.id.«lab») (by simp only [Exec.evalExpr, Refine.pi, ho dense.id.«lab» (by decide), hlab]) rfl
      (Refine.tv dense.id.«i») k hk hi rfl _ (st.canonlab[k]! : Int)
      (eval_canonlabAt (e := nEnv bI) rfl (by rw [hu.load _ _ _ nC]; exact hpCL) (harrCL.unch hu nCL) hS1.nlt hi hk) rfl ?_
    intro m'' harr'' hu'' hg''
    rw [show (Vint (ir (st.canonlab[k]! : Int))) = ints st.canonlab k from rfl, copyFrom_succ] at harr''
    exact ⟨rfl, hk, hi, harr'', hu.trans hu'', fun z hz => hg'' _ (hg z hz), ho⟩
  · rintro k le' m' ⟨hk, hi, harr', hu, hg, ho⟩
    refine ⟨hi, by omega, temps_gss _ _ _, harr', hu, hg, fun x hx => ?_⟩
    rw [temps_gso _ _ hx, ho x hx]
  · rintro le2 m2 ⟨-, hi2, harr2, hu2, hg2, ho2⟩
    simp only [seqPost, Post.after, E0_append]
    have hsb : S.sb = 0 := by simp [SLoc.sb, hso]
    have hblS : S.bl ∈ S.blocks := by simp [SLoc.blocks]
    have hbstS : S.bst ∈ S.blocks := by simp [SLoc.blocks]
    have ld : ∀ z ∈ [Block.invarsuclevel, Block.invapplics, Block.invsuccesses], ∀ chunk o,
        Mem.load chunk m2 z o = Mem.load chunk m z o := fun z hz chunk o => by
      obtain ⟨h1, h2, h3⟩ := hout z hz
      rw [hu2.load _ _ _ (fun e => h1 (by rw [e]; exact hblS)), SStep.keepOut hstep1 h1 h2 h3]
    have hout' := hout
    simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at hout'
    obtain ⟨-, ⟨oA, -, -⟩, ⟨oS, -, -⟩⟩ := hout'
    have nStats : Search.Block.stats ≠ S.bl := by sep_ne hd1
    have nbst : S.bst ≠ S.bl := by sep_ne hd1
    have hR2 : Mem.range_perm m2 S.bst (zOfInt 0) (zOfInt 88) .Cur .Freeable := by
      have := (hS1.stats.unch hu2 nbst).perm; rw [hsb] at this; simpa using this
    refine wp_statsTail hso (hS1.fixed.stats.unch hu2 nStats) hR2
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
    have hS5 := SearchAt.postLab hS1 hu3 hlabF ((hsT (hS1.stats.unch hu2 nbst)).cast rfl) hcl hcs
    have nL : ∀ z ∈ S.blocks, z ≠ S.bl → z ≠ S.bst → ¬ z ∈ [S.bl, S.bst] := by
      intro z _ h1 h2 h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with h | h; exact h1 h; exact h2 h
    obtain ⟨cw, hG⟩ := hG1
    have hbcL := nL S.bc (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)
    have hwG : ∀ z ∈ [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
        Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
        Block.nautilWorkperm, Block.nautilWorkpermSz], ¬ z ∈ [S.bl, S.bst] := by
      intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact nL _ (by simp [SLoc.blocks]) (by sep_ne hd1) (by sep_ne hd1)
    refine hQ _ m5 hS5 ⟨cw, ⟨hG.arr.unch hu3 hbcL, hG.rep⟩⟩
      (SStep.trans hstep1 ⟨⟨hu3.mono fun z hz => .inl (Processnode.SLoc.wr_chg hd1 (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          rcases hz with rfl | rfl <;> simp [SLoc.wr, SLoc.wrV])), fun z hz => hg5 _ (hg2 _ hz)⟩,
        fun z hz => .inl (IsWork.back hS1 hu3 hwG hz)⟩) ?_
    intro x h1 h2
    rw [ho5 x h2, ho2 x h1]

end NautyVerified.Proofs.Top
