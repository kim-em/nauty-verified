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
          rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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

end NautyVerified.Proofs.Top
