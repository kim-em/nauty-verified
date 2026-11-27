import NautyVerified.Proofs.Search.Processnode.Calls
import NautyVerified.Logic.Grow

/-!
# `processnode`'s comparison with the best leaf

`wp_updatecan`: `(*dispatch.updatecan)(g, canong, canonlab, samerows, m, n)`
leaves `canong` holding HexGraphIso's `updatecan`.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (Keep DynAt)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

/-- `sr` holds `v`. -/
abbrev SrAt (m : mem) (bsr : block) (v : Int) : Prop :=
  ArrayAt m .Mint32 bsr (intOfZ (Ptrofs.unsigned Ptrofs.zero)) (fun _ => .Vint (ir v)) 1

/-- A pointer global. -/
theorem eval_gptr {e : env} {le : temp_env} {m : mem} {g : ident} {b : block} {v : val}
    {ty : type} (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some b)
    (hacc : access_mode ty = .By_value .Mint64) (h : PtrAt m b v) :
    Exec.evalExpr ge e le m (.Evar g ty) = some v := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, hg, Exec.derefLoc, hacc, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]
  exact h.load

abbrev updatecanCall : statement :=
  .Scall none
    (.Ederef
      (.Efield (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr)) dense.id.«updatecan»
        (tptr (tfun [(tptr tulong), (tptr tulong), (tptr tint), tint, tint, tint] .Tvoid)))
      (tfun [(tptr tulong), (tptr tulong), (tptr tint), tint, tint, tint] .Tvoid))
    [(.Evar dense.id.«nauty:g» (tptr tulong)),
     (.Evar dense.id.«nauty:canong» (tptr tulong)),
     (.Evar dense.id.«nauty:canonlab» (tptr tint)),
     (.Evar dense.id.«nauty:samerows» tint),
     (.Evar dense.id.«nauty:m» tint),
     (.Evar dense.id.«nauty:n» tint)]

variable {n : Nat} {m₀ m₁ m : mem} {S : SLoc} {ctx : Ctx n} {e : env} {bsr : block}
  {st : Search n} {nsp : Bool}

theorem wp_updatecan {f : function} {Q : Post} {le : temp_env} (c : PCtx m₀ m₁ S e bsr)
    (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ v < n, ∃ i < n, st.canonlab[i]! = v)
    (hQ : ∀ m', PAt m₀ m₁ m' S ctx bsr
        { st with canong := updatecan ctx st.canong st.canonlab st.samerows } nsp →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Q.normal E0 e le m') :
    Wp xi ge f updatecanCall Q e le m := by
  have hs := h.search
  have hd := hs.distinct
  have hinv := hs.inv
  have hn0 := hs.n0
  have hnlt := hs.nlt
  obtain ⟨cw, hca, hcr⟩ := hs.arrays.canong.arr
  obtain ⟨cW, bW, cS, bS, cB, bB, cN, bN, dW, dS, dB, dN, nW, nS, nB, nN, pWS, pWB, pSB, pNW,
    pNS, pNB⟩ := hs.work.arr
  have hcCL : 0 < S.capCL := by have := hs.dyns.capCL; omega
  have hvm : ∀ z ∈ S.blocks, Mem.valid_block m z := fun z hz => h.frame.2 _ (c.valid0 z hz)
  have hMn : 0 < S.M * n := Nat.mul_pos hs.M1 hn0
  refine wp_call (vf := .Vptr Block.updatecanFn Ptrofs.zero)
    (targs := [tptr tulong, tptr tulong, tptr tint, tint, tint, tint]) (tres := .Tvoid)
    (cc := cc_default) (vargs := [.Vptr S.bg S.gofs, .Vptr S.bc S.cofs, .Vptr S.bCL Ptrofs.zero,
      .Vint (ir st.samerows), .Vint (ir S.M), .Vint (ir n)]) _ _
    (Satisfies.grow (Updatecan.updatecan_satisfies S.bg S.gofs S.gw ctx.g S.bc S.cofs cw st.canong S.bCL Ptrofs.zero
      st.canonlab st.samerows S.M cW bW)) rfl
    (eval_dispatch (c.eg _ (by decide)) field_dUpdatecan rfl (by decide) (by decide)
      hs.fixed.dUpdatecan)
    ?_ (by simp [Genv.find_funct, funct_updatecanFn]) type_updatecan ?_ ?_
  · simp only [Exec.evalExprlist,
      eval_gptr (ty := tptr tulong) (c.eg _ (by decide)) find_g rfl hs.fixed.g,
      eval_gptr (ty := tptr tulong) (c.eg _ (by decide)) find_canong rfl hs.fixed.canong,
      eval_gptr (ty := tptr tint) (c.eg _ (by decide)) find_nautyCanonlab rfl ⟨hs.dyns.canonlab.ptr hcCL,
        hs.dyns.canonlab.bpW⟩,
      eval_gint (c.eg _ (by decide)) find_samerows hs.scalars.samerows,
      eval_gint (c.eg _ (by decide)) find_m hs.fixed.mm,
      eval_gint (c.eg _ (by decide)) find_n hs.fixed.nn, typeof, cop]
  · have vbg : Mem.valid_block m S.bg := hvm _ (by simp [SLoc.blocks])
    have vbc : Mem.valid_block m S.bc := hvm _ (by simp [SLoc.blocks])
    have vbl : Mem.valid_block m S.bCL := hvm _ (by simp [SLoc.blocks])
    have wnb : 0 < cW → bW ∉ S.blocks := nW
    refine ⟨rfl, hs.arrays.graph, ⟨hca, hcr⟩, hinv.canongSize, hs.arrays.canonlab,
      hinv.canonlabSize, hcl, hcs, dW, hs.tables.left, hs.tables.nautilBit, vbg, vbc, vbl,
      by sep_ne hd, by sep_ne hd, ?_, ?_, hinv.samerows, hs.M1, hs.Mlt, hs.nM⟩
    · rintro z (rfl | rfl | rfl | rfl) <;> exact ⟨by sep_ne hd, by sep_ne hd, by sep_ne hd⟩
    · intro hc
      have hb := wnb hc
      refine ⟨fun e => hb (e ▸ ?_), fun e => hb (e ▸ ?_), fun e => hb (e ▸ ?_), fun e => hb (e ▸ ?_),
        fun e => hb (e ▸ ?_)⟩ <;> simp [SLoc.blocks]
  · rintro t r m' ⟨⟨rfl, cw', cap', b', hg', hD', hcap, hrel, hu⟩, hv⟩
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
    have hsrW : ¬ W bsr := by
      rintro (e | e | e | ⟨hc, e⟩ | ⟨hnv, e⟩)
      · exact c.ne_blocks (by simp [SLoc.blocks]) e.symm
      · exact c.ne_blocks (by simp [SLoc.blocks]) e.symm
      · exact c.ne_blocks (by simp [SLoc.blocks]) e.symm
      · exact h.work_ne c (.inl ⟨cW, hc, dW⟩) e.symm
      · exact hnv (e ▸ h.grow1 _ c.valid1)
    refine hQ m' (PAt.call c h hu ?_ ?_ hv hwm hwk
      ((hs.scalars.unch hu (by all_notW hd, notW)).cast rfl)
      ((hs.stats.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))).cast rfl)
      ?_ ?_ (hu.access _ _ _ _ hsrW h.srW)) fun v hv' => hv'.unch hu hsrW
    · rintro z (rfl | rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩)
      · exact .inl (by simp [SLoc.wr, wrG, SLoc.wrV])
      · exact .inr (.inl (by decide))
      · exact .inr (.inl (by decide))
      · exact .inr (.inr (.inl (.inl ⟨cW, hc, dW⟩)))
      · exact .inr (.inr (.inr (.inl hnv)))
    · intro z hz
      exact Keep.unch hu (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
    · have nw := fun z (hz : z ∈ S.blocks) h1 h2 h3 => notW z hz h1 h2 h3
      exact hs.arrays.set hu
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
    · exact { hinv with canongSize := by rw [updatecan_size]; exact hinv.canongSize }

end NautyVerified.Proofs.Search.Processnode
