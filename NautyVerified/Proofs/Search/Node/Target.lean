import NautyVerified.Proofs.Search.Node.Realloc
import NautyVerified.Proofs.Search.Node.Fields
import NautyVerified.Proofs.Search.Node.OtherSteps
import NautyVerified.Proofs.Maketargetcell.Satisfies
import NautyVerified.Logic.Grow

/-!
# A search node's `maketargetcell` call

`mtcCall hintE` is the call
`maketargetcell(g, lab, ptn, level, tcell, &tcellsize, &tc, tc_level, digraph,
hint, dispatch.targetcell, M, n)` both nodes make (`othernode0` with the hint
`firsttc[level]` or `-1`, `firstpathnode0` with `-1`). `wp_nodeTarget` runs it
over `SearchAt`: the target cell, `*tcellsize` and `*tc` receive
HexGraphIso's `maketargetcell`, and the search state is unchanged (the work
arrays may have moved, `SearchAt.realloc`).
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep dyn3Set)
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

/-- The type of `maketargetcell`. -/
abbrev mtcType : Cfrontend.Ctypes.type :=
  tfun [tptr tulong, tptr tint, tptr tint, tint, tptr tulong, tptr tint, tptr tint, tint, tint, tint,
    tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tint, tint, tint] tint), tint,
    tint] .Tvoid

/-- `maketargetcell(g, lab, ptn, level, tcell, &tcellsize, &tc, tc_level, digraph, hint,
dispatch.targetcell, M, n)`. -/
abbrev mtcCall (hintE : expr) : statement :=
  .Scall none (.Evar dense.id.«maketargetcell» mtcType)
    [.Evar dense.id.«nauty:g» (tptr tulong), .Etempvar dense.id.«lab» (tptr tint),
     .Etempvar dense.id.«ptn» (tptr tint), Refine.tv dense.id.«level», .Etempvar dense.id.«tcell» (tptr tulong),
     .Eaddrof (.Evar dense.id.«tcellsize» tint) (tptr tint), .Eaddrof (.Evar dense.id.«tc» tint) (tptr tint),
     .Evar dense.id.«nauty:tc_level» tint, .Evar dense.id.«nauty:digraph» tint, hintE,
     .Efield (.Evar dense.id.«nauty:dispatch» (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr))
       dense.id.«targetcell»
       (tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tint, tint, tint] tint)),
     .Evar dense.id.«nauty:m» tint, .Evar dense.id.«nauty:n» tint]

set_option maxHeartbeats 4000000 in
theorem wp_nodeTarget {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level : Nat}
    (h : SearchAt m S ctx st pre nsp) (hvU : Mem.valid_block m S.bUA)
    (hvT : Mem.valid_block m Block.tcnode0)
    {bt bz bc : block}
    (hloc : [bt, bz, bc].Pairwise (· ≠ ·))
    (hlocS : ∀ z ∈ [bt, bz, bc], z ∉ S.blocks ∧ Mem.valid_block m z ∧ ¬ IsWork m z)
    (htc : PTree.get dense.id.«tcell» le = some (.Vptr bt Ptrofs.zero))
    (hez : PTree.get dense.id.«tcellsize» e = some (bz, tint))
    (hec : PTree.get dense.id.«tc» e = some (bc, tint))
    (hge : ∀ x ∈ [dense.id.«maketargetcell», dense.id.«nauty:g», dense.id.«nauty:tc_level»,
      dense.id.«nauty:digraph», dense.id.«nauty:dispatch», dense.id.«nauty:m», dense.id.«nauty:n»],
      PTree.get x e = none)
    (ht : ∃ v, ArrayAt m .Mint64 bt 0 v S.M) (hz : ∃ v, ArrayAt m .Mint32 bz 0 v 1)
    (hc : ∃ v, ArrayAt m .Mint32 bc 0 v 1)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hl1 : 1 ≤ level) (hln : level ≤ n)
    {hintE : expr} {hint : Int} (hhint : Exec.evalExpr ge e le m hintE = some (.Vint (ir hint)))
    (hhty : typeof hintE = tint) (hh1 : -1 ≤ hint) (hh2 : hint < n)
    (hnt : ∃ x < n, level < st.ptn[x]!)
    (hQ : ∀ m', SearchAt m' S ctx st pre nsp →
      (∃ ws, ArrayAt m' .Mint64 bt 0 (longs ws) S.M ∧
        SetRep (fun w => bv64 (ws w)) S.M (maketargetcell ctx st.lab st.ptn level 100 hint).2.1) →
      ArrayAt m' .Mint32 bz 0
        (fun _ => .Vint (ir ((maketargetcell ctx st.lab st.ptn level 100 hint).2.2 : Int))) 1 →
      ArrayAt m' .Mint32 bc 0
        (fun _ => .Vint (ir ((maketargetcell ctx st.lab st.ptn level 100 hint).1 : Int))) 1 →
      Unch m m' (fun z => z ∈ S.blocks ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨ z = bt ∨ z = bz ∨
        z = bc) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (mtcCall hintE) Q e le m := by
  have hv := h.valid_all hvU hvT
  have hd := h.distinct
  have hI := h.inv
  have hnl := h.nlt
  obtain ⟨cW, bW, cS, bS, cB, bB, cN, bN, dW, dS, dB, dN, nW, nS, nB, nN, pWS, pWB, pSB, pNW,
    pNS, pNB⟩ := h.work.arr
  obtain ⟨tv0, ht⟩ := ht
  obtain ⟨zv, hz⟩ := hz
  obtain ⟨cv, hc⟩ := hc
  simp only [List.forall_mem_cons] at hlocS hge
  obtain ⟨⟨tS, tV, tW⟩, ⟨zS, zV, zW⟩, ⟨cSn, cV, cWn⟩, -⟩ := hlocS
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, -⟩ := hge
  simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true] at hloc
  -- blocks of `S` are none of the work blocks in use
  have wS : ∀ z ∈ S.blocks, (0 < cW → z ≠ bW) ∧ (0 < cS → z ≠ bS) ∧ (0 < cB → z ≠ bB) :=
    fun z hz => ⟨fun hc e => nW hc (e ▸ hz), fun hc e => nS hc (e ▸ hz), fun hc e => nB hc (e ▸ hz)⟩
  -- a local is not a work block in use
  have wL : ∀ z, ¬ IsWork m z → (0 < cW → z ≠ bW) ∧ (0 < cS → z ≠ bS) ∧ (0 < cB → z ≠ bB) :=
    fun z hz => ⟨fun hc e => hz (e ▸ .inl ⟨cW, hc, dW⟩), fun hc e => hz (e ▸ .inr (.inl ⟨cS, hc, dS⟩)),
      fun hc e => hz (e ▸ .inr (.inr (.inl ⟨cB, hc, dB⟩)))⟩
  have mem : ∀ {z : block}, z ∈ S.blocks → ∀ {y : block}, y ∉ S.blocks → z ≠ y :=
    fun hz _ hy e => hy (e ▸ hz)
  have iG : S.bg ∈ S.blocks := by simp [SLoc.blocks]
  have iL : S.bl ∈ S.blocks := by simp [SLoc.blocks]
  have iP : S.bp ∈ S.blocks := by simp [SLoc.blocks]
  have iBit : Block.nautilBit ∈ S.blocks := by simp [SLoc.blocks]
  have hpre : Bestcell.Pre m S.bg S.gofs S.gw ctx.g S.bl S.lofs st.lab S.bp S.pofs st.ptn level S.M
      cW bW cS bS cB bB :=
    { graph := h.arrays.graph
      larr := h.arrays.lab
      lsmall := hI.labSmall
      parr := h.arrays.ptn
      psize := hI.ptnSize
      psmall := fun x hx => by
        rcases hI.ptnVals x hx with hv' | hv'
        · omega
        · rw [hv']; decide
      plast := by have := hI.ptnLast; omega
      levlt := by omega
      dP := dW, dS := dS, dB := dB
      bit := h.tables.naugraphBit
      caller := fun z hz => by
        rcases hz with rfl | rfl | rfl
        · exact ⟨hv _ iG, by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd,
            by sep_ne hd, by sep_ne hd, (wS _ iG).1, (wS _ iG).2.1, (wS _ iG).2.2⟩
        · exact ⟨hv _ iL, by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd,
            by sep_ne hd, by sep_ne hd, (wS _ iL).1, (wS _ iL).2.1, (wS _ iL).2.2⟩
        · exact ⟨hv _ iP, by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd,
            by sep_ne hd, by sep_ne hd, (wS _ iP).1, (wS _ iP).2.1, (wS _ iP).2.2⟩
      sP := fun hc => ⟨Ne.symm (mem (by simp [SLoc.blocks]) (nW hc)),
        Ne.symm (mem (by simp [SLoc.blocks]) (nW hc)), Ne.symm (mem (by simp [SLoc.blocks]) (nW hc)),
        Ne.symm (mem (by simp [SLoc.blocks]) (nW hc)), Ne.symm (mem (by simp [SLoc.blocks]) (nW hc)),
        pWS hc, pWB hc⟩
      sS := fun hc => ⟨Ne.symm (mem (by simp [SLoc.blocks]) (nS hc)),
        Ne.symm (mem (by simp [SLoc.blocks]) (nS hc)), Ne.symm (mem (by simp [SLoc.blocks]) (nS hc)),
        Ne.symm (mem (by simp [SLoc.blocks]) (nS hc)), Ne.symm (mem (by simp [SLoc.blocks]) (nS hc)),
        pSB hc⟩
      sB := fun hc => ⟨Ne.symm (mem (by simp [SLoc.blocks]) (nB hc)),
        Ne.symm (mem (by simp [SLoc.blocks]) (nB hc)), Ne.symm (mem (by simp [SLoc.blocks]) (nB hc)),
        Ne.symm (mem (by simp [SLoc.blocks]) (nB hc)), Ne.symm (mem (by simp [SLoc.blocks]) (nB hc))⟩
      n0 := h.n0, nlt := h.nlt, M1 := h.M1, Mlt := h.Mlt, nM := h.nM }
  have hout : Maketargetcell.Out m cW bW cS bS cB bB S.bg S.bl S.bp bt bz bc :=
    { out := fun z hz => by
        rcases hz with rfl | rfl | rfl | rfl
        · exact ⟨tV, Ne.symm (mem (by simp [SLoc.blocks]) tS), Ne.symm (mem (by simp [SLoc.blocks]) tS),
            Ne.symm (mem (by simp [SLoc.blocks]) tS), Ne.symm (mem (by simp [SLoc.blocks]) tS),
            Ne.symm (mem (by simp [SLoc.blocks]) tS), Ne.symm (mem (by simp [SLoc.blocks]) tS),
            (wL _ tW).1, (wL _ tW).2.1, (wL _ tW).2.2⟩
        · exact ⟨zV, Ne.symm (mem (by simp [SLoc.blocks]) zS), Ne.symm (mem (by simp [SLoc.blocks]) zS),
            Ne.symm (mem (by simp [SLoc.blocks]) zS), Ne.symm (mem (by simp [SLoc.blocks]) zS),
            Ne.symm (mem (by simp [SLoc.blocks]) zS), Ne.symm (mem (by simp [SLoc.blocks]) zS),
            (wL _ zW).1, (wL _ zW).2.1, (wL _ zW).2.2⟩
        · exact ⟨cV, Ne.symm (mem (by simp [SLoc.blocks]) cSn), Ne.symm (mem (by simp [SLoc.blocks]) cSn),
            Ne.symm (mem (by simp [SLoc.blocks]) cSn), Ne.symm (mem (by simp [SLoc.blocks]) cSn),
            Ne.symm (mem (by simp [SLoc.blocks]) cSn), Ne.symm (mem (by simp [SLoc.blocks]) cSn),
            (wL _ cWn).1, (wL _ cWn).2.1, (wL _ cWn).2.2⟩
        · exact ⟨hv _ iBit, by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd,
            by sep_ne hd, (wS _ iBit).1, (wS _ iBit).2.1, (wS _ iBit).2.2⟩
      sep := fun z hz => by
        rcases hz with rfl | rfl | rfl
        · exact ⟨Ne.symm (mem iG tS), Ne.symm (mem iL tS), Ne.symm (mem iP tS), Ne.symm (mem iBit tS)⟩
        · exact ⟨Ne.symm (mem iG zS), Ne.symm (mem iL zS), Ne.symm (mem iP zS), Ne.symm (mem iBit zS)⟩
        · exact ⟨Ne.symm (mem iG cSn), Ne.symm (mem iL cSn), Ne.symm (mem iP cSn), Ne.symm (mem iBit cSn)⟩
      tz := hloc.1.1, tc := hloc.1.2, zc := hloc.2 }
  refine wp_call (vf := .Vptr Block.maketargetcellFn Ptrofs.zero)
    (targs := [tptr tulong, tptr tint, tptr tint, tint, tptr tulong, tptr tint, tptr tint, tint, tint,
      tint, tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tint, tint, tint] tint),
      tint, tint])
    (tres := .Tvoid) (cc := Common.AST.cc_default)
    (vargs := [.Vptr S.bg S.gofs, .Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level),
      .Vptr bt Ptrofs.zero, .Vptr bz Ptrofs.zero, .Vptr bc Ptrofs.zero, .Vint (ir ((100 : Nat) : Int)),
      .Vint (ir 0), .Vint (ir hint), .Vptr Program.Block.targetcell Ptrofs.zero, .Vint (ir S.M),
      .Vint (ir n)]) (.Internal dense.fn.maketargetcell) _
    (Satisfies.grow (Maketargetcell.maketargetcell_satisfies S.bg S.gofs S.gw ctx.g S.bl S.lofs
      st.lab S.bp S.pofs st.ptn level bt Ptrofs.zero tv0 bz Ptrofs.zero zv bc Ptrofs.zero cv 100
      (ir 0) hint S.M cW bW cS bS cB bB)) rfl ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_maketargetcellFn]) rfl
    ⟨rfl, hpre, hh2, by omega, by decide, hnt, ht, hz, hc, h.tables.nautilBit, hout⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, g1, find_maketargetcellFn, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode]
  · simp only [Exec.evalExprlist, hhint, hhty]
    simp only [Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar, g2, g3, g4, g5, g6, g7, hez, hec,
      find_g, find_tcLevel, find_digraph, find_dispatch, find_m, find_n, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode, Mem.loadv, field_dTargetcell, Alloc.Mptr_eq,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h.fixed.g.load, h.fixed.tcLevel.load,
      h.fixed.digraph.load, h.fixed.mm.load, h.fixed.nn.load, htc, hlab, hptn, hlev,
      typeof, cop]
    rw [show Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 48))) = zOfInt 48 from rfl,
      h.fixed.dTargetcell.load]
    simp only [ite_true, cop]
    rfl
  · rintro t v m' ⟨⟨rfl, hT, hZ, hC, cW', bW', cS', bS', cB', bB', dW', dS', dB', fW, fS, fB, hU,
      pWS', pWB', pSB', -⟩, hgrow⟩
    have hX : ∀ z ∈ S.blocks, ¬ (z = bt ∨ z = bz ∨ z = bc) := by
      rintro z hzm (e | e | e)
      · exact tS (e ▸ hzm)
      · exact zS (e ▸ hzm)
      · exact cSn (e ▸ hzm)
    have hXN : 0 < cN → ¬ (bN = bt ∨ bN = bz ∨ bN = bc) := by
      intro hc
      have hw : IsWork m bN := .inr (.inr (.inr ⟨cN, hc, dN⟩))
      rintro (e | e | e)
      · exact tW (e ▸ hw)
      · exact zW (e ▸ hw)
      · exact cWn (e ▸ hw)
    have hS' := h.realloc hvU hvT dN nW nS nB nN pNW pNS pNB (X := fun z => z = bt ∨ z = bz ∨ z = bc) hU
      hX hXN dW' dS' dB' fW fS fB pWS' pWB' pSB'
    refine hQ m' hS' hT hZ hC (hU.mono fun z hz => ?_) hgrow
    rcases hz with h6 | hx
    · unfold dyn3Set at h6
      rcases h6 with e | e | e | e | e | e | ⟨hc, e⟩ | ⟨hc, e⟩ | ⟨hc, e⟩ | hnv
      · exact .inl (e ▸ by simp [SLoc.blocks])
      · exact .inl (e ▸ by simp [SLoc.blocks])
      · exact .inl (e ▸ by simp [SLoc.blocks])
      · exact .inl (e ▸ by simp [SLoc.blocks])
      · exact .inl (e ▸ by simp [SLoc.blocks])
      · exact .inl (e ▸ by simp [SLoc.blocks])
      · exact .inr (.inr (.inl (e ▸ .inl ⟨cW, hc, dW⟩)))
      · exact .inr (.inr (.inl (e ▸ .inr (.inl ⟨cS, hc, dS⟩))))
      · exact .inr (.inr (.inl (e ▸ .inr (.inr (.inl ⟨cB, hc, dB⟩)))))
      · exact .inr (.inl hnv)
    · exact .inr (.inr (.inr hx))

end NautyVerified.Proofs.Search
