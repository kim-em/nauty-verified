import NautyVerified.Proofs.Search.Node.LocDistinct
import NautyVerified.Proofs.Search.Node.Fields
import NautyVerified.Proofs.Doref.Satisfies
import NautyVerified.Proofs.Refine1.Satisfies
import NautyVerified.Logic.Grow

/-!
# A search node's call of `doref`

`wp_nodeDoref`: `doref(g, lab, ptn, level, &numcells, &qinvar, workperm, active,
&refcode, dispatch.refine, invarproc, mininvarlevel, maxinvarlevel, invararg,
digraph, M, n)` from a node's state is HexGraphIso's `refine` (the refinement
step of `visit`): afterwards `lab`, `ptn` and `active` are `refine`'s, the
local `numcells` holds its cell count and `refcode` its code.

`refine`'s locations (`Refine.Loc`) are built from `S`, the node's locals and
the work arrays in use; a work array of capacity 0 is given a block of
nauty.c's statics (`DynAt.reblock`), which is distinct from all the others.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

/-- `refine`'s state after a node's refinement. -/
abbrev visitSt {n : Nat} (ctx : Ctx n) (level numcells : Nat) (st : Search n) : Search n :=
  { st with
    lab := (refine ctx level st.lab st.ptn st.active numcells).lab
    ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
    active := (refine ctx level st.lab st.ptn st.active numcells).active }

/-- The call statement. -/
abbrev dorefCall : statement :=
  .Scall none
    (.Evar dense.id.«doref»
      (tfun [tptr tulong, tptr tint, tptr tint, tint, tptr tint, tptr tint, tptr tint,
        tptr tulong, tptr tint, tptr Refine.refprocType,
        tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tptr tint, tint, tint,
          tint, tint] .Tvoid), tint, tint, tint, tint, tint, tint] .Tvoid))
    [.Evar dense.id.«nauty:g» (tptr tulong), .Etempvar dense.id.«lab» (tptr tint),
     .Etempvar dense.id.«ptn» (tptr tint), .Etempvar dense.id.«level» tint,
     .Eaddrof (.Evar dense.id.«numcells» tint) (tptr tint),
     .Eaddrof (.Evar dense.id.«qinvar» tint) (tptr tint),
     .Evar dense.id.«nauty:workperm» (tptr tint), .Evar dense.id.«nauty:active» (tptr tulong),
     .Eaddrof (.Evar dense.id.«refcode» tint) (tptr tint),
     .Efield (.Evar dense.id.«nauty:dispatch» (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr))
       dense.id.«refine» (tptr Refine.refprocType),
     .Evar dense.id.«nauty:invarproc»
       (tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tptr tint, tint, tint,
         tint, tint] .Tvoid)),
     .Evar dense.id.«nauty:mininvarlevel» tint, .Evar dense.id.«nauty:maxinvarlevel» tint,
     .Evar dense.id.«nauty:invararg» tint, .Evar dense.id.«nauty:digraph» tint,
     .Evar dense.id.«nauty:m» tint, .Evar dense.id.«nauty:n» tint]

theorem wp_nodeDoref {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre : Bool} {level numcells : Nat}
    (h : SearchAt m S ctx st pre false)
    (hRef : Refine.RefineFn xi S.M (.Vptr S.refineBlock Ptrofs.zero))
    {bnc bq bk : block}
    (hloc : [bnc, bq, bk].Pairwise (· ≠ ·))
    (hlocS : ∀ z ∈ [bnc, bq, bk], z ∉ S.blocks ∧ Mem.valid_block m z ∧ ¬ IsWork m z)
    (henc : PTree.get dense.id.«numcells» e = some (bnc, tint))
    (heq : PTree.get dense.id.«qinvar» e = some (bq, tint))
    (hek : PTree.get dense.id.«refcode» e = some (bk, tint))
    (hge : ∀ x ∈ [dense.id.«doref», dense.id.«nauty:g», dense.id.«nauty:workperm»,
      dense.id.«nauty:active», dense.id.«nauty:dispatch», dense.id.«nauty:invarproc»,
      dense.id.«nauty:mininvarlevel», dense.id.«nauty:maxinvarlevel», dense.id.«nauty:invararg»,
      dense.id.«nauty:digraph», dense.id.«nauty:m», dense.id.«nauty:n»], PTree.get x e = none)
    (hnc : ArrayAt m .Mint32 bnc 0 (fun _ => .Vint (ir numcells)) 1)
    (hq : ∃ v, ArrayAt m .Mint32 bq 0 v 1) (hk : ∃ v, ArrayAt m .Mint32 bk 0 v 1)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hl1 : 1 ≤ level) (hln : level ≤ n) (hncn : numcells ≤ n)
    (hQ : ∀ (L : Refine.Loc) (aw : Nat → Lib.Integers.int64) (cN : Nat) (bN : block)
        (mi ma ia : Lib.Integers.int),
      L.bg = S.bg → L.gofs = S.gofs → L.gw = S.gw → L.bl = S.bl → L.lofs = S.lofs →
      L.bp = S.bp → L.pofs = S.pofs → L.bn = bnc → L.nofs = Ptrofs.zero → L.bc = S.bWP →
      L.cofs = Ptrofs.zero → L.ba = S.bA → L.aofs = Ptrofs.zero → L.bk = bk →
      L.kofs = Ptrofs.zero → L.level = level → L.M = S.M →
      DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 L.capW L.bW →
      DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 L.capS L.bS →
      DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 L.capB L.bB →
      DynAt m Block.nautilWorkperm Block.nautilWorkpermSz 4 cN bN →
      (0 < L.capW → IsWork m L.bW) → (0 < L.capS → IsWork m L.bS) →
      (0 < L.capB → IsWork m L.bB) → (0 < cN → IsWork m bN) →
      ∀ t v m', (Doref.dorefSpec xi L ctx st.lab st.ptn st.active numcells aw bq Ptrofs.zero
          S.refineBlock mi ma ia (ir 0) cN bN).post
        [.Vptr S.bg S.gofs, .Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level),
          .Vptr bnc Ptrofs.zero, .Vptr bq Ptrofs.zero, .Vptr S.bWP Ptrofs.zero,
          .Vptr S.bA Ptrofs.zero, .Vptr bk Ptrofs.zero, .Vptr S.refineBlock Ptrofs.zero, Vnullptr,
          .Vint mi, .Vint ma, .Vint ia, .Vint (ir 0), .Vint (ir S.M), .Vint (ir n)] m t v m' →
        (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
        Q.normal t e (set_opttemp none v le) m') :
    Wp xi ge f dorefCall Q e le m := by
  obtain ⟨cW, bW, cS, bS, cB, bB, cN, bN, dW, dS, dB, dN, nW, nS, nB, nN, pWS, pWB, pSB, pNW,
    pNS, pNB⟩ := h.work.arr
  have hl1 := hlocS bnc (by simp)
  have hl2 := hlocS bq (by simp)
  have hl3 := hlocS bk (by simp)
  -- a work block in use is not a local
  have wl : ∀ {bp bs : block} {c cap : Nat} {b : block}, (∀ cap', 0 < cap' →
      DynAt m bp bs c cap' b → IsWork m b) → DynAt m bp bs c cap b → 0 < cap →
      b ≠ bnc ∧ b ≠ bq ∧ b ≠ bk := fun hw d hc =>
    ⟨fun e => hl1.2.2 (e ▸ hw _ hc d), fun e => hl2.2.2 (e ▸ hw _ hc d),
     fun e => hl3.2.2 (e ▸ hw _ hc d)⟩
  -- the work blocks refine's `Loc` uses
  obtain ⟨bW', dW', hW'⟩ : ∃ b', DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW b' ∧
      WorkBlk S Block.gcaFirst bnc bq bk b' ∧ (0 < cW → b' = bW) ∧ (cW = 0 → b' = Block.gcaFirst) := by
    rcases Nat.eq_zero_or_pos cW with h0 | hc
    · exact ⟨_, dW.reblock h0 _, .inl rfl, fun hc => absurd h0 (by omega), fun _ => rfl⟩
    · exact ⟨_, dW, .inr ⟨nW hc, wl (fun c hc d => .inl ⟨c, hc, d⟩) dW hc⟩, fun _ => rfl,
        fun h0 => absurd h0 (by omega)⟩
  obtain ⟨bS', dS', hS'⟩ : ∃ b', DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 cS b' ∧
      WorkBlk S Block.gcaCanon bnc bq bk b' ∧ (0 < cS → b' = bS) ∧ (cS = 0 → b' = Block.gcaCanon) := by
    rcases Nat.eq_zero_or_pos cS with h0 | hc
    · exact ⟨_, dS.reblock h0 _, .inl rfl, fun hc => absurd h0 (by omega), fun _ => rfl⟩
    · exact ⟨_, dS, .inr ⟨nS hc, wl (fun c hc d => .inr (.inl ⟨c, hc, d⟩)) dS hc⟩, fun _ => rfl,
        fun h0 => absurd h0 (by omega)⟩
  obtain ⟨bB', dB', hB'⟩ : ∃ b', DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 cB b' ∧
      WorkBlk S Block.noncheaplevel bnc bq bk b' ∧ (0 < cB → b' = bB) ∧ (cB = 0 → b' = Block.noncheaplevel) := by
    rcases Nat.eq_zero_or_pos cB with h0 | hc
    · exact ⟨_, dB.reblock h0 _, .inl rfl, fun hc => absurd h0 (by omega), fun _ => rfl⟩
    · exact ⟨_, dB, .inr ⟨nB hc, wl (fun c hc d => .inr (.inr (.inl ⟨c, hc, d⟩))) dB hc⟩,
        fun _ => rfl, fun h0 => absurd h0 (by omega)⟩
  -- a work block outside `S` is in use
  have inUse : ∀ {c : block} {cap : Nat} {b b' : block}, c ∈ S.blocks →
      (0 < cap → b' = b) → (cap = 0 → b' = c) → b' ∉ S.blocks → 0 < cap ∧ b' = b := by
    intro c cap b b' hc he h0 hn
    rcases Nat.eq_zero_or_pos cap with hz | hp
    · exact absurd (h0 hz ▸ hc) hn
    · exact ⟨hp, he hp⟩
  have cW1 : Block.gcaFirst ∈ S.blocks := by simp [SLoc.blocks]
  have cS1 : Block.gcaCanon ∈ S.blocks := by simp [SLoc.blocks]
  have cB1 : Block.noncheaplevel ∈ S.blocks := by simp [SLoc.blocks]
  have hdist := loc_distinct (bW := bW') (bS := bS') (bB := bB') h.distinct hloc
    (fun z hz => (hlocS z hz).1) hW'.1 hS'.1 hB'.1
    (fun h1 h2 => by
      obtain ⟨c1, e1⟩ := inUse cW1 hW'.2.1 hW'.2.2 h1
      obtain ⟨c2, e2⟩ := inUse cS1 hS'.2.1 hS'.2.2 h2
      rw [e1, e2]; exact pWS c1 c2)
    (fun h1 h2 => by
      obtain ⟨c1, e1⟩ := inUse cW1 hW'.2.1 hW'.2.2 h1
      obtain ⟨c2, e2⟩ := inUse cB1 hB'.2.1 hB'.2.2 h2
      rw [e1, e2]; exact pWB c1 c2)
    (fun h1 h2 => by
      obtain ⟨c1, e1⟩ := inUse cS1 hS'.2.1 hS'.2.2 h1
      obtain ⟨c2, e2⟩ := inUse cB1 hB'.2.1 hB'.2.2 h2
      rw [e1, e2]; exact pSB c1 c2)
  let L : Refine.Loc :=
    { bg := S.bg, gofs := S.gofs, gw := S.gw, bl := S.bl, lofs := S.lofs, bp := S.bp,
      pofs := S.pofs, bn := bnc, nofs := Ptrofs.zero, bc := S.bWP, cofs := Ptrofs.zero,
      ba := S.bA, aofs := Ptrofs.zero, bk := bk, kofs := Ptrofs.zero, bW := bW', capW := cW,
      bS := bS', capS := cS, bB := bB', capB := cB, level := level, M := S.M }
  have hp : Refine.PreOk n L := ⟨hdist, h.n0, h.nM, h.M1, h.Mlt,
    show level < 2147483648 by have := h.nlt; omega, h.nlt⟩
  obtain ⟨aw, haw, hawr⟩ := h.arrays.active
  have hmem : Refine.Mem m L ctx (Refine.initSt st.lab st.ptn st.active numcells) aw :=
    { graph := h.arrays.graph
      lab := h.arrays.lab
      ptn := h.arrays.ptn
      nc := hnc
      act := haw
      actRep := hawr
      cnt := h.arrays.workperm
      dW := dW', dS := dS', dB := dB'
      bit := h.tables.naugraphBit
      bytes := h.tables.bytes
      left := h.tables.left }
  obtain ⟨mi, hmi⟩ := h.fixed.mininv
  obtain ⟨ma, hma⟩ := h.fixed.maxinv
  obtain ⟨ia, hia⟩ := h.fixed.invarg
  obtain ⟨qv, hqv⟩ := hq
  obtain ⟨kv, hkv⟩ := hk
  have hgn : ∀ x, x ∈ [dense.id.«doref», dense.id.«nauty:g», dense.id.«nauty:workperm»,
      dense.id.«nauty:active», dense.id.«nauty:dispatch», dense.id.«nauty:invarproc»,
      dense.id.«nauty:mininvarlevel», dense.id.«nauty:maxinvarlevel», dense.id.«nauty:invararg»,
      dense.id.«nauty:digraph», dense.id.«nauty:m», dense.id.«nauty:n»] → PTree.get x e = none := hge
  have hargs : Exec.evalExprlist ge e le m
      [.Evar dense.id.«nauty:g» (tptr tulong), .Etempvar dense.id.«lab» (tptr tint),
       .Etempvar dense.id.«ptn» (tptr tint), .Etempvar dense.id.«level» tint,
       .Eaddrof (.Evar dense.id.«numcells» tint) (tptr tint),
       .Eaddrof (.Evar dense.id.«qinvar» tint) (tptr tint),
       .Evar dense.id.«nauty:workperm» (tptr tint), .Evar dense.id.«nauty:active» (tptr tulong),
       .Eaddrof (.Evar dense.id.«refcode» tint) (tptr tint),
       .Efield (.Evar dense.id.«nauty:dispatch» (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr))
         dense.id.«refine» (tptr Refine.refprocType),
       .Evar dense.id.«nauty:invarproc»
         (tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tptr tint, tint, tint,
           tint, tint] .Tvoid)),
       .Evar dense.id.«nauty:mininvarlevel» tint, .Evar dense.id.«nauty:maxinvarlevel» tint,
       .Evar dense.id.«nauty:invararg» tint, .Evar dense.id.«nauty:digraph» tint,
       .Evar dense.id.«nauty:m» tint, .Evar dense.id.«nauty:n» tint]
      [tptr tulong, tptr tint, tptr tint, tint, tptr tint, tptr tint, tptr tint,
        tptr tulong, tptr tint, tptr Refine.refprocType,
        tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tptr tint, tint, tint,
          tint, tint] .Tvoid), tint, tint, tint, tint, tint, tint] =
      some [.Vptr S.bg S.gofs, .Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level),
        .Vptr bnc Ptrofs.zero, .Vptr bq Ptrofs.zero, .Vptr S.bWP Ptrofs.zero,
        .Vptr S.bA Ptrofs.zero, .Vptr bk Ptrofs.zero, .Vptr S.refineBlock Ptrofs.zero, Vnullptr,
        .Vint mi, .Vint ma, .Vint ia, .Vint (ir 0), .Vint (ir S.M), .Vint (ir n)] := by
    have g1 := hgn dense.id.«nauty:g» (by simp)
    have g2 := hgn dense.id.«nauty:workperm» (by simp)
    have g3 := hgn dense.id.«nauty:active» (by simp)
    have g4 := hgn dense.id.«nauty:dispatch» (by simp)
    have g5 := hgn dense.id.«nauty:invarproc» (by simp)
    have g6 := hgn dense.id.«nauty:mininvarlevel» (by simp)
    have g7 := hgn dense.id.«nauty:maxinvarlevel» (by simp)
    have g8 := hgn dense.id.«nauty:invararg» (by simp)
    have g9 := hgn dense.id.«nauty:digraph» (by simp)
    have g10 := hgn dense.id.«nauty:m» (by simp)
    have g11 := hgn dense.id.«nauty:n» (by simp)
    simp only [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, Exec.evalLvalue,
      g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, henc, heq, hek, hlab, hptn, hlev, find_g,
      find_nautyWorkperm, find_nautyActive,
      find_dispatch, find_invarproc, find_mininvarlevel, find_maxinvarlevel, find_invararg,
      find_digraph, find_m, find_n]
    have hW1 := h.dyns.workperm.ptr (by have := h.dyns.capWP; have := h.n0; omega)
    have hA1 := h.dyns.active.ptr (by have := h.dyns.capA; have := h.M1; omega)
    simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h.fixed.g.load, hW1, hA1,
      h.fixed.invarproc.load, hmi.load, hma.load, hia.load, h.fixed.digraph.load, h.fixed.mm.load,
      h.fixed.nn.load, ite_true, typeof, cop]
    have hd24 : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 24))) = zOfInt 24 := by
      decide
    simp only [field_dRefine, hd24, h.fixed.dRefine.load, cop]
    have hnull : Cfrontend.Cop.sem_cast Vnullptr
        (tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tptr tint, tint, tint, tint,
          tint] .Tvoid))
        (tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tptr tint, tint, tint, tint,
          tint] .Tvoid)) m = some Vnullptr := rfl
    simp only [hnull]
  have hvalid : ∀ z ∈ [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk], Mem.valid_block m z := by
    have va : ∀ {chunk b base vals k}, 0 < k → ArrayAt m chunk b base vals k → Mem.valid_block m b :=
      fun hk ha => Alloc.valid_of_access (ha.writable 0 hk)
    have hn0 := h.n0
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact va (by have := h.M1; exact Nat.mul_pos this hn0) h.arrays.graph.arr
    · exact va hn0 h.arrays.lab
    · exact va hn0 h.arrays.ptn
    · exact hl1.2.1
    · obtain ⟨v, hv⟩ := h.arrays.workperm; exact va hn0 hv
    · exact va h.M1 haw
    · exact hl3.2.1
  have hsep := loc_sep (bW := bW') (bS := bS') (bB := bB') (bN := bN) (cN := cN) h.distinct hloc
    (fun z hz => (hlocS z hz).1) hW'.1 hS'.1 hB'.1 nN
    (wl (fun c hc d => .inr (.inr (.inr ⟨c, hc, d⟩))) dN)
    (fun hc h1 => by obtain ⟨c1, e1⟩ := inUse cW1 hW'.2.1 hW'.2.2 h1; rw [e1]; exact pNW hc c1)
    (fun hc h1 => by obtain ⟨c1, e1⟩ := inUse cS1 hS'.2.1 hS'.2.2 h1; rw [e1]; exact pNS hc c1)
    (fun hc h1 => by obtain ⟨c1, e1⟩ := inUse cB1 hB'.2.1 hB'.2.2 h1; rw [e1]; exact pNB hc c1)
  refine wp_call (vf := .Vptr Block.dorefFn Ptrofs.zero) _ _
    (Satisfies.grow (Doref.doref_satisfies (xi := xi) L ctx st.lab st.ptn st.active numcells aw bq
      Ptrofs.zero S.refineBlock mi ma ia (ir 0) cN bN))
    rfl ?_ hargs ?_ rfl ?_ ?_
  · simp [Exec.evalExpr, Exec.lvalOfVar, hgn dense.id.«doref» (by simp), find_dorefFn,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  · simp [Genv.find_funct, funct_dorefFn]
  · refine ⟨rfl, ⟨rfl, hp, hmem, ⟨kv, hkv⟩, hvalid, ?_, ?_, hncn⟩, hRef, dN, ⟨qv, hqv⟩, hl2.2.1,
      ?_, ?_⟩
    · have hi := h.inv
      refine ⟨hi.labSize, fun i hiz => hi.labSmall i (by have := hi.labSize; simp only [Refine.initSt] at hiz; omega),
        hi.ptnSize, ?_⟩
      show st.ptn[st.ptn.size - 1]! ≤ level
      rw [hi.ptnSize]; have := hi.ptnLast; omega
    · intro i hin
      have := h.nlt
      rcases h.inv.ptnVals i hin with hv | hv
      · show st.ptn[i]! < 2147483648; omega
      · show st.ptn[i]! < 2147483648; rw [hv]; decide
    · exact hsep
    · exact ⟨ne_of_notin hl2.1 (by simp [SLoc.blocks]), ne_of_notin hl2.1 (by simp [SLoc.blocks]),
        fun hc => Ne.symm (wl (fun c hc d => .inr (.inr (.inr ⟨c, hc, d⟩))) dN hc).2.1⟩
  · rintro t v m' ⟨hpost, hg⟩
    exact hQ L aw cN bN mi ma ia rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      dW' dS' dB' dN
      (fun hc => by show IsWork m bW'; rw [hW'.2.1 hc]; exact .inl ⟨cW, hc, dW⟩)
      (fun hc => by show IsWork m bS'; rw [hS'.2.1 hc]; exact .inr (.inl ⟨cS, hc, dS⟩))
      (fun hc => by show IsWork m bB'; rw [hB'.2.1 hc]; exact .inr (.inr (.inl ⟨cB, hc, dB⟩)))
      (fun hc => .inr (.inr (.inr ⟨cN, hc, dN⟩))) t v m' hpost hg

end NautyVerified.Proofs.Search
