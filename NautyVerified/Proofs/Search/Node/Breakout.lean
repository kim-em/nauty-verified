import NautyVerified.Proofs.Search.Node.Fixed
import NautyVerified.Proofs.Breakout.Satisfies
import NautyVerified.Logic.Grow

/-!
# A node's `breakout` call

`breakout(lab, ptn, level + 1, tc, tv, active, M)` individualizes `tv` in the
target cell starting at `tc`: `wp_nodeBreakout` gives `SearchAt` for
HexGraphIso's `breakout n lab ptn (level + 1) tc tv` in `lab`, `ptn` and
`active`. The invariant `SInv` of the new state is a hypothesis.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

/-- The `breakout` call statement. -/
abbrev breakCall : statement :=
  Set.sk (.Scall none
    (.Evar dense.id.«breakout»
      (tfun [tptr tint, tptr tint, tint, tint, tint, tptr tulong, tint] .Tvoid))
    [.Etempvar dense.id.«lab» (tptr tint), .Etempvar dense.id.«ptn» (tptr tint),
     .Ebinop .Oadd (Refine.tv dense.id.«level») (ci 1 tint) tint,
     .Evar dense.id.«tc» tint, Refine.tv dense.id.«tv»,
     .Evar dense.id.«nauty:active» (tptr tulong), .Evar dense.id.«nauty:m» tint])

/-- The state after `breakout`. -/
abbrev brokenSt {n : Nat} (level tc tv : Nat) (st : Search n) : Search n :=
  { st with
    lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
    ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
    active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2 }

theorem wp_nodeBreakout {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level tc v : Nat}
    (h : SearchAt m S ctx st pre nsp)
    {btc : block} (hetc : PTree.get dense.id.«tc» e = some (btc, tint))
    (htcv : Mem.load .Mint32 m btc (zOfInt 0) = some (.Vint (ir tc)))
    (hge : ∀ x ∈ [dense.id.«breakout», dense.id.«nauty:active», dense.id.«nauty:m»],
      PTree.get x e = none)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (htv : PTree.get dense.id.«tv» le = some (.Vint (ir v)))
    (hln : level ≤ n) (htc : tc < n)
    (hj : ∃ j, tc ≤ j ∧ j < n ∧ st.lab[j]! = v)
    (hinv : SInv (brokenSt level tc v st))
    (hQ : ∀ m', SearchAt m' S ctx (brokenSt level tc v st) pre nsp →
      Unch m m' (fun z => z = S.bl ∨ z = S.bp ∨ z = S.bA) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f breakCall Q e le m := by
  have hd := h.distinct
  have hI := h.inv
  have hnl := h.nlt
  have hn0 := h.n0
  have hM1 := h.M1
  have hMl := h.Mlt
  have hnM := h.nM
  simp only [List.forall_mem_cons, List.forall_mem_nil] at hge
  obtain ⟨g1, g2, g3, -⟩ := hge
  obtain ⟨aw, ha, -⟩ := h.arrays.active
  have hA1 := h.dyns.active.ptr (by have := h.dyns.capA; omega)
  wp_step; wp_step
  refine wp_call (vf := .Vptr Block.breakoutFn Ptrofs.zero)
    (targs := [tptr tint, tptr tint, tint, tint, tint, tptr tulong, tint])
    (tres := .Tvoid) (cc := Common.AST.cc_default)
    (vargs := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir ((level + 1 : Nat) : Int)),
      .Vint (ir tc), .Vint (ir v), .Vptr S.bA Ptrofs.zero, .Vint (ir S.M)])
    (.Internal dense.fn.«breakout») _
    (Satisfies.grow (Breakout.breakout_satisfies S.bl S.lofs S.bp S.pofs S.bA Ptrofs.zero
      st.lab st.ptn n (level + 1) tc v S.M aw)) rfl ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_breakoutFn]) rfl
    ⟨rfl, h.arrays.lab, h.arrays.ptn, ha, h.tables.nautilBit, by sep_ne hd, by sep_ne hd,
      by sep_ne hd, by sep_ne hd, hI.labSize, hI.ptnSize, hI.labSmall, hj, by omega, by omega,
      hM1, by omega, hnM⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, g1, find_breakoutFn, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode]
  · simp only [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, g2, g3, hetc, hlab, hptn, hlev,
      htv, Program.find_nautyActive, find_m, Exec.derefLoc, Cfrontend.Ctypes.access_mode,
      Mem.loadv, Alloc.Mptr_eq, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hA1, htcv,
      h.fixed.mm.load, ite_true, Refine.tv, typeof, cop, ir_add]
    push_cast
    rfl
  · rintro t _ m' ⟨⟨rfl, hL, hP, hA, hAr, hU, hK⟩, hg⟩
    simp only [List.forall_mem_cons, List.forall_mem_nil] at hK
    obtain ⟨kl, kp, ka, -⟩ := hK
    have nb : ∀ {z : block}, z ∈ S.blocks → z ≠ S.bl → z ≠ S.bp → z ≠ S.bA →
        ¬ (z = S.bl ∨ z = S.bp ∨ z = S.bA) := fun _ h1 h2 h3 => by
      rintro (e | e | e) <;> contradiction
    have har : Arrays m' S ctx (brokenSt level tc v st) :=
      { lab := hL
        ptn := hP
        orbits := h.arrays.orbits.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
        active := ⟨_, hA, hAr⟩
        fixedpts := let ⟨fw, hf, hr⟩ := h.arrays.fixedpts; ⟨fw, hf.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)), hr⟩
        workperm := let ⟨wv, hw⟩ := h.arrays.workperm; ⟨wv, hw.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))⟩
        firstlab := h.arrays.firstlab.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
        canonlab := h.arrays.canonlab.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
        firstcode := h.arrays.firstcode.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
        canoncode := h.arrays.canoncode.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
        firsttc := h.arrays.firsttc.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
        canong := h.arrays.canong.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
        autos := h.arrays.autos.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)) (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
        graph := ⟨h.arrays.graph.arr.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)), h.arrays.graph.rep⟩ }
    refine hQ m' ?_ hU hg
    refine h.rebuild (L := [S.bl, S.bp, S.bA]) (hU.mono fun z hz => by simpa using hz)
      (fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> simp [SLoc.wr, SLoc.wrV]) ?_
      { h.scalars.unch hU (fun z hz => nb (by revert z hz; simp [SLoc.blocks]) (by revert z hz; sep_all hd) (by revert z hz; sep_all hd) (by revert z hz; sep_all hd)) with } { h.stats.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)) with } har hinv
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ka
    all_goals exact Keep.unch hU (nb (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))

end NautyVerified.Proofs.Search
