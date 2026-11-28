import NautyVerified.Proofs.Search.Node.Breakout
import NautyVerified.Proofs.Search.Recover.Satisfies
import NautyVerified.Proofs.Refine.Guard

/-!
# Steps of a node's child loop

- `wp_nodeRecover`: `recover(ptn, level)` is HexGraphIso's `recover` at `level`;
- `wp_nodeNext`: `tv = nextelement(tcell, M, tv)` steps to the target cell's
  next vertex, HexGraphIso's `tcell.nextElem (some tv)`, with `-1` for `none`.
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

/-- `recover(ptn, level)`. -/
abbrev recCall : statement :=
  Set.sk (.Scall none (.Evar dense.id.«nauty:recover» (tfun [tptr tint, tint] .Tvoid))
    [.Etempvar dense.id.«ptn» (tptr tint), Refine.tv dense.id.«level»])

theorem wp_nodeRecover {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre : Bool} {level : Nat}
    (h : SearchAt m S ctx st pre false)
    (hge : PTree.get dense.id.«nauty:recover» e = none)
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hl1 : 1 ≤ level) (hln : level ≤ n)
    (hQ : ∀ m', SearchAt m' S ctx (Hex.GraphIso.Nauty.recover nautyInf level st) pre false →
      SFrame m m' S → (∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z) →
      Q.normal E0 e le m') :
    Wp xi ge f recCall Q e le m := by
  wp_step; wp_step
  refine wp_call (vf := .Vptr Block.recoverFn Ptrofs.zero) (targs := [tptr tint, tint])
    (tres := .Tvoid) (cc := Common.AST.cc_default)
    (vargs := [.Vptr S.bp S.pofs, .Vint (ir level)])
    (.Internal dense.fn.«nauty:recover») _ (Recover.recover_satisfies S ctx st level pre) rfl ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_recoverFn]) rfl ⟨rfl, h, hl1, hln⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, hge, find_recoverFn, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode]
  · simp only [Exec.evalExprlist, Exec.evalExpr, hptn, hlev, Refine.tv, typeof, cop]
  · rintro t _ m' ⟨rfl, h', hF, hW⟩
    exact hQ m' h' hF hW

/-- `t716 = nextelement(tcell, M, tv); tv = t716;` -/
abbrev nextStep : statement :=
  .Ssequence
    (Set.sk (.Scall (some (idOf 716))
      (.Evar dense.id.«nextelement» (tfun [tptr tulong, tint, tint] tint))
      [.Etempvar dense.id.«tcell» (tptr tulong), .Evar dense.id.«nauty:m» tint,
       Refine.tv dense.id.«tv»]))
    (.Sset dense.id.«tv» (Refine.tv (idOf 716)))

theorem wp_nodeNext {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    (h : SearchAt m S ctx st pre nsp)
    (hge : ∀ x ∈ [dense.id.«nextelement», dense.id.«nauty:m»], PTree.get x e = none)
    {btc : block} (htl : PTree.get dense.id.tcell le = some (.Vptr btc Ptrofs.zero))
    {tw : Nat → Lib.Integers.int64} (htw : ArrayAt m .Mint64 btc 0 (longs tw) S.M)
    {cell : VSet n} (hrep : SetRep (fun w => bv64 (tw w)) S.M cell)
    {p : Nat} (htv : PTree.get dense.id.«tv» le = some (.Vint (ir p))) (hp : p < n)
    (hQ : ∀ r : Int, ((cell.nextElem (some p) = none ∧ r = -1) ∨
        ∃ v : Nat, cell.nextElem (some p) = some v ∧ r = v) →
      Q.normal E0 e (PTree.set dense.id.«tv» (.Vint (ir r))
        (PTree.set (idOf 716) (.Vint (ir r)) le)) m) :
    Wp xi ge f nextStep Q e le m := by
  have hM1 := h.M1
  have hMl := h.Mlt
  have hnM := h.nM
  simp only [List.forall_mem_cons] at hge
  obtain ⟨g1, g2, -⟩ := hge
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.nextelement Ptrofs.zero) (targs := [tptr tulong, tint, tint])
    (tres := tint) (cc := Common.AST.cc_default)
    (vargs := [.Vptr btc Ptrofs.zero, .Vint (ir S.M), .Vint (ir ((p : Nat) : Int))]) _
    (Nextelement.nextSpec btc Ptrofs.zero S.M (Refine.posOf (some p)) tw)
    (Nextelement.nextelement_satisfies _ _ _ _ _) rfl ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_nextelement]) Isautom.type_nextelement
    ⟨rfl, by simp [Refine.posOf], by simp [Refine.posOf]; omega, hM1, by omega,
      Graph.wordsAt_of htw, h.tables.left⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, g1, find_nextelement, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode]
  · simp only [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, g2, find_m, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode, Mem.loadv, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
      h.fixed.mm.load, htl, htv, Refine.tv, typeof, cop]
  · rintro t' v m' ⟨rfl, rfl, r, rfl, hspec⟩
    simp only [set_opttemp]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, Refine.tv]
    exact hQ r (Refine.next_eq hrep hspec)

end NautyVerified.Proofs.Search
