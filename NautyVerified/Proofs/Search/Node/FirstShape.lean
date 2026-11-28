import NautyVerified.Proofs.Search.Node.LoopShape
import NautyVerified.Proofs.Search.Node.FirstMisc

/-!
# The shape of `firstpathnode0`'s child loop

`fpnLoop_eq`: the loop over the target cell is, statement for statement, the
pieces proved separately: the `tv >= 0` test, `fpnChild` (the orbit test around
`breakCall`, `ADDELEMENT(fixedpts, tv)`, `cosetindex = tv`, the recursive call
on the first path or off it, `DELELEMENT(fixedpts, tv)`, `earlyRet`, `prune0`
and `recCall`), the `index` count, and `nextStepAt (idOf 715)` as the
increment. `wp_nodeNextAt` is `wp_nodeNext` for any result temporary.
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

/-- `rtnlevel = firstpathnode0(lab, ptn, level + 1, numcells + 1, tcnode_this);` -/
abbrev fpnCall : statement :=
  .Ssequence
    (Set.sk (.Scall (some (idOf 716))
      (.Evar dense.id.«nauty:firstpathnode0»
        (tfun [tptr tint, tptr tint, tint, tint, tptr tcStruct] tint))
      [.Etempvar dense.id.«lab» (tptr tint), .Etempvar dense.id.«ptn» (tptr tint),
       .Ebinop .Oadd (Refine.tv dense.id.«level») (ci 1 tint) tint,
       .Ebinop .Oadd (.Evar dense.id.«numcells» tint) (ci 1 tint) tint,
       .Etempvar dense.id.«tcnode_this» (tptr tcStruct)]))
    (.Sset dense.id.«rtnlevel» (Refine.tv (idOf 716)))

/-- After the first child: `childcount = 1; gca_first = level; stabvertex = tv1;` -/
abbrev firstAfter : statement :=
  .Ssequence (Set.sk (.Sset dense.id.«childcount» (ci 1 tint)))
    (.Ssequence (Set.sk (.Sassign (.Evar dense.id.«nauty:gca_first» tint) (Refine.tv dense.id.«level»)))
      (Set.sk (.Sassign (.Evar dense.id.«nauty:stabvertex» tint) (Refine.tv dense.id.«tv1»))))

/-- The recursive call: on the first path for `tv1`, off it for the others. -/
abbrev callIf : statement :=
  .Sifthenelse (.Ebinop .Oeq (Refine.tv dense.id.«tv») (Refine.tv dense.id.«tv1») tint)
    (.Ssequence fpnCall firstAfter)
    (.Ssequence childCall
      (Set.sk (.Sset dense.id.«childcount»
        (.Ebinop .Oadd (Refine.tv dense.id.«childcount») (ci 1 tint) tint))))

/-- `orbits[tv]` -/
abbrev orbAt (x : ident) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar dense.id.«nauty:orbits» (tptr tint)) (Refine.tv x) (tptr tint)) tint

/-- One vertex of the sweep: `if (orbits[tv] == tv) { … }`. -/
abbrev fpnChild : statement :=
  .Sifthenelse (.Ebinop .Oeq (orbAt dense.id.«tv») (Refine.tv dense.id.«tv») tint)
    (.Ssequence breakCall
      (.Ssequence (Set.addElementG dense.id.«nauty:fixedpts» dense.id.«nauty:bit» (Refine.tv dense.id.«tv»))
        (.Ssequence (Set.sk (.Sassign (.Evar dense.id.«nauty:cosetindex» tint) (Refine.tv dense.id.«tv»)))
          (.Ssequence (Set.sk callIf)
            (.Ssequence (Set.delElementG dense.id.«nauty:fixedpts» dense.id.«nauty:bit» (Refine.tv dense.id.«tv»))
              (.Ssequence (Set.sk earlyRet)
                (.Ssequence (Set.sk Othernode.prune0) recCall)))))))
    .Sskip

/-- `if (orbits[tv] == tv1) ++index;` -/
abbrev indexIf : statement :=
  .Sifthenelse (.Ebinop .Oeq (orbAt dense.id.«tv») (Refine.tv dense.id.«tv1») tint)
    (Set.sk (.Sset dense.id.«index» (.Ebinop .Oadd (Refine.tv dense.id.«index») (ci 1 tint) tint)))
    .Sskip

/-- `tv = nextelement(tcell, M, tv)` with the call's result in `x`. -/
abbrev nextStepAt (x : ident) : statement :=
  .Ssequence
    (Set.sk (.Scall (some x)
      (.Evar dense.id.«nextelement» (tfun [tptr tulong, tint, tint] tint))
      [.Etempvar dense.id.tcell (tptr tulong), .Evar dense.id.«nauty:m» tint,
       Refine.tv dense.id.«tv»]))
    (.Sset dense.id.«tv» (Refine.tv x))

theorem fpnLoop_eq : Firstpathnode.childLoop =
    .Sloop
      (.Ssequence
        (Set.sk (.Sifthenelse (.Ebinop .Oge (Refine.tv dense.id.«tv») (ci 0 tint) tint) .Sskip .Sbreak))
        (.Ssequence (Set.sk fpnChild) (Set.sk indexIf)))
      (nextStepAt (idOf 715)) := rfl

theorem wp_nodeNextAt {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool} (x : ident)
    (h : SearchAt m S ctx st pre nsp)
    (hge : ∀ x ∈ [dense.id.«nextelement», dense.id.«nauty:m»], PTree.get x e = none)
    {btc : block} (htl : PTree.get dense.id.tcell le = some (.Vptr btc Ptrofs.zero))
    {tw : Nat → Lib.Integers.int64} (htw : ArrayAt m .Mint64 btc 0 (longs tw) S.M)
    {cell : VSet n} (hrep : SetRep (fun w => bv64 (tw w)) S.M cell)
    {p : Nat} (htv : PTree.get dense.id.«tv» le = some (.Vint (ir p))) (hp : p < n)
    (hQ : ∀ r : Int, ((cell.nextElem (some p) = none ∧ r = -1) ∨
        ∃ v : Nat, cell.nextElem (some p) = some v ∧ r = v) →
      Q.normal E0 e (PTree.set dense.id.«tv» (.Vint (ir r))
        (PTree.set x (.Vint (ir r)) le)) m) :
    Wp xi ge f (nextStepAt x) Q e le m := by
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
