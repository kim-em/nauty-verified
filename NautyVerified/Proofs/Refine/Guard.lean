import NautyVerified.Proofs.Refine.State
import NautyVerified.Proofs.Isautom.Scan

/-!
# `refine`'s loop guard

`wp_guard`: the loop test `*numcells < n && (split1 = hint, ISELEMENT(active,
split1) || (split1 = nextelement(active, M, split1)) >= 0 || (split1 =
nextelement(active, M, -1)) >= 0)` continues with `split1` holding
HexGraphIso's `pickSplit active hint`, and breaks exactly when `numcells ≥ n`
or `pickSplit` finds nothing. `next_eq` reads `nextelement`'s result as
`VSet.nextElem`.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (longs BitTable)
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

/-- The `int` position `nextelement` is called with for `q`. -/
def posOf : Option Nat → Int
  | none => -1
  | some p => p

/-- `nextelement`'s result on words representing `s` is `s.nextElem`. -/
theorem next_eq {n M : Nat} {ws : Nat → Lib.Integers.int64} {s : VSet n}
    (hs : SetRep (fun w => bv64 (ws w)) M s) {q : Option Nat} {r : Int}
    (h : Nextelement.NextSpec (fun w => bv64 (ws w)) M (posOf q) r) :
    (s.nextElem q = none ∧ r = -1) ∨ ∃ v : Nat, s.nextElem q = some v ∧ r = v := by
  have hst : ∀ v : Nat, posOf q < v ↔ VSet.scanStart q ≤ v := fun v => by
    cases q <;> simp [posOf, VSet.scanStart] <;> omega
  rcases h with ⟨rfl, hnone⟩ | ⟨v, rfl, hpv, hin, hmin⟩
  · left
    refine ⟨?_, rfl⟩
    rcases hq : s.nextElem q with _ | v
    · rfl
    · obtain ⟨hm, hv, -⟩ := VSet.nextElem_eq_some_iff.1 hq
      exact absurd ((Isautom.inSet_iff hs).2 hm) (hnone v ((hst v).2 hv))
  · right
    refine ⟨v, VSet.nextElem_eq_some_iff.2 ⟨(Isautom.inSet_iff hs).1 hin, (hst v).1 hpv,
      fun w hw hwv => ?_⟩, rfl⟩
    rcases hm : s.mem w with _ | _
    · rfl
    · exact absurd ((Isautom.inSet_iff hs).2 hm) (hmin w ((hst w).2 hw) (by omega))

/-- `*numcells`. -/
theorem eval_numcells {n : Nat} {e : env} {le : temp_env} {m : mem} {L : Loc} {ctx : Ctx n}
    {st : RefineSt n} {aw : Nat → Lib.Integers.int64} (hm : Mem m L ctx st aw) (ht : Tmp le L st) :
    Exec.evalExpr ge e le m (.Ederef (.Etempvar dense.id.numcells (tptr tint)) tint) =
      some (.Vint (ir st.numcells)) := by
  simp only [Exec.evalExpr, ht.numcells, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  apply load_array hm.nc (show 0 < 1 by decide)
  unfold elemOfs
  rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ]

/-- `t = nextelement(active, M, pos)` for `pos` holding `posOf q`. -/
theorem wp_next {n : Nat} {f : function} {Q : Post} {le : temp_env} {m : mem} {L : Loc}
    {ctx : Ctx n} {st : RefineSt n} {aw : Nat → Lib.Integers.int64} (hok : Ok n L)
    (hm : Mem m L ctx st aw) (ht : Tmp le L st) {t : ident} {pe : expr} {q : Option Nat}
    (hpe : Exec.evalExpr ge empty_env le m pe = some (.Vint (ir (posOf q))))
    (hty : typeof pe = tint) (hq : posOf q < 64 * L.M)
    (hQ : ∀ r : Int, ((st.active.nextElem q = none ∧ r = -1) ∨
        ∃ v : Nat, st.active.nextElem q = some v ∧ r = v) →
      Q.normal E0 empty_env (PTree.set t (.Vint (ir r)) le) m) :
    Wp xi ge f (.Scall (some t) (.Evar dense.id.nextelement (tfun [tptr tulong, tint, tint] tint))
      [.Etempvar dense.id.active (tptr tulong), .Etempvar dense.id.m tint, pe]) Q empty_env le m := by
  have hM1 := hok.M1
  have hM2 := hok.Mlt
  refine wp_call (vf := .Vptr Block.nextelement Ptrofs.zero) (targs := [tptr tulong, tint, tint])
    (tres := tint) (cc := Common.AST.cc_default) _ (Nextelement.nextSpec L.ba L.aofs L.M (posOf q) aw)
    (Nextelement.nextelement_satisfies _ _ _ _ _) rfl
    (by simp only [Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get Source.dense.id.nextelement (empty_env : env) = none from rfl,
      find_nextelement, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
    (by simp only [Exec.evalExprlist, hpe, hty]
        simp only [Exec.evalExpr, ht.active, ht.m, typeof, cop])
    (by simp [Common.Globalenvs.Genv.find_funct, funct_nextelement]) Isautom.type_nextelement
    ⟨rfl, by cases q <;> simp [posOf], hq, hM1, by omega, Graph.wordsAt_of hm.act, hm.left⟩ ?_
  rintro t' v m' ⟨rfl, rfl, r, rfl, hspec⟩
  exact hQ r (next_eq hm.actRep hspec)

end NautyVerified.Proofs.Refine
