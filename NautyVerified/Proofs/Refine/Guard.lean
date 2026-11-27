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

set_option linter.unusedSimpArgs false

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

/-- `if (t) ; else break;` on a boolean temporary. -/
theorem wp_tail {f : function} {Q : Post} {le : temp_env} {m : mem} (t : ident) (b : Bool)
    (h : PTree.get t le = some (.Vint (if b then Lib.Integers.Int.one else Lib.Integers.Int.zero)))
    (hn : b = true → Q.normal E0 empty_env le m) (hb : b = false → Q.brk E0 empty_env le m) :
    Wp xi ge f (.Sifthenelse (tv t) .Sskip .Sbreak) Q empty_env le m := by
  apply wp_if_eval
  simp only [Exec.evalExpr, h, typeof]
  cases b
  · simp only [Bool.false_eq_true, ite_false, cop]
    rw [ite_eq_right (by decide)]
    exact wp_break (hb rfl)
  · simp only [ite_true, cop]
    rw [ite_eq_left (by decide)]
    exact wp_skip (hn rfl)

/-- The loop guard: continue with `split1 = pickSplit active hint`, or break. -/
theorem wp_guard {n : Nat} {Q : Post} {le : temp_env} {m : mem} {L : Loc} {ctx : Ctx n}
    {st : RefineSt n} {aw : Nat → Lib.Integers.int64} (hok : Ok n L) (hm : Mem m L ctx st aw)
    (ht : Tmp le L st) (hi : StInv n L st)
    (hQb : ∀ le', (¬ st.numcells < n ∨ pickSplit st.active st.hint = none) → Tmp le' L st →
      Q.brk E0 empty_env le' m)
    (hQn : ∀ le' s, st.numcells < n → pickSplit st.active st.hint = some s → Tmp le' L st →
      PTree.get dense.id.split1 le' = some (.Vint (ir s)) → Q.normal E0 empty_env le' m) :
    Wp xi ge dense.fn.refine guard Q empty_env le m := by
  have hn0 := hok.n0
  have hnM := hok.nM
  have hnc2 := hi.ncSmall
  have hh := hi.hint
  have hMl := hok.Mlt
  have hnl := hok.nlt
  simp only [guard, Set.sk]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_numcells hm ht, show Exec.evalExpr ge empty_env le m (tv dense.id.n) = _
    from ht.n]
  simp only [typeof, cop]
  rw [ir_lt (a := (st.numcells : Int)) (b := n) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hlt : st.numcells < n
  · rw [ite_eq_left (by simpa using hlt)]
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, ht.hint]
    have ht1 : Tmp (PTree.set dense.id.split1 (.Vint (ir st.hint)) le) L st :=
      ht.set _ (by decide)
    have hel := Set.eval_isElement (e := empty_env) (le := PTree.set dense.id.split1
      (.Vint (ir st.hint)) le) (s := dense.id.active) (bitId := dense.id.«naugraph:bit»)
      (a := tv dense.id.split1) hm.act (by omega) ht1.active (by simp [Exec.evalExpr, temps_gss])
      rfl (c := st.hint) (by omega) (by omega) hm.bit rfl find_naugraphBit
    rw [hm.actRep.2 _ (by omega)] at hel
    simp only [seqPost, Post.after, E0_append]
    apply wp_if_eval
    rw [hel]
    cases hmem : st.active.mem st.hint
    · simp only [typeof, cop, Bool.false_eq_true, ite_false]
      wp_step; wp_step; wp_step; wp_step; wp_step
      refine wp_next (q := some st.hint) (pe := tv dense.id.split1) hok hm ht1 (by simp [Exec.evalExpr, temps_gss, posOf])
        rfl (by simp [posOf]; omega) ?_
      intro r hr
      simp only [set_opttemp, seqPost, Post.after, E0_append]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss]
      apply wp_set_eval
      simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, temps_gso, typeof, cop]
      have hr1 : -1 ≤ r ∧ r < 2147483648 := by
        rcases hr with ⟨-, rfl⟩ | ⟨v, hv, rfl⟩
        · omega
        · have := VSet.mem_lt (VSet.nextElem_eq_some_iff.1 hv).1; omega
      rw [ir_lt (a := r) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
      rcases hr with ⟨hnone, rfl⟩ | ⟨v, hv, rfl⟩
      · simp only [show decide ((-1 : Int) < 0) = true from rfl, Bool.not_true, Val.of_bool,
          Bool.false_eq_true, ite_false, cop]
        apply wp_if_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop]
        rw [ite_eq_right (by decide)]
        wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
        have ht2 : Tmp (PTree.set (idOf 710) (.Vint Lib.Integers.Int.zero) (PTree.set dense.id.split1
            (.Vint (ir (-1))) (PTree.set (idOf 712) (.Vint (ir (-1))) (PTree.set (idOf 711)
            (.Vint (ir (-1))) (PTree.set dense.id.split1 (.Vint (ir st.hint)) le))))) L st :=
          (((ht1.set _ (by decide)).set _ (by decide)).set _ (by decide)).set _ (by decide)
        refine wp_next (q := none) (pe := .Eunop .Oneg (ci 1 tint) tint) hok hm ht2 rfl rfl
          (by simp [posOf]; omega) ?_
        intro r2 hr2
        simp only [set_opttemp, seqPost, Post.after, E0_append]
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop]
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gss]
        apply wp_set_eval
        simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, temps_gso, typeof, cop]
        have hr3 : -1 ≤ r2 ∧ r2 < 2147483648 := by
          rcases hr2 with ⟨-, rfl⟩ | ⟨v, hv, rfl⟩
          · omega
          · have := VSet.mem_lt (VSet.nextElem_eq_some_iff.1 hv).1; omega
        rw [ir_lt (a := r2) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
        have ht3 := (((ht2.set (x := idOf 713) (.Vint (ir r2)) (by decide)).set (x := idOf 714)
          (.Vint (ir r2)) (by decide)).set (x := dense.id.split1) (.Vint (ir r2)) (by decide))
        rcases hr2 with ⟨hnone2, rfl⟩ | ⟨v, hv, rfl⟩
        · simp only [show decide ((-1 : Int) < 0) = true from rfl, Bool.not_true, Val.of_bool,
            Bool.false_eq_true, ite_false, cop]
          apply wp_set_eval
          simp only [Exec.evalExpr, temps_gss, typeof, cop]
          refine wp_tail (idOf 709) false (by rw [temps_gss]; rfl) (fun h => absurd h (by decide))
            (fun _ => ?_)
          exact hQb _ (.inr (by simp [pickSplit, hmem, hnone, hnone2])) ((ht3.set _ (by decide)).set _
            (by decide))
        · simp only [show decide ((v : Int) < 0) = false by simp, Bool.not_false, Val.of_bool,
            ite_true, cop]
          apply wp_set_eval
          simp only [Exec.evalExpr, temps_gss, typeof, cop]
          have hvn := VSet.mem_lt (VSet.nextElem_eq_some_iff.1 hv).1
          refine wp_tail (idOf 709) true (by rw [temps_gss]; rfl) (fun _ => ?_)
            (fun h => absurd h (by decide))
          refine hQn _ v hlt (by simp [pickSplit, hmem, hnone, hv]) ((ht3.set _ (by decide)).set _
            (by decide)) ?_
          simp (config := {decide := true}) only [temps_gso, temps_gss]
      · simp only [show decide ((v : Int) < 0) = false by simp, Bool.not_false, Val.of_bool,
          ite_true, cop]
        apply wp_if_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop]
        rw [ite_eq_left (by decide)]
        wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, typeof, cop]
        simp only [seqPost, Post.after, E0_append]
        have hvn := VSet.mem_lt (VSet.nextElem_eq_some_iff.1 hv).1
        refine wp_tail (idOf 709) true (by rw [temps_gss]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
        refine hQn _ v hlt (by simp [pickSplit, hmem, hv])
          ((((ht1.set _ (by decide)).set _ (by decide)).set _ (by decide)).set _ (by decide) |>.set _
            (by decide)) ?_
        simp (config := {decide := true}) only [temps_gso, temps_gss]
    · simp only [typeof, cop, ite_true]
      apply wp_set_eval
      simp only [Exec.evalExpr]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      rw [ite_eq_left (by decide)]
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, typeof, cop]
      simp only [seqPost, Post.after, E0_append]
      refine wp_tail (idOf 709) true (by rw [temps_gss]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
      refine hQn _ st.hint hlt (by simp [pickSplit, hmem]) ((ht1.set _ (by decide)).set _ (by decide)) ?_
      rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gss]
  · rw [ite_eq_right (by simpa using hlt)]
    apply wp_set_eval
    simp only [Exec.evalExpr, seqPost, Post.after, E0_append]
    refine wp_tail (idOf 709) false (by rw [temps_gss]; rfl) (fun h => absurd h (by decide))
      (fun _ => ?_)
    exact hQb _ (.inl hlt) (ht.set _ (by decide))

end NautyVerified.Proofs.Refine
