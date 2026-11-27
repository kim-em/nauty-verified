import NautyVerified.Proofs.Refine.State
import NautyVerified.Proofs.Isautom.Scan
import NautyVerified.Proofs.Refine.Dialect
import NautyVerified.Proofs.Refine1.Syntax

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

/-- `t = nextelement(active, M, pos)` for `pos` holding `posOf q`, in dialect `D`. -/
theorem wp_nextG {D : Dialect} (hD : D.Sem) {n : Nat} {f : function} {Q : Post} {le : temp_env} {m : mem} {L : Loc}
    {ctx : Ctx n} {st : RefineSt n} {aw : Nat → Lib.Integers.int64} (hMok : D.okM L.M) (hok : Ok n L)
    (hm : Mem m L ctx st aw) (ht : Tmp le L st) {t : ident} {pe : expr} {q : Option Nat}
    (hpe : Exec.evalExpr ge empty_env le m pe = some (.Vint (ir (posOf q))))
    (hty : typeof pe = tint) (hq : posOf q < 64 * L.M)
    (hQ : ∀ r : Int, ((st.active.nextElem q = none ∧ r = -1) ∨
        ∃ v : Nat, st.active.nextElem q = some v ∧ r = v) →
      Q.normal E0 empty_env (PTree.set t (.Vint (ir r)) le) m) :
    Wp xi ge f (.Scall (some t) (.Evar dense.id.nextelement (tfun [tptr tulong, tint, tint] tint))
      [.Etempvar dense.id.active (tptr tulong), D.mE, pe]) Q empty_env le m := by
  obtain ⟨hmE, hmT⟩ := hD.mE (e := empty_env) (le := le) (m := m) hMok ht.m
  have hM1 := hok.M1
  have hM2 := hok.Mlt
  refine wp_call (vf := .Vptr Block.nextelement Ptrofs.zero) (targs := [tptr tulong, tint, tint])
    (tres := tint) (cc := Common.AST.cc_default) _ (Nextelement.nextSpec L.ba L.aofs L.M (posOf q) aw)
    (Nextelement.nextelement_satisfies _ _ _ _ _) rfl
    (by simp only [Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get Source.dense.id.nextelement (empty_env : env) = none from rfl,
      find_nextelement, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
    (by simp only [Exec.evalExprlist, hpe, hty, hmE, hmT]
        simp only [Exec.evalExpr, ht.active, typeof, cop])
    (by simp [Common.Globalenvs.Genv.find_funct, funct_nextelement]) Isautom.type_nextelement
    ⟨rfl, by cases q <;> simp [posOf], hq, hM1, by omega, Graph.wordsAt_of hm.act, hm.left⟩ ?_
  rintro t' v m' ⟨rfl, rfl, r, rfl, hspec⟩
  exact hQ r (next_eq hm.actRep hspec)

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
      [.Etempvar dense.id.active (tptr tulong), .Etempvar dense.id.m tint, pe]) Q empty_env le m :=
  wp_nextG D0_sem True.intro hok hm ht hpe hty hq hQ

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

section Generic
open NautyVerified.Proofs.Set (sk pv)
abbrev guardG (D : Dialect) (u0 u1 u2 u3 u4 u5 : Common.AST.ident) : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Olt (.Ederef (pi dense.id.«numcells») tint) (tv dense.id.«n») tint)
        (.Ssequence
          (.Ssequence
            (sk (.Sset dense.id.«split1» (tv dense.id.«hint»)))
            (.Sifthenelse
              (D.isE dense.id.«active» (tv dense.id.«split1»))
              (.Sset u1 (ci 1 tint))
              (.Ssequence
                (.Ssequence
                  (.Ssequence
                    (sk
                      (.Scall
                        (some u2)
                        (.Evar dense.id.«nextelement» (tfun [(tptr tulong), tint, tint] tint))
                        [(pv dense.id.«active»), D.mE, (tv dense.id.«split1»)]))
                    (.Sset u3 (.Ecast (tv u2) tint)))
                  (.Sset dense.id.«split1» (tv u3)))
                (.Sset u1 (.Ecast (.Ebinop .Oge (tv u3) (ci 0 tint) tint) tbool)))))
          (.Sifthenelse
            (tv u1)
            (sk (.Sset u0 (.Ecast (ci 1 tint) tbool)))
            (.Ssequence
              (.Ssequence
                (.Ssequence
                  (.Ssequence
                    (sk
                      (.Scall
                        (some u4)
                        (.Evar dense.id.«nextelement» (tfun [(tptr tulong), tint, tint] tint))
                        [(pv dense.id.«active»), D.mE, (.Eunop .Oneg (ci 1 tint) tint)]))
                    (.Sset u5 (.Ecast (tv u4) tint)))
                  (.Sset dense.id.«split1» (tv u5)))
                (.Sset u0 (.Ecast (.Ebinop .Oge (tv u5) (ci 0 tint) tint) tbool)))
              (.Sset u0 (.Ecast (tv u0) tbool)))))
        (.Sset u0 (ci 0 tint))))
    (.Sifthenelse (tv u0) .Sskip .Sbreak))
end Generic

/-- The six condition temporaries of the guard are distinct, and none is an
argument, `longcode`, `hint`, `maxpos` or `split1`. -/
def GuardOk (u : List ident) : Prop :=
  u.Pairwise (· ≠ ·) ∧ ∀ x ∈ u, x ∉ args ∧ x ≠ dense.id.longcode ∧ x ≠ dense.id.hint ∧
    x ≠ dense.id.maxpos ∧ x ≠ dense.id.split1

instance (u : List ident) : Decidable (GuardOk u) := by unfold GuardOk; infer_instance

theorem GuardOk.ne {u : List ident} (h : GuardOk u) (i j : Nat) (hij : i < j)
    (hj : j < u.length := by simp) : u[i]'(Nat.lt_trans hij hj) ≠ u[j] := by
  have := h.1
  induction u generalizing i j with
  | nil => simp at hj
  | cons a l ih =>
    rw [List.pairwise_cons] at this
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => exact this.1 _ (List.getElem_mem _)
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        exact ih ⟨this.2, fun x hx => h.2 x (by simp [hx])⟩ i j (by omega) (by simpa using hj) this.2

theorem GuardOk.fresh {u : List ident} (h : GuardOk u) {x : ident} (hx : x ∈ u) :
    x ∉ args ∧ x ≠ dense.id.longcode ∧ x ≠ dense.id.hint ∧ x ≠ dense.id.maxpos :=
  ⟨(h.2 x hx).1, (h.2 x hx).2.1, (h.2 x hx).2.2.1, (h.2 x hx).2.2.2.1⟩

theorem GuardOk.split1 {u : List ident} (h : GuardOk u) {x : ident} (hx : x ∈ u) :
    x ≠ dense.id.split1 := (h.2 x hx).2.2.2.2

set_option hygiene false in
/-- A side condition of the guard proof: by `decide`, or from `hT : GuardOk [u0, …, u5]`. -/
macro "gscr" : tactic => `(tactic| first
  | decide
  | (refine hT.fresh ?_; simp)
  | (refine hT.split1 ?_; simp)
  | (refine Ne.symm (hT.split1 ?_); simp)
  | exact (hT.ne 0 1 (by decide)) | exact (hT.ne 0 2 (by decide)) | exact (hT.ne 0 3 (by decide))
  | exact (hT.ne 0 4 (by decide)) | exact (hT.ne 0 5 (by decide)) | exact (hT.ne 1 2 (by decide))
  | exact (hT.ne 1 3 (by decide)) | exact (hT.ne 1 4 (by decide)) | exact (hT.ne 1 5 (by decide))
  | exact (hT.ne 2 3 (by decide)) | exact (hT.ne 2 4 (by decide)) | exact (hT.ne 2 5 (by decide))
  | exact (hT.ne 3 4 (by decide)) | exact (hT.ne 3 5 (by decide)) | exact (hT.ne 4 5 (by decide))
  | exact Ne.symm (hT.ne 0 1 (by decide)) | exact Ne.symm (hT.ne 0 2 (by decide))
  | exact Ne.symm (hT.ne 0 3 (by decide)) | exact Ne.symm (hT.ne 0 4 (by decide))
  | exact Ne.symm (hT.ne 0 5 (by decide)) | exact Ne.symm (hT.ne 1 2 (by decide))
  | exact Ne.symm (hT.ne 1 3 (by decide)) | exact Ne.symm (hT.ne 1 4 (by decide))
  | exact Ne.symm (hT.ne 1 5 (by decide)) | exact Ne.symm (hT.ne 2 3 (by decide))
  | exact Ne.symm (hT.ne 2 4 (by decide)) | exact Ne.symm (hT.ne 2 5 (by decide))
  | exact Ne.symm (hT.ne 3 4 (by decide)) | exact Ne.symm (hT.ne 3 5 (by decide))
  | exact Ne.symm (hT.ne 4 5 (by decide)))

/-- The loop guard in dialect `D`: continue with `split1 = pickSplit active hint`, or break. -/
theorem wp_guardG {D : Dialect} (hD : D.Sem) {u0 u1 u2 u3 u4 u5 : ident}
    (hT : GuardOk [u0, u1, u2, u3, u4, u5]) {f : function} {n : Nat} {Q : Post} {le : temp_env}
    {m : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n} {aw : Nat → Lib.Integers.int64}
    (hMok : D.okM L.M) (hok : Ok n L) (hm : Mem m L ctx st aw)
    (ht : Tmp le L st) (hi : StInv n L st)
    (hQb : ∀ le', (¬ st.numcells < n ∨ pickSplit st.active st.hint = none) → Tmp le' L st →
      Q.brk E0 empty_env le' m)
    (hQn : ∀ le' s, st.numcells < n → pickSplit st.active st.hint = some s → Tmp le' L st →
      PTree.get dense.id.split1 le' = some (.Vint (ir s)) → Q.normal E0 empty_env le' m) :
    Wp xi ge f (guardG D u0 u1 u2 u3 u4 u5) Q empty_env le m := by
  have hn0 := hok.n0
  have hnM := hok.nM
  have hnc2 := hi.ncSmall
  have hh := hi.hint
  have hMl := hok.Mlt
  have hnl := hok.nlt
  simp only [guardG, Set.sk]
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
      ht.set _ (by gscr)
    have hel := hD.isE (e := empty_env) (le := PTree.set dense.id.split1
      (.Vint (ir st.hint)) le) (s := dense.id.active)
      (a := tv dense.id.split1) hMok hMl hm.act ht1.active (by simp [Exec.evalExpr, temps_gss])
      rfl (c := st.hint) (by omega) hm.bit rfl
    rw [hm.actRep.2 _ (by omega)] at hel
    simp only [seqPost, Post.after, E0_append]
    apply wp_if_eval
    rw [hel, hD.isTy]
    cases hmem : st.active.mem st.hint
    · simp only [typeof, cop, Bool.false_eq_true, ite_false]
      wp_step; wp_step; wp_step; wp_step; wp_step
      refine wp_nextG hD (q := some st.hint) (pe := tv dense.id.split1) hMok hok hm ht1 (by simp [Exec.evalExpr, temps_gss, posOf])
        rfl (by simp [posOf]; omega) ?_
      intro r hr
      simp only [set_opttemp, seqPost, Post.after, E0_append]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss]
      apply wp_set_eval
      simp (disch := gscr) only [Exec.evalExpr, temps_gss, temps_gso, typeof, cop]
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
        rw [ite_eq_right (by gscr)]
        wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
        have ht2 : Tmp (PTree.set u1 (.Vint Lib.Integers.Int.zero) (PTree.set dense.id.split1
            (.Vint (ir (-1))) (PTree.set u3 (.Vint (ir (-1))) (PTree.set u2
            (.Vint (ir (-1))) (PTree.set dense.id.split1 (.Vint (ir st.hint)) le))))) L st :=
          (((ht1.set _ (by gscr)).set _ (by gscr)).set _ (by gscr)).set _ (by gscr)
        refine wp_nextG hD (q := none) (pe := .Eunop .Oneg (ci 1 tint) tint) hMok hok hm ht2 rfl rfl
          (by simp [posOf]; omega) ?_
        intro r2 hr2
        simp only [set_opttemp, seqPost, Post.after, E0_append]
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop]
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gss]
        apply wp_set_eval
        simp (disch := gscr) only [Exec.evalExpr, temps_gss, temps_gso, typeof, cop]
        have hr3 : -1 ≤ r2 ∧ r2 < 2147483648 := by
          rcases hr2 with ⟨-, rfl⟩ | ⟨v, hv, rfl⟩
          · omega
          · have := VSet.mem_lt (VSet.nextElem_eq_some_iff.1 hv).1; omega
        rw [ir_lt (a := r2) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
        have ht3 := (((ht2.set (x := u4) (.Vint (ir r2)) (by gscr)).set (x := u5)
          (.Vint (ir r2)) (by gscr)).set (x := dense.id.split1) (.Vint (ir r2)) (by gscr))
        rcases hr2 with ⟨hnone2, rfl⟩ | ⟨v, hv, rfl⟩
        · simp only [show decide ((-1 : Int) < 0) = true from rfl, Bool.not_true, Val.of_bool,
            Bool.false_eq_true, ite_false, cop]
          apply wp_set_eval
          simp only [Exec.evalExpr, temps_gss, typeof, cop]
          refine wp_tail u0 false (by rw [temps_gss]; rfl) (fun h => absurd h (by gscr))
            (fun _ => ?_)
          exact hQb _ (.inr (by simp [pickSplit, hmem, hnone, hnone2])) ((ht3.set _ (by gscr)).set _
            (by gscr))
        · simp only [show decide ((v : Int) < 0) = false by simp, Bool.not_false, Val.of_bool,
            ite_true, cop]
          apply wp_set_eval
          simp only [Exec.evalExpr, temps_gss, typeof, cop]
          have hvn := VSet.mem_lt (VSet.nextElem_eq_some_iff.1 hv).1
          refine wp_tail u0 true (by rw [temps_gss]; rfl) (fun _ => ?_)
            (fun h => absurd h (by gscr))
          refine hQn _ v hlt (by simp [pickSplit, hmem, hnone, hv]) ((ht3.set _ (by gscr)).set _
            (by gscr)) ?_
          simp (disch := gscr) only [temps_gso, temps_gss]
      · simp only [show decide ((v : Int) < 0) = false by simp, Bool.not_false, Val.of_bool,
          ite_true, cop]
        apply wp_if_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop]
        rw [ite_eq_left (by gscr)]
        wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, typeof, cop]
        simp only [seqPost, Post.after, E0_append]
        have hvn := VSet.mem_lt (VSet.nextElem_eq_some_iff.1 hv).1
        refine wp_tail u0 true (by rw [temps_gss]; rfl) (fun _ => ?_) (fun h => absurd h (by gscr))
        refine hQn _ v hlt (by simp [pickSplit, hmem, hv])
          ((((ht1.set _ (by gscr)).set _ (by gscr)).set _ (by gscr)).set _ (by gscr) |>.set _
            (by gscr)) ?_
        simp (disch := gscr) only [temps_gso, temps_gss]
    · simp only [typeof, cop, ite_true]
      apply wp_set_eval
      simp only [Exec.evalExpr]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      rw [ite_eq_left (by gscr)]
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, typeof, cop]
      simp only [seqPost, Post.after, E0_append]
      refine wp_tail u0 true (by rw [temps_gss]; rfl) (fun _ => ?_) (fun h => absurd h (by gscr))
      refine hQn _ st.hint hlt (by simp [pickSplit, hmem]) ((ht1.set _ (by gscr)).set _ (by gscr)) ?_
      rw [temps_gso _ _ (by gscr), temps_gso _ _ (by gscr), temps_gss]
  · rw [ite_eq_right (by simpa using hlt)]
    apply wp_set_eval
    simp only [Exec.evalExpr, seqPost, Post.after, E0_append]
    refine wp_tail u0 false (by rw [temps_gss]; rfl) (fun h => absurd h (by gscr))
      (fun _ => ?_)
    exact hQb _ (.inl hlt) (ht.set _ (by gscr))


/-- The loop guard: continue with `split1 = pickSplit active hint`, or break. -/
theorem wp_guard {n : Nat} {Q : Post} {le : temp_env} {m : mem} {L : Loc} {ctx : Ctx n}
    {st : RefineSt n} {aw : Nat → Lib.Integers.int64} (hok : Ok n L) (hm : Mem m L ctx st aw)
    (ht : Tmp le L st) (hi : StInv n L st)
    (hQb : ∀ le', (¬ st.numcells < n ∨ pickSplit st.active st.hint = none) → Tmp le' L st →
      Q.brk E0 empty_env le' m)
    (hQn : ∀ le' s, st.numcells < n → pickSplit st.active st.hint = some s → Tmp le' L st →
      PTree.get dense.id.split1 le' = some (.Vint (ir s)) → Q.normal E0 empty_env le' m) :
    Wp xi ge dense.fn.refine guard Q empty_env le m :=
  wp_guardG D0_sem (by decide) True.intro hok hm ht hi hQb hQn

theorem guard_D0 : guard = guardG D0 (idOf 709) (idOf 710) (idOf 711) (idOf 712) (idOf 713)
    (idOf 714) := rfl

theorem guard_D1 : Refine1.guard = guardG D1 (idOf 707) (idOf 708) (idOf 709) (idOf 710)
    (idOf 711) (idOf 712) := rfl

end NautyVerified.Proofs.Refine
