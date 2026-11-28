import NautyVerified.Proofs.Search.Node.FirstEnd
import NautyVerified.Proofs.Search.Node.OtherBodySteps
import NautyVerified.Proofs.Search.Firstterminal.Satisfies

/-!
# Small steps of `firstpathnode0`'s body

- `chooseTarget_true_eq`: HexGraphIso's `chooseTarget true`, case by case;
- `wp_fpnInvstat0`: the invariant statistics do nothing when `qinvar` is 0;
- `wp_fpnFirst`: `t713 = nextelement(tcell, M, -1); t714 = t713; tv = t714; tv1 = t714;`
  is the target cell's first element;
- `wp_fpnLeaf`: `if (numcells == n) { firstterminal(lab, level); …; return level - 1; }`
  installs the first leaf (`firstterminal`) and returns `level - 1`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk longs)
open NautyVerified.Proofs.Refine (tv)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

/-- `chooseTarget true`, case by case. -/
theorem chooseTarget_true_eq (ctx : Ctx n) (tl level nc : Nat) (st : Search n) :
    chooseTarget true ctx tl level nc st =
      if nc ≠ n then
        (((maketargetcell ctx st.lab st.ptn level tl (-1)).1 : Int),
         (maketargetcell ctx st.lab st.ptn level tl (-1)).2.1,
         (maketargetcell ctx st.lab st.ptn level tl (-1)).2.2,
         { { st with tctotal := st.tctotal + (maketargetcell ctx st.lab st.ptn level tl (-1)).2.2 } with
           firsttc := st.firsttc.set! level ((maketargetcell ctx st.lab st.ptn level tl (-1)).1 : Int) })
      else ((-1 : Int), VSet.empty, 0, { st with firsttc := st.firsttc.set! level (-1) }) := by
  unfold chooseTarget
  by_cases hc : nc = n
  · simp [hc]
  · simp [hc]

/-- The invariant statistics, with `qinvar` 0. -/
theorem wp_fpnInvstat0 {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bq : block}
    (heq : PTree.get dense.id.qinvar e = some (bq, tint))
    (hqv : Mem.load .Mint32 m bq (zOfInt 0) = some (.Vint (ir 0)))
    (hQ : Q.normal E0 e le m) :
    Wp xi ge f (sk Firstpathnode.invstat) Q e le m := by
  wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_local heq hqv]
  simp only [Exec.evalExpr, typeof, cop]
  rw [ir_lt (a := 0) (b := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
  simp only [Int.lt_irrefl, decide_false]
  exact wp_skip hQ

/-- `t713 = nextelement(tcell, M, -1); t714 = t713; tv = t714; tv1 = t714;` -/
abbrev fpnFirst : statement :=
  .Ssequence
    (.Ssequence
      (.Ssequence
        (sk (.Scall (some (idOf 713))
          (.Evar dense.id.«nextelement» (tfun [tptr tulong, tint, tint] tint))
          [.Etempvar dense.id.«tcell» (tptr tulong), .Evar dense.id.«nauty:m» tint,
           .Eunop .Oneg (ci 1 tint) tint]))
        (.Sset (idOf 714) (.Ecast (tv (idOf 713)) tint)))
      (.Sset dense.id.«tv» (tv (idOf 714))))
    (.Sset dense.id.«tv1» (tv (idOf 714)))

theorem wp_fpnFirst {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    (h : SearchAt m S ctx st pre nsp)
    (hge : ∀ x ∈ [dense.id.«nextelement», dense.id.«nauty:m»], PTree.get x e = none)
    {btc : block} (htl : PTree.get dense.id.tcell le = some (.Vptr btc Ptrofs.zero))
    {tw : Nat → Lib.Integers.int64} (htw : ArrayAt m .Mint64 btc 0 (longs tw) S.M)
    {cell : VSet n} (hrep : SetRep (fun w => bv64 (tw w)) S.M cell)
    (hQ : ∀ r : Int, ((cell.nextElem none = none ∧ r = -1) ∨
        ∃ v : Nat, cell.nextElem none = some v ∧ r = v) →
      Q.normal E0 e (PTree.set dense.id.«tv1» (.Vint (ir r)) (PTree.set dense.id.«tv» (.Vint (ir r))
        (PTree.set (idOf 714) (.Vint (ir r)) (PTree.set (idOf 713) (.Vint (ir r)) le)))) m) :
    Wp xi ge f fpnFirst Q e le m := by
  have hM1 := h.M1
  have hMl := h.Mlt
  have hnM := h.nM
  simp only [List.forall_mem_cons] at hge
  obtain ⟨g1, g2, -⟩ := hge
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.nextelement Ptrofs.zero) (targs := [tptr tulong, tint, tint])
    (tres := tint) (cc := Common.AST.cc_default)
    (vargs := [.Vptr btc Ptrofs.zero, .Vint (ir S.M), .Vint (ir (-1))]) _
    (Nextelement.nextSpec btc Ptrofs.zero S.M (Refine.posOf none) tw)
    (Nextelement.nextelement_satisfies _ _ _ _ _) rfl ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_nextelement]) Isautom.type_nextelement
    ⟨rfl, by simp [Refine.posOf], by simp [Refine.posOf]; omega, hM1, by omega,
      Graph.wordsAt_of htw, h.tables.left⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, g1, find_nextelement, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode]
  · simp only [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, g2, find_m, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode, Mem.loadv, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
      h.fixed.mm.load, htl, Refine.tv, typeof, cop]
    rfl
  · rintro t' v m' ⟨rfl, rfl, r, rfl, hspec⟩
    simp only [set_opttemp, seqPost, Post.after, E0_append]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, Refine.tv]
    apply wp_set_eval
    rw [Exec.evalExpr, temps_gso _ _ (show idOf 714 ≠ dense.id.tv by decide), temps_gss]
    simp only [E0_append]
    exact hQ r (Refine.next_eq hrep hspec)

set_option maxHeartbeats 4000000 in
/-- `if (numcells == n) { firstterminal(lab, level); …; return level - 1; }`. -/
theorem wp_fpnLeaf {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {level nc : Nat} {bnc : block}
    (h : SearchAt m S ctx st true false)
    (hge : ∀ x ∈ [dense.id.«nauty:n», dense.id.«nauty:firstterminal», dense.id.«nauty:userlevelproc»,
      dense.id.«nauty:getcanon», dense.id.«nauty:usercanonproc»], PTree.get x e = none)
    (hfr : f.fn_return = tint)
    (henc : PTree.get dense.id.numcells e = some (bnc, tint))
    (hncv : Mem.load .Mint32 m bnc (zOfInt 0) = some (.Vint (ir nc))) (hncl : nc ≤ n)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hl1 : 1 ≤ level) (hln : level ≤ n)
    (hQl : nc = n → ∀ m', SearchAt m' S ctx (firstterminal level st) false false → SFrame m m' S →
      match Mem.free_list m' (blocks_of_env ge e) with
      | some m'' => Q.ret E0 (.Vint (ir ((level : Int) - 1))) m''
      | none => False)
    (hQn : nc ≠ n → Q.normal E0 e le m) :
    Wp xi ge f Firstpathnode.leaf Q e le m := by
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at hge
  obtain ⟨g1, g2, g3, g4, g5⟩ := hge
  have hnl := h.nlt
  apply wp_if_eval
  rw [Exec.evalExpr, eval_local henc hncv, eval_gint g1 find_n h.fixed.nn]
  simp only [typeof, cop]
  rw [ir_eq (a := (nc : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hne : nc = n
  · rw [ite_eq_left (by simp [hne])]
    wp_step; wp_step; wp_step
    refine wp_call (vf := .Vptr Block.firstterminalFn Ptrofs.zero)
      (targs := [tptr tint, tint]) (tres := .Tvoid) (cc := Common.AST.cc_default)
      (vargs := [.Vptr S.bl S.lofs, .Vint (ir level)])
      (.Internal dense.fn.«nauty:firstterminal») _
      (Firstterminal.firstterminal_satisfies S ctx st level) rfl ?_ ?_
      (by simp [Common.Globalenvs.Genv.find_funct, funct_firstterminalFn]) rfl
      ⟨rfl, h, hl1, hln⟩ ?_
    · simp only [Exec.evalExpr, Exec.lvalOfVar, g2, find_firstterminalFn, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode]
    · simp only [Exec.evalExprlist, Exec.evalExpr, hlab, hlev, Refine.tv, typeof, cop]
    rintro t v m' ⟨rfl, h', hF⟩
    simp only [set_opttemp, seqPost, Post.after, E0_append]
    -- userlevelproc
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, Exec.lvalOfVar, g3, find_userlevelproc, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h'.fixed.userlevelproc.load, typeof]
    rw [show Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) tint
      (tptr .Tvoid) m' = some (.Vlong (Lib.Integers.Int64.repr
        (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0))))) from rfl]
    dsimp only
    rw [ne_null]
    dsimp only
    rw [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m' = some false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    -- `getcanon && usercanonproc != NULL`
    wp_step; wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [eval_gint g4 find_getcanon h'.fixed.getcanon]
    simp only [typeof]
    rw [show Cfrontend.Cop.bool_val (.Vint (ir 1)) tint m' = some true from rfl]
    simp only [ite_true]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, Exec.lvalOfVar, g5, find_usercanonproc, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h'.fixed.usercanonproc.load, typeof]
    rw [show Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) tint
      (tptr .Tvoid) m' = some (.Vlong (Lib.Integers.Int64.repr
        (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0))))) from rfl]
    dsimp only
    rw [ne_null]
    dsimp only
    rw [show Cfrontend.Cop.sem_cast (Val.of_bool false) tint tbool m' =
      some (Val.of_bool false) from rfl]
    dsimp only
    simp only [seqPost, Post.after, E0_append]
    apply wp_if_eval
    simp only [Exec.evalExpr, Refine.tv, temps_gss, typeof]
    rw [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m' = some false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    apply wp_return_some_eval
    simp only [Exec.evalExpr, Refine.tv, temps_gso _ _ (show dense.id.level ≠ idOf 709 by decide),
      hlev, typeof, cop, hfr]
    rw [show Lib.Integers.Int.repr (zOfInt 1) = ir 1 from rfl, ir_sub]
    exact hQl hne m' h' hF
  · rw [ite_eq_right (by simp; omega)]
    exact wp_skip (hQn hne)

end NautyVerified.Proofs.Search
