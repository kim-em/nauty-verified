import NautyVerified.Proofs.Search.Node.OtherLoop
import NautyVerified.Proofs.Search.Node.NodePrologue

/-!
# Small steps of `othernode0`'s body

- `wp_otherKill`: `t708 = nauty_kill_request; if (t708) return -12;`, reading 0;
- `wp_codeSet`: `code = (short)refcode;` for a code below `2^15`;
- `wp_invstat0`: the invariant statistics do nothing when `qinvar` is 0;
- `wp_userNode`: `if (usernodeproc != NULL) …` does nothing: the pinned
  configuration has no node callback;
- `wp_firstNext`: `t714 = nextelement(tcell, M, -1); t715 = t714; tv = t715; tv1 = t715;`
  is the target cell's first element.
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

/-- `t708 = nauty_kill_request; if (t708) return -12;` reading 0. -/
theorem wp_otherKill {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    (hge : PTree.get dense.id.«nauty_kill_request» e = none)
    (hQ : Q.normal [killEv] e (PTree.set (idOf 708) (.Vint Int.zero) le) m) :
    Wp xi ge f (.Ssequence
      (sk (.Sbuiltin (some (idOf 708)) (.EF_vload .Mint32)
        [tptr (Cfrontend.Ctypes.Tint .I32 .Signed NautyVerified.Proofs.vattr)]
        [.Eaddrof (.Evar dense.id.«nauty_kill_request»
            (Cfrontend.Ctypes.Tint .I32 .Signed NautyVerified.Proofs.vattr))
          (tptr (Cfrontend.Ctypes.Tint .I32 .Signed NautyVerified.Proofs.vattr))]))
      (.Sifthenelse (.Etempvar (idOf 708) (Cfrontend.Ctypes.Tint .I32 .Signed NautyVerified.Proofs.vattr))
        (sk (.Sreturn (some (.Eunop .Oneg (ci 12 tint) tint)))) .Sskip)) Q e le m := by
  wp_step; wp_step; wp_step
  refine wp_builtin (vargs := [.Vptr Block.killRequest Ptrofs.zero]) (t := [killEv])
    (vres := .Vint Int.zero) (m' := m) ?_ ?_ ?_
  · simp only [Exec.evalExprlist, Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar, hge,
      find_killRequest, typeof]
    rfl
  · have hv := volatile_load_vol (ge := Genv.to_senv ge.genv_genv) .Mint32 m Block.killRequest
      Ptrofs.zero dense.id.«nauty_kill_request» (.EVint Int.zero) (.Vint Int.zero)
      volatile_killRequest senv_find_killRequest (ev_match_int _)
    exact volatile_load_sem_intro _ _ _ _ _ hv
  simp only [set_opttemp, seqPost, Post.after]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, typeof]
  rw [show Cfrontend.Cop.bool_val (.Vint Int.zero)
    (Cfrontend.Ctypes.Tint .I32 .Signed NautyVerified.Proofs.vattr) m = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  exact hQ

/-- `code = (short)refcode;` -/
theorem wp_codeSet {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bk : block}
    {c : Nat} (hek : PTree.get dense.id.refcode e = some (bk, tint))
    (hkv : Mem.load .Mint32 m bk (zOfInt 0) = some (.Vint (ir c))) (hc : c < 32768)
    (hQ : Q.normal E0 e (PTree.set dense.id.code (.Vint (ir c)) le) m) :
    Wp xi ge f (sk (.Sset dense.id.«code» (.Ecast (.Ecast (.Evar dense.id.«refcode» tint) tshort)
      tshort))) Q e le m := by
  wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, Exec.evalExpr, eval_local hek hkv]
  simp only [typeof, cop, sign_ext16_ir (a := (c : Int)) (by omega) (by omega)]
  exact hQ

/-- The invariant statistics, with `qinvar` 0. -/
theorem wp_invstat0 {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bq : block}
    (heq : PTree.get dense.id.qinvar e = some (bq, tint))
    (hqv : Mem.load .Mint32 m bq (zOfInt 0) = some (.Vint (ir 0)))
    (hQ : Q.normal E0 e le m) :
    Wp xi ge f (sk Othernode.invstat) Q e le m := by
  wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_local heq hqv]
  simp only [Exec.evalExpr, typeof, cop]
  rw [ir_lt (a := 0) (b := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
  simp only [Int.lt_irrefl, decide_false]
  exact wp_skip hQ

/-- `if (usernodeproc != NULL) …`: no node callback. -/
theorem wp_userNode {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    (hE : PTree.get dense.id.«nauty:usernodeproc» e = none) {τ : Cfrontend.Ctypes.type}
    {call : statement} (hQ : Q.normal E0 e le m) :
    Wp xi ge f (sk (.Sifthenelse (.Ebinop .One (.Evar dense.id.«nauty:usernodeproc» (tptr τ))
      (.Ecast (ci 0 tint) (tptr .Tvoid)) tint) call .Sskip)) Q e le m := by
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar, hE, find_usernodeproc, Exec.derefLoc,
    Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h.fixed.usernodeproc.load, typeof]
  exact wp_skip hQ

/-- `t714 = nextelement(tcell, M, -1); t715 = t714; tv = t715; tv1 = t715;` -/
abbrev firstNext : statement :=
  .Ssequence
    (.Ssequence
      (.Ssequence
        (sk (.Scall (some (idOf 714))
          (.Evar dense.id.«nextelement» (tfun [tptr tulong, tint, tint] tint))
          [.Etempvar dense.id.«tcell» (tptr tulong), .Evar dense.id.«nauty:m» tint,
           .Eunop .Oneg (ci 1 tint) tint]))
        (.Sset (idOf 715) (.Ecast (tv (idOf 714)) tint)))
      (.Sset dense.id.«tv» (tv (idOf 715))))
    (.Sset dense.id.«tv1» (tv (idOf 715)))

theorem wp_firstNext {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    (h : SearchAt m S ctx st pre nsp)
    (hge : ∀ x ∈ [dense.id.«nextelement», dense.id.«nauty:m»], PTree.get x e = none)
    {btc : block} (htl : PTree.get dense.id.tcell le = some (.Vptr btc Ptrofs.zero))
    {tw : Nat → Lib.Integers.int64} (htw : ArrayAt m .Mint64 btc 0 (longs tw) S.M)
    {cell : VSet n} (hrep : SetRep (fun w => bv64 (tw w)) S.M cell)
    (hQ : ∀ r : Int, ((cell.nextElem none = none ∧ r = -1) ∨
        ∃ v : Nat, cell.nextElem none = some v ∧ r = v) →
      Q.normal E0 e (PTree.set dense.id.«tv1» (.Vint (ir r)) (PTree.set dense.id.«tv» (.Vint (ir r))
        (PTree.set (idOf 715) (.Vint (ir r)) (PTree.set (idOf 714) (.Vint (ir r)) le)))) m) :
    Wp xi ge f firstNext Q e le m := by
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
    rw [Exec.evalExpr, temps_gso _ _ (show idOf 715 ≠ dense.id.tv by decide), temps_gss]
    simp only [E0_append]
    exact hQ r (Refine.next_eq hrep hspec)

end NautyVerified.Proofs.Search
