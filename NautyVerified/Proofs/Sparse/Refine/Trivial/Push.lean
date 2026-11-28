import NautyVerified.Proofs.Sparse.Refine.Trivial.Part

/-!
# Activating a cell and comparing `int`s

`wp_push`: `ADDELEMENT(active, x); ACTIVE[nactive++] = x;` is HexGraphIso's
`RefineSt.push`. `eval_eqi`, `eval_nei`, `eval_lei`: `==`, `!=`, `<=` on
`int` temporaries in range.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Trivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk addElementB)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem eval_eqi {le : temp_env} {m : mem} {a b : expr} {x y : Int}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir x))) (hta : typeof a = tint)
    (hb : Exec.evalExpr sge empty_env le m b = some (.Vint (ir y))) (htb : typeof b = tint)
    (hx : InInt x) (hy : InInt y) :
    Exec.evalExpr sge empty_env le m (.Ebinop .Oeq a b tint) = some (Val.of_bool (decide (x = y))) := by
  rw [eval_binop ha hb, hta, htb]
  simp only [cop]
  rw [ir_eq hx hy]

theorem eval_nei {le : temp_env} {m : mem} {a b : expr} {x y : Int}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir x))) (hta : typeof a = tint)
    (hb : Exec.evalExpr sge empty_env le m b = some (.Vint (ir y))) (htb : typeof b = tint)
    (hx : InInt x) (hy : InInt y) :
    Exec.evalExpr sge empty_env le m (.Ebinop .One a b tint) = some (Val.of_bool (!decide (x = y))) := by
  rw [eval_binop ha hb, hta, htb]
  simp only [cop]
  rw [ir_eq hx hy]

theorem eval_lei {le : temp_env} {m : mem} {a b : expr} {x y : Int}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir x))) (hta : typeof a = tint)
    (hb : Exec.evalExpr sge empty_env le m b = some (.Vint (ir y))) (htb : typeof b = tint)
    (hx : InInt x) (hy : InInt y) :
    Exec.evalExpr sge empty_env le m (.Ebinop .Ole a b tint) = some (Val.of_bool (decide (x ≤ y))) := by
  rw [eval_binop ha hb, hta, htb]
  simp only [cop]
  rw [ir_lt hy hx]
  congr 2
  by_cases h : x ≤ y
  · simp [h]
  · simp [h]; omega

theorem notbool_ob (b : Bool) (m : mem) :
    Cfrontend.Cop.sem_unary_operation .Onotbool (Val.of_bool b) tint m = some (Val.of_bool (!b)) := by
  cases b <;> rfl

/-- `ADDELEMENT(active, x); ACTIVE[nactive++] = x;` with temporary `T`. -/
theorem wp_push {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t) {X T : ident} {x : Nat}
    (hx : PTree.get X le = some (.Vint (ir x))) (hxn : x < n) (hq : t.queue.size < n)
    (hT : T ∉ args ∧ T ≠ id.longcode ∧ T ≠ id.nactive) (hXT : X ≠ T) (hXn : X ≠ id.nactive)
    (hQ : ∀ le' m' S', Mem m' L G (t.push x) S' → Rep L (t.push x) S' → Tmp le' L (t.push x) →
      S'.w1 = S.w1 → S'.w3 = S.w3 → S'.w4 = S.w4 → S'.st1 = S.st1 → S'.mk1 = S.mk1 →
      S'.st2 = S.st2 → S'.mk2 = S.mk2 → Frame L m m' →
      (∀ y, y ≠ T → y ≠ id.nactive → PTree.get y le' = PTree.get y le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge f (.Ssequence (addElementB id.active id.«nausparse:bit» (tv X))
      (.Ssequence (.Ssequence (sk (.Sset T (tv id.nactive)))
        (.Sset id.nactive (.Ebinop .Oadd (tv T) (ci 1 tint) tint)))
        (.Sassign (gix id.«nausparse:work2» (tv T)) (tv X)))) Q empty_env le m := by
  wp_step
  refine wp_addAct hok hm ht (eval_tv hx) rfl hxn fun m1 aw hm1 hf1 => ?_
  simp only [E0_append]
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_tv ht.nactive]
  dsimp only
  apply wp_set_eval
  rw [eval_inc (temps_gss _ _ _)]
  dsimp only
  let le2 := PTree.set id.nactive (.Vint (ir ((t.queue.size : Int) + 1)))
    (PTree.set T (.Vint (ir (t.queue.size : Int))) le)
  have hT2 : PTree.get T le2 = some (.Vint (ir (t.queue.size : Int))) := by
    rw [temps_gso _ _ hT.2.2]; exact temps_gss _ _ _
  have hX2 : PTree.get X le2 = some (.Vint (ir x)) := by
    rw [temps_gso _ _ hXn, temps_gso _ _ hXT]; exact hx
  refine wp_w2 hok hm1 (eval_tv hT2) rfl (by have := hok.c2; omega) (eval_tv hX2) rfl ?_
  intro m2 hm2 hf2
  have hpush : (t.push x).queue = t.queue.push x := rfl
  refine hQ le2 m2 _ (hm2.congr rfl rfl rfl rfl) ⟨hr.starts, fun i hi => ?_, hr.w3size, hr.w3small, hr.ptnSmall⟩ ?_ rfl rfl rfl
    rfl rfl rfl rfl (hf1.trans hf2) fun y h1 h2 => by rw [temps_gso _ _ h2, temps_gso _ _ h1]
  · simp only [hpush, Array.size_push] at hi
    by_cases he : i = t.queue.size
    · subst he; simp only [upd_same, hpush, push_size]
    · simp only [hpush]
      rw [upd_ne _ _ he, push_lt _ _ _ (by omega)]; exact hr.queue i (by omega)
  · have h1 : Tmp (PTree.set T (.Vint (ir (t.queue.size : Int))) le) L t := ht.set _ hT
    have h2 := h1.setNactive (t.push x) rfl
    have he : ((t.push x).queue.size : Int) = (t.queue.size : Int) + 1 := by
      simp [RefineSt.push]
    rw [he] at h2
    exact h2

end NautyVerified.Proofs.Sparse.Refine.Trivial
