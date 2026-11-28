import NautyVerified.Proofs.Sparse.Refine.Count.Install

/-!
# After the first two fragments

`wp_two`: when the first two fragments are the whole cell, one of them is
pushed. `wp_big`: the larger of the first two fragments (`big`).
`wp_replace`: the largest fragment's queue place goes to the first when that
is not active (`replace`).
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk isElement addElementB delElementB)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- `(bool) !ISELEMENT(active, x)`. -/
theorem eval_notAct {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S) (ht : Tmp le L t)
    {x : ident} {c : Nat} (hx : PTree.get x le = some (.Vint (ir c))) (hc : c < n) :
    Exec.evalExpr sge empty_env le m
      (.Ecast (.Eunop .Onotbool (isElement id.active id.«nausparse:bit» (tv x)) tint) tbool) =
      some (Val.of_bool (!t.active.mem c)) := by
  have h := eval_isAct hok hm ht (a := tv x) (show Exec.evalExpr sge empty_env le m (tv x) = _ from hx) rfl hc
  simp only [Exec.evalExpr] at h ⊢
  rw [h]
  cases t.active.mem c <;> rfl

/-- `a - b` of two `int` temporaries, `b ≤ a`. -/
theorem eval_subT {le : temp_env} {m : mem} {a b : ident} {A B : Nat} (h : B ≤ A)
    (ha : PTree.get a le = some (.Vint (ir A))) (hb : PTree.get b le = some (.Vint (ir B))) :
    Exec.evalExpr sge empty_env le m (.Ebinop .Osub (tv a) (tv b) tint) =
      some (.Vint (ir ((A - B : Nat) : Int))) := by
  simp only [Exec.evalExpr, ha, hb, typeof, cop, ir_sub]
  congr 3; omega

/-- The case of two fragments filling the cell. -/
abbrev twoS (t1 t2 t3 : ident) : statement :=
  .Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Ole
          (.Ebinop .Osub (tv id.«v2») (tv id.«v1») tint)
          (.Ebinop .Osub (tv id.«v3») (tv id.«v2») tint)
          tint)
        (sk
          (.Sset t1
            (.Ecast
              (.Eunop .Onotbool
                (isElement id.«active» id.«nausparse:bit» (tv id.«v1»))
                tint)
              tbool)))
        (.Sset t1 (ci 0 tint))))
    (.Sifthenelse
      (tv t1)
      (.Ssequence (addElementB id.«active» id.«nausparse:bit» (tv id.«v1»)) (enq t2 id.«v1»))
      (.Ssequence (addElementB id.«active» id.«nausparse:bit» (tv id.«v2»)) (enq t3 id.«v2»)))

/-- The temporary names an insertion uses, apart from the rest. -/
def TT (x : ident) : Prop :=
  x ∉ args ∧ x ≠ id.longcode ∧ x ≠ id.nactive ∧
    x ∉ [id.«v1», id.«v2», id.«v3», id.«j», id.«k», id.«bigpos», id.«bigsize»]

theorem TT.ne {x : ident} (h : TT x) : x ∉ args ∧ x ≠ id.longcode ∧ x ≠ id.nactive := ⟨h.1, h.2.1, h.2.2.1⟩

theorem TT.ne' {x y : ident} (h : TT x)
    (hy : y ∈ [id.«v1», id.«v2», id.«v3», id.«j», id.«k», id.«bigpos», id.«bigsize»]) : y ≠ x :=
  fun e => h.2.2.2 (e ▸ hy)

/-- What a step after the installation leaves. -/
def After2 (L : Loc) (G : Hex.SparseGraph n) (S0 : Scr) (m0 : mem) (le0 : temp_env) (ws : List ident)
    (r : RefineSt n) (le : temp_env) (m : mem) (S' : Scr) : Prop :=
  Mem m L G r S' ∧ Rep L r S' ∧ Tmp le L r ∧ Frame L m0 m ∧ Keeps S0 S' ∧
    ∀ x, x ∉ ws → x ≠ id.longcode → x ≠ id.nactive → PTree.get x le = PTree.get x le0

theorem wp_two {Q : Post} {le : temp_env} {m : mem} {t1 t2 t3 : ident} (h1 : TT t1) (h2 : TT t2)
    (h3 : TT t3) (hok : Ok n L) (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t)
    {first v2 v3 : Nat} (h12 : first + 1 ≤ v2) (h23 : v2 ≤ v3) (h2n : v2 < n) (h3n : v3 ≤ n)
    (hv1 : PTree.get id.«v1» le = some (.Vint (ir first)))
    (hv2 : PTree.get id.«v2» le = some (.Vint (ir v2)))
    (hv3 : PTree.get id.«v3» le = some (.Vint (ir v3)))
    (hq : t.queue.size < n)
    (hQ : ∀ le' m' S', After2 L G S m le [t1, t2, t3]
      (if v2 - first ≤ v3 - v2 && !t.active.mem first then t.push first else t.push v2) le' m' S' →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F (twoS t1 t2 t3) Q empty_env le m := by
  have hnl := hok.nlt
  apply wp_seq
  wp_step; wp_step
  apply wp_if_eval
  rw [eval_binop (eval_subT (by omega) hv2 hv1) (eval_subT (by omega) hv3 hv2)]
  simp only [typeof, cop]
  rw [ir_lt (a := ((v3 - v2 : Nat) : Int)) (b := ((v2 - first : Nat) : Int)) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩]
  -- after `t1` is set to the push test
  have hT : ∀ (b : Bool), b = (v2 - first ≤ v3 - v2 && !t.active.mem first) →
      Wp xi sge F (.Sifthenelse (tv t1)
        (.Ssequence (addElementB id.«active» id.«nausparse:bit» (tv id.«v1»)) (enq t2 id.«v1»))
        (.Ssequence (addElementB id.«active» id.«nausparse:bit» (tv id.«v2»)) (enq t3 id.«v2»)))
        Q empty_env (PTree.set t1 (Val.of_bool b) le) m := by
    intro b hb
    have ht1 := ht.set (x := t1) (Val.of_bool b) h1.ne
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof]
    cases b
    · simp (config := {decide := true}) only [Val.of_bool, cop, ite_false]
      refine wp_pushA h3.ne (h3.ne' (by simp)) (by decide) hok hm hr ht1 (c := v2)
        (by rw [temps_gso _ _ (h1.ne' (by simp))]; exact hv2) (by omega) hq ?_
      rintro le' m' S' ⟨hm', hr', ht', hf', hk', -, ho'⟩
      rw [show (v2 - first ≤ v3 - v2 && !t.active.mem first) = false from hb.symm] at hQ
      refine hQ le' m' S' ⟨hm', hr', ht', hf', hk', fun x hx _ hxn => ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
      rw [ho' x hx.2.2 hxn, temps_gso _ _ hx.1]
    · simp (config := {decide := true}) only [Val.of_bool, cop, ite_true]
      refine wp_pushA h2.ne (h2.ne' (by simp)) (by decide) hok hm hr ht1 (c := first)
        (by rw [temps_gso _ _ (h1.ne' (by simp))]; exact hv1) (by omega) hq ?_
      rintro le' m' S' ⟨hm', hr', ht', hf', hk', -, ho'⟩
      rw [show (v2 - first ≤ v3 - v2 && !t.active.mem first) = true from hb.symm] at hQ
      refine hQ le' m' S' ⟨hm', hr', ht', hf', hk', fun x hx _ hxn => ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
      rw [ho' x hx.2.1 hxn, temps_gso _ _ hx.1]
  by_cases hle : v2 - first ≤ v3 - v2
  · rw [show decide (((v3 - v2 : Nat) : Int) < ((v2 - first : Nat) : Int)) = false from
      decide_eq_false (by omega)]
    simp (config := {decide := true}) only [Val.of_bool, cop, ite_true]
    wp_step; wp_step
    apply wp_set_eval
    rw [eval_notAct hok hm ht hv1 (by omega)]
    simp only [seqPost, after_E0, E0_append]
    exact hT _ (by simp [hle])
  · rw [show decide (((v3 - v2 : Nat) : Int) < ((v2 - first : Nat) : Int)) = true from
      decide_eq_true (by omega)]
    simp (config := {decide := true}) only [Val.of_bool, cop, ite_false]
    apply wp_set_eval
    simp only [Exec.evalExpr, seqPost, after_E0, E0_append]
    exact hT false (by simp [hle])

/-- The larger of the first two fragments. -/
abbrev bigS (d : Bool) : statement :=
  .Sifthenelse
    (.Ebinop .Oge
      (.Ebinop .Osub (tv id.«v2») (tv id.«v1») tint)
      (.Ebinop .Osub (tv id.«v3») (tv id.«v2») tint)
      tint)
    (.Ssequence
      (sk (.Sset id.«bigpos» (.Eunop .Oneg (ci 1 tint) tint)))
      (sk (.Sset id.«bigsize» (.Ebinop .Osub (tv id.«v2») (tv id.«v1») tint))))
    (.Ssequence
      (sk (.Sset id.«bigpos» (.Ebinop .Osub (tv id.«nactive») (ci 1 tint) tint)))
      (optEnd (!d)
        (sk (.Sset id.«bigsize» (.Ebinop .Osub (tv id.«v3») (tv id.«v2») tint)))
        (sk (mash (tv id.«bigsize»)))))

theorem wp_big {Q : Post} {le : temp_env} {m : mem} {d : Bool} (hok : Ok n L) (ht : Tmp le L t)
    {first v2 v3 : Nat} (h12 : first + 1 ≤ v2) (h23 : v2 ≤ v3) (h3n : v3 ≤ n) (hq : 1 ≤ t.queue.size)
    (hqn : t.queue.size ≤ n) (hc : t.longcode < 2 ^ 62)
    (hv1 : PTree.get id.«v1» le = some (.Vint (ir first)))
    (hv2 : PTree.get id.«v2» le = some (.Vint (ir v2)))
    (hv3 : PTree.get id.«v3» le = some (.Vint (ir v3)))
    (hQ : ∀ le', Tmp le' L (big first d t v2 v3).1 → (big first d t v2 v3).1.longcode < 2 ^ 62 →
      PTree.get id.«bigpos» le' = some (.Vint (ir (bpInt (big first d t v2 v3).2.1))) →
      PTree.get id.«bigsize» le' = some (.Vint (ir (big first d t v2 v3).2.2)) →
      (∀ x, x ≠ id.«bigpos» → x ≠ id.«bigsize» → x ≠ id.longcode → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m) :
    Wp xi sge F (bigS d) Q empty_env le m := by
  have hnl := hok.nlt
  apply wp_if_eval
  rw [eval_binop (eval_subT (by omega) hv2 hv1) (eval_subT (by omega) hv3 hv2)]
  simp only [typeof, cop]
  rw [ir_lt (a := ((v2 - first : Nat) : Int)) (b := ((v3 - v2 : Nat) : Int)) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩]
  by_cases hlt : v2 - first < v3 - v2
  · rw [show decide (((v2 - first : Nat) : Int) < ((v3 - v2 : Nat) : Int)) = true from
      decide_eq_true (by omega)]
    simp (config := {decide := true}) only [cop, ite_false, Bool.not_true]
    have hb : big first d t v2 v3 = (hashIf (!d) t (v3 - v2), some (t.queue.size - 1), v3 - v2) := by
      simp only [big, hlt, ite_true]
    rw [hb] at hQ
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_dec hq ht.nactive]
    have ht1 := ht.set (x := id.«bigpos») (.Vint (ir ((t.queue.size - 1 : Nat) : Int))) (by decide)
    have hbp1 : PTree.get id.«bigpos» (PTree.set id.«bigpos» (.Vint (ir ((t.queue.size - 1 : Nat) : Int))) le) =
        some (.Vint (ir (bpInt (some (t.queue.size - 1))))) := by rw [temps_gss]; rfl
    have hv3' : PTree.get id.«v3» (PTree.set id.«bigpos» (.Vint (ir ((t.queue.size - 1 : Nat) : Int))) le) =
        some (.Vint (ir v3)) := by rw [temps_gso _ _ (by decide)]; exact hv3
    have hv2' : PTree.get id.«v2» (PTree.set id.«bigpos» (.Vint (ir ((t.queue.size - 1 : Nat) : Int))) le) =
        some (.Vint (ir v2)) := by rw [temps_gso _ _ (by decide)]; exact hv2
    cases d
    · -- the nontrivial pass hashes `bigsize`
      simp only [optEnd, Bool.not_false, ite_true]
      apply wp_seq
      wp_step; wp_step
      apply wp_set_eval
      rw [eval_subT (by omega) hv3' hv2']
      simp only [seqPost, after_E0, E0_append]
      have ht2 := ht1.set (x := id.«bigsize») (.Vint (ir ((v3 - v2 : Nat) : Int))) (by decide)
      wp_step; wp_step
      refine wp_mash (i := v3 - v2) ht2.longcode hc (show Exec.evalExpr sge empty_env _ m (tv id.«bigsize») = _ by
        simp only [Exec.evalExpr, temps_gss]) rfl (by omega) ?_
      refine hQ _ (ht2.hash _) ?_ ?_ ?_ ?_
      · show Hex.GraphIso.Nauty.mash _ _ < _
        exact Nat.lt_of_lt_of_le (NautyVerified.Proofs.Refine.mash_lt _ _) (by decide)
      · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hbp1
      · rw [temps_gso _ _ (by decide), temps_gss]
      · intro x h1 h2 h3
        rw [temps_gso _ _ h3, temps_gso _ _ h2, temps_gso _ _ h1]
    · simp only [optEnd, Bool.not_true, Bool.false_eq_true, ite_false]
      wp_step; wp_step
      apply wp_set_eval
      rw [eval_subT (by omega) hv3' hv2']
      refine hQ _ (ht1.set (x := id.«bigsize») _ (by decide)) hc ?_ (by rw [temps_gss]) ?_
      · rw [temps_gso _ _ (by decide)]; exact hbp1
      · intro x h1 h2 _
        rw [temps_gso _ _ h2, temps_gso _ _ h1]
  · rw [show decide (((v2 - first : Nat) : Int) < ((v3 - v2 : Nat) : Int)) = false from
      decide_eq_false (by omega)]
    simp (config := {decide := true}) only [cop, ite_true, Bool.not_false]
    have hb : big first d t v2 v3 = (t, none, v2 - first) := by simp only [big, hlt, ite_false]
    rw [hb] at hQ
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop, ir_neg]
    wp_step; wp_step
    apply wp_set_eval
    have hv2' : PTree.get id.«v2» (PTree.set id.«bigpos» (.Vint (ir (-1))) le) = some (.Vint (ir v2)) := by
      rw [temps_gso _ _ (by decide)]; exact hv2
    have hv1' : PTree.get id.«v1» (PTree.set id.«bigpos» (.Vint (ir (-1))) le) = some (.Vint (ir first)) := by
      rw [temps_gso _ _ (by decide)]; exact hv1
    rw [eval_subT (by omega) hv2' hv1']
    refine hQ _ ((ht.set (x := id.«bigpos») _ (by decide)).set (x := id.«bigsize») _ (by decide)) hc ?_
      (by rw [temps_gss]) ?_
    · rw [temps_gso _ _ (by decide), temps_gss]; rfl
    · intro x h1 h2 _
      rw [temps_gso _ _ h2, temps_gso _ _ h1]

/-- The largest fragment's queue place to the first. -/
abbrev replaceS (d : Bool) (t5 : ident) : statement :=
  .Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Oge (tv id.«bigpos») (ci 0 tint) tint)
        (sk
          (.Sset t5
            (.Ecast
              (.Eunop .Onotbool
                (isElement id.«active» id.«nausparse:bit» (tv id.«v1»))
                tint)
              tbool)))
        (.Sset t5 (ci 0 tint))))
    (.Sifthenelse
      (tv t5)
      (optSeq d (sk (mash (tv id.«bigpos»)))
        (.Ssequence
          (delElementB id.«active» id.«nausparse:bit»
            (gix id.«nausparse:work2» (tv id.«bigpos»)))
          (.Ssequence
            (addElementB id.«active» id.«nausparse:bit» (tv id.«v1»))
            (sk
              (.Sassign
                (gix id.«nausparse:work2» (tv id.«bigpos»))
                (tv id.«v1»))))))
      .Sskip)

theorem hashIf_with (b : Bool) (t : RefineSt n) (i : Nat) (a : Hex.GraphIso.Nauty.VSet n)
    (q : Array Nat) : { hashIf b t i with active := a, queue := q } =
      { t with active := a, queue := q, longcode := (hashIf b t i).longcode } := by
  cases b <;> rfl

theorem replace_none (first : Nat) (d : Bool) (s : RefineSt n) : replace first d s none = s := rfl

theorem replace_some (first : Nat) (d : Bool) (s : RefineSt n) (pos : Nat) :
    replace first d s (some pos) = if !s.active.mem first then
      { hashIf d s pos with
        active := (s.active.erase s.queue[pos]!).insert first
        queue := s.queue.set! pos first }
    else s := by
  unfold replace
  cases d <;> by_cases h : s.active.mem first <;> simp [h, Id.run, hashIf, RefineSt.hash] <;> rfl

theorem wp_replace {Q : Post} {le : temp_env} {m : mem} {d : Bool} {t5 : ident} (h5 : TT t5)
    (hok : Ok n L) (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t) {first : Nat}
    {bp : Option Nat} (hf : first < n) (hqs : t.queue.size ≤ n) (hbp : ∀ p, bp = some p → p < t.queue.size)
    (hqe : ∀ i < t.queue.size, t.queue[i]! < n) (hc : t.longcode < 2 ^ 62)
    (hv1 : PTree.get id.«v1» le = some (.Vint (ir first)))
    (hbpv : PTree.get id.«bigpos» le = some (.Vint (ir (bpInt bp))))
    (hQ : ∀ le' m' S', After2 L G S m le [t5] (replace first d t bp) le' m' S' →
      (replace first d t bp).longcode < 2 ^ 62 → Q.normal E0 empty_env le' m') :
    Wp xi sge F (replaceS d t5) Q empty_env le m := by
  have hnl := hok.nlt
  have hc2 := hok.c2
  apply wp_seq
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hbpv, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl]
  have hskip : ∀ le', Tmp le' L t → (∀ x, x ≠ t5 → PTree.get x le' = PTree.get x le) →
      replace first d t bp = t → Q.normal E0 empty_env le' m := fun le' ht' ho' he => by
    refine hQ le' m S ⟨by rw [he]; exact hm, by rw [he]; exact hr, by rw [he]; exact ht', Frame.refl _ _,
      Keeps.refl _, fun x hx _ _ => ho' x (by simpa using hx)⟩ (by rw [he]; exact hc)
  cases bp with
  | none =>
    rw [ir_lt (a := bpInt none) (b := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
    simp (config := {decide := true}) only [bpInt, cop, ite_false]
    apply wp_set_eval
    simp only [Exec.evalExpr, seqPost, after_E0, E0_append]
    apply wp_if_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, typeof, cop, ite_false]
    apply wp_skip
    exact hskip _ (ht.set (x := t5) _ h5.ne) (fun x hx => temps_gso _ _ hx) (replace_none _ _ _)
  | some pos =>
    have hpos := hbp pos rfl
    rw [ir_lt (a := bpInt (some pos)) (b := 0) ⟨by simp only [bpInt]; omega, by simp only [bpInt]; omega⟩
      ⟨by decide, by decide⟩]
    simp (config := {decide := true}) only [bpInt, show decide ((pos : Int) < 0) = false from
      decide_eq_false (by omega), cop, ite_true]
    wp_step; wp_step
    apply wp_set_eval
    rw [eval_notAct hok hm ht hv1 hf]
    simp only [seqPost, after_E0, E0_append]
    have ht1 := ht.set (x := t5) (Val.of_bool (!t.active.mem first)) h5.ne
    have hbp1 : PTree.get id.«bigpos» (PTree.set t5 (Val.of_bool (!t.active.mem first)) le) =
        some (.Vint (ir (pos : Int))) := by rw [temps_gso _ _ (h5.ne' (by simp))]; exact hbpv
    have hv1' : PTree.get id.«v1» (PTree.set t5 (Val.of_bool (!t.active.mem first)) le) =
        some (.Vint (ir first)) := by rw [temps_gso _ _ (h5.ne' (by simp))]; exact hv1
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof]
    cases ha : t.active.mem first
    · simp (config := {decide := true}) only [Bool.not_false, Val.of_bool, cop, ite_true]
      simp only [ha, Bool.not_false, Val.of_bool, ite_true] at ht1 hbp1 hv1'
      refine wp_optMash (t := t) d ht1 hc (show Exec.evalExpr sge empty_env _ m (tv id.«bigpos») = _
        from hbp1) rfl (by omega) ?_
      intro le2 ht2 ho2
      have hbp2 : PTree.get id.«bigpos» le2 = some (.Vint (ir (pos : Int))) := by
        rw [ho2 _ (by decide)]; exact hbp1
      have hv12 : PTree.get id.«v1» le2 = some (.Vint (ir first)) := by
        rw [ho2 _ (by decide)]; exact hv1'
      let s1 := hashIf d t pos
      have hm1 : Mem m L G s1 S := Mem.hashIf hm d pos
      have hq1 : s1.queue = t.queue := by cases d <;> rfl
      have hac1 : s1.active = t.active := by cases d <;> rfl
      apply wp_seq
      refine wp_delAct hok hm1 ht2 (c := t.queue[pos]!)
        (by rw [eval_gw2 hok hm1 (show Exec.evalExpr sge empty_env le2 m (tv id.«bigpos») = _ from hbp2)
          rfl (by omega), hr.queue pos hpos]) rfl (hqe pos hpos) ?_
      intro m1 aw1 hm1' hf1
      simp only [seqPost, after_E0, E0_append]
      let s2 : RefineSt n := { s1 with active := s1.active.erase t.queue[pos]! }
      apply wp_seq
      refine wp_addAct (t := s2) hok hm1' (ht2.congr rfl rfl) (show Exec.evalExpr sge empty_env le2 m1
        (tv id.«v1») = _ from hv12) rfl hf ?_
      intro m2 aw2 hm2 hf2
      simp only [seqPost, after_E0, E0_append]
      wp_step; wp_step
      refine wp_w2F hok hm2 (show Exec.evalExpr sge empty_env le2 m2 (tv id.«bigpos») = _ from hbp2) rfl
        (by omega) (show Exec.evalExpr sge empty_env le2 m2 (tv id.«v1») = _ from hv12) rfl ?_
      intro m3 hm3 hf3
      have hrep := replace_some first d t pos
      rw [ha] at hrep
      simp only [Bool.not_false, ite_true] at hrep
      rw [hrep, hashIf_with] at hQ
      have hr3 := Rep.setQ hr hpos first ((t.active.erase t.queue[pos]!).insert first)
      refine hQ le2 m3 _ ⟨hm3.congr (by cases d <;> rfl) (by cases d <;> rfl) (by cases d <;> rfl)
        (by cases d <;> rfl), { hr3 with },
        ht2.congr rfl (by simp only [Array.size_set!]; rw [hq1]), hf1.trans (hf2.trans hf3), ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
        fun x hx h1 _ => by rw [ho2 x h1, temps_gso _ _ (by simpa using hx)]⟩ (hashIf_code (b := d) (i := pos) hc)
    · simp (config := {decide := true}) only [Bool.not_true, Val.of_bool, cop, ite_false]
      simp only [ha, Bool.not_true, Val.of_bool, Bool.false_eq_true, ite_false] at ht1
      apply wp_skip
      have hrep := replace_some first d t pos
      rw [ha] at hrep
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hrep
      exact hskip _ ht1 (fun x hx => temps_gso _ _ hx) hrep

end NautyVerified.Proofs.Sparse.Refine.Count
