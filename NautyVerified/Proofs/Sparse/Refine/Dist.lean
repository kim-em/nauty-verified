import NautyVerified.Proofs.Sparse.Refine.DistLoop
import NautyVerified.Proofs.Sparse.Distvals.Satisfies
import NautyVerified.Proofs.Sparse.Sort.Pivot

/-!
# The distance pass of `refine_sg`

`if (level <= 2 && nactive == 1 && ptn[ACTIVE[0]] <= level && *numcells <= n/8)`:
the sole queue entry is taken out of the queue and `active`, `distvals`
fills `HITS` with the distances from its vertex, and the cell loop
(`wp_distLoop`) splits every cell by distance. `wp_distTest`: the test leaves
`distCond`, HexGraphIso's test, in its temporary.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open NautyVerified.Spec.SortC (iterF)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph splitCounts DistanceState)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n}

/-- The distance pass's test. -/
def distCond (level : Nat) (t : RefineSt n) : Bool :=
  level <= 2 && t.queue.size == 1 && t.ptn[t.queue[0]!]! <= level && t.numcells <= n / 8

/-- The test of `dist`. -/
abbrev distTest : statement :=
  (.Ssequence
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Ole (tv id.«level») (ci 2 tint) tint)
          (sk (.Sset (idOf 726) (.Ecast (.Ebinop .Oeq (tv id.«nactive») (ci 1 tint) tint) tbool)))
          (.Sset (idOf 726) (ci 0 tint))))
      (.Sifthenelse
        (tv (idOf 726))
        (sk
          (.Sset
            (idOf 727)
            (.Ecast
              (.Ebinop .Ole
                (ix id.«ptn» (gix id.«nausparse:work2» (ci 0 tint)))
                (tv id.«level»)
                tint)
              tbool)))
        (.Sset (idOf 727) (ci 0 tint))))
    (.Sifthenelse
      (tv (idOf 727))
      (sk
        (.Sset
          (idOf 728)
          (.Ecast
            (.Ebinop .Ole
              (.Ederef (pi id.«numcells») tint)
              (.Ebinop .Odiv (tv id.«n») (ci 8 tint) tint)
              tint)
            tbool)))
      (.Sset (idOf 728) (ci 0 tint))))

/-- The test: `t728` holds `distCond`. -/
theorem wp_distTest {Q : Post} {le : temp_env} {m : mem} {t : RefineSt n} {S : Scr} (hok : Ok n L)
    (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t) (hv : t.Valid L.level)
    (hnc : t.numcells ≤ 2 * n)
    (hQ : ∀ v726 v727, Q.normal E0 empty_env (PTree.set (idOf 728) (Val.of_bool (distCond L.level t))
      (PTree.set (idOf 727) v727 (PTree.set (idOf 726) v726 le))) m) :
    Wp xi sge F distTest Q empty_env le m := by
  have hnl := hok.nlt
  have hll := hok.levlt
  have hqn : t.queue.size ≤ n := queue_size_le hv.queue.set
  wp_step; wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, ht.level, typeof, cop]
  rw [ir_lt (a := 2) (b := (L.level : Int)) ⟨by decide, by decide⟩ ⟨by omega, by omega⟩]
  by_cases hl2 : L.level ≤ 2
  · rw [show decide ((2 : Int) < L.level) = false from decide_eq_false (by omega)]
    simp (config := {decide := true}) only [ite_true]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, ht.nactive, typeof, cop, cast_b]
    rw [ir_eq (a := (t.queue.size : Int)) (b := 1) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof]
    by_cases h1 : t.queue.size = 1
    · rw [show decide ((t.queue.size : Int) = 1) = true from decide_eq_true (by omega)]
      simp (config := {decide := true}) only [Val.of_bool, cop, ite_true]
      have hq0 := queue_lt hv (show 0 < t.queue.size by omega)
      have hp0 := hr.ptnSmall _ hq0
      wp_step; wp_step
      apply wp_set_eval
      have ht1 := ht.set (x := idOf 726) Vtrue (by decide)
      have hw := eval_gw2 (le := PTree.set (idOf 726) Vtrue le) (S := S) hok hm
        (a := ci 0 tint) (c := 0) rfl rfl (by have := hok.c2; omega)
      rw [hr.queue 0 (by omega)] at hw
      rw [Exec.evalExpr, eval_binop (eval_ptn hok hm ht1 hw rfl hq0)
        (show Exec.evalExpr sge empty_env _ m (tv id.«level») = _ from ht1.level)]
      simp only [typeof, cop, cast_b]
      rw [ir_lt (a := (L.level : Int)) (b := (t.ptn[t.queue[0]!]! : Int)) ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof]
      by_cases hp : t.ptn[t.queue[0]!]! ≤ L.level
      · rw [show decide ((L.level : Int) < (t.ptn[t.queue[0]!]! : Int)) = false from
          decide_eq_false (by omega)]
        simp (config := {decide := true}) only [Val.of_bool, cop, ite_true]
        wp_step; wp_step
        apply wp_set_eval
        have ht2 := ht1.set (x := idOf 727) Vtrue (by decide)
        have hdiv : Exec.evalExpr sge empty_env (PTree.set (idOf 727) Vtrue (PTree.set (idOf 726) Vtrue le)) m
            (.Ebinop .Odiv (tv id.«n») (ci 8 tint) tint) = some (.Vint (ir ((n / 8 : Nat) : Int))) := by
          rw [eval_binop (show Exec.evalExpr sge empty_env _ m (tv id.«n») = _ from ht2.n) rfl]
          simp only [typeof, Exec.div_ii]
          rw [show Lib.Integers.Int.eq (Lib.Integers.Int.repr (zOfInt 8)) Lib.Integers.Int.zero = false
            from by decide,
            show Lib.Integers.Int.eq (Lib.Integers.Int.repr (zOfInt 8)) Lib.Integers.Int.mone = false
            from by decide, Bool.and_false, Bool.false_or]
          simp only [Bool.false_eq_true, ite_false]
          rw [show (Lib.Integers.Int.repr (zOfInt 8)) = ir ((8 : Nat) : Int) from rfl,
            Sort.ir_divs (by omega) (by decide) (by decide)]
        rw [Exec.evalExpr, eval_binop (eval_nc hm ht2) hdiv]
        simp only [typeof, cop, cast_b]
        rw [ir_lt (a := ((n / 8 : Nat) : Int)) (b := (t.numcells : Int)) ⟨by omega, by omega⟩
          ⟨by omega, by omega⟩]
        have hd : distCond L.level t = !decide (((n / 8 : Nat) : Int) < (t.numcells : Int)) := by
          simp only [distCond, hl2, h1, hp, decide_true, Bool.true_and, beq_self_eq_true]
          by_cases hc8 : t.numcells ≤ n / 8 <;> simp [hc8] <;> omega
        have := hQ Vtrue Vtrue
        rw [hd] at this
        exact this
      · rw [show decide ((L.level : Int) < (t.ptn[t.queue[0]!]! : Int)) = true from
          decide_eq_true (by omega)]
        simp (config := {decide := true}) only [Val.of_bool, cop, ite_false]
        apply wp_set_eval
        simp only [Exec.evalExpr]
        have hd : distCond L.level t = false := by simp [distCond, hp]
        have := hQ Vtrue Vfalse
        rw [hd] at this
        exact this
    · rw [show decide ((t.queue.size : Int) = 1) = false from decide_eq_false (by omega)]
      simp (config := {decide := true}) only [Val.of_bool, cop, ite_false]
      apply wp_set_eval
      simp only [Exec.evalExpr]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      simp (config := {decide := true}) only [ite_false]
      apply wp_set_eval
      simp only [Exec.evalExpr]
      have hd : distCond L.level t = false := by simp [distCond, h1]
      have := hQ Vfalse Vfalse
      rw [hd] at this
      exact this
  · rw [show decide ((2 : Int) < L.level) = true from decide_eq_true (by omega)]
    simp (config := {decide := true}) only [ite_false]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    simp (config := {decide := true}) only [ite_false]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    simp (config := {decide := true}) only [ite_false]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    have hd : distCond L.level t = false := by simp [distCond]; omega
    have := hQ Vfalse Vfalse
    rw [hd] at this
    exact this

end NautyVerified.Proofs.Sparse.Refine
