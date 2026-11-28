import NautyVerified.Proofs.Search.Processnode.Stores

/-!
# `int` comparisons

`eval_eqI` … `eval_geI`: `a op b` for `int` operands holding `x` and `y`.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word

variable {e : env} {le : temp_env} {m : mem} {a b : expr} {x y : Int}

section
variable (ha : Exec.evalExpr ge e le m a = some (.Vint (ir x)))
  (hb : Exec.evalExpr ge e le m b = some (.Vint (ir y)))
  (hta : typeof a = tint) (htb : typeof b = tint) (hx : InInt x) (hy : InInt y)
include ha hb hta htb hx hy

theorem eval_eqI : Exec.evalExpr ge e le m (.Ebinop .Oeq a b tint) =
    some (Val.of_bool (decide (x = y))) := by
  simp only [Exec.evalExpr, ha, hb, hta, htb, cop]
  rw [ir_eq hx hy]

theorem eval_neI : Exec.evalExpr ge e le m (.Ebinop .One a b tint) =
    some (Val.of_bool (decide (x ≠ y))) := by
  simp only [Exec.evalExpr, ha, hb, hta, htb, cop]
  rw [ir_eq hx hy]
  by_cases h : x = y <;> simp [h]

theorem eval_ltI : Exec.evalExpr ge e le m (.Ebinop .Olt a b tint) =
    some (Val.of_bool (decide (x < y))) := by
  simp only [Exec.evalExpr, ha, hb, hta, htb, cop]
  rw [ir_lt hx hy]

theorem eval_gtI : Exec.evalExpr ge e le m (.Ebinop .Ogt a b tint) =
    some (Val.of_bool (decide (y < x))) := by
  simp only [Exec.evalExpr, ha, hb, hta, htb, cop]
  rw [ir_lt hy hx]

theorem eval_leI : Exec.evalExpr ge e le m (.Ebinop .Ole a b tint) =
    some (Val.of_bool (decide (x ≤ y))) := by
  simp only [Exec.evalExpr, ha, hb, hta, htb, cop]
  rw [ir_lt hy hx]
  simp only [← Int.not_lt, decide_not]

theorem eval_geI : Exec.evalExpr ge e le m (.Ebinop .Oge a b tint) =
    some (Val.of_bool (decide (y ≤ x))) := by
  simp only [Exec.evalExpr, ha, hb, hta, htb, cop]
  rw [ir_lt hx hy]
  simp only [← Int.not_lt, decide_not]

end

theorem eval_ci (z : Int) : Exec.evalExpr ge e le m (ci z tint) = some (.Vint (ir z)) := rfl

theorem wp_ifB {xi : Common.ExternalCalls.ExternalCalls} {f : function} {c : expr}
    {s1 s2 : statement} {Q : Post} {bb : Bool}
    (hc : Exec.evalExpr ge e le m c = some (Val.of_bool bb)) (hct : typeof c = tint)
    (h : Wp xi ge f (if bb then s1 else s2) Q e le m) : Wp xi ge f (.Sifthenelse c s1 s2) Q e le m := by
  apply wp_if_eval
  rw [hc, hct]
  cases bb <;> exact h

end NautyVerified.Proofs.Search.Processnode
