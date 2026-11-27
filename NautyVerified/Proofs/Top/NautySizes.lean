import NautyVerified.Proofs.Top.NautySyntax
import NautyVerified.Proofs.Search.Ops

/-!
# `nauty()`'s size checks

`wp_tSizes`: for `0 < n ≤ 64 m` and `m` small, neither size check fires and
the graph is not empty, so `nauty()` goes on to `tMain`.
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source

set_option linter.unusedSimpArgs false

theorem div_inf (ce : composite_env) (m : mem) :
    Cfrontend.Cop.sem_binary_operation ce .Odiv (.Vint (Lib.Integers.Int.repr (zOfInt 2000000002))) tint
      (.Vint (Lib.Integers.Int.repr (zOfInt 64))) tint m = some (.Vint (ir 31250000)) := by
  simp [Cfrontend.Cop.sem_binary_operation, Cfrontend.Cop.sem_div, Cfrontend.Cop.sem_binarith,
    Cfrontend.Cop.classify_binarith, Cfrontend.Cop.sem_cast, Cfrontend.Cop.classify_cast,
    Cfrontend.Cop.binarith_type, CompCert4Lean.X86_64.Archi.ptr64]
  exact ⟨⟨by decide, fun _ => by decide⟩, by decide⟩

variable {xi : ExternalCalls} in
theorem wp_tSizes {Q : Post} {le : temp_env} {m : mem} {M n : Nat}
    (hm : PTree.get dense.id.m_arg le = some (.Vint (ir M)))
    (hn : PTree.get dense.id.n_arg le = some (.Vint (ir n)))
    (hn0 : 0 < n) (hnl : n < 1073741824) (hnM : n ≤ 64 * M) (hMl : M ≤ 31250001)
    (hQ : ∀ le', (∀ x, x ≠ idOf 707 → PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tMain Q empty_env le' m) :
    Wp xi ge dense.fn.nauty Nauty.tSizes Q empty_env le m := by
  simp only [Nauty.tSizes]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hm, Refine.tv, typeof, div_inf, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 1) = ir 1 from rfl, ir_add,
    ir_lt (a := 31250000 + 1) (b := M) ⟨by decide, by decide⟩ ⟨by omega, by omega⟩]
  rw [ite_eq_right (by simp; omega)]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hn, Refine.tv, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 2000000002) = ir 2000000002 from rfl,
    show Lib.Integers.Int.repr (zOfInt 2) = ir 2 from rfl, ir_sub,
    ir_lt (a := 2000000002 - 2) (b := n) ⟨by decide, by decide⟩ ⟨by omega, by omega⟩]
  rw [ite_eq_right (by simp; omega)]
  wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hn, hm, Refine.tv, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 64) = ir 64 from rfl, ir_mul,
    ir_lt (a := 64 * M) (b := n) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  rw [show decide (64 * (M : Int) < n) = false by simp; omega]
  simp only [seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop, Val.of_bool]
  rw [ite_eq_right (by decide)]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  simp only [Nauty.tZero]
  wp_step; wp_step; wp_step
  simp only [Nauty.zeroIf]
  apply wp_if_eval
  simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, temps_gss, hn, Refine.tv,
    typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl,
    ir_eq (a := (n : Int)) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
  rw [ite_eq_right (by simp; omega)]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  exact hQ _ fun x hx => temps_gso _ _ hx

end NautyVerified.Proofs.Top
