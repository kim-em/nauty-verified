import NautyVerified.Proofs.Harness.Calls
import NautyVerified.Proofs.Search.Spec

/-!
# The harness's automorphism callback

`emit_generator(count, perm, orbits, numorbits, stabvertex, n)` writes `1`
and then `perm[0..n)`: `automCb_emit` is `AutomCb` for its block, in the
end-to-end environment.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Harness (writeSpec write_satisfies funct_nvWrite find_nvWrite signed_lr)

set_option linter.unusedSimpArgs false

kernel_rfl funct_emitGenerator : Genv.find_funct_ptr ge.genv_genv Harness.Block.emitGenerator =
  some (.Internal dense.fn.«dense_main:emit_generator»)

/-- `nv_write(a)` in any function, for a `long` value. -/
theorem wp_write {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : expr}
    {x : Lib.Integers.int64} (he : PTree.get dense.id.nv_write e = none)
    (ha : Exec.evalExprlist ge e le m [a] [tlong] = some [.Vlong x])
    (hQ : ∀ t, Writes t [intOfZ (Lib.Integers.Int64.signed x)] → Q.normal t e le m) :
    Wp Statement.xi ge f (.Scall none (.Evar dense.id.nv_write (tfun [tlong] .Tvoid)) [a])
      Q e le m := by
  refine wp_call (vf := .Vptr Harness.Block.nvWrite Ptrofs.zero) (targs := [tlong]) (tres := .Tvoid)
    (cc := cc_default) _ (writeSpec x) (write_satisfies x) rfl
    (by simp only [Exec.evalExpr, Exec.lvalOfVar, he, find_nvWrite, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode])
    ha (by simp [Genv.find_funct, funct_nvWrite]) rfl rfl ?_
  rintro t' v m' ⟨hw, rfl⟩
  exact hQ t' hw

/-- `emit_generator`'s body. -/
abbrev emitBody : statement :=
  .Ssequence (Set.sk (.Scall none (.Evar dense.id.nv_write (tfun [tlong] .Tvoid)) [ci 1 tint]))
    (Logic.forLoop dense.id.i dense.id.n
      (Set.sk (.Scall none (.Evar dense.id.nv_write (tfun [tlong] .Tvoid))
        [Refine.ix dense.id.perm (Refine.tv dense.id.i)])))

kernel_rfl emit_body_eq : dense.body.«dense_main:emit_generator» = emitBody

/-- The temporaries on entry. -/
def emitTemps (count : Lib.Integers.int) (bp : block) (pofs : ptrofs) (bo : block)
    (oofs : ptrofs) (no sv : Lib.Integers.int) (n : Nat) : temp_env :=
  PTree.set dense.id.n (.Vint (ir n)) (PTree.set dense.id.stabvertex (.Vint sv)
    (PTree.set dense.id.numorbits (.Vint no) (PTree.set dense.id.orbits (.Vptr bo oofs)
      (PTree.set dense.id.perm (.Vptr bp pofs) (PTree.set dense.id.count (.Vint count)
        (create_undef_temps dense.fn.«dense_main:emit_generator».fn_temps))))))

theorem automCb_emit : AutomCb Statement.xi Harness.Block.emitGenerator := by
  refine ⟨.Internal dense.fn.«dense_main:emit_generator», by simp [Genv.find_funct, funct_emitGenerator], rfl, ?_⟩
  intro count bp pofs p n bo oofs no sv
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = emitTemps count bp pofs bo oofs no sv n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, emitTemps count bp pofs bo oofs no sv n, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩,
      rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, harr, hn, hps⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [dense.fn.«dense_main:emit_generator».fn_body_eq, emit_body_eq]
    have hpv : PTree.get dense.id.perm (emitTemps count bp pofs bo oofs no sv n) =
        some (.Vptr bp pofs) := by
      simp (config := {decide := true}) only [emitTemps, temps_gso, temps_gss]
    have hnv : PTree.get dense.id.n (emitTemps count bp pofs bo oofs no sv n) =
        some (.Vint (ir n)) := by
      simp (config := {decide := true}) only [emitTemps, temps_gss]
    simp only [emitBody, Set.sk]
    wp_step; wp_step; wp_step
    refine wp_write (x := lr 1) rfl
      (by simp only [Exec.evalExprlist, Exec.evalExpr, typeof, cop,
        cast_int_long_ir (a := 1) ⟨by decide, by decide⟩]) ?_
    intro t1 ht1
    have hw1 : Writes t1 [1] := by
      rw [show intOfZ (Lib.Integers.Int64.signed (lr 1)) = 1 from signed_lr (by decide) (by decide)]
        at ht1
      exact ht1
    simp only [seqPost, Post.after]
    -- the loop over `perm`
    let w := fun k => (List.range k).map fun i => ((p[i]! : Nat) : Int)
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, seqPost, Post.after]
    refine wp_loop (I := fun v t e' le' m' => e' = empty_env ∧ m' = m ∧ ∃ k, k ≤ n ∧ v = n - k ∧
        Writes t (w k) ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧
        (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x (emitTemps count bp pofs bo oofs no sv n)))
      (J := fun v t e' le' m' => e' = empty_env ∧ m' = m ∧ ∃ k, k < n ∧ v = n - k ∧
        Writes t (w (k + 1)) ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧
        (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x (emitTemps count bp pofs bo oofs no sv n)))
      ?_ ?_ (n := n) ⟨rfl, rfl, 0, Nat.zero_le _, by omega, .nil, temps_gss _ _ _,
        fun x hx => temps_gso _ _ hx⟩
    · rintro v t e' le' m' ⟨rfl, hm, k, hk, rfl, hwk, hi, ho⟩
      subst hm
      have hn' : PTree.get dense.id.n le' = some (.Vint (ir n)) := by
        rw [ho _ (by decide)]; exact hnv
      have hp' : PTree.get dense.id.perm le' = some (.Vptr bp pofs) := by
        rw [ho _ (by decide)]; exact hpv
      wp_step; wp_step; wp_step
      apply wp_if_eval
      simp only [Exec.evalExpr, hi, hn', typeof, cop,
        ir_lt (a := (k : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      by_cases hlt : k < n
      · rw [ite_eq_left (by simpa using hlt)]
        apply wp_skip
        simp only [seqPost, Post.after]
        wp_step; wp_step
        have hpe := eval_at (ge := ge) (e := empty_env) harr hn dense.id.perm hp' (Refine.tv dense.id.i)
          k hlt hi rfl
        refine wp_write (x := lr (p[k]! : Int)) rfl
          (by simp only [Exec.evalExprlist, hpe]
              simp only [ints, typeof, cop,
                cast_int_long_ir (a := (p[k]! : Int)) ⟨by omega, by have := hps k hlt; omega⟩]) ?_
        intro t' ht'
        rw [signed_lr (by omega) (by have := hps k hlt; omega)] at ht'
        refine ⟨rfl, rfl, k, hlt, by omega, ?_, hi, ho⟩
        simp only [w, List.range_succ, List.map_append, List.map_cons, List.map_nil]
        exact hwk.append ht'
      · rw [ite_eq_right (by simpa using hlt)]
        apply wp_break
        refine ⟨m', Nextelement.free_empty m', ?_, rfl⟩
        have hk' : k = n := by omega
        subst hk'
        have e : t ++ E0 = t := List.append_nil t
        rw [e]
        exact hw1.append hwk
    · rintro v t e' le' m' ⟨rfl, rfl, k, hk, rfl, hwk, hi, ho⟩
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hi, typeof, cop, ir_add]
      refine ⟨n - (k + 1), by omega, by first | rfl | trivial, by first | rfl | trivial, k + 1,
        by omega, rfl, ?_, by rw [temps_gss]; rfl,
        fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩
      have e : t ++ E0 = t := List.append_nil t
      rw [e]; exact hwk

end NautyVerified.Proofs.Search
