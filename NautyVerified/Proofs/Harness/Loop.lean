import NautyVerified.Proofs.Harness.Calls
import NautyVerified.Logic.For

/-!
# Counting loops that emit events

`wp_forT`: `for (i = 0; i < bound; ++i) body` where `bound` is an `int`
expression with a fixed value `N` and the body may produce events. The
invariant `Inv k t le m` holds when `i = k` after the trace `t`.
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source

variable {xi : ExternalCalls}

/-- `for (i = 0; i < bound; ++i) body`, as SimplExpr writes it. -/
abbrev forT (i : ident) (bound : expr) (body : statement) : statement :=
  .Ssequence
    (.Ssequence .Sskip (.Sset i (ci 0 tint)))
    (.Sloop
      (.Ssequence
        (.Ssequence .Sskip (.Sifthenelse (.Ebinop .Olt (.Etempvar i tint) bound tint) .Sskip .Sbreak))
        body)
      (.Ssequence .Sskip (.Sset i (.Ebinop .Oadd (.Etempvar i tint) (ci 1 tint) tint))))

theorem wp_forT {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    (i : ident) (bound : expr) (body : statement) (N : Nat) (hN : N < 2147483648)
    (Inv : Nat → trace → temp_env → mem → Prop)
    (hinv : ∀ k t le m, Inv k t le m → k ≤ N ∧ PTree.get i le = some (.Vint (ir k)) ∧
      Exec.evalExpr ge e le m bound = some (.Vint (ir N)) ∧ typeof bound = tint)
    (hinit : Inv 0 E0 (PTree.set i (.Vint (ir 0)) le) m)
    (hbody : ∀ k t le m, k < N → Inv k t le m → Wp xi ge f body
      { normal := fun t' _ le' m' => PTree.get i le' = some (.Vint (ir k)) ∧
          Inv (k + 1) (t ++ t') (PTree.set i (.Vint (ir (k + 1))) le') m',
        brk := fun _ _ _ _ => False, cont := fun _ _ _ _ => False, ret := fun _ _ _ => False } e le m)
    (hexit : ∀ t le m, Inv N t le m → Q.normal t e le m) :
    Wp xi ge f (forT i bound body) Q e le m := by
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  refine wp_loop (I := fun v t e' le' m' => e = e' ∧ Inv (N - v) t le' m' ∧ v ≤ N)
    (J := fun v t e' le' m' => e = e' ∧ ∃ k, k < N ∧ v = N - k ∧
      PTree.get i le' = some (.Vint (ir k)) ∧
      Inv (k + 1) t (PTree.set i (.Vint (ir (k + 1))) le') m') ?_ ?_
    (n := N) ⟨rfl, by simpa using hinit, Nat.le_refl _⟩
  · rintro v t e' le' m' ⟨rfl, hI, hv⟩
    obtain ⟨hk, hi, hb, hty⟩ := hinv _ _ _ _ hI
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hi, hb, hty]
    simp only [typeof, cop,
      ir_lt (a := ((N - v : Nat) : Int)) (b := N) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hlt : N - v < N
    · rw [ite_eq_left (by simpa using hlt)]
      apply wp_skip
      simp only [seqPost, Post.after, E0_append]
      refine wp_conseq ?_ ?_ ?_ ?_ (wp_env (hbody _ _ _ _ hlt hI))
      · rintro t' e'' le'' m'' ⟨rfl, hi', hI'⟩
        refine ⟨rfl, N - v, hlt, by omega, hi', ?_⟩
        simpa using hI'
      · intro _ _ _ _ h; exact h.elim
      · intro _ _ _ _ h; exact h.elim
      · intro _ _ _ h; exact h.elim
    · rw [ite_eq_right (by simpa using hlt)]
      apply wp_break
      show Q.normal (t ++ E0) _ _ _
      rw [show t ++ E0 = t from List.append_nil t]
      apply hexit
      rw [show N = N - v by omega]
      exact hI
  · rintro v t e' le' m' ⟨rfl, k, hk, rfl, hi, hI⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hi, typeof, cop, ir_add]
    refine ⟨N - (k + 1), by omega, True.intro, ?_, by omega⟩
    rw [show N - (N - (k + 1)) = k + 1 by omega]
    simpa using hI

end NautyVerified.Proofs.Harness
