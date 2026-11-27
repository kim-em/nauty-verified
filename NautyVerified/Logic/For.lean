import NautyVerified.Logic.Wp
import NautyVerified.Logic.Simp
import NautyVerified.Exec.Cop
import NautyVerified.Word.Repr
import NautyVerified.Proofs.Syntax

/-!
# Counting loops

`for (i = 0; i < n; ++i) body`, as SimplExpr writes it (`forLoop`), with an
invariant `Inv k` holding when `i = k`. `wp_forLoop`: if `Inv 0` holds after
`i = 0`, each body run from `Inv k` (`k < N`) ends normally, without events,
in a state `Mid k` where `i` still holds `k`, and incrementing `i` from
`Mid k` gives `Inv (k + 1)`, then the loop ends in `Inv N`.
-/

namespace NautyVerified.Logic

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Values
open CompCert4Lean.Common.Events CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps
open NautyVerified.Word NautyVerified.Proofs

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable {xi : ExternalCalls} {ge : genv}

/-- `for (i = 0; i < n; ++i) body`, as SimplExpr writes it. -/
abbrev forLoop (i n : Common.AST.ident) (body : statement) : statement :=
  .Ssequence
    (.Ssequence .Sskip (.Sset i (ci 0 tint)))
    (.Sloop
      (.Ssequence
        (.Ssequence .Sskip
          (.Sifthenelse (.Ebinop .Olt (.Etempvar i tint) (.Etempvar n tint) tint) .Sskip .Sbreak))
        body)
      (.Ssequence .Sskip (.Sset i (.Ebinop .Oadd (.Etempvar i tint) (ci 1 tint) tint))))

theorem wp_forLoop {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    (i n : Common.AST.ident) (body : statement) (N : Nat) (hN : N < 2147483648)
    (Inv Mid : Nat → temp_env → mem → Prop)
    (hinv : ∀ k le m, Inv k le m → k ≤ N ∧ PTree.get i le = some (.Vint (ir k)) ∧
      PTree.get n le = some (.Vint (ir N)))
    (hinit : Inv 0 (PTree.set i (.Vint (ir 0)) le) m)
    (hbody : ∀ k le m, k < N → Inv k le m → Wp xi ge f body
      { normal := fun t _ le' m' => t = E0 ∧ Mid k le' m' } e le m)
    (hmid : ∀ k le m, Mid k le m → PTree.get i le = some (.Vint (ir k)) ∧
      Inv (k + 1) (PTree.set i (.Vint (ir (k + 1))) le) m)
    (hexit : ∀ le m, Inv N le m → Q.normal E0 e le m) :
    Wp xi ge f (forLoop i n body) Q e le m := by
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, seqPost, Post.after, E0_append]
  refine wp_loop (I := fun v t e' le' m' => t = E0 ∧ e = e' ∧ Inv (N - v) le' m' ∧ v ≤ N)
    (J := fun v t e' le' m' => t = E0 ∧ e = e' ∧ ∃ k, k < N ∧ v = N - k ∧ Mid k le' m') ?_ ?_
    (n := N) ⟨rfl, rfl, by simpa using hinit, Nat.le_refl _⟩
  · rintro v t e' le' m' ⟨rfl, rfl, hI, hv⟩
    obtain ⟨hk, hi, hn⟩ := hinv _ _ _ hI
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hi, hn, typeof, cop,
      ir_lt (a := ((N - v : Nat) : Int)) (b := N) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hlt : N - v < N
    · rw [ite_eq_left (by simpa using hlt)]
      apply wp_skip
      simp only [seqPost, Post.after, E0_append]
      refine wp_conseq ?_ ?_ ?_ ?_ (wp_env (hbody _ _ _ hlt hI))
      · rintro t e'' le'' m'' ⟨rfl, rfl, hm⟩
        exact ⟨by simp, rfl, N - v, hlt, by omega, hm⟩
      · intro _ _ _ _ h; exact h.elim
      · intro _ _ _ _ h; exact h.elim
      · intro _ _ _ h; exact h.elim
    · rw [ite_eq_right (by simpa using hlt)]
      apply wp_break
      simp only [E0_append]
      apply hexit
      rw [show N = N - v by omega]
      exact hI
  · rintro v t e' le' m' ⟨rfl, rfl, k, hk, rfl, hM⟩
    obtain ⟨hi, hI⟩ := hmid _ _ _ hM
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hi, typeof, cop, ir_add]
    refine ⟨N - (k + 1), by omega, by simp, trivial, ?_, by omega⟩
    rw [show N - (N - (k + 1)) = k + 1 by omega]
    simpa using hI

end NautyVerified.Logic
