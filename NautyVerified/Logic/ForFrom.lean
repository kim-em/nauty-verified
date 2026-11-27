import NautyVerified.Logic.For

/-!
# Counting loops from a given start

`for (i = a; i < n; ++i) body` (`forLoopFrom`), as `wp_forLoop` with the
invariant indexed from `a`; `forLoop` is the case `a = 0`.
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

/-- `for (i = a; i < n; ++i) body`, as SimplExpr writes it. -/
abbrev forLoopFrom (a : Int) (i n : Common.AST.ident) (body : statement) : statement :=
  .Ssequence
    (.Ssequence .Sskip (.Sset i (ci a tint)))
    (.Sloop
      (.Ssequence
        (.Ssequence .Sskip
          (.Sifthenelse (.Ebinop .Olt (.Etempvar i tint) (.Etempvar n tint) tint) .Sskip .Sbreak))
        body)
      (.Ssequence .Sskip (.Sset i (.Ebinop .Oadd (.Etempvar i tint) (ci 1 tint) tint))))

theorem wp_forLoopFrom {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    (i n : Common.AST.ident) (body : statement) (a N : Nat) (haN : a ≤ N) (hN : N < 2147483648)
    (Inv Mid : Nat → temp_env → mem → Prop)
    (hinv : ∀ k le m, Inv k le m → a ≤ k ∧ k ≤ N ∧ PTree.get i le = some (.Vint (ir k)) ∧
      PTree.get n le = some (.Vint (ir N)))
    (hinit : Inv a (PTree.set i (.Vint (ir a)) le) m)
    (hbody : ∀ k le m, a ≤ k → k < N → Inv k le m → Wp xi ge f body
      { normal := fun t _ le' m' => t = E0 ∧ Mid k le' m' } e le m)
    (hmid : ∀ k le m, Mid k le m → PTree.get i le = some (.Vint (ir k)) ∧
      Inv (k + 1) (PTree.set i (.Vint (ir (k + 1))) le) m)
    (hexit : ∀ le m, Inv N le m → Q.normal E0 e le m) :
    Wp xi ge f (forLoopFrom a i n body) Q e le m := by
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  refine wp_loop (I := fun v t e' le' m' => t = E0 ∧ e = e' ∧ Inv (N - v) le' m' ∧ v ≤ N - a)
    (J := fun v t e' le' m' => t = E0 ∧ e = e' ∧ ∃ k, a ≤ k ∧ k < N ∧ v = N - k ∧ Mid k le' m')
    ?_ ?_ (n := N - a) ⟨rfl, rfl, by rw [show N - (N - a) = a by omega]; exact hinit, Nat.le_refl _⟩
  · rintro v t e' le' m' ⟨rfl, rfl, hI, hv⟩
    obtain ⟨hk0, hk, hi, hn⟩ := hinv _ _ _ hI
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hi, hn, typeof, cop,
      ir_lt (a := ((N - v : Nat) : Int)) (b := N) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hlt : N - v < N
    · rw [ite_eq_left (by simpa using hlt)]
      apply wp_skip
      simp only [E0_append]
      refine wp_conseq ?_ ?_ ?_ ?_ (wp_env (hbody _ _ _ hk0 hlt hI))
      · rintro t e'' le'' m'' ⟨rfl, rfl, hm⟩
        exact ⟨by simp, rfl, N - v, hk0, hlt, by omega, hm⟩
      · intro _ _ _ _ h; exact h.elim
      · intro _ _ _ _ h; exact h.elim
      · intro _ _ _ h; exact h.elim
    · rw [ite_eq_right (by simpa using hlt)]
      apply wp_break
      apply hexit
      rw [show N = N - v by omega]
      exact hI
  · rintro v t e' le' m' ⟨rfl, rfl, k, hk0, hk, rfl, hM⟩
    obtain ⟨hi, hI⟩ := hmid _ _ _ hM
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hi, typeof, cop, ir_add]
    refine ⟨N - (k + 1), by omega, by simp, trivial, ?_, by omega⟩
    rw [show N - (N - (k + 1)) = k + 1 by omega]
    simpa using hI

end NautyVerified.Logic
