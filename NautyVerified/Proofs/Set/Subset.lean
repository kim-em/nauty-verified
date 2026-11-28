import NautyVerified.Program.Env
import NautyVerified.Proofs.Set.Inter

/-!
# The `NOTSUBSET` scan

`wp_subsetLoop`: `for (i = 0; i < m; ++i) if (NOTSUBSET(p[i], q[i])) break;`
ends with `i = m` exactly when every word of `p` lies inside the word of `q`
(which `setRep_subset` turns into HexGraphIso's `subset`).
-/

namespace NautyVerified.Proofs.Set

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec

variable {xi : ExternalCalls}

/-- `if (NOTSUBSET(p[i], q[i])) break;` -/
abbrev notSubsetBreak (p q i : Common.AST.ident) : statement :=
  sk (.Sifthenelse (.Ebinop .Oand (word p (.Etempvar i tint))
    (.Eunop .Onotint (word q (.Etempvar i tint)) tulong) tulong) .Sbreak .Sskip)

/-- Word `k` of `p` lies inside word `k` of `q`. -/
abbrev WordIn (wp wq : Nat → Lib.Integers.int64) (k : Nat) : Prop :=
  bv64 (wp k) &&& ~~~ bv64 (wq k) = 0

theorem wp_subsetLoop {p q i mv : Common.AST.ident} {f : function} {Q : Post} {e : env}
    {le : temp_env} {m : mem} {bp : block} {pofs : ptrofs} {bq : block} {qofs : ptrofs}
    {wp wq : Nat → Lib.Integers.int64} {M : Nat}
    (hparr : ArrayAt m .Mint64 bp (intOfZ (Ptrofs.unsigned pofs)) (longs wp) M)
    (hqarr : ArrayAt m .Mint64 bq (intOfZ (Ptrofs.unsigned qofs)) (longs wq) M)
    (hM : M < 2147483648) (hp : PTree.get p le = some (.Vptr bp pofs))
    (hq : PTree.get q le = some (.Vptr bq qofs)) (hm : PTree.get mv le = some (.Vint (ir M)))
    (hpi : p ≠ i) (hqi : q ≠ i) (hmi : mv ≠ i)
    (hQ : ∀ le' r, r ≤ M → PTree.get i le' = some (.Vint (ir r)) →
      (r = M ↔ ∀ k < M, WordIn wp wq k) →
      (∀ k, k ≠ i → PTree.get k le' = PTree.get k le) → Q.normal E0 e le' m) :
    Wp xi ge f (forLoop i mv (notSubsetBreak p q i)) Q e le m := by
  let Oth := fun le' : temp_env => ∀ k, k ≠ i → PTree.get k le' = PTree.get k le
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  refine wp_loop
    (I := fun v t e' le' m' => t = E0 ∧ e = e' ∧ m = m' ∧ ∃ k, k ≤ M ∧ v = M - k ∧
      PTree.get i le' = some (.Vint (ir k)) ∧ (∀ k' < k, WordIn wp wq k') ∧ Oth le')
    (J := fun v t e' le' m' => t = E0 ∧ e = e' ∧ m = m' ∧ ∃ k, k < M ∧ v = M - k ∧
      PTree.get i le' = some (.Vint (ir k)) ∧ (∀ k' ≤ k, WordIn wp wq k') ∧ Oth le')
    ?_ ?_ (n := M - 0)
    ⟨rfl, rfl, rfl, 0, Nat.zero_le _, rfl, temps_gss _ _ _, fun _ h => absurd h (by omega),
      fun k hk => temps_gso _ _ hk⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, k, hk, rfl, hik, hall, ho⟩
    wp_step; wp_step; wp_step
    have hm' : PTree.get mv le' = some (.Vint (ir M)) := by rw [ho _ hmi]; exact hm
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge e le' m (.Etempvar i tint) = _ from hik,
      show Exec.evalExpr ge e le' m (.Etempvar mv tint) = _ from hm']
    simp only [typeof, cop]
    rw [ir_lt (a := (k : Int)) (b := (M : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hkM : k < M
    · rw [ite_eq_left (by simpa using hkM)]
      apply wp_skip
      have hp' : PTree.get p le' = some (.Vptr bp pofs) := by rw [ho _ hpi]; exact hp
      have hq' : PTree.get q le' = some (.Vptr bq qofs) := by rw [ho _ hqi]; exact hq
      have hep := eval_word (e := e) hparr hM p hp' (.Etempvar i tint) k hkM hik rfl
      have heq := eval_word (e := e) hqarr hM q hq' (.Etempvar i tint) k hkM hik rfl
      wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, hep, Exec.evalExpr, heq]
      simp only [typeof, cop, bv64_eq, bv64_and, bv64_not, bv64_zero]
      by_cases hz : WordIn wp wq k
      · rw [ite_eq_right (by simpa [WordIn] using hz)]
        apply wp_skip
        refine ⟨by simp, rfl, rfl, k, hkM, rfl, hik, fun k' hk' => ?_, ho⟩
        rcases Nat.lt_or_ge k' k with h | h
        · exact hall k' h
        · rw [show k' = k by omega]; exact hz
      · rw [ite_eq_left (by simpa [WordIn] using hz)]
        apply wp_break
        simpa using hQ le' k (by omega) hik ⟨fun h => absurd h (by omega), fun h => absurd (h k hkM) hz⟩ ho
    · rw [ite_eq_right (by simpa using hkM)]
      apply wp_break
      have hkM' : k = M := by omega
      subst hkM'
      simpa using hQ le' k hk hik ⟨fun _ => hall, fun _ => rfl⟩ ho
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, k, hk, rfl, hik, hall, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge e le' m (.Etempvar i tint) = _ from hik]
    simp only [Exec.evalExpr, typeof, cop, ir_add]
    refine ⟨M - (k + 1), by omega, by simp, trivial, trivial, k + 1, by omega, rfl, temps_gss _ _ _,
      fun k' hk' => hall k' (by omega), fun k' hk' => by rw [temps_gso _ _ hk', ho _ hk']⟩

end NautyVerified.Proofs.Set
