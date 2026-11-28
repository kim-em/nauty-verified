import NautyVerified.Program.Env
import NautyVerified.Proofs.Fmperm.Syntax
import NautyVerified.Proofs.Alloc.Global

/-!
# Clearing `workperm` in `fmperm`

`wp_clearWp`: `for (i = n; --i >= 0;) workperm[i] = 0;` leaves the first `n`
entries of `workperm` zero.
-/

namespace NautyVerified.Proofs.Fmperm

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Proofs.Alloc (gat eval_gat wp_gstore)

variable {xi : ExternalCalls}

/-- Entries from `j` on cleared. -/
def clearedAbove (vals : Nat → val) (j k : Nat) : val := if j ≤ k then .Vint (ir 0) else vals k

theorem wp_clearWp {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {b : block}
    {vals : Nat → val} {n : Nat} (hge : PTree.get id.wp e = none)
    (hp : 0 < n → Mem.load .Mint64 m E.nautilWorkperm (zOfInt 0) = some (.Vptr b Ptrofs.zero))
    (harr : ArrayAt m .Mint32 b 0 vals n) (hn : n < 2147483648)
    (hbw : 0 < n → E.nautilWorkperm ≠ b) (hnv : PTree.get id.n le = some (.Vint (ir n)))
    (hQ : ∀ le' m', ArrayAt m' .Mint32 b 0 (fun _ => .Vint (ir 0)) n →
      Unch m m' (fun z => 0 < n ∧ z = b) → Alloc.Keep m m' b →
      (∀ k, k ≠ id.i → k ≠ id.t5 → PTree.get k le' = PTree.get k le) → Q.normal E0 e le' m') :
    Wp xi ge f clearWp Q e le m := by
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hnv, E0_append]
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    v ≤ n ∧ PTree.get id.i le' = some (.Vint (ir v)) ∧
    ArrayAt m' .Mint32 b 0 (clearedAbove vals v) n ∧ Unch m m' (fun z => 0 < n ∧ z = b) ∧
    Alloc.Keep m m' b ∧ ∀ k, k ≠ id.i → k ≠ id.t5 → PTree.get k le' = PTree.get k le
  refine wp_loop (I := I) (J := fun v t e' le' m' => ∃ v', v' < v ∧ I v' t e' le' m') ?_ ?_
    (n := n) ⟨rfl, rfl, Nat.le_refl _, temps_gss _ _ _,
      harr.congr fun k hk => by simp [clearedAbove, Nat.not_le.2 hk],
      Unch.refl _ _, Alloc.Keep.refl _ _, fun k hk _ => temps_gso _ _ hk⟩
  · rintro v t e' le' m' ⟨rfl, rfl, hv, hi, harr', hu, hk, ho⟩
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hi, typeof, cop, ir_sub]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, E0_append]
    apply wp_if_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, temps_gss, typeof, cop]
    rw [ir_lt (a := (v : Int) - 1) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
    by_cases h0 : v = 0
    · subst h0
      rw [ite_eq_right (by simp)]
      apply wp_break
      simpa using hQ _ m' (harr'.congr fun k _ => by simp [clearedAbove]) hu hk
        fun k h1 h2 => by rw [temps_gso _ _ h1, temps_gso _ _ h2, ho k h1 h2]
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      have hiv : PTree.get id.i (PTree.set id.i (.Vint (ir ((v : Int) - 1)))
          (PTree.set id.t5 (.Vint (ir ((v : Int) - 1))) le')) = some (.Vint (ir ((v - 1 : Nat) : Int))) := by
        rw [temps_gss]; congr 3; omega
      wp_step; wp_step
      refine wp_gstore hge E.find_nautilWorkperm (by rw [hu.load _ _ _ (fun h => hbw (by omega) h.2)]; exact hp (by omega)) harr' hn (tv id.i) (v - 1) (by omega)
        hiv rfl (ci 0 tint) 0 rfl rfl ?_
      intro m'' harr'' hu'' hk''
      refine ⟨v - 1, by omega, by simp, rfl, by omega, hiv, ?_,
        hu.trans (hu''.mono fun z hz => ⟨by omega, hz⟩), hk.trans hk'', fun k h1 h2 => by
        rw [temps_gso _ _ h1, temps_gso _ _ h2, ho k h1 h2]⟩
      refine harr''.congr fun k _ => ?_
      simp only [upd, clearedAbove]
      split
      · rename_i hk; rw [ite_eq_left (by omega)]
      · rename_i hk
        by_cases hvk : v ≤ k
        · rw [ite_eq_left hvk, ite_eq_left (by omega)]
        · rw [ite_eq_right hvk, ite_eq_right (by omega)]
  · rintro v t e' le' m' hJ
    apply wp_skip
    simpa using hJ

end NautyVerified.Proofs.Fmperm
