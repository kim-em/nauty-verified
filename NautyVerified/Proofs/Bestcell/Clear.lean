import NautyVerified.Proofs.Bestcell.Frame

/-!
# Clearing `bucket` in `bestcell`

`wp_clear`: `for (i = nnt; --i >= 0;) bucket[i] = 0;` zeroes `bucket[0..nnt)`.
-/

namespace NautyVerified.Proofs.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Proofs.Alloc (gat eval_gat wp_gstore Keep)
open NautyVerified.Proofs.Updatecan (tv)

variable {xi : ExternalCalls}

theorem wp_clear {Q : Post} {le : temp_env} {m : mem} {bB : block} {bv : Nat → val} {N K : Nat}
    (hp : Mem.load .Mint64 m BK (zOfInt 0) = some (.Vptr bB Ptrofs.zero))
    (harr : ArrayAt m .Mint32 bB 0 bv N) (hN : N < 2147483648) (hKN : K ≤ N) (hbk : BK ≠ bB)
    (hK : PTree.get id.nnt le = some (.Vint (ir K)))
    (hQ : ∀ le' m' bv', ArrayAt m' .Mint32 bB 0 bv' N → (∀ x < K, bv' x = .Vint (ir 0)) →
      Unch m m' (· = bB) → Keep m m' bB →
      (∀ k, k ≠ id.i → k ≠ id.t11 → PTree.get k le' = PTree.get k le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.«naugraph:bestcell» clear Q empty_env le m := by
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hK, E0_append]
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ v ≤ K ∧ PTree.get id.i le' = some (.Vint (ir v)) ∧ ∃ bv',
    ArrayAt m' .Mint32 bB 0 bv' N ∧ (∀ x, v ≤ x → x < K → bv' x = .Vint (ir 0)) ∧
    Unch m m' (· = bB) ∧ Keep m m' bB ∧
    ∀ k, k ≠ id.i → k ≠ id.t11 → PTree.get k le' = PTree.get k le
  refine wp_loop (I := I) (J := fun v t e' le' m' => ∃ v', v' < v ∧ I v' t e' le' m') ?_ ?_
    (n := K) ⟨rfl, rfl, Nat.le_refl _, temps_gss _ _ _, bv, harr, fun x h1 h2 => absurd h2 (by omega),
      Unch.refl _ _, Keep.refl _ _, fun k hk _ => temps_gso _ _ hk⟩
  · rintro v t e' le' m' ⟨rfl, rfl, hv, hi, bv', harr', hz, hu, hk, ho⟩
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
      simpa using hQ _ m' bv' harr' (fun x hx => hz x (Nat.zero_le _) hx) hu hk
        fun k h1 h2 => by rw [temps_gso _ _ h1, temps_gso _ _ h2, ho k h1 h2]
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      have hiv : PTree.get id.i (PTree.set id.i (.Vint (ir ((v : Int) - 1)))
          (PTree.set id.t11 (.Vint (ir ((v : Int) - 1))) le')) =
          some (.Vint (ir ((v - 1 : Nat) : Int))) := by
        rw [temps_gss]; congr 3; omega
      wp_step; wp_step
      refine wp_gstore rfl find_naugraphBucket (by rw [hu.load _ _ _ hbk]; exact hp) harr' hN
        (tv id.i) (v - 1) (by omega) hiv rfl (ci 0 tint) 0 rfl rfl ?_
      intro m'' harr'' hu'' hk''
      refine ⟨v - 1, by omega, by simp, rfl, by omega, hiv, _, harr'', fun x h1 h2 => ?_,
        hu.trans hu'', hk.trans hk'', fun k h1 h2 => by
        rw [temps_gso _ _ h1, temps_gso _ _ h2, ho k h1 h2]⟩
      simp only [upd]
      split
      · rfl
      · exact hz x (by omega) h2
  · rintro v t e' le' m' hJ
    apply wp_skip
    simpa using hJ

end NautyVerified.Proofs.Bestcell
