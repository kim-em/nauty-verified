import NautyVerified.Program.Env
import NautyVerified.Proofs.Maketargetcell.Syntax
import NautyVerified.Proofs.Bestcell.Rows

/-!
# The loops of `maketargetcell`

`wp_jloop`: from the start `c` of a nontrivial cell, `for (j = i + 1; ptn[j] > level; ++j)`
ends at `cellEnd ptn level (c + 1)`. `wp_kloop`: `for (k = i; k <= j; ++k)
ADDELEMENT(tcell, lab[k])` adds the cell `lab[c..j]` (HexGraphIso's `worksetOf`).
-/

namespace NautyVerified.Proofs.Maketargetcell

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (BitTable longs addW)
open NautyVerified.Proofs.Updatecan (tv labAt)
open NautyVerified.Proofs.Bestcell (ptnAt part part_succ)
open Hex.GraphIso.Nauty (VSet cellEnd worksetOf)

variable {xi : ExternalCalls}

theorem wp_jloop {Q : Post} {le : temp_env} {m : mem} {bp : block} {pofs : ptrofs}
    {ptn : Array Nat} {n level c : Nat}
    (hptn : PTree.get id.ptn le = some (.Vptr bp pofs))
    (harr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n)
    (hn : n < 2147483648) (hlev : PTree.get id.level le = some (.Vint (ir level)))
    (hlevlt : level < 2147483648) (hsmall : ∀ x < n, ptn[x]! < 2147483648)
    (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) (hc : c < n) (hgt : level < ptn[c]!)
    (hi : PTree.get id.i le = some (.Vint (ir c)))
    (hQ : ∀ le', PTree.get id.j le' = some (.Vint (ir (cellEnd ptn level (c + 1) : Nat))) →
      (∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m) :
    Wp xi ge Source.dense.fn.maketargetcell jloop Q empty_env le m := by
  have hc1 : c + 1 < n := by
    rcases Nat.lt_or_ge (c + 1) n with h1 | h1
    · exact h1
    · have : c = n - 1 := by omega
      subst this; omega
  have sp := cellEnd_spec hs hc1 hlast
  obtain ⟨e, he⟩ : ∃ e, e = cellEnd ptn level (c + 1) := ⟨_, rfl⟩
  rw [← he] at sp hQ
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hi, typeof, cop, ir_add, E0_append]
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ j, c + 1 ≤ j ∧ j ≤ e ∧ v = e - j ∧
      PTree.get id.j le' = some (.Vint (ir j)) ∧ ∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ j, c + 1 ≤ j ∧ j < e ∧ v = e - j ∧
      PTree.get id.j le' = some (.Vint (ir j)) ∧ ∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := e - (c + 1)) ⟨rfl, rfl, rfl, c + 1, Nat.le_refl _,
    sp.1, rfl, by rw [temps_gss]; push_cast; rfl, fun x hx => temps_gso _ _ hx⟩
  · rintro v t e' le' m' ⟨rfl, rfl, hmm, j, hj1, hj2, rfl, hij, ho⟩
    rw [hmm]
    have hp' : PTree.get id.ptn le' = some (.Vptr bp pofs) := by rw [ho _ (by decide)]; exact hptn
    have hl' : PTree.get id.level le' = some (.Vint (ir level)) := by rw [ho _ (by decide)]; exact hlev
    have hjn : j < n := by have := sp.2.1; omega
    have hpj := eval_at (ge := ge) (e := empty_env) harr hn id.ptn hp' (tv id.j) j hjn hij rfl
    have := hsmall j hjn
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, hpj, show Exec.evalExpr ge empty_env le' m (tv id.level) = _ from hl']
    simp only [ints, typeof, cop]
    rw [ir_lt (a := (level : Int)) (b := (ptn[j]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hend : j = e
    · subst hend
      rw [ite_eq_right (by simp; have := sp.2.2.1; omega)]
      apply wp_break
      exact hQ le' hij ho
    · have hg := sp.2.2.2 j hj1 (by omega)
      rw [ite_eq_left (by simpa using hg)]
      apply wp_skip
      apply wp_skip
      exact ⟨rfl, rfl, rfl, j, hj1, by omega, rfl, hij, ho⟩
  · rintro v t e' le' m' ⟨rfl, rfl, hmm, j, hj1, hj2, rfl, hij, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hij, typeof, cop, ir_add]
    refine ⟨e - (j + 1), by omega, by simp, rfl, hmm, j + 1, by omega, by omega, rfl,
      by rw [temps_gss]; push_cast; rfl, fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩

theorem wp_kloop {Q : Post} {le : temp_env} {m : mem} {bl bt : block} {lofs tofs : ptrofs}
    {lab : Array Nat} {n M c e : Nat} {ws : Nat → Lib.Integers.int64}
    (hlab : PTree.get id.lab le = some (.Vptr bl lofs))
    (hlarr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n)
    (hlsmall : ∀ x < n, lab[x]! < n) (hn : n < 2147483648) (hnM : n ≤ 64 * M)
    (hM : M < 2147483648) (hlt : bl ≠ bt)
    (htc : PTree.get id.tcell le = some (.Vptr bt tofs))
    (htarr : ArrayAt m .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) (longs ws) M)
    (hW : SetRep (fun w => bv64 (ws w)) M (VSet.empty : VSet n))
    (hbit : BitTable m E.nautilBit) (hbt : E.nautilBit ≠ bt)
    (hce : c ≤ e) (hen : e < n) (hi : PTree.get id.i le = some (.Vint (ir c)))
    (hj : PTree.get id.j le = some (.Vint (ir e)))
    (hQ : ∀ le' m' ws', ArrayAt m' .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) (longs ws') M →
      SetRep (fun w => bv64 (ws' w)) M (worksetOf n lab c e) → Unch m m' (· = bt) →
      Outside m m' bt (intOfZ (Ptrofs.unsigned tofs)) (intOfZ (Ptrofs.unsigned tofs) + 8 * M) →
      (∀ x, x ≠ id.k → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.maketargetcell kloop Q empty_env le m := by
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hi, E0_append]
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ k ws', c ≤ k ∧ k ≤ e + 1 ∧ v = e + 1 - k ∧
      PTree.get id.k le' = some (.Vint (ir k)) ∧
      ArrayAt m' .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) (longs ws') M ∧
      SetRep (fun w => bv64 (ws' w)) M (part n lab c (k - c)) ∧ Unch m m' (· = bt) ∧
      Outside m m' bt (intOfZ (Ptrofs.unsigned tofs)) (intOfZ (Ptrofs.unsigned tofs) + 8 * M) ∧
      ∀ x, x ≠ id.k → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ k ws', c ≤ k ∧ k ≤ e ∧ v = e + 1 - k ∧
      PTree.get id.k le' = some (.Vint (ir k)) ∧
      ArrayAt m' .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) (longs ws') M ∧
      SetRep (fun w => bv64 (ws' w)) M (part n lab c (k + 1 - c)) ∧ Unch m m' (· = bt) ∧
      Outside m m' bt (intOfZ (Ptrofs.unsigned tofs)) (intOfZ (Ptrofs.unsigned tofs) + 8 * M) ∧
      ∀ x, x ≠ id.k → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := e + 1 - c) ⟨rfl, rfl, c, ws, Nat.le_refl _, by omega,
    rfl, temps_gss _ _ _, htarr, by simpa [part] using hW, Unch.refl _ _, Outside.refl _ _ _ _,
    fun x hx => temps_gso _ _ hx⟩
  · rintro v t e' le' m' ⟨rfl, rfl, k, ws', hk1, hk2, rfl, hik, harr', hW', hu, hout, ho⟩
    have hj' : PTree.get id.j le' = some (.Vint (ir e)) := by rw [ho _ (by decide)]; exact hj
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hik, hj', typeof, cop]
    rw [ir_lt (a := (e : Int)) (b := (k : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hke : k ≤ e
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      simp only [E0_append]
      have hkn : k < n := by omega
      have hl' : PTree.get id.lab le' = some (.Vptr bl lofs) := by rw [ho _ (by decide)]; exact hlab
      have hle := eval_at (ge := ge) (e := empty_env) (hlarr.unch hu hlt) hn id.lab hl' (tv id.k) k hkn
        hik rfl
      have hlk := hlsmall k hkn
      refine Set.wp_addElement' harr' hM (by rw [ho _ (by decide)]; exact htc) hle rfl (by omega)
        (by omega) (hbit.unch hu hbt) rfl ?_
      intro m2 harr2 hu2 hout2
      refine ⟨rfl, rfl, k, addW ws' lab[k]!, hk1, hke, rfl, hik, harr2, ?_, hu.trans hu2,
        hout.trans hout2, ho⟩
      rw [show k + 1 - c = (k - c) + 1 by omega, part_succ, show c + (k - c) = k by omega]
      exact Set.setRep_add hW' hlk
    · rw [ite_eq_right (by simp; omega)]
      apply wp_break
      refine hQ le' m' ws' harr' ?_ hu hout ho
      rw [show worksetOf n lab c e = part n lab c (k - c) by
        simp only [worksetOf, part]; rw [show e + 1 - c = k - c by omega]]
      exact hW'
  · rintro v t e' le' m' ⟨rfl, rfl, k, ws', hk1, hk2, rfl, hik, harr', hW', hu, hout, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hik, typeof, cop, ir_add]
    refine ⟨e + 1 - (k + 1), by omega, by simp, rfl, k + 1, ws', by omega, by omega, rfl,
      by rw [temps_gss]; push_cast; rfl, harr', by rw [show k + 1 - c = (k + 1) - c from rfl]; exact hW',
      hu, hout, fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩

end NautyVerified.Proofs.Maketargetcell
