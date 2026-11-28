import NautyVerified.Proofs.Sparse.Refine.Count.Syntax
import NautyVerified.Proofs.Sparse.Refine.Count.Model
import NautyVerified.Proofs.Sparse.Refine.Select

/-!
# The first run

`wp_run`: `while (ptn[v2-1] > level && HITS[lab[v2]] == w1) ++v2;` from
`v2 = first + 1` stops at HexGraphIso's `firstRun`: the first position after
`first` that ends the cell or holds a different key.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem eval_cast {e : env} {le : temp_env} {m : mem} {a : expr} {ty : Cfrontend.Ctypes.type}
    {v : val} (h : Exec.evalExpr sge e le m a = some v) :
    Exec.evalExpr sge e le m (.Ecast a ty) = Cfrontend.Cop.sem_cast v (typeof a) ty m := by
  simp only [Exec.evalExpr, h]

/-- Inside a cell, `ptn[q] > level` exactly before its last position. -/
theorem cell_gt {ptn : Array Nat} {level a len q : Nat} (hc : IsCell ptn level a len) (h1 : a ≤ q)
    (h2 : q < a + len) : (ptn[q]! > level ↔ q + 1 < a + len) := by
  obtain ⟨hl, -, hin, hend⟩ := hc
  constructor
  · intro h
    refine Decidable.byContradiction fun hq => ?_
    have : q = a + len - 1 := by omega
    subst this; omega
  · exact hin q h1

/-- The keys and entries a cell split reads are in range. -/
structure Keys (n : Nat) (L : Loc) (t : RefineSt n) (S : Scr) (first len : Nat) : Prop where
  cell : IsCell t.ptn L.level first len
  bound : first + len ≤ n
  lab : ∀ q < n, t.lab[q]! < n
  hits : ∀ v < n, S.w3[v]! = t.hits[v]!
  small : ∀ q, first ≤ q → q < first + len → t.hits[t.lab[q]!]! < n + 2

theorem wp_run {Q : Post} {le : temp_env} {m : mem} {tv0 : ident} (htv : tv0 ∉ args ∧
    tv0 ≠ id.longcode ∧ tv0 ≠ id.nactive ∧ tv0 ≠ id.«v2» ∧ tv0 ≠ id.«w1»)
    (hok : Ok n L) (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t) {first len : Nat}
    (hk : Keys n L t S first len)
    (hv2 : PTree.get id.«v2» le = some (.Vint (ir (first + 1))))
    (hw1 : PTree.get id.«w1» le = some (.Vint (ir t.hits[t.lab[first]!]!)))
    (hQ : ∀ le', PTree.get id.«v2» le' = some (.Vint (ir
        (Hex.GraphIso.Nauty.Sparse.CountSort.firstRun t.lab t.hits first (first + len)))) →
      (∀ x, x ∉ [id.«v2», tv0] → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m) :
    Wp xi sge F (runG tv0) Q empty_env le m := by
  have hnl := hok.nlt
  have hll := hok.levlt
  have hcl := hk.cell.1
  have hb := hk.bound
  let w := t.hits[t.lab[first]!]!
  have hwl : w < n + 2 := hk.small first (Nat.le_refl _) (by omega)
  have hws : ∀ x ∈ [id.«v2», tv0], x ∉ args ∧ x ≠ id.longcode ∧ x ≠ id.nactive := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · exact ⟨htv.1, htv.2.1, htv.2.2.1⟩
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ k, v = first + len - k ∧ first + 1 ≤ k ∧ k ≤ first + len ∧
      (∀ q, first + 1 ≤ q → q < k → t.hits[t.lab[q]!]! = w) ∧
      PTree.get id.«v2» le' = some (.Vint (ir k)) ∧
      ∀ x, x ∉ [id.«v2», tv0] → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ k, v = first + len - k ∧ first + 1 ≤ k ∧ k < first + len ∧
      (∀ q, first + 1 ≤ q → q < k + 1 → t.hits[t.lab[q]!]! = w) ∧
      PTree.get id.«v2» le' = some (.Vint (ir (k + 1))) ∧
      ∀ x, x ∉ [id.«v2», tv0] → PTree.get x le' = PTree.get x le
  have hexit : ∀ k le', first + 1 ≤ k → k ≤ first + len →
      (∀ q, first + 1 ≤ q → q < k → t.hits[t.lab[q]!]! = w) →
      (k = first + len ∨ t.hits[t.lab[k]!]! ≠ w) →
      PTree.get id.«v2» le' = some (.Vint (ir k)) →
      (∀ x, x ∉ [id.«v2», tv0] → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m :=
    fun k le' h1 h2 heq hstop hk' ho => by
      rw [← Count.firstRun_spec t.lab t.hits h1 h2 heq hstop] at hk'
      exact hQ le' hk' ho
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := first + len - (first + 1))
    ⟨rfl, rfl, rfl, first + 1, rfl, Nat.le_refl _, by omega, fun q h1 h2 => absurd h2 (by omega),
      hv2, fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, rfl, k, rfl, hk1, hk2, hpre, hik, ho⟩
    have ht' := ht.frame ho hws
    have hw1' : PTree.get id.«w1» le' = some (.Vint (ir w)) := by
      have hn : id.«w1» ∉ [id.«v2», tv0] := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
        exact ⟨by decide, fun h => htv.2.2.2.2 h.symm⟩
      rw [ho _ hn]; exact hw1
    wp_step; wp_step; wp_step; wp_step
    apply wp_if_eval
    have hsub : Exec.evalExpr sge empty_env le' m' (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint) =
        some (.Vint (ir ((k - 1 : Nat) : Int))) := by
      simp only [Exec.evalExpr, hik, typeof, cop, ir_sub]
      congr 3; omega
    have hpk : k - 1 < n := by omega
    rw [eval_binop (eval_ptn hok hm ht' hsub rfl hpk) (show Exec.evalExpr sge empty_env le' m' (tv id.«level») = _ from ht'.level)]
    simp only [typeof, cop]
    have hpl := hr.ptnSmall _ hpk
    rw [ir_lt (a := (L.level : Int)) (b := (t.ptn[k - 1]! : Int)) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    have hgt := cell_gt hk.cell (q := k - 1) (by omega) (by omega)
    by_cases hkl : k < first + len
    · rw [show decide ((L.level : Int) < (t.ptn[k - 1]! : Int)) = true from
        decide_eq_true (by have := hgt.2 (by omega); omega)]
      simp (config := {decide := true}) only [ite_true]
      wp_step; wp_step
      apply wp_set_eval
      have hlk := hk.lab k (by omega)
      have hkw := hr.w3small _ hlk
      rw [hk.hits _ hlk] at hkw
      have hb : Exec.evalExpr sge empty_env le' m' (.Ebinop .Oeq (gix id.«nausparse:work3»
          (ix id.lab (tv id.«v2»))) (tv id.«w1») tint) =
          some (Val.of_bool (decide (t.hits[t.lab[k]!]! = w))) := by
        rw [eval_binop (eval_gw3 hok hm (eval_lab hok hm ht' (show Exec.evalExpr sge empty_env le' m'
          (tv id.«v2») = _ from hik) rfl (by omega)) rfl hlk) (show Exec.evalExpr sge empty_env le' m'
          (tv id.«w1») = _ from hw1'), hk.hits _ hlk]
        simp only [typeof, cop]
        rw [ir_eq (a := (t.hits[t.lab[k]!]! : Int)) (b := (w : Int)) ⟨by omega, by omega⟩
          ⟨by omega, by omega⟩]
        congr 2
        exact decide_eq_decide.2 Int.ofNat_inj
      rw [eval_cast hb]
      simp only [typeof, cast_b]
      have hset : ∀ bv, (∀ x, x ∉ [id.«v2», tv0] → PTree.get x (PTree.set tv0 bv le') =
          PTree.get x le) ∧ PTree.get id.«v2» (PTree.set tv0 bv le') = some (.Vint (ir k)) :=
        fun bv => ⟨fun x hx => by rw [temps_gso _ _ (fun h => hx (by simp [h]))]; exact ho x hx,
          by rw [temps_gso _ _ (fun h => htv.2.2.2.1 h.symm)]; exact hik⟩
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof]
      by_cases heq : t.hits[t.lab[k]!]! = w
      · simp (config := {decide := true}) only [heq, decide_true, Val.of_bool, cop, ite_true]
        apply wp_skip
        wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, (hset _).2, typeof, cop, ir_add]
        refine ⟨by simp, rfl, rfl, k, rfl, hk1, hkl, fun q h1 h2 => ?_, by simp, fun x hx => ?_⟩
        · by_cases hqk : q = k
          · subst hqk; exact heq
          · exact hpre q h1 (by omega)
        · rw [temps_gso _ _ (fun h => hx (by simp [h]))]; exact (hset _).1 x hx
      · simp (config := {decide := true}) only [heq, decide_false, Val.of_bool, cop, ite_false]
        apply wp_break
        exact hexit k _ hk1 hk2 hpre (.inr heq) (hset _).2 (hset _).1
    · rw [show decide ((L.level : Int) < (t.ptn[k - 1]! : Int)) = false from
        decide_eq_false (by have := hgt.1; omega)]
      simp (config := {decide := true}) only [ite_false]
      wp_step
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      simp (config := {decide := true}) only [ite_false]
      apply wp_break
      exact hexit k _ hk1 hk2 hpre (.inl (by omega))
        (by rw [temps_gso _ _ (fun h => htv.2.2.2.1 h.symm)]; exact hik)
        (fun x hx => by rw [temps_gso _ _ (fun h => hx (by simp [h]))]; exact ho x hx)
  · rintro v tr e' le' m' ⟨rfl, rfl, rfl, k, rfl, hk1, hk2, hpre, hik, ho⟩
    apply wp_skip
    exact ⟨first + len - (k + 1), by omega, by simp, rfl, rfl, k + 1, rfl, by omega, by omega, hpre,
      hik, ho⟩

end NautyVerified.Proofs.Sparse.Refine.Count
