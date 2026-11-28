import NautyVerified.Program.Env
import NautyVerified.Proofs.Fmptn.Syntax
import NautyVerified.Proofs.Set.Add
import NautyVerified.Logic.Ints
import NautyVerified.Spec.Fmptn

/-!
# The minimum search of `fmptn`

`wp_scan`: in a cell `c1 .. c2` (`c1 < c2`, `ptn[k] > level` below `c2`,
`ptn[c2] ≤ level`), `do if (lab[++i] < lmin) lmin = lab[i]; while (ptn[i] > level);`
started at `i = c1`, `lmin = lab[c1]` ends with `i = c2` and `lmin` the least
label of the cell, HexGraphIso's `scanMin`.
-/

namespace NautyVerified.Proofs.Fmptn

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec

variable {xi : ExternalCalls}

/-- The arguments `fmptn` reads, in its temporaries and memory. -/
structure Frame (m : mem) (le : temp_env) (bl : block) (lofs : ptrofs) (bp : block)
    (pofs : ptrofs) (lab ptn : Array Nat) (n level : Nat) : Prop where
  hlab : PTree.get id.lab le = some (.Vptr bl lofs)
  hptn : PTree.get id.ptn le = some (.Vptr bp pofs)
  hlev : PTree.get id.level le = some (.Vint (ir level))
  hn : PTree.get id.n le = some (.Vint (ir n))
  larr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n
  parr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n
  nlt : n < 2147483648
  levlt : level < 2147483648
  lsmall : ∀ x < n, lab[x]! < n
  psmall : ∀ x < n, ptn[x]! < 2147483648

theorem Frame.temps {m : mem} {le le' : temp_env} {bl : block} {lofs : ptrofs} {bp : block}
    {pofs : ptrofs} {lab ptn : Array Nat} {n level : Nat}
    (h : Frame m le bl lofs bp pofs lab ptn n level)
    (hle : ∀ k, k ≠ id.i → k ≠ id.lmin → k ≠ id.t3 → k ≠ id.es → k ≠ id.es1 → k ≠ id.t1 →
      k ≠ id.t2 → PTree.get k le' = PTree.get k le) :
    Frame m le' bl lofs bp pofs lab ptn n level :=
  { h with
    hlab := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.hlab
    hptn := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.hptn
    hlev := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.hlev
    hn := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.hn }

theorem Frame.unch {m m' : mem} {le : temp_env} {bl : block} {lofs : ptrofs} {bp : block}
    {pofs : ptrofs} {lab ptn : Array Nat} {n level : Nat}
    (h : Frame m le bl lofs bp pofs lab ptn n level) {S : block → Prop} (hu : Unch m m' S)
    (hl : ¬ S bl) (hp : ¬ S bp) : Frame m' le bl lofs bp pofs lab ptn n level :=
  { h with larr := h.larr.unch hu hl, parr := h.parr.unch hu hp }

theorem scanMin_snoc (lab : Array Nat) (a k s : Nat) :
    scanMin lab (List.range' a (k + 1)) s =
      if lab[a + k]! < scanMin lab (List.range' a k) s then lab[a + k]!
      else scanMin lab (List.range' a k) s := by
  simp only [scanMin, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
    Nat.one_mul]
  rfl

theorem scanMin_lt {lab : Array Nat} {B : Nat} :
    ∀ (l : List Nat) (s : Nat), (∀ i ∈ l, lab[i]! < B) → s < B → scanMin lab l s < B
  | [], _, _, hs => hs
  | i :: l, s, hl, hs => by
    simp only [scanMin, List.foldl_cons]
    apply scanMin_lt l
    · exact fun j hj => hl j (List.mem_cons_of_mem _ hj)
    · split
      · exact hl i (List.mem_cons_self ..)
      · exact hs

theorem wp_scan {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bl : block}
    {lofs : ptrofs} {bp : block} {pofs : ptrofs} {lab ptn : Array Nat} {n level c1 c2 : Nat}
    (h : Frame m le bl lofs bp pofs lab ptn n level) (hc : c1 < c2) (hc2 : c2 < n)
    (hend : ptn[c2]! ≤ level) (hgt : ∀ k, c1 ≤ k → k < c2 → level < ptn[k]!)
    (hi : PTree.get id.i le = some (.Vint (ir c1)))
    (hl : PTree.get id.lmin le = some (.Vint (ir lab[c1]!)))
    (hQ : ∀ le', PTree.get id.i le' = some (.Vint (ir c2)) →
      PTree.get id.lmin le' =
        some (.Vint (ir (scanMin lab (List.range' (c1 + 1) (c2 - c1)) lab[c1]! : Nat))) →
      (∀ k, k ≠ id.i → k ≠ id.lmin → k ≠ id.t3 → PTree.get k le' = PTree.get k le) →
      Q.normal E0 e le' m) :
    Wp xi ge f scan Q e le m := by
  let cur := fun j => scanMin lab (List.range' (c1 + 1) (j - c1)) lab[c1]!
  have hcur : ∀ j, c1 ≤ j → j ≤ c2 → cur j < n := fun j _ _ =>
    scanMin_lt _ _ (fun x hx => h.lsmall x (by simp [List.mem_range'] at hx; omega))
      (h.lsmall c1 (by omega))
  have hother : ∀ le', (∀ k, k ≠ id.i → k ≠ id.lmin → k ≠ id.t3 → PTree.get k le' = PTree.get k le) →
      Frame m le' bl lofs bp pofs lab ptn n level := fun le' ho =>
    h.temps fun k h1 h2 h3 _ _ _ _ => ho k h1 h2 h3
  refine wp_loop
    (I := fun v t e' le' m' => t = E0 ∧ e = e' ∧ m = m' ∧ ∃ j, c1 ≤ j ∧ j < c2 ∧ v = c2 - j ∧
      PTree.get id.i le' = some (.Vint (ir j)) ∧
      PTree.get id.lmin le' = some (.Vint (ir (cur j : Nat))) ∧
      ∀ k, k ≠ id.i → k ≠ id.lmin → k ≠ id.t3 → PTree.get k le' = PTree.get k le)
    (J := fun v t e' le' m' => t = E0 ∧ e = e' ∧ m = m' ∧ ∃ j, c1 < j ∧ j ≤ c2 ∧ v = c2 - j + 1 ∧
      PTree.get id.i le' = some (.Vint (ir j)) ∧
      PTree.get id.lmin le' = some (.Vint (ir (cur j : Nat))) ∧
      ∀ k, k ≠ id.i → k ≠ id.lmin → k ≠ id.t3 → PTree.get k le' = PTree.get k le)
    ?_ ?_ (n := c2 - c1)
    ⟨rfl, rfl, rfl, c1, Nat.le_refl _, hc, rfl, hi, by simpa [cur, scanMin] using hl,
      fun _ _ _ _ => rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, j, hj1, hj2, rfl, hij, hlj, ho⟩
    have hf := hother le' ho
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hij, typeof, cop, ir_add]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, E0_append]
    let le2 := PTree.set id.i (.Vint (ir ((j : Int) + 1)))
      (PTree.set id.t3 (.Vint (ir ((j : Int) + 1))) le')
    have hf2 : Frame m le2 bl lofs bp pofs lab ptn n level := hf.temps fun k h1 _ h3 _ _ _ _ => by
      simp only [le2]; rw [temps_gso _ _ h1, temps_gso _ _ h3]
    have hj1n : j + 1 < n := by omega
    have hlab3 := eval_at (ge := ge) (e := e) hf2.larr hf2.nlt id.lab hf2.hlab (tv id.t3) (j + 1) hj1n
      (by simp (config := {decide := true}) only [Exec.evalExpr, le2, temps_gso, temps_gss]; rfl) rfl
    have hlmin2 : PTree.get id.lmin le2 = some (.Vint (ir (cur j : Nat))) := by
      simp (config := {decide := true}) only [le2, temps_gso]; exact hlj
    have hsm := h.lsmall (j + 1) hj1n
    have hcj := hcur j hj1 (by omega)
    have hnlt := h.nlt
    apply wp_if_eval
    rw [Exec.evalExpr, hlab3, show Exec.evalExpr ge e le2 m (tv id.lmin) = _ from hlmin2]
    simp only [ints, typeof, cop]
    rw [ir_lt (a := (lab[j + 1]! : Int)) (b := (cur j : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    have hnext : cur (j + 1) = if lab[j + 1]! < cur j then lab[j + 1]! else cur j := by
      simp only [cur]
      rw [show j + 1 - c1 = (j - c1) + 1 by omega, scanMin_snoc,
        show c1 + 1 + (j - c1) = j + 1 by omega]
    have hrest : ∀ k, k ≠ id.i → k ≠ id.lmin → k ≠ id.t3 → PTree.get k le2 = PTree.get k le :=
      fun k h1 h2 h3 => by simp only [le2]; rw [temps_gso _ _ h1, temps_gso _ _ h3, ho k h1 h2 h3]
    by_cases hlt : lab[j + 1]! < cur j
    · rw [ite_eq_left (by simpa using hlt)]
      wp_step; wp_step
      apply wp_set_eval
      have hlab2 := eval_at (ge := ge) (e := e) hf2.larr hf2.nlt id.lab hf2.hlab (tv id.i) (j + 1) hj1n
        (by simp (config := {decide := true}) only [Exec.evalExpr, le2, temps_gss]; rfl) rfl
      rw [hlab2]
      refine ⟨by simp, rfl, rfl, j + 1, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · simp (config := {decide := true}) only [temps_gso, temps_gss]; rfl
      · rw [temps_gss, hnext, ite_eq_left hlt]; rfl
      · intro k h1 h2 h3; rw [temps_gso _ _ h2, hrest k h1 h2 h3]
    · rw [ite_eq_right (by simpa using hlt)]
      apply wp_skip
      refine ⟨by simp, rfl, rfl, j + 1, by omega, by omega, by omega, ?_, ?_, hrest⟩
      · simp (config := {decide := true}) only [temps_gss]; rfl
      · rw [hlmin2, hnext, ite_eq_right hlt]
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, j, hj1, hj2, rfl, hij, hlj, ho⟩
    have hf := hother le' ho
    have hnlt := h.nlt
    have hlv := h.levlt
    have hpj := h.psmall j (by omega)
    have hptn := eval_at (ge := ge) (e := e) hf.parr hf.nlt id.ptn hf.hptn (tv id.i) j (by omega)
      hij rfl
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, hptn, show Exec.evalExpr ge e le' m (tv id.level) = _ from hf.hlev]
    simp only [ints, typeof, cop]
    rw [ir_lt (a := (level : Int)) (b := (ptn[j]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hjc : j < c2
    · have hg := hgt j (by omega) hjc
      rw [ite_eq_left (by simpa using hg)]
      apply wp_skip
      exact ⟨c2 - j, by omega, by simp, rfl, rfl, j, by omega, hjc, rfl, hij, hlj, ho⟩
    · have hjc' : j = c2 := by omega
      subst hjc'
      rw [ite_eq_right (by simp; omega)]
      apply wp_break
      exact hQ le' hij hlj ho

end NautyVerified.Proofs.Fmptn
