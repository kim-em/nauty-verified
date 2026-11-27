import NautyVerified.Proofs.Bestcell.Frame

/-!
# `bestcell`'s first loop

`wp_skipCell`: `while (ptn[i] > level) ++i;` from the start of a cell ends at
its end. `wp_starts`: the loop over cells writes the starts of the nontrivial
cells (`startsOf`, HexGraphIso's `starts`) into `workperm[0..nnt)`.
-/

namespace NautyVerified.Proofs.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Spec.Bestcell
open NautyVerified.Proofs.Alloc (Keep gat)
open NautyVerified.Proofs.Updatecan (tv labAt)
open Hex.GraphIso.Nauty (VSet cellEnd cells)

variable {xi : ExternalCalls}

section
variable {n : Nat} {bg : block} {gofs : ptrofs}
  {gw : Nat → Lib.Integers.int64} {grows : Array (VSet n)} {bl : block} {lofs : ptrofs}
  {lab : Array Nat} {bp : block} {pofs : ptrofs} {ptn : Array Nat} {level M : Nat}
  {bP bS bB : block}

theorem wp_skipCell {Q : Post} {le : temp_env} {m : mem}
    (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {c : Nat} (hc : c < n) (hi : PTree.get id.i le = some (.Vint (ir c)))
    (hQ : ∀ le', PTree.get id.i le' = some (.Vint (ir (cellEnd ptn level c : Nat))) →
      (∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m) :
    Wp xi ge Source.dense.fn.«naugraph:bestcell» skipCell Q empty_env le m := by
  have sp := cellEnd_spec h.psize hc h.plast
  obtain ⟨ce, hce⟩ : ∃ ce, ce = cellEnd ptn level c := ⟨_, rfl⟩
  rw [← hce] at sp hQ
  have hnlt := h.nlt
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ j, c ≤ j ∧ j ≤ ce ∧ v = ce - j ∧
      PTree.get id.i le' = some (.Vint (ir j)) ∧ ∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := fun v t e' le' m' => ∃ v', v' < v ∧ I v' t e' le' m') ?_ ?_
    (n := ce - c) ⟨rfl, rfl, rfl, c, Nat.le_refl _, sp.1, rfl, hi, fun _ _ => rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, j, hj1, hj2, rfl, hij, ho⟩
    have hf := h.temps (le' := le') fun x hx => ho x (by
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [eval_ptnGt hf j (by omega) hij]
    simp only [typeof, cop]
    by_cases hend : j = ce
    · subst hend
      rw [ite_eq_right (by simp; omega)]
      apply wp_break
      exact hQ le' hij ho
    · have hgt := sp.2.2.2 j hj1 (by omega)
      rw [ite_eq_left (by simpa using hgt)]
      apply wp_skip
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hij, typeof, cop, ir_add]
      refine ⟨ce - (j + 1), by omega, by simp, rfl, rfl, j + 1, by omega, by omega, rfl,
        by rw [temps_gss]; push_cast; rfl, fun x hx => ?_⟩
      rw [temps_gso _ _ hx, ho x hx]
  · rintro v t e' le' m' hJ
    apply wp_skip
    simpa using hJ

/-- The starts of the nontrivial cells, HexGraphIso's `starts`. -/
abbrev starts' (ptn : Array Nat) (level n : Nat) : List Nat :=
  startsOf (cells.go ptn level n (n - 0) 0)

theorem getElem!_append_left {l : List Nat} {k : Nat} (a : Nat) (hk : k < l.length) :
    (l ++ [a])[k]! = l[k]! := by
  rw [getElem!_pos (l ++ [a]) k (by simp; omega), getElem!_pos l k hk, List.getElem_append_left hk]

theorem getElem!_append_last (l : List Nat) (a : Nat) : (l ++ [a])[l.length]! = a := by
  rw [getElem!_pos (l ++ [a]) l.length (by simp)]
  simp

theorem wp_starts {Q : Post} {le : temp_env} {m : mem}
    (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {wv : Nat → val} (hw : ArrayAt m .Mint32 bP 0 wv n)
    (hi : PTree.get id.i le = some (.Vint (ir 0))) (hnnt : PTree.get id.nnt le = some (.Vint (ir 0)))
    (hQ : ∀ le' m' wv', ArrayAt m' .Mint32 bP 0 wv' n →
      (∀ k < (starts' ptn level n).length, wv' k = .Vint (ir ((starts' ptn level n)[k]! : Int))) →
      PTree.get id.nnt le' = some (.Vint (ir ((starts' ptn level n).length : Int))) →
      Unch m m' (· = bP) → Keep m m' bP → (∀ x, Args x → PTree.get x le' = PTree.get x le) →
      (starts' ptn level n).length ≤ n → Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.«naugraph:bestcell» starts Q empty_env le m := by
  have hnlt := h.nlt
  have hs := h.psize
  have hlast := h.plast
  let S := starts' ptn level n
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ (c : Nat) (pre : List Nat) (wv' : Nat → val), c ≤ n ∧ v = n - c ∧
      PTree.get id.i le' = some (.Vint (ir c)) ∧
      PTree.get id.nnt le' = some (.Vint (ir (pre.length : Int))) ∧ pre.length ≤ c ∧
      pre ++ startsOf (cells.go ptn level n (n - c) c) = S ∧
      ArrayAt m' .Mint32 bP 0 wv' n ∧ (∀ k < pre.length, wv' k = .Vint (ir (pre[k]! : Int))) ∧
      Unch m m' (· = bP) ∧ Keep m m' bP ∧ ∀ x, Args x → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := fun v t e' le' m' => ∃ v', v' < v ∧ I v' t e' le' m') ?_ ?_
    (n := n - 0) ⟨rfl, rfl, 0, [], wv, Nat.zero_le _, rfl, hi, hnnt, Nat.le_refl _, rfl, hw,
      fun k hk => absurd hk (by simp), Unch.refl _ _, Keep.refl _ _, fun _ _ => rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, c, pre, wv', hc, rfl, hic, hnc, hpl, hpre, hw', hwv, hu, hk, ho⟩
    have hf := (h.unch (hu.mono fun _ hz => .inl hz)).temps ho
    have hn' := hf.hn
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hic, hn', typeof, cop,
      ir_lt (a := (c : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hcn : c < n
    · rw [ite_eq_left (by simpa using hcn)]
      apply wp_skip
      simp only [E0_append]
      have hstep := starts_step hs hlast hcn
      have sp := cellEnd_spec hs hcn hlast
      wp_step; wp_step; wp_step
      apply wp_if_eval
      rw [eval_ptnGt hf c hcn hic]
      simp only [typeof, cop]
      by_cases hgt : level < ptn[c]!
      · rw [ite_eq_left (by simpa using hgt)]
        rw [ite_eq_left hgt] at hstep
        wp_step; wp_step; wp_step; wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, hnc]
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop, ir_add]
        refine Alloc.wp_gstore rfl find_naugraphWorkperm hf.wpP hw' (by omega) (tv id.t10)
          pre.length (by omega)
          (by show PTree.get _ _ = _; rw [temps_gso _ _ (by decide), temps_gss]) rfl
          (tv id.i) c (by show PTree.get _ _ = _; rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hic) rfl ?_
        intro m2 hw2 hu2 hk2
        simp only [E0_append]
        have hf2 := (hf.unch (hu2.mono fun _ hz => .inl hz)).temps (le' := PTree.set id.nnt
          (.Vint (ir ((pre.length : Int) + 1))) (PTree.set id.t10 (.Vint (ir (pre.length : Int))) le'))
          fun x hx => by
            rw [temps_gso _ _ (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
              temps_gso _ _ (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
        refine wp_skipCell hf2 hcn (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hic) ?_
        intro le3 hi3 ho3
        wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, hi3, typeof, cop, ir_add]
        refine ⟨n - (cellEnd ptn level c + 1), by omega, by simp, rfl, cellEnd ptn level c + 1,
          pre ++ [c], upd wv' pre.length (.Vint (ir (c : Int))), by omega, rfl,
          by rw [temps_gss]; push_cast; rfl, ?_, by simp; omega, ?_, hw2, ?_,
          hu.trans hu2, hk.trans hk2, ?_⟩
        · rw [temps_gso _ _ (by decide), ho3 _ (by decide), temps_gss]; simp
        · rw [List.append_assoc, ← hpre, hstep]
        · intro k hk'
          simp only [List.length_append, List.length_singleton] at hk'
          simp only [upd]
          by_cases hkl : k = pre.length
          · subst hkl; rw [ite_eq_left rfl, getElem!_append_last]
          · rw [ite_eq_right hkl, getElem!_append_left c (by omega)]; exact hwv k (by omega)
        · intro x hx
          rw [temps_gso _ _ (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
            ho3 _ (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
            temps_gso _ _ (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
            temps_gso _ _ (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ho x hx]
      · rw [ite_eq_right (by simpa using hgt)]
        rw [ite_eq_right hgt, List.nil_append] at hstep
        have hce := cellEnd_self hs hlast hcn (by omega)
        apply wp_skip
        wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, hic, typeof, cop, ir_add]
        refine ⟨n - (c + 1), by omega, by simp, rfl, c + 1, pre, wv', by omega, rfl,
          by rw [temps_gss]; push_cast; rfl, by rw [temps_gso _ _ (by decide)]; exact hnc, by omega,
          ?_, hw', hwv, hu, hk, ?_⟩
        · rw [← hpre, hstep, hce]
        · intro x hx
          rw [temps_gso _ _ (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ho x hx]
    · rw [ite_eq_right (by simpa using hcn)]
      apply wp_break
      have hcn' : c = n := by omega
      subst hcn'
      rw [starts_end _ _ (Nat.le_refl _), List.append_nil] at hpre
      subst hpre
      exact hQ le' m' wv' hw' hwv hnc hu hk ho hpl
  · rintro v t e' le' m' hJ
    apply wp_skip
    simpa using hJ

end

end NautyVerified.Proofs.Bestcell
