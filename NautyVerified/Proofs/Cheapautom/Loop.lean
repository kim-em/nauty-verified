import NautyVerified.Proofs.Cheapautom.Syntax
import NautyVerified.Logic.Ints
import NautyVerified.Spec.Fmptn
import NautyVerified.Program.Dense

/-!
# The loops of `cheapautom`

`wp_skip`: `while (ptn[++i] > level) {}` from the start `c` of a nontrivial
cell ends at its end, `cellEnd ptn level (c + 1)`. `wp_loop`: the loop over
cells computes HexGraphIso's `cheapautom.go`.
-/

namespace NautyVerified.Proofs.Cheapautom

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Spec
open Hex.GraphIso.Nauty (cellEnd)

variable {xi : ExternalCalls}

/-- `cheapautom` reads `ptn` (in block `bp`), `level` and `n`. -/
structure Frame (m : mem) (le : temp_env) (bp : block) (pofs : ptrofs) (ptn : Array Nat)
    (level n : Nat) : Prop where
  hptn : PTree.get id.ptn le = some (.Vptr bp pofs)
  hlev : PTree.get id.level le = some (.Vint (ir level))
  hn : PTree.get id.n le = some (.Vint (ir n))
  arr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n
  size : ptn.size = n
  small : ∀ x < n, ptn[x]! < 2147483648
  last : ptn[n - 1]! ≤ level
  nlt : n < 2147483648
  levlt : level < 2147483648

theorem Frame.temps {m : mem} {le le' : temp_env} {bp : block} {pofs : ptrofs} {ptn : Array Nat}
    {level n : Nat} (h : Frame m le bp pofs ptn level n)
    (hle : ∀ x, x ≠ id.i → x ≠ id.k → x ≠ id.nnt → x ≠ id.t1 → x ≠ id.t2 →
      PTree.get x le' = PTree.get x le) : Frame m le' bp pofs ptn level n :=
  { h with
    hptn := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.hptn
    hlev := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.hlev
    hn := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.hn }

/-- `ptn[e] > level` for `e` holding `c < n`. -/
theorem eval_gt {e : env} {le : temp_env} {m : mem} {bp : block} {pofs : ptrofs}
    {ptn : Array Nat} {level n : Nat} (h : Frame m le bp pofs ptn level n) (a : expr) (c : Nat)
    (hc : c < n) (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge e le m (.Ebinop .Ogt (ptnAt a) (tv id.level) tint) =
      some (Val.of_bool (decide (level < ptn[c]!))) := by
  have hpe := eval_at (ge := ge) (e := e) h.arr h.nlt id.ptn h.hptn a c hc ha hty
  have := h.small c hc
  have := h.levlt
  rw [Exec.evalExpr, hpe, show Exec.evalExpr ge e le m (tv id.level) = _ from h.hlev]
  simp only [ints, typeof, cop]
  rw [ir_lt (a := (level : Int)) (b := (ptn[c]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  congr 2
  apply decide_eq_decide.2; omega

theorem wp_skipCell {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bp : block}
    {pofs : ptrofs} {ptn : Array Nat} {level n c : Nat} (h : Frame m le bp pofs ptn level n)
    (hc : c < n) (hgt : level < ptn[c]!) (hi : PTree.get id.i le = some (.Vint (ir c)))
    (hQ : ∀ le', PTree.get id.i le' = some (.Vint (ir (cellEnd ptn level (c + 1) : Nat))) →
      (∀ x, x ≠ id.i → x ≠ id.t1 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m) :
    Wp xi ge f skip Q e le m := by
  have hc1 : c + 1 < n := by
    rcases Nat.lt_or_ge (c + 1) n with h1 | h1
    · exact h1
    · have hcn : c = n - 1 := by omega
      rw [hcn] at hgt; have := h.last; omega
  obtain ⟨ce, hce⟩ : ∃ ce, ce = cellEnd ptn level (c + 1) := ⟨_, rfl⟩
  have hsp := cellEnd_spec h.size hc1 h.last
  rw [← hce] at hsp
  have hnlt := h.nlt
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    m = m' ∧ ∃ j, c ≤ j ∧ j < ce ∧ v = ce - j ∧ PTree.get id.i le' = some (.Vint (ir j)) ∧
      ∀ x, x ≠ id.i → x ≠ id.t1 → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := fun v t e' le' m' => ∃ v', v' < v ∧ I v' t e' le' m') ?_ ?_
    (n := ce - c) ⟨rfl, rfl, rfl, c, Nat.le_refl _, by omega, rfl, hi, fun _ _ _ => rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, j, hj1, hj2, rfl, hij, ho⟩
    have hf := h.temps fun x h1 _ _ h4 _ => ho x h1 h4
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hij, typeof, cop, ir_add]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    apply wp_if_eval
    have hj1n : j + 1 < n := by have := hsp.2.1; omega
    let le2 := PTree.set id.i (.Vint (ir ((j : Int) + 1))) (PTree.set id.t1 (.Vint (ir ((j : Int) + 1))) le')
    have hf2 : Frame m le2 bp pofs ptn level n := hf.temps fun x h1 _ _ h4 _ => by
      simp only [le2]; rw [temps_gso _ _ h1, temps_gso _ _ h4]
    rw [eval_gt hf2 (tv id.t1) (j + 1) hj1n (by
      simp only [Exec.evalExpr, le2]; rw [temps_gso _ _ (by decide), temps_gss]; rfl) rfl]
    simp only [typeof, cop]
    by_cases hend : j + 1 = ce
    · have hle := hsp.2.2.1
      rw [ite_eq_right (by simp; rw [show j + 1 = ce from hend]; omega)]
      apply wp_break
      simp only [E0_append]
      apply hQ le2 (by simp only [le2]; rw [temps_gss, ← hce, ← hend]; push_cast; rfl)
      intro x h1 h2
      simp only [le2]; rw [temps_gso _ _ h1, temps_gso _ _ h2, ho x h1 h2]
    · have hgt' := hsp.2.2.2 (j + 1) (by omega) (by omega)
      rw [ite_eq_left (by simpa using hgt')]
      apply wp_skip
      apply wp_skip
      refine ⟨ce - (j + 1), by omega, by simp, rfl, rfl, j + 1, by omega, by omega, rfl,
        by rw [temps_gss]; rfl, fun x h1 h2 => ?_⟩
      rw [temps_gso _ _ h1, temps_gso _ _ h2, ho x h1 h2]
  · rintro v t e' le' m' hJ
    apply wp_skip
    simpa using hJ

theorem go_succ_lt (ptn : Array Nat) (level F c k nnt : Nat) (hc : c < ptn.size) :
    Hex.GraphIso.Nauty.cheapautom.go ptn level (F + 1) c k nnt =
      if ptn[c]! > level then
        Hex.GraphIso.Nauty.cheapautom.go ptn level F (cellEnd ptn level (c + 1) + 1) (k - 1) (nnt + 1)
      else Hex.GraphIso.Nauty.cheapautom.go ptn level F (c + 1) (k - 1) nnt := by
  rw [Hex.GraphIso.Nauty.cheapautom.go, ite_eq_left hc]

theorem go_ge (ptn : Array Nat) (level F c k nnt : Nat) (hc : ¬ c < ptn.size) :
    Hex.GraphIso.Nauty.cheapautom.go ptn level F c k nnt = (k, nnt) := by
  cases F <;> simp [Hex.GraphIso.Nauty.cheapautom.go, hc]

theorem wp_cells {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bp : block}
    {pofs : ptrofs} {ptn : Array Nat} {level n : Nat} (h : Frame m le bp pofs ptn level n)
    (hk : PTree.get id.k le = some (.Vint (ir n))) (hnnt : PTree.get id.nnt le = some (.Vint (ir 0)))
    (hQ : ∀ le', PTree.get id.k le' =
        some (.Vint (ir (((Hex.GraphIso.Nauty.cheapautom.go ptn level n 0 n 0).1 : Nat) : Int))) →
      PTree.get id.nnt le' =
        some (.Vint (ir (((Hex.GraphIso.Nauty.cheapautom.go ptn level n 0 n 0).2 : Nat) : Int))) →
      (∀ x, x ≠ id.i → x ≠ id.k → x ≠ id.nnt → x ≠ id.t1 → PTree.get x le' = PTree.get x le) →
      Q.normal E0 e le' m) :
    Wp xi ge f loop Q e le m := by
  let R := Hex.GraphIso.Nauty.cheapautom.go ptn level n 0 n 0
  have hnlt := h.nlt
  have hsz := h.size
  let Oth := fun le' : temp_env =>
    ∀ x, x ≠ id.i → x ≠ id.k → x ≠ id.nnt → x ≠ id.t1 → PTree.get x le' = PTree.get x le
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    m = m' ∧ ∃ c kH nn F, c ≤ n ∧ v = n - c ∧ n - c ≤ F ∧
      Hex.GraphIso.Nauty.cheapautom.go ptn level F c kH nn = R ∧ n ≤ kH + c ∧ kH ≤ n ∧ nn ≤ c ∧
      PTree.get id.i le' = some (.Vint (ir c)) ∧ PTree.get id.k le' = some (.Vint (ir kH)) ∧
      PTree.get id.nnt le' = some (.Vint (ir nn)) ∧ Oth le'
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    m = m' ∧ ∃ c c2 kH nn F, c ≤ c2 ∧ c2 < n ∧ v = n - c ∧ n - (c2 + 1) ≤ F ∧
      Hex.GraphIso.Nauty.cheapautom.go ptn level F (c2 + 1) kH nn = R ∧ n ≤ kH + c2 + 1 ∧ kH ≤ n ∧
      nn ≤ c2 + 1 ∧
      PTree.get id.i le' = some (.Vint (ir c2)) ∧ PTree.get id.k le' = some (.Vint (ir kH)) ∧
      PTree.get id.nnt le' = some (.Vint (ir nn)) ∧ Oth le'
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0)
    ⟨rfl, rfl, rfl, 0, n, 0, n, Nat.zero_le _, rfl, by omega, rfl, by omega, Nat.le_refl _,
      Nat.le_refl _, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hk,
      by rw [temps_gso _ _ (by decide)]; exact hnnt, fun x hx _ _ _ => temps_gso _ _ hx⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, c, kH, nn, F, hcn, rfl, hF, hgo, hk1, hk2, hnn, hi, hkv,
      hnv, ho⟩
    have hf := h.temps fun x h1 h2 h3 h4 _ => ho x h1 h2 h3 h4
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge e le' m (tv id.i) = _ from hi,
      show Exec.evalExpr ge e le' m (tv id.n) = _ from hf.hn]
    simp only [typeof, cop]
    rw [ir_lt (a := (c : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hc : c < n
    · rw [ite_eq_left (by simpa using hc)]
      apply wp_skip
      obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [go_succ_lt _ _ _ _ _ _ (by omega)] at hgo
      wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hkv, typeof, cop, ir_sub]
      let le2 := PTree.set id.k (.Vint (ir ((kH : Int) - 1))) le'
      have hf2 : Frame m le2 bp pofs ptn level n := hf.temps fun x _ h2 _ _ _ => temps_gso _ _ h2
      have hi2 : PTree.get id.i le2 = some (.Vint (ir c)) := by
        simp only [le2]; rw [temps_gso _ _ (by decide)]; exact hi
      have hk2' : PTree.get id.k le2 = some (.Vint (ir ((kH - 1 : Nat) : Int))) := by
        simp only [le2]; rw [temps_gss]; congr 3; omega
      wp_step; wp_step
      apply wp_if_eval
      rw [eval_gt hf2 (tv id.i) c hc hi2 rfl]
      simp only [typeof, cop]
      by_cases hgt : level < ptn[c]!
      · rw [ite_eq_left (by simpa using hgt)]
        rw [ite_eq_left (by simpa using hgt)] at hgo
        have hnn2 : PTree.get id.nnt le2 = some (.Vint (ir nn)) := by
          simp only [le2]; rw [temps_gso _ _ (by decide)]; exact hnv
        wp_step; wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr]
        rw [show PTree.get id.nnt (PTree.set id.k (.Vint (ir ((kH : Int) - 1))) le') =
          some (.Vint (ir nn)) from hnn2]
        simp only [typeof, cop, ir_add]
        let le3 := PTree.set id.nnt (.Vint (ir ((nn : Int) + 1))) le2
        have hf3 : Frame m le3 bp pofs ptn level n := hf2.temps fun x _ _ h3 _ _ => temps_gso _ _ h3
        refine wp_skipCell hf3 hc hgt (by rw [temps_gso _ _ (by decide)]; exact hi2) ?_
        intro le4 hi4 ho4
        have hc1 : c + 1 < n := by
          rcases Nat.lt_or_ge (c + 1) n with h1 | h1
          · exact h1
          · have hcn : c = n - 1 := by omega
            rw [hcn] at hgt; have := h.last; omega
        have hsp := cellEnd_spec h.size hc1 h.last
        refine ⟨by simp, rfl, rfl, c, cellEnd ptn level (c + 1), kH - 1, nn + 1, F, by omega,
          hsp.2.1, rfl, by omega, hgo, by omega, by omega, by omega, hi4, ?_, ?_, ?_⟩
        · rw [ho4 _ (by decide) (by decide)]; rw [temps_gso _ _ (by decide)]
          exact hk2'
        · rw [ho4 _ (by decide) (by decide)]; rw [temps_gss]; congr 3
        · intro x h1 h2 h3 h4
          rw [ho4 x h1 h4]
          rw [temps_gso _ _ h3, temps_gso _ _ h2, ho x h1 h2 h3 h4]
      · rw [ite_eq_right (by simpa using hgt)]
        rw [ite_eq_right (by simpa using hgt)] at hgo
        apply wp_skip
        refine ⟨by simp, rfl, rfl, c, c, kH - 1, nn, F, Nat.le_refl _, hc, rfl, by omega, hgo,
          by omega, by omega, by omega, hi2, hk2', ?_, ?_⟩
        · rw [temps_gso _ _ (by decide)]; exact hnv
        · intro x h1 h2 h3 h4
          rw [temps_gso _ _ h2, ho x h1 h2 h3 h4]
    · rw [ite_eq_right (by simpa using hc)]
      apply wp_break
      have hcn' : c = n := by omega
      subst hcn'
      rw [go_ge _ _ _ _ _ _ (by omega)] at hgo
      have hR : Hex.GraphIso.Nauty.cheapautom.go ptn level c 0 c 0 = (kH, nn) := hgo.symm
      rw [hR] at hQ
      simpa using hQ le' hkv hnv ho
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, c, c2, kH, nn, F, hcc, hc2, rfl, hF, hgo, hk1, hk2, hnn, hi,
      hkv, hnv, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge e le' m (tv id.i) = _ from hi]
    simp only [Exec.evalExpr, typeof, cop, ir_add]
    refine ⟨n - (c2 + 1), by omega, by simp, rfl, rfl, c2 + 1, kH, nn, F, by omega, rfl, hF, hgo,
      by omega, hk2, by omega, by rw [temps_gss]; rfl, by rw [temps_gso _ _ (by decide)]; exact hkv,
      by rw [temps_gso _ _ (by decide)]; exact hnv, fun x h1 h2 h3 h4 => by
        rw [temps_gso _ _ h1, ho x h1 h2 h3 h4]⟩

end NautyVerified.Proofs.Cheapautom
