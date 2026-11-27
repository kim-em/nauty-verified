import NautyVerified.Proofs.Refine.State
import NautyVerified.Logic.Ints

/-!
# `for (x = y; ptn[x] > level; ++x) {}`

`wp_scanEnd`: from `y` holding `c`, the scan stops at the first `e ≥ c` with
`ptn[e] ≤ level`. The array is any `ints p`, so callers can scan a `ptn` that
differs from a snapshot outside the positions read.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Source NautyVerified.Proofs

variable {xi : ExternalCalls}

/-- `ptn[a] > level`, for `a` holding `j < n`. -/
theorem eval_ptn_gt {e : env} {le : temp_env} {m : mem} {bp : block} {pofs : ptrofs}
    {p : Array Nat} {n level j : Nat}
    (harr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints p) n) (hn : n < 2147483648)
    (hp : PTree.get dense.id.ptn le = some (.Vptr bp pofs))
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (hlevlt : level < 2147483648)
    (hsmall : p[j]! < 2147483648) (a : expr) (hj : j < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir j))) (hty : typeof a = tint) :
    Exec.evalExpr ge e le m (.Ebinop .Ogt (ix dense.id.ptn a) (tv dense.id.level) tint) =
      some (Val.of_bool (decide (level < p[j]!))) := by
  have hpe := eval_at (ge := ge) (e := e) harr hn dense.id.ptn hp a j hj ha hty
  rw [Exec.evalExpr, hpe, show Exec.evalExpr ge e le m (tv dense.id.level) = _ from hlev]
  simp only [ints, typeof, cop]
  rw [ir_lt (a := (level : Int)) (b := (p[j]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  congr 2
  apply decide_eq_decide.2; omega

theorem wp_scanEnd {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {x y : Common.AST.ident} (hxp : x ≠ dense.id.ptn) (hxl : x ≠ dense.id.level)
    {bp : block} {pofs : ptrofs} {p : Array Nat} {n level c en : Nat}
    (harr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints p) n) (hn : n < 2147483648)
    (hp : PTree.get dense.id.ptn le = some (.Vptr bp pofs))
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (hlevlt : level < 2147483648)
    (hsmall : ∀ i < n, p[i]! < 2147483648)
    (hy : PTree.get y le = some (.Vint (ir c)))
    (hce : c ≤ en) (hen : en < n) (hstop : p[en]! ≤ level)
    (hgo : ∀ i, c ≤ i → i < en → level < p[i]!)
    (hQ : ∀ le', PTree.get x le' = some (.Vint (ir en)) →
      (∀ z, z ≠ x → PTree.get z le' = PTree.get z le) → Q.normal E0 e le' m) :
    Wp xi ge f (scanEnd x y) Q e le m := by
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    m = m' ∧ ∃ j, c ≤ j ∧ j ≤ en ∧ v = en - j ∧ PTree.get x le' = some (.Vint (ir j)) ∧
      ∀ z, z ≠ x → PTree.get z le' = PTree.get z le
  simp only [scanEnd, Set.sk]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hy, E0_append]
  refine wp_loop (I := I) (J := fun v t e' le' m' => ∃ v', v' < v ∧ I (v' + 1) t e' le' m'
      ∧ True) ?_ ?_ (n := en - c)
    ⟨rfl, rfl, rfl, c, Nat.le_refl _, hce, rfl, temps_gss _ _ _, fun z hz => temps_gso _ _ hz⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, j, hj1, hj2, rfl, hxj, ho⟩
    have hp' : PTree.get dense.id.ptn le' = some (.Vptr bp pofs) := by rw [ho _ (Ne.symm hxp)]; exact hp
    have hl' : PTree.get dense.id.level le' = some (.Vint (ir level)) := by
      rw [ho _ (Ne.symm hxl)]; exact hlev
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [eval_ptn_gt harr hn hp' hl' hlevlt (hsmall j (by omega)) (tv x) (by omega) hxj rfl]
    simp only [typeof, cop]
    by_cases hend : j = en
    · subst hend
      rw [ite_eq_right (by simp; omega)]
      apply wp_break
      exact hQ le' hxj ho
    · have hgt := hgo j hj1 (by omega)
      rw [ite_eq_left (by simpa using hgt)]
      apply wp_skip
      apply wp_skip
      exact ⟨en - (j + 1), by omega, ⟨by simp, rfl, rfl, j, hj1, hj2, by omega, hxj, ho⟩, True.intro⟩
  · rintro v t e' le' m' ⟨v', hv', ⟨rfl, rfl, rfl, j, hj1, hj2, hv, hxj, ho⟩, -⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hxj, typeof, cop, ir_add]
    refine ⟨en - (j + 1), by omega, by simp, rfl, rfl, j + 1, by omega, by omega, rfl, ?_, ?_⟩
    · rw [temps_gss]; push_cast; rfl
    · intro z hz; rw [temps_gso _ _ hz, ho z hz]

end NautyVerified.Proofs.Refine
