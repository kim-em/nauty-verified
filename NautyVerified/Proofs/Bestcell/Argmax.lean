import NautyVerified.Proofs.Bestcell.Frame
import NautyVerified.Proofs.Nextelement.Body

/-!
# The argmax of `bestcell`

`wp_argmax`: `v1 = 0; v2 = bucket[0]; for (i = 1; i < nnt; ++i) if (bucket[i] > v2)
{ v1 = i; v2 = bucket[i]; } return workperm[v1];` returns the start at
HexGraphIso's `argmaxLoop` position.
-/

namespace NautyVerified.Proofs.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Alloc (Keep gat)
open NautyVerified.Proofs.Updatecan (tv)
open Hex.GraphIso.Nauty (VSet argmaxLoop)

variable {xi : ExternalCalls}

section
variable {n : Nat} {bg : block} {gofs : ptrofs}
  {gw : Nat → Lib.Integers.int64} {grows : Array (VSet n)} {bl : block} {lofs : ptrofs}
  {lab : Array Nat} {bp : block} {pofs : ptrofs} {ptn : Array Nat} {level M : Nat}
  {bP bS bB : block}

theorem wp_argmax {Q : Post} {le : temp_env} {m : mem}
    (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {wv : Nat → val} (hw : ArrayAt m .Mint32 bP 0 wv n) {S : List Nat}
    (hwS : ∀ k < S.length, wv k = .Vint (ir (S[k]! : Int))) (hSlen : S.length ≤ n)
    (hS1 : 1 ≤ S.length)
    {bv : Nat → val} (hb : ArrayAt m .Mint32 bB 0 bv (n + 2)) {B : Array Nat}
    (hbv : ∀ x < S.length, bv x = .Vint (ir (B[x]! : Int))) (hBlt : ∀ x : Nat, B[x]! < 2147483648)
    (hnnt : PTree.get id.nnt le = some (.Vint (ir (S.length : Int))))
    (hQ : Q.ret E0 (.Vint (ir (S[argmaxLoop B (List.range' 1 (S.length - 1)) 0 B[0]!]! : Int))) m) :
    Wp xi ge Source.dense.fn.«naugraph:bestcell» argmax Q empty_env le m := by
  have hnlt := h.nlt
  let K := S.length
  let R := argmaxLoop B (List.range' 1 (K - 1)) 0 B[0]!
  have ho0 : ∀ x, x ≠ id.v1 → x ≠ id.v2 → x ≠ id.i → ∀ le' : temp_env,
      (∀ y, y ≠ id.v1 → y ≠ id.v2 → y ≠ id.i → PTree.get y le' = PTree.get y le) →
      PTree.get x le' = PTree.get x le := fun x h1 h2 h3 le' ho => ho x h1 h2 h3
  simp only [argmax]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  let le1 := PTree.set id.v1 (.Vint (ir 0)) le
  have hf1 := h.temps (le' := le1) fun x hx => temps_gso _ _ (by
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  rw [eval_bk hf1 hb (ci 0 tint) 0 (by omega) rfl rfl, hbv 0 (by omega)]
  simp only [E0_append]
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) => m' = m ∧ 1 ≤ k ∧ k ≤ K ∧
    PTree.get id.i le' = some (.Vint (ir k)) ∧ ∃ a, a < k ∧
      PTree.get id.v1 le' = some (.Vint (ir a)) ∧
      PTree.get id.v2 le' = some (.Vint (ir (B[a]! : Int))) ∧
      argmaxLoop B (List.range' k (K - k)) a B[a]! = R ∧
      ∀ y, y ≠ id.v1 → y ≠ id.v2 → y ≠ id.i → PTree.get y le' = PTree.get y le
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) => m' = m ∧
    PTree.get id.i le' = some (.Vint (ir k)) ∧ 1 ≤ k ∧ k < K ∧ ∃ a, a ≤ k ∧
      PTree.get id.v1 le' = some (.Vint (ir a)) ∧
      PTree.get id.v2 le' = some (.Vint (ir (B[a]! : Int))) ∧
      argmaxLoop B (List.range' (k + 1) (K - (k + 1))) a B[a]! = R ∧
      ∀ y, y ≠ id.v1 → y ≠ id.v2 → y ≠ id.i → PTree.get y le' = PTree.get y le
  wp_step
  refine wp_forLoopFrom id.i id.nnt amBody 1 K hS1 (by omega) Inv Mid ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨-, hk1, hk, hi, -, -, -, -, -, ho⟩
    exact ⟨hk1, hk, hi, by rw [ho _ (by decide) (by decide) (by decide)]; exact hnnt⟩
  · refine ⟨rfl, Nat.le_refl _, hS1, temps_gss _ _ _, 0, by omega,
      by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gss]; rfl, by
        rw [temps_gso _ _ (by decide), temps_gss], rfl, fun y h1 h2 h3 => ?_⟩
    rw [temps_gso _ _ h3, temps_gso _ _ h2, temps_gso _ _ h1]
  · rintro k le' m' hk1 hk ⟨rfl, -, -, hi, a, ha, hv1, hv2, hR, ho⟩
    have hf := h.temps (le' := le') fun x hx => ho x
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have ek := eval_bk hf hb (tv id.i) k (by omega) hi rfl
    rw [hbv k hk] at ek
    have hstep : List.range' k (K - k) = k :: List.range' (k + 1) (K - (k + 1)) := by
      rw [show K - k = (K - (k + 1)) + 1 by omega]; rfl
    rw [hstep, argmaxLoop] at hR
    have hBk := hBlt k
    have hBa := hBlt a
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, ek, show Exec.evalExpr ge empty_env le' m' (tv id.v2) = _ from hv2]
    simp only [typeof, cop]
    rw [ir_lt (a := (B[a]! : Int)) (b := (B[k]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hgt : B[a]! < B[k]!
    · rw [ite_eq_left (by simpa using hgt)]
      rw [ite_eq_left hgt] at hR
      wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hi, E0_append]
      wp_step; wp_step
      apply wp_set_eval
      rw [eval_bk (hf.temps (le' := PTree.set id.v1 (.Vint (ir k)) le') fun x hx => temps_gso _ _ (by
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hb (tv id.i) k (by omega)
        (by show PTree.get _ _ = _; rw [temps_gso _ _ (by decide)]; exact hi) rfl, hbv k hk]
      refine ⟨by simp, rfl, by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hi,
        hk1, hk, k, Nat.le_refl _, by rw [temps_gso _ _ (by decide), temps_gss], temps_gss _ _ _, hR,
        fun y h1 h2 h3 => ?_⟩
      rw [temps_gso _ _ h2, temps_gso _ _ h1, ho y h1 h2 h3]
    · rw [ite_eq_right (by simpa using hgt)]
      rw [ite_eq_right (by omega)] at hR
      apply wp_skip
      exact ⟨by simp, rfl, hi, hk1, hk, a, by omega, hv1, hv2, hR, ho⟩
  · rintro k le' m' ⟨rfl, hi, hk1, hk, a, ha, hv1, hv2, hR, ho⟩
    exact ⟨hi, rfl, by omega, by omega, temps_gss _ _ _, a, by omega,
      by rw [temps_gso _ _ (by decide)]; exact hv1, by rw [temps_gso _ _ (by decide)]; exact hv2, hR,
      fun y h1 h2 h3 => by rw [temps_gso _ _ h3, ho y h1 h2 h3]⟩
  · rintro le' m' ⟨hmm, -, -, hi, a, ha, hv1, hv2, hR, ho⟩
    rw [hmm]
    rw [Nat.sub_self, List.range'_zero, argmaxLoop] at hR
    have hQ' : Q.ret E0 (.Vint (ir (S[a]! : Int))) m := by rw [hR]; exact hQ
    have hf := h.temps (le' := le') fun x hx => ho x
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    wp_step; wp_step
    apply wp_return_some_eval
    rw [Exec.evalExpr, eval_wp hf hw (tv id.v1) a (by omega) hv1 rfl, hwS a ha]
    simp only [typeof, cop, Source.dense.fn.«naugraph:bestcell».fn_return_eq,
      Nextelement.free_empty]
    exact hQ'

end

end NautyVerified.Proofs.Bestcell
