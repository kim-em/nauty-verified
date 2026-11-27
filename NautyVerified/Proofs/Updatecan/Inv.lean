import NautyVerified.Proofs.Updatecan.Syntax
import NautyVerified.Spec.InvPerm

/-!
# The inverse of `lab` in `updatecan`

`wp_inv`: `for (i = 0; i < n; ++i) workperm[lab[i]] = i;` writes what
HexGraphIso's `invPerm.go` computes at every position some `lab[j]` hits.
-/

namespace NautyVerified.Proofs.Updatecan

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Alloc (gat eval_gat wp_gstore Keep)
open Hex.GraphIso.Nauty (invPerm)

variable {xi : ExternalCalls}

/-- `workperm` after writing `lab[0 .. k-1]`. -/
def written (lab : Array Nat) (n : Nat) (vals : Nat → val) (k p : Nat) : val :=
  if ∃ j < k, lab[j]! = p then
    .Vint (ir ((invPerm.go lab (List.range k) (Array.replicate n 0))[p]! : Int))
  else vals p

theorem written_succ (lab : Array Nat) (n : Nat) (vals : Nat → val) (k : Nat) (hk : lab[k]! < n) :
    upd (written lab n vals k) lab[k]! (.Vint (ir (k : Int))) = written lab n vals (k + 1) := by
  funext p
  have hsz : (invPerm.go lab (List.range k) (Array.replicate n 0)).size = n := by
    rw [invPerm_go_size]; simp
  simp only [upd, written, invPerm_go_succ]
  by_cases hp : p = lab[k]!
  · subst hp
    rw [ite_eq_left rfl, ite_eq_left ⟨k, by omega, rfl⟩, Array.getElem!_set!_self _ _ _ (by omega)]
  · rw [ite_eq_right hp, Array.getElem!_set!_ne _ _ _ _ (Ne.symm hp)]
    have : (∃ j < k + 1, lab[j]! = p) ↔ (∃ j < k, lab[j]! = p) :=
      ⟨fun ⟨j, hj, he⟩ => ⟨j, by
        rcases Nat.lt_or_ge j k with h | h
        · exact h
        · exact absurd (show j = k by omega ▸ he).symm hp, he⟩,
       fun ⟨j, hj, he⟩ => ⟨j, by omega, he⟩⟩
    by_cases hex : ∃ j < k, lab[j]! = p
    · rw [ite_eq_left (this.2 hex), ite_eq_left hex]
    · rw [ite_eq_right (fun h => hex (this.1 h)), ite_eq_right hex]

theorem wp_inv {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bl : block}
    {lofs : ptrofs} {bW : block} {lab : Array Nat} {n : Nat} {vals : Nat → val}
    (hge : PTree.get id.wp e = none) (hl : PTree.get id.lab le = some (.Vptr bl lofs))
    (hlarr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n)
    (hls : ∀ j < n, lab[j]! < n) (hnv : PTree.get id.n le = some (.Vint (ir n)))
    (hn : n < 2147483648)
    (hwp : 0 < n → Mem.load .Mint64 m Block.naugraphWorkperm (zOfInt 0) = some (.Vptr bW Ptrofs.zero))
    (hwarr : ArrayAt m .Mint32 bW 0 vals n)
    (hbl : 0 < n → bl ≠ bW) (hbw : 0 < n → Block.naugraphWorkperm ≠ bW)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bW 0 (written lab n vals n) n →
      Unch m m' (fun z => 0 < n ∧ z = bW) → Keep m m' bW →
      (∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f inv Q e le m := by
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) => k ≤ n ∧
    PTree.get id.i le' = some (.Vint (ir k)) ∧ PTree.get id.n le' = some (.Vint (ir n)) ∧
    ArrayAt m' .Mint32 bW 0 (written lab n vals k) n ∧ Unch m m' (fun z => 0 < n ∧ z = bW) ∧
    Keep m m' bW ∧ ∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    PTree.get id.i le' = some (.Vint (ir k)) ∧ k < n ∧ PTree.get id.n le' = some (.Vint (ir n)) ∧
    ArrayAt m' .Mint32 bW 0 (written lab n vals (k + 1)) n ∧ Unch m m' (fun z => 0 < n ∧ z = bW) ∧
    Keep m m' bW ∧ ∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le
  refine wp_forLoop id.i id.n _ n hn Inv Mid ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, hn', -⟩
    exact ⟨hk, hi, hn'⟩
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hnv,
      hwarr.congr fun p _ => by simp [written], Unch.refl _ _, Keep.refl _ _,
      fun x hx => temps_gso _ _ hx⟩
  · rintro k le' m' hk ⟨-, hi, hn', harr, hu, hkp, ho⟩
    have hlk := hls k hk
    have hlarr' := hlarr.unch hu (fun ⟨_, h⟩ => hbl (by omega) h)
    have hl' : PTree.get id.lab le' = some (.Vptr bl lofs) := by
      rw [ho _ (by decide)]; exact hl
    wp_step; wp_step
    refine wp_gstore hge find_naugraphWorkperm
      (by rw [hu.load _ _ _ (fun ⟨_, h⟩ => hbw (by omega) h)]; exact hwp (by omega)) harr hn
      (labAt (tv id.i)) lab[k]! hlk (eval_at (ge := ge) (e := e) hlarr' hn id.lab hl' (tv id.i) k hk hi rfl)
      rfl (tv id.i) k hi rfl ?_
    intro m'' harr' hu' hk'
    rw [written_succ lab n vals k hlk] at harr'
    exact ⟨rfl, hi, hk, hn', harr', hu.trans (hu'.mono fun z hz => ⟨by omega, hz⟩), hkp.trans hk', ho⟩
  · rintro k le' m' ⟨hi, hk, hn', harr, hu, hkp, ho⟩
    exact ⟨hi, by omega, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hn', harr, hu, hkp,
      fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩
  · rintro le' m' ⟨-, -, -, harr, hu, hkp, ho⟩
    exact hQ le' m' harr hu hkp ho

end NautyVerified.Proofs.Updatecan
