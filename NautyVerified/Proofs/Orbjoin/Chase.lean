import NautyVerified.Proofs.Orbjoin.Syntax
import NautyVerified.Spec.Orbjoin
import NautyVerified.Logic.Ints
import NautyVerified.Logic.Wp
import NautyVerified.Logic.Simp
import NautyVerified.Exec.Cop
import NautyVerified.Program.Dense

/-!
# The root-chasing loops of `orbjoin`

`wp_chase`: on a descending orbit forest held in the `orbits` array, the loop
`while (orbits[j] != j) j = orbits[j];` started at `start` ends with `j` the
root `chaseList` finds, and changes no other temporary.
-/

namespace NautyVerified.Proofs.Orbjoin

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open Hex.GraphIso.Nauty.Orbit

variable {xi : ExternalCalls}

/-- Reading `orbits[e]` for an index `e` holding `c < n`. -/
theorem eval_orb {e : env} {le : temp_env} {m : mem} {bo : block} {ofs : ptrofs}
    {o : Array Nat} {n : Nat} (harr : ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (ints o) n)
    (hn : n < 2147483648) (horb : PTree.get id.orbits le = some (.Vptr bo ofs))
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge e le m (orb a) = some (ints o c) := by
  simp only [orb, Exec.evalExpr, horb, ha, hty]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  apply load_array harr hc
  apply addr_elem ofs _ .Mint32 rfl rfl (by omega)
  have hf := harr.fits
  have h4 : csize .Mint32 = 4 := rfl
  rw [h4] at hf ⊢
  omega

theorem ints_lt {o : Array Nat} {n : Nat} (hd : Descending o n) {c : Nat} (hc : c < n) :
    o[c]! < n := Nat.lt_of_le_of_lt (hd.2 c hc) hc

/-- The chase loop reaches the root. -/
theorem wp_chase (f : function) (j : Common.AST.ident) (hj : j ≠ id.orbits) {Q : Post} {e : env}
    {le : temp_env} {m : mem} {bo : block} {ofs : ptrofs} {o : Array Nat} {n : Nat}
    (harr : ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (ints o) n)
    (hn : n < 2147483648) (horb : PTree.get id.orbits le = some (.Vptr bo ofs))
    (hd : Descending o n) {start : Nat} (hs : start < n)
    (hjv : PTree.get j le = some (.Vint (ir start)))
    (hQ : ∀ le' : temp_env, PTree.get j le' = some (.Vint (ir (chaseList o (List.range n) start))) →
      (∀ k, k ≠ j → PTree.get k le' = PTree.get k le) → Q.normal E0 e le' m) :
    Wp xi ge f (chase j) Q e le m := by
  -- The invariant: `j` holds `cur`, whose root is that of `start`.
  let I : Nat → trace → Assn := fun k t e' le' m' => t = E0 ∧ e = e' ∧ m = m' ∧
    PTree.get j le' = some (.Vint (ir k)) ∧ k < n ∧
    chaseList o (List.range n) k = chaseList o (List.range n) start ∧
    ∀ k', k' ≠ j → PTree.get k' le' = PTree.get k' le
  refine wp_loop (I := I) (J := fun k t e' le' m' => ∃ k' < k, I k' t e' le' m') ?_ ?_
    (n := start) ⟨rfl, rfl, rfl, hjv, hs, rfl, fun _ _ => rfl⟩
  · rintro cur t e' le' m' ⟨rfl, rfl, rfl, hcur, hcn, hroot, hother⟩
    have horb' : PTree.get id.orbits le' = some (.Vptr bo ofs) := by rw [hother _ hj.symm, horb]
    have hjc : Exec.evalExpr ge e le' m (tv j) = some (.Vint (ir cur)) := hcur
    have hoc := eval_orb harr hn horb' (tv j) cur hcn hjc rfl
    have hlt := ints_lt hd hcn
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, hoc, hjc]
    simp only [ints, typeof, cop]
    rw [ir_eq (a := (o[cur]! : Int)) (b := cur) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hr : o[cur]! = cur
    · rw [ite_eq_right (by simp [hr])]
      apply wp_break
      apply hQ le' _ hother
      rw [hcur, ← hroot]
      have := chaseList_root hd (List.range n) cur hcn (by simpa using hcn)
      congr 3
      cases n with
      | zero => omega
      | succ n => simp [List.range_succ_eq_map, chaseList, hr]
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      simp only [seqPost, Post.after, E0_append]
      wp_step; wp_step
      apply wp_set_eval
      rw [hoc]
      simp only [ints]
      have hdown : o[cur]! < cur := by have := hd.2 cur hcn; omega
      refine ⟨o[cur]!, hdown, rfl, rfl, rfl, temps_gss _ _ _, hlt, ?_, fun k' hk' => ?_⟩
      · rw [← hroot]
        cases n with
        | zero => omega
        | succ n =>
          have h2 := (chaseList_root hd (List.range (n + 1)) o[cur]! hlt (by simpa using hlt)).2.2
          conv => rhs; rw [List.range_succ_eq_map]
          simp only [chaseList, hr, beq_iff_eq, ite_false]
          exact (h2 _ (by simp only [List.length_map, List.length_range]; omega)).symm
      · rw [temps_gso _ _ hk', hother k' hk']
  · rintro k t e' le' m' ⟨k', hk', hI⟩
    apply wp_skip
    exact ⟨k', hk', by simpa using hI⟩

end NautyVerified.Proofs.Orbjoin
