import NautyVerified.Proofs.Testcanlab.Syntax
import NautyVerified.Proofs.Alloc.Global
import NautyVerified.Proofs.Set.Add
import NautyVerified.Spec.WordCmp

/-!
# The row comparison of `testcanlab`

`wp_cmp`: the loop over the `M` words of `workset` and row `ph` of `canong`
returns `-1` or `1` (after writing `*samerows = i`) exactly as
`wordScan` finds a first difference, and otherwise ends normally.
-/

namespace NautyVerified.Proofs.Testcanlab

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Updatecan (tv)

variable {xi : ExternalCalls}

/-- `workset[e]` through the static pointer. -/
theorem eval_wsAt {le : temp_env} {m : mem} {bWS : block} {ws : Nat → Lib.Integers.int64} {M k : Nat}
    (hp : Mem.load .Mint64 m Block.naugraphWorkset (zOfInt 0) = some (.Vptr bWS Ptrofs.zero))
    (harr : ArrayAt m .Mint64 bWS 0 (longs ws) M) (hM : M < 2147483648) (hk : k < M)
    (hj : PTree.get id.j le = some (.Vint (ir k))) :
    Exec.evalExpr ge empty_env le m wsAt = some (.Vlong (ws k)) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get id.ws (empty_env : env) = none from rfl,
    find_naugraphWorkset, hj]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp]
  show Mem.load _ _ _ (Ptrofs.unsigned _) = _
  rw [Set.addr_word (ofs := Ptrofs.zero) harr hk hM]
  exact harr.load k hk

theorem wp_cmp {Q : Post} {le : temp_env} {m : mem} {bWS bc bs : block} {pofs so : ptrofs}
    {ws pw : Nat → Lib.Integers.int64} {vals : Nat → val} {M c : Nat}
    (hp : 0 < M → Mem.load .Mint64 m Block.naugraphWorkset (zOfInt 0) = some (.Vptr bWS Ptrofs.zero))
    (hwarr : ArrayAt m .Mint64 bWS 0 (longs ws) M)
    (hph : PTree.get id.ph le = some (.Vptr bc pofs))
    (hparr : ArrayAt m .Mint64 bc (intOfZ (Ptrofs.unsigned pofs)) (longs pw) M)
    (hsr : PTree.get id.samerows le = some (.Vptr bs so))
    (hsarr : ArrayAt m .Mint32 bs (intOfZ (Ptrofs.unsigned so)) vals 1)
    (hi : PTree.get id.i le = some (.Vint (ir c))) (hm : PTree.get id.m le = some (.Vint (ir M)))
    (hM : M < 2147483648)
    (hQn : wordScan (fun w => bv64 (ws w)) (fun w => bv64 (pw w)) M 0 = .eq →
      ∀ le', (∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m)
    (hQr : ∀ m', ArrayAt m' .Mint32 bs (intOfZ (Ptrofs.unsigned so)) (fun _ => .Vint (ir c)) 1 →
      Unch m m' (· = bs) →
      (wordScan (fun w => bv64 (ws w)) (fun w => bv64 (pw w)) M 0 = .lt →
        Q.ret E0 (.Vint (ir (-1))) m') ∧
      (wordScan (fun w => bv64 (ws w)) (fun w => bv64 (pw w)) M 0 = .gt →
        Q.ret E0 (.Vint (ir 1)) m')) :
    Wp xi ge Source.dense.fn.testcanlab cmp Q empty_env le m := by
  let S := wordScan (fun w => bv64 (ws w)) (fun w => bv64 (pw w))
  -- `*samerows = i;`
  obtain ⟨m', hst, harr', -⟩ := store_array hsarr (show 0 < 1 by decide) (.Vint (ir c)) rfl
  have harr'' : ArrayAt m' .Mint32 bs (intOfZ (Ptrofs.unsigned so)) (fun _ => .Vint (ir c)) 1 :=
    harr'.congr fun i hi => by simp [upd, show i = 0 by omega]
  have hstop : ∀ (le' : temp_env) (a : expr) (r : Int) (Q' : Post),
      (∀ le'' m'', Exec.evalExpr ge empty_env le'' m'' a = some (.Vint (ir r))) → typeof a = tint →
      PTree.get id.samerows le' = some (.Vptr bs so) → PTree.get id.i le' = some (.Vint (ir c)) →
      Q'.ret E0 (.Vint (ir r)) m' →
      Wp xi ge Source.dense.fn.testcanlab (stop a) Q' empty_env le' m := by
    intro le' a r Q' ha hty h1 h2 hret
    wp_step; wp_step; wp_step
    apply wp_assign_eval
    simp only [Exec.evalLvalue, Exec.evalExpr, h1, h2, typeof, cop, Exec.assignLoc,
      Cfrontend.Ctypes.access_mode, Mem.storev]
    rw [show Ptrofs.unsigned so = elemOfs .Mint32 (intOfZ (Ptrofs.unsigned so)) 0 by
      unfold elemOfs
      rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ], hst]
    wp_step; wp_step
    apply wp_return_some_eval
    rw [ha]
    simp only [hty, cop, Source.dense.fn.testcanlab.fn_return_eq, Nextelement.free_empty]
    exact hret
  have hnS : ∀ (F k : Nat), S (F + 1) k = if (bv64 (ws k)).toNat < (bv64 (pw k)).toNat then .lt
      else if (bv64 (pw k)).toNat < (bv64 (ws k)).toNat then .gt else S F (k + 1) := fun _ _ => rfl
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m'' : mem) => t = E0 ∧
    e' = empty_env ∧ m'' = m ∧ ∃ k, k ≤ M ∧ v = M - k ∧ PTree.get id.j le' = some (.Vint (ir k)) ∧
      S M 0 = S (M - k) k ∧ ∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m'' : mem) => t = E0 ∧
    e' = empty_env ∧ m'' = m ∧ ∃ k, k < M ∧ v = M - k ∧ PTree.get id.j le' = some (.Vint (ir k)) ∧
      S M 0 = S (M - (k + 1)) (k + 1) ∧ ∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_
    (n := M - 0) ⟨rfl, rfl, rfl, 0, Nat.zero_le _, rfl, temps_gss _ _ _, rfl,
      fun x hx => temps_gso _ _ hx⟩
  · rintro v t e' le' m'' ⟨rfl, rfl, rfl, k, hk, rfl, hj, hS, ho⟩
    have hm' : PTree.get id.m le' = some (.Vint (ir M)) := by rw [ho _ (by decide)]; exact hm
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge empty_env le' _ (tv id.j) = _ from hj,
      show Exec.evalExpr ge empty_env le' _ (tv id.m) = _ from hm']
    simp only [typeof, cop]
    rw [ir_lt (a := (k : Int)) (b := (M : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hkM : k < M
    · rw [ite_eq_left (by simpa using hkM)]
      apply wp_skip
      have hw := eval_wsAt (hp (by omega)) hwarr hM hkM hj
      have hpa := Set.eval_word (e := empty_env) hparr hM id.ph (by rw [ho _ (by decide)]; exact hph)
        (tv id.j) k hkM hj rfl
      have hSk : S (M - k) k = if (bv64 (ws k)).toNat < (bv64 (pw k)).toNat then .lt
          else if (bv64 (pw k)).toNat < (bv64 (ws k)).toNat then .gt else S (M - (k + 1)) (k + 1) := by
        rw [show M - k = (M - (k + 1)) + 1 by omega, hnS]
      have hsr' : PTree.get id.samerows le' = some (.Vptr bs so) := by rw [ho _ (by decide)]; exact hsr
      have hi' : PTree.get id.i le' = some (.Vint (ir c)) := by rw [ho _ (by decide)]; exact hi
      wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, hw, hpa]
      simp only [typeof, cop, bv64_ltu]
      by_cases hlt : (bv64 (ws k)).toNat < (bv64 (pw k)).toNat
      · rw [ite_eq_left (by simpa using hlt)]
        refine hstop le' _ (-1) _ (fun _ _ => by simp only [Exec.evalExpr, typeof, cop]; rfl) rfl hsr' hi' ?_
        exact (hQr m' harr'' (Unch.store hst rfl)).1 (hS.trans (hSk.trans (ite_eq_left hlt)))
      · rw [ite_eq_right (by simpa using hlt)]
        wp_step; wp_step
        apply wp_if_eval
        rw [Exec.evalExpr, hw, hpa]
        simp only [typeof, cop, bv64_ltu]
        by_cases hgt : (bv64 (pw k)).toNat < (bv64 (ws k)).toNat
        · rw [ite_eq_left (by simpa using hgt)]
          refine hstop le' _ 1 _ (fun _ _ => rfl) rfl hsr' hi' ?_
          exact (hQr m' harr'' (Unch.store hst rfl)).2
            (hS.trans (hSk.trans ((ite_eq_right hlt).trans (ite_eq_left hgt))))
        · rw [ite_eq_right (by simpa using hgt)]
          apply wp_skip
          exact ⟨rfl, rfl, rfl, k, hkM, rfl, hj,
            hS.trans (hSk.trans ((ite_eq_right hlt).trans (ite_eq_right hgt))), ho⟩
    · rw [ite_eq_right (by simpa using hkM)]
      apply wp_break
      have hkM' : M - k = 0 := by omega
      have hS0 : S M 0 = .eq := by rw [hkM'] at hS; exact hS
      simpa using hQn hS0 le' ho
  · rintro v t e' le' m'' ⟨rfl, rfl, rfl, k, hk, rfl, hj, hS, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge empty_env le' _ (tv id.j) = _ from hj]
    simp only [Exec.evalExpr, typeof, cop, ir_add]
    refine ⟨M - (k + 1), by omega, by simp, rfl, rfl, k + 1, by omega, rfl, temps_gss _ _ _, hS,
      fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩

end NautyVerified.Proofs.Testcanlab
