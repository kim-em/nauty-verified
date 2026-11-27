import NautyVerified.Proofs.Bestcell.Frame

/-!
# `bestcell`'s word loop

`wp_orLoop`: `for (i = m; --i >= 0;) { setword1 |= workset[i] & gp[i];
setword2 |= workset[i] & ~gp[i]; }` leaves `setword1` zero exactly when the
words of `workset` and row `gp` share no bit, and `setword2` zero exactly
when `workset`'s words lie inside the row's. `setRep_eq_empty` turns those
into HexGraphIso's `interIsEmpty` and `subset`.
-/

namespace NautyVerified.Proofs.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Updatecan (tv)
open Hex.GraphIso.Nauty (VSet)

variable {xi : ExternalCalls}

theorem setRep_eq_empty {n M : Nat} {x : Nat → BitVec 64} {s : VSet n} (h : SetRep x M s) :
    s = VSet.empty ↔ ∀ w < M, x w = 0 := by
  constructor
  · rintro rfl w hw
    apply BitVec.eq_of_getMsbD_eq
    intro j hj
    have := h.2 (64 * w + j) (by omega)
    simp only [SetwordsMem, VSet.mem_empty, show (64 * w + j) / 64 = w by omega,
      show (64 * w + j) % 64 = j by omega] at this
    simp [this]
  · intro hz
    rw [VSet.eq_empty_iff]
    intro v
    rcases Nat.lt_or_ge v (64 * M) with hv | hv
    · rw [← h.2 v hv]
      simp only [SetwordsMem, hz (v / 64) (by omega)]
      simp
    · cases hm : s.mem v
      · rfl
      · have := VSet.mem_lt hm; have := h.1; omega

theorem interIsEmpty_iff {n M : Nat} {ws wt : Nat → BitVec 64} {s t : VSet n} (hs : SetRep ws M s)
    (ht : SetRep wt M t) : s.interIsEmpty t = true ↔ ∀ w < M, ws w &&& wt w = 0 := by
  rw [VSet.interIsEmpty_eq, VSet.isEmpty_iff]
  exact setRep_eq_empty (setRep_inter hs ht)

/-- `workset[a]` through the static pointer. -/
theorem eval_wsAt {le : temp_env} {m : mem} {bS : block} {ws : Nat → Lib.Integers.int64} {M : Nat}
    (hp : Mem.load .Mint64 m WS (zOfInt 0) = some (.Vptr bS Ptrofs.zero))
    (harr : ArrayAt m .Mint64 bS 0 (longs ws) M) (hM : M < 2147483648) (a : expr) (k : Nat)
    (hk : k < M) (ha : Exec.evalExpr ge empty_env le m a = some (.Vint (ir k)))
    (hty : typeof a = tint) :
    Exec.evalExpr ge empty_env le m (wsAt a) = some (.Vlong (ws k)) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get id.ws (empty_env : env) = none from rfl,
    find_naugraphWorkset, ha, hty]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp]
  show Mem.load _ _ _ (Ptrofs.unsigned _) = _
  rw [Set.addr_word (ofs := Ptrofs.zero) harr hk hM]
  exact harr.load k hk

/-- What the word loop computes, as a property of the final words. -/
def OrInv (ws rw : Nat → Lib.Integers.int64) (k M : Nat) (b1 b2 : Lib.Integers.int64) : Prop :=
  (bv64 b1 = 0 ↔ ∀ w, k ≤ w → w < M → bv64 (ws w) &&& bv64 (rw w) = 0) ∧
  (bv64 b2 = 0 ↔ ∀ w, k ≤ w → w < M → bv64 (ws w) &&& ~~~ bv64 (rw w) = 0)

theorem OrInv.step {ws rw : Nat → Lib.Integers.int64} {k M : Nat} {b1 b2 : Lib.Integers.int64}
    (h : OrInv ws rw (k + 1) M b1 b2) (hk : k < M) :
    OrInv ws rw k M (Int64.or b1 (Int64.and (ws k) (rw k)))
      (Int64.or b2 (Int64.and (ws k) (Int64.not (rw k)))) := by
  constructor
  · rw [bv64_or, bv64_and, show ∀ x y : BitVec 64, (x ||| y = 0) ↔ (x = 0 ∧ y = 0) from
      fun _ _ => BitVec.or_eq_zero_iff, h.1]
    constructor
    · rintro ⟨h1, h2⟩ w hw1 hw2
      by_cases e : w = k
      · subst e; exact h2
      · exact h1 w (by omega) hw2
    · intro hw; exact ⟨fun w h1 h2 => hw w (by omega) h2, hw k (Nat.le_refl _) hk⟩
  · rw [bv64_or, bv64_and, bv64_not, show ∀ x y : BitVec 64, (x ||| y = 0) ↔ (x = 0 ∧ y = 0) from
      fun _ _ => BitVec.or_eq_zero_iff, h.2]
    constructor
    · rintro ⟨h1, h2⟩ w hw1 hw2
      by_cases e : w = k
      · subst e; exact h2
      · exact h1 w (by omega) hw2
    · intro hw; exact ⟨fun w h1 h2 => hw w (by omega) h2, hw k (Nat.le_refl _) hk⟩

theorem wp_orLoop {Q : Post} {le : temp_env} {m : mem} {bS bg : block} {gofs : ptrofs}
    {ws rw : Nat → Lib.Integers.int64} {M : Nat} {b1 b2 : Lib.Integers.int64}
    (hp : Mem.load .Mint64 m WS (zOfInt 0) = some (.Vptr bS Ptrofs.zero))
    (hws : ArrayAt m .Mint64 bS 0 (longs ws) M)
    (hgp : PTree.get id.gp le = some (.Vptr bg gofs))
    (hrw : ArrayAt m .Mint64 bg (intOfZ (Ptrofs.unsigned gofs)) (longs rw) M)
    (hM : M < 2147483648) (hm : PTree.get id.m le = some (.Vint (ir M)))
    (hs1 : PTree.get id.sw1 le = some (.Vlong b1)) (hs2 : PTree.get id.sw2 le = some (.Vlong b2))
    (h0 : bv64 b1 = 0 ∧ bv64 b2 = 0)
    (hQ : ∀ le' c1 c2, PTree.get id.sw1 le' = some (.Vlong c1) →
      PTree.get id.sw2 le' = some (.Vlong c2) → OrInv ws rw 0 M c1 c2 →
      (∀ x, x ≠ id.i → x ≠ id.t14 → x ≠ id.sw1 → x ≠ id.sw2 → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m) :
    Wp xi ge Source.dense.fn.«naugraph:bestcell» orLoop Q empty_env le m := by
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hm, E0_append]
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ v ≤ M ∧ PTree.get id.i le' = some (.Vint (ir v)) ∧ ∃ c1 c2,
    PTree.get id.sw1 le' = some (.Vlong c1) ∧ PTree.get id.sw2 le' = some (.Vlong c2) ∧
    OrInv ws rw v M c1 c2 ∧
    ∀ x, x ≠ id.i → x ≠ id.t14 → x ≠ id.sw1 → x ≠ id.sw2 → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := fun v t e' le' m' => ∃ v', v' < v ∧ I v' t e' le' m') ?_ ?_
    (n := M) ⟨rfl, rfl, rfl, Nat.le_refl _, temps_gss _ _ _, b1, b2,
      by rw [temps_gso _ _ (by decide)]; exact hs1, by rw [temps_gso _ _ (by decide)]; exact hs2,
      ⟨by rw [h0.1]; exact ⟨fun _ w h1 h2 => absurd h2 (by omega), fun _ => rfl⟩,
       by rw [h0.2]; exact ⟨fun _ w h1 h2 => absurd h2 (by omega), fun _ => rfl⟩⟩,
      fun x hx _ _ _ => temps_gso _ _ hx⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, hv, hi, c1, c2, hc1, hc2, hor, ho⟩
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hi, typeof, cop, ir_sub]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, E0_append]
    apply wp_if_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, temps_gss, typeof, cop]
    rw [ir_lt (a := (v : Int) - 1) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
    by_cases hz : v = 0
    · subst hz
      rw [ite_eq_right (by simp)]
      apply wp_break
      refine hQ _ c1 c2 (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hc1)
        (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hc2) hor fun x h1 h2 h3 h4 => ?_
      rw [temps_gso _ _ h1, temps_gso _ _ h2, ho x h1 h2 h3 h4]
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      let le2 := PTree.set id.i (.Vint (ir ((v : Int) - 1)))
        (PTree.set id.t14 (.Vint (ir ((v : Int) - 1))) le')
      have hiv : Exec.evalExpr ge empty_env le2 m' (tv id.i) = some (.Vint (ir ((v - 1 : Nat) : Int))) := by
        show PTree.get _ _ = _
        rw [temps_gss]; congr 3; omega
      have hgp2 : PTree.get id.gp le2 = some (.Vptr bg gofs) := by
        rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), ho _ (by decide) (by decide)
          (by decide) (by decide)]; exact hgp
      have ews := eval_wsAt hp hws hM (tv id.i) (v - 1) (by omega) hiv rfl
      have egp := Set.eval_word (e := empty_env) hrw hM id.gp hgp2 (tv id.i) (v - 1) (by omega) hiv rfl
      have hc1' : PTree.get id.sw1 le2 = some (.Vlong c1) := by
        rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hc1
      have hc2' : PTree.get id.sw2 le2 = some (.Vlong c2) := by
        rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hc2
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [Exec.evalExpr, show Exec.evalExpr ge empty_env le2 m' (lv id.sw1) = _ from hc1',
        Exec.evalExpr, ews, egp]
      simp only [typeof, cop]
      wp_step; wp_step
      apply wp_set_eval
      have ews' := eval_wsAt (le := PTree.set id.sw1 (.Vlong (Int64.or c1 (Int64.and (ws (v - 1))
        (rw (v - 1))))) le2) hp hws hM (tv id.i) (v - 1) (by omega)
        (by show PTree.get _ _ = _; rw [temps_gso _ _ (by decide)]; exact hiv) rfl
      have egp' := Set.eval_word (e := empty_env) (le := PTree.set id.sw1 (.Vlong (Int64.or c1 (Int64.and (ws (v - 1))
        (rw (v - 1))))) le2) hrw hM id.gp (by rw [temps_gso _ _ (by decide)]; exact hgp2)
        (tv id.i) (v - 1) (by omega)
        (by show PTree.get _ _ = _; rw [temps_gso _ _ (by decide)]; exact hiv) rfl
      have hc2'' : Exec.evalExpr ge empty_env (PTree.set id.sw1 (.Vlong (Int64.or c1
          (Int64.and (ws (v - 1)) (rw (v - 1))))) le2) m' (lv id.sw2) = some (.Vlong c2) := by
        show PTree.get _ _ = _; rw [temps_gso _ _ (by decide)]; exact hc2'
      rw [Exec.evalExpr, hc2'', Exec.evalExpr, ews', Exec.evalExpr, egp']
      simp only [typeof, cop]
      have hv1 : v - 1 + 1 = v := by omega
      refine ⟨v - 1, by omega, by simp, rfl, rfl, by omega, ?_, _, _,
        by rw [temps_gso _ _ (by decide), temps_gss], temps_gss _ _ _,
        OrInv.step (by rw [hv1]; exact hor) (by omega), fun x h1 h2 h3 h4 => ?_⟩
      · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hiv
      · rw [temps_gso _ _ h4, temps_gso _ _ h3, temps_gso _ _ h1, temps_gso _ _ h2,
          ho x h1 h2 h3 h4]
  · rintro v t e' le' m' hJ
    apply wp_skip
    simpa using hJ

end NautyVerified.Proofs.Bestcell
