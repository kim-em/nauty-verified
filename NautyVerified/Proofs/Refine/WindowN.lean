import NautyVerified.Proofs.Refine.Frame
import NautyVerified.Proofs.Alloc.Global

/-!
# Growing the bucket window

`wp_widenLo`: `while (bmin > cnt) bucket[--bmin] = 0;` lowers `bmin` to
`min bmin cnt`, zeroing the new slots; `wp_widenHi` is the same for `bmax`.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word
open NautyVerified.Source NautyVerified.Proofs NautyVerified.Proofs.Alloc

variable {xi : ExternalCalls}

/-- `while (bmin > cnt) bucket[--bmin] = 0;` with SimplExpr's temporary `t`. -/
abbrev widenLo (t : Common.AST.ident) : statement :=
  .Sloop
    (.Ssequence
      (Set.sk (.Sifthenelse (.Ebinop .Ogt (tv dense.id.bmin) (tv dense.id.cnt) tint) .Sskip .Sbreak))
      (.Ssequence
        (.Ssequence
          (Set.sk (.Sset t (.Ecast (.Ebinop .Osub (tv dense.id.bmin) (ci 1 tint) tint) tint)))
          (.Sset dense.id.bmin (tv t)))
        (.Sassign (gix dense.id.«naugraph:bucket» (tv t)) (ci 0 tint))))
    .Sskip

/-- `while (bmax < cnt) bucket[++bmax] = 0;` with SimplExpr's temporary `t`. -/
abbrev widenHi (t : Common.AST.ident) : statement :=
  .Sloop
    (.Ssequence
      (Set.sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.bmax) (tv dense.id.cnt) tint) .Sskip .Sbreak))
      (.Ssequence
        (.Ssequence
          (Set.sk (.Sset t (.Ecast (.Ebinop .Oadd (tv dense.id.bmax) (ci 1 tint) tint) tint)))
          (.Sset dense.id.bmax (tv t)))
        (.Sassign (gix dense.id.«naugraph:bucket» (tv t)) (ci 0 tint))))
    .Sskip

theorem wp_widenLo {Q : Post} {le : temp_env} {m : mem} {t : Common.AST.ident}
    (ht1 : t ≠ dense.id.bmin) (ht2 : t ≠ dense.id.cnt) {bB : block} {bv : Nat → val} {cap B c : Nat}
    (hb : PTree.get dense.id.bmin le = some (.Vint (ir B)))
    (hc : PTree.get dense.id.cnt le = some (.Vint (ir c)))
    (harr : ArrayAt m .Mint32 bB 0 bv cap)
    (hp : Mem.load .Mint64 m Block.naugraphBucket (zOfInt 0) = some (.Vptr bB Ptrofs.zero))
    (hbg : Block.naugraphBucket ≠ bB) (hB : B < cap) (hcap : cap < 2147483648) (hcc : c < cap)
    (hQ : ∀ le' m', PTree.get dense.id.bmin le' = some (.Vint (ir (min B c : Nat))) →
      ArrayAt m' .Mint32 bB 0 (fun v => if min B c ≤ v ∧ v < B then .Vint (ir 0) else bv v) cap →
      Unch m m' (· = bB) → Keep m m' bB →
      (∀ z, z ≠ dense.id.bmin → z ≠ t → PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.refine (widenLo t) Q empty_env le m := by
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ j, min B c ≤ j ∧ j ≤ B ∧ v = j - min B c ∧
      PTree.get dense.id.bmin le' = some (.Vint (ir (j : Nat))) ∧
      ArrayAt m' .Mint32 bB 0 (fun v => if j ≤ v ∧ v < B then .Vint (ir 0) else bv v) cap ∧
      Unch m m' (· = bB) ∧ Keep m m' bB ∧
      (∀ z, z ≠ dense.id.bmin → z ≠ t → PTree.get z le' = PTree.get z le)
  refine wp_loop (I := I) (J := fun v tr e' le' m' => ∃ v', v' < v ∧ I v' tr e' le' m') ?_ ?_
    (n := B - min B c) ⟨rfl, rfl, B, Nat.min_le_left _ _, Nat.le_refl _, rfl, hb,
      harr.congr fun v _ => (ite_eq_right (by omega)).symm,
      Unch.refl _ _, Keep.refl _ _, fun _ _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, j, hj1, hj2, rfl, hbj, harr', hu, hk, ho⟩
    have hc' : PTree.get dense.id.cnt le' = some (.Vint (ir c)) := by
      rw [ho _ (by decide) (Ne.symm ht2)]; exact hc
    have hp' : Mem.load .Mint64 m' Block.naugraphBucket (zOfInt 0) =
        some (.Vptr bB Ptrofs.zero) := by rw [hu.load _ _ _ hbg]; exact hp
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hbj, hc', typeof, cop]
    rw [ir_lt (a := (c : Int)) (b := (j : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hjc : c < j
    · rw [ite_eq_left (by simpa using hjc)]
      apply wp_skip
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hbj, typeof, cop, ir_sub]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss]
      have hj1' : ((j : Int) - 1) = ((j - 1 : Nat) : Int) := by omega
      rw [hj1']
      refine wp_gstore rfl find_naugraphBucket hp' harr' (by omega) (tv t) (j - 1) (by omega)
        (by show PTree.get _ _ = _; rw [temps_gso _ _ ht1, temps_gss]) rfl (ci 0 tint) 0 rfl rfl ?_
      intro m2 harr2 hu2 hk2
      refine ⟨j - 1 - min B c, by omega, ⟨by simp, rfl, j - 1, by omega, by omega, rfl,
        temps_gss _ _ _, harr2.congr fun v _ => ?_, hu.trans hu2, hk.trans hk2, fun z h1 h2 => ?_⟩⟩
      · simp only [upd]
        by_cases hv : v = j - 1
        · rw [ite_eq_left hv, ite_eq_left (by omega)]
        · rw [ite_eq_right hv]
          by_cases hv2 : j ≤ v ∧ v < B
          · rw [ite_eq_left hv2, ite_eq_left (by omega)]
          · rw [ite_eq_right hv2, ite_eq_right (by omega)]
      · rw [temps_gso _ _ h1, temps_gso _ _ h2, ho z h1 h2]
    · rw [ite_eq_right (by simpa using hjc)]
      apply wp_break
      have hj : j = min B c := by omega
      subst hj
      exact hQ le' m' hbj harr' hu hk ho
  · rintro v tr e' le' m' hJ
    apply wp_skip
    simpa using hJ

theorem wp_widenHi {Q : Post} {le : temp_env} {m : mem} {t : Common.AST.ident}
    (ht1 : t ≠ dense.id.bmax) (ht2 : t ≠ dense.id.cnt) {bB : block} {bv : Nat → val} {cap B c : Nat}
    (hb : PTree.get dense.id.bmax le = some (.Vint (ir B)))
    (hc : PTree.get dense.id.cnt le = some (.Vint (ir c)))
    (harr : ArrayAt m .Mint32 bB 0 bv cap)
    (hp : Mem.load .Mint64 m Block.naugraphBucket (zOfInt 0) = some (.Vptr bB Ptrofs.zero))
    (hbg : Block.naugraphBucket ≠ bB) (hB : B < cap) (hcap : cap < 2147483648) (hcc : c < cap)
    (hQ : ∀ le' m', PTree.get dense.id.bmax le' = some (.Vint (ir (max B c : Nat))) →
      ArrayAt m' .Mint32 bB 0 (fun v => if B < v ∧ v ≤ max B c then .Vint (ir 0) else bv v) cap →
      Unch m m' (· = bB) → Keep m m' bB →
      (∀ z, z ≠ dense.id.bmax → z ≠ t → PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.refine (widenHi t) Q empty_env le m := by
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ j, B ≤ j ∧ j ≤ max B c ∧ v = max B c - j ∧
      PTree.get dense.id.bmax le' = some (.Vint (ir (j : Nat))) ∧
      ArrayAt m' .Mint32 bB 0 (fun v => if B < v ∧ v ≤ j then .Vint (ir 0) else bv v) cap ∧
      Unch m m' (· = bB) ∧ Keep m m' bB ∧
      (∀ z, z ≠ dense.id.bmax → z ≠ t → PTree.get z le' = PTree.get z le)
  refine wp_loop (I := I) (J := fun v tr e' le' m' => ∃ v', v' < v ∧ I v' tr e' le' m') ?_ ?_
    (n := max B c - B) ⟨rfl, rfl, B, Nat.le_refl _, Nat.le_max_left _ _, rfl, hb,
      harr.congr fun v _ => (ite_eq_right (by omega)).symm,
      Unch.refl _ _, Keep.refl _ _, fun _ _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, j, hj1, hj2, rfl, hbj, harr', hu, hk, ho⟩
    have hc' : PTree.get dense.id.cnt le' = some (.Vint (ir c)) := by
      rw [ho _ (by decide) (Ne.symm ht2)]; exact hc
    have hp' : Mem.load .Mint64 m' Block.naugraphBucket (zOfInt 0) =
        some (.Vptr bB Ptrofs.zero) := by rw [hu.load _ _ _ hbg]; exact hp
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hbj, hc', typeof, cop]
    rw [ir_lt (a := (j : Int)) (b := (c : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hjc : j < c
    · rw [ite_eq_left (by simpa using hjc)]
      apply wp_skip
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hbj, typeof, cop, ir_add]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss]
      have hj1' : ((j : Int) + 1) = ((j + 1 : Nat) : Int) := by omega
      rw [hj1']
      refine wp_gstore rfl find_naugraphBucket hp' harr' (by omega) (tv t) (j + 1) (by omega)
        (by show PTree.get _ _ = _; rw [temps_gso _ _ ht1, temps_gss]) rfl (ci 0 tint) 0 rfl rfl ?_
      intro m2 harr2 hu2 hk2
      refine ⟨max B c - (j + 1), by omega, ⟨by simp, rfl, j + 1, by omega, by omega, rfl,
        temps_gss _ _ _, harr2.congr fun v _ => ?_, hu.trans hu2, hk.trans hk2, fun z h1 h2 => ?_⟩⟩
      · simp only [upd]
        by_cases hv : v = j + 1
        · rw [ite_eq_left hv, ite_eq_left (by omega)]
        · rw [ite_eq_right hv]
          by_cases hv2 : B < v ∧ v ≤ j
          · rw [ite_eq_left hv2, ite_eq_left (by omega)]
          · rw [ite_eq_right hv2, ite_eq_right (by omega)]
      · rw [temps_gso _ _ h1, temps_gso _ _ h2, ho z h1 h2]
    · rw [ite_eq_right (by simpa using hjc)]
      apply wp_break
      have hj : j = max B c := by omega
      subst hj
      exact hQ le' m' hbj harr' hu hk ho
  · rintro v tr e' le' m' hJ
    apply wp_skip
    simpa using hJ

end NautyVerified.Proofs.Refine
