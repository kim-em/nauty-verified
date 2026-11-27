import NautyVerified.Proofs.Permset.Many

/-!
# The one-word case of `permset`

`wp_one`: for `m = 1`, `*set2 = 0;` followed by the loop over the set bits
of `set1[0]`, each adding `bit[perm[b]]` to `*set2`, leaves `set2`
representing HexGraphIso's `s.permset perm`.
-/

namespace NautyVerified.Proofs.Permset

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (BitTable longs addW)
open NautyVerified.Proofs.Nextelement (LeadBit)
open Hex.GraphIso.Nauty (VSet)

variable {xi : ExternalCalls}

theorem unsigned_elem0 (o : ptrofs) :
    Ptrofs.unsigned o = elemOfs .Mint64 (intOfZ (Ptrofs.unsigned o)) 0 := by
  unfold elemOfs
  rw [show csize .Mint64 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ]

/-- `*set2 = *set2 | bit[a]` for `a` holding `p < 64`. -/
theorem wp_orWord0 {f : function} {Q : Post} {le : temp_env} {m : mem} {b2 : block} {o2 : ptrofs}
    {w2 : Nat → Lib.Integers.int64} (harr : ArrayAt m .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2) 1)
    (hs : PTree.get id.set2 le = some (.Vptr b2 o2)) (hbit : BitTable m Block.nautilBit)
    (a : expr) (p : Nat) (hp : p < 64) (ha : Exec.evalExpr ge empty_env le m a = some (.Vint (ir p)))
    (hty : typeof a = tint)
    (hQ : ∀ m', ArrayAt m' .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs (addW w2 p)) 1 →
      Unch m m' (· = b2) →
      Outside m m' b2 (intOfZ (Ptrofs.unsigned o2)) (intOfZ (Ptrofs.unsigned o2) + 8 * 1) →
      Q.normal E0 empty_env le m') :
    Wp xi ge f (.Sassign (.Ederef (Set.pv id.set2) tulong)
      (.Ebinop .Oor (.Ederef (Set.pv id.set2) tulong) (bitAt a) tulong)) Q empty_env le m := by
  have hl : Mem.load .Mint64 m b2 (Ptrofs.unsigned o2) = some (longs w2 0) := by
    rw [unsigned_elem0]; exact harr.load 0 (by decide)
  have hb := eval_bitAt hbit rfl a p hp ha hty
  obtain ⟨m', hst, harr', -⟩ := store_array harr (show 0 < 1 by decide)
    (.Vlong (Lib.Integers.Int64.or (w2 0) (lr ((2 ^ (63 - p) : Nat) : Int)))) rfl
  have hd : Exec.evalExpr ge empty_env le m (.Ederef (Set.pv id.set2) tulong) = some (.Vlong (w2 0)) := by
    simp only [Exec.evalExpr, hs, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, hl, longs]
  have hor : Exec.evalExpr ge empty_env le m (.Ebinop .Oor (.Ederef (Set.pv id.set2) tulong) (bitAt a) tulong) =
      some (.Vlong (Lib.Integers.Int64.or (w2 0) (lr ((2 ^ (63 - p) : Nat) : Int)))) := by
    rw [Exec.evalExpr, hd, hb]; simp only [typeof, cop]
  apply wp_assign_eval
  rw [hor]
  simp only [Exec.evalLvalue, Exec.evalExpr, hs, typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode,
    Mem.storev]
  rw [unsigned_elem0, hst]
  apply hQ m' _ (Unch.store hst rfl) (Outside.store harr (show 0 < 1 by decide) hst (Int.le_refl _)
    (by rw [show csize .Mint64 = 8 from rfl]; exact Int.le_refl _))
  rw [Set.longs_upd] at harr'
  have : addW w2 p = upd w2 0 (Lib.Integers.Int64.or (w2 0) (lr ((2 ^ (63 - p) : Nat) : Int))) := by
    simp only [addW, show p / 64 = 0 by omega, show p % 64 = p by omega]
  rw [this]; exact harr'

theorem wp_one {Q : Post} {f : function} {le : temp_env} {m : mem} {n : Nat} {b1 : block}
    {o1 : ptrofs} {w1 : Nat → Lib.Integers.int64} {s : VSet n} {bp : block} {po : ptrofs}
    {perm : Array Nat} {b2 : block} {o2 : ptrofs} {w2 : Nat → Lib.Integers.int64}
    (h : Frame m le b1 o1 w1 s bp po perm b2 o2 1)
    (harr2 : ArrayAt m .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2) 1)
    (hQ : ∀ le' m' w2', ArrayAt m' .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2') 1 →
      SetRep (fun w => bv64 (w2' w)) 1 (s.permset perm) → Unch m m' (· = b2) →
      Outside m m' b2 (intOfZ (Ptrofs.unsigned o2)) (intOfZ (Ptrofs.unsigned o2) + 8 * 1) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge f one Q empty_env le m := by
  have hnM := h.rep1.1
  have hmem : ∀ u, s.mem u = true → (bv64 (w1 0)).getMsbD (u % 64) = true := by
    intro u hu
    have hun := VSet.mem_lt hu
    rw [← h.rep1.2 u (by omega)] at hu
    simpa [SetwordsMem, show u / 64 = 0 by omega] using hu
  -- `*set2 = 0;`
  obtain ⟨m0, hst0, harr0, -⟩ := store_array harr2 (show 0 < 1 by decide) (.Vlong (lr 0)) rfl
  wp_step; wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, h.hset2, typeof, cop, Exec.assignLoc,
    Cfrontend.Ctypes.access_mode, Mem.storev, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
  rw [unsigned_elem0, hst0]
  have hu0 : Unch m m0 (· = b2) := Unch.store hst0 rfl
  have hout0 : Outside m m0 b2 (intOfZ (Ptrofs.unsigned o2)) (intOfZ (Ptrofs.unsigned o2) + 8 * 1) :=
    Outside.store harr2 (show 0 < 1 by decide) hst0 (Int.le_refl _)
      (by rw [show csize .Mint64 = 8 from rfl]; exact Int.le_refl _)
  have harr0' : ArrayAt m0 .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs fun _ => lr 0) 1 :=
    harr0.congr fun i hi => by simp [upd, longs, show i = 0 by omega]
  have hf0 := h.unch hu0
  have hw1 := Set.eval_word (e := empty_env) hf0.arr1 (by decide) id.set1 hf0.hset1 (ci 0 tint) 0
    (by decide) rfl rfl
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ x w2' acc', v = (bv64 x).toNat ∧ PTree.get id.setw le' = some (.Vlong x) ∧
      (∀ j < 64, (bv64 x).getMsbD j = true → (bv64 (w1 0)).getMsbD j = true) ∧
      ArrayAt m' .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2') 1 ∧
      SetRep (fun w => bv64 (w2' w)) 1 acc' ∧ Covers acc' s perm (Done 0 x) ∧ Unch m m' (· = b2) ∧
      Outside m m' b2 (intOfZ (Ptrofs.unsigned o2)) (intOfZ (Ptrofs.unsigned o2) + 8 * 1) ∧
      ∀ y, y ≠ id.setw → y ≠ id.b → y ≠ id.t1 → PTree.get y le' = PTree.get y le
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [hw1]
  refine wp_loop (I := I) (J := fun v t e' le' m' => ∃ v', v' < v ∧ I v' t e' le' m') ?_ ?_
    (n := (bv64 (w1 0)).toNat)
    ⟨rfl, rfl, w1 0, _, VSet.empty, rfl, temps_gss _ _ _, fun _ _ h => h, harr0',
      Set.setRep_zero hnM, fun t => ⟨fun h => by simp at h, fun ⟨u, hu, hs, _⟩ => by
        rcases hu with hu | ⟨_, h2⟩
        · omega
        · rw [hmem u hs] at h2; cases h2⟩, hu0, hout0, fun y h1 _ _ => temps_gso _ _ h1⟩
  · rintro v t e' le' m' ⟨rfl, rfl, x, w2', acc', rfl, hsw, hsub, harr', hrep', hcov', hu, hout, ho⟩
    have hf := (h.temps fun y h1 _ h3 _ _ h6 _ _ => ho y h1 h3 h6).unch hu
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge empty_env le' m' sw = _ from hsw]
    simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩, bv64_eq,
      show bv64 (lr 0) = 0 by simp [intOfZ_zOfInt]]
    by_cases hx : bv64 x = 0
    · rw [hx]
      simp only [decide_true, Bool.not_true, cop, Bool.false_eq_true, ite_false]
      apply wp_break
      refine hQ le' m' w2' harr' ?_ hu hout
      rw [← covers_image (hcov'.congr fun u hu => ⟨fun _ => trivial, fun _ => by
        have := VSet.mem_lt hu
        simp only [Done, hx]
        simp only [show ∀ i, (0 : BitVec 64).getMsbD i = false from fun i => BitVec.getMsbD_zero, and_true]
        omega⟩) h.psmall]
      exact hrep'
    · rw [ite_eq_left (by simpa using hx)]
      apply wp_skip
      wp_step
      refine wp_takebit id.t1 (by decide) x hsw hx rfl rfl hf.lb hf.bit ?_
      intro k le1 hk hsw1 hb1 ho1
      have hk64 := hk.1
      have hu0s : s.mem k = true := by
        have hb := hsub k hk64 hk.2.1
        rw [← h.rep1.2 k (by omega)]
        simp only [SetwordsMem]
        rw [show k / 64 = 0 by omega, show k % 64 = k by omega]
        exact hb
      have hu0n := VSet.mem_lt hu0s
      have hpu := h.psmall k hu0n
      have hpe := eval_at (ge := ge) (e := empty_env) hf.parr (by omega) id.perm
        (by rw [ho1 _ (by decide) (by decide) (by decide)]; exact hf.hperm) (tv id.b) k hu0n hb1 rfl
      wp_step; wp_step
      refine wp_orWord0 harr' (by rw [ho1 _ (by decide) (by decide) (by decide)]; exact hf.hset2) hf.bit
        _ perm[k]! (by omega) (by rw [hpe]; rfl) rfl ?_
      intro m3 harr3 hu3 hout3
      refine ⟨(bv64 (clearBit x k)).toNat, clearBit_lt x hk, rfl, rfl, clearBit x k, _, _, rfl,
        hsw1, fun j hj hb => ?_, harr3, Set.setRep_add hrep' hpu,
        hcov'.insert hu0s hpu _ (fun u => by simpa using Done.clear (w0 := 0) hk u),
        hu.trans hu3, hout.trans hout3, ?_⟩
      · rw [getMsbD_clearBit x hk64 hj hk.2.1] at hb
        simp only [Bool.and_eq_true] at hb
        exact hsub j hj hb.1
      · intro y h1 h2 h3
        rw [ho1 y h3 h2 h1, ho y h1 h2 h3]
  · rintro v t e' le' m' hJ
    apply wp_skip
    simpa using hJ

end NautyVerified.Proofs.Permset
