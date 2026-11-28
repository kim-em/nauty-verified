import NautyVerified.Program.Env
import NautyVerified.Proofs.Permset.Take
import NautyVerified.Logic.Ints

/-!
# One word of `permset`

`Covers acc s perm D`: `acc` holds exactly the images `perm[u]` of the
members `u` of `s` with `D u`. `wp_word`: the loop over the set bits of word
`w0` of `set1` adds the images of that word's members to `set2`.
-/

namespace NautyVerified.Proofs.Permset

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (BitTable longs addW)
open NautyVerified.Proofs.Nextelement (LeadBit LeftbitTable)
open Hex.GraphIso.Nauty (VSet)

/-- `acc` holds the images of the members of `s` satisfying `D`. -/
def Covers {n : Nat} (acc s : VSet n) (perm : Array Nat) (D : Nat → Prop) : Prop :=
  ∀ t, acc.mem t = true ↔ ∃ u, D u ∧ s.mem u = true ∧ perm[u]! = t

theorem Covers.insert {n : Nat} {acc s : VSet n} {perm : Array Nat} {D : Nat → Prop}
    (h : Covers acc s perm D) {u0 : Nat} (hu0 : s.mem u0 = true) (hp : perm[u0]! < n)
    (D' : Nat → Prop) (hD' : ∀ u, D' u ↔ D u ∨ u = u0) :
    Covers (acc.insert perm[u0]!) s perm D' := by
  intro t
  rw [VSet.mem_insert_of_lt acc hp, Bool.or_eq_true, h t]
  constructor
  · rintro (⟨u, hu, hs, rfl⟩ | ht)
    · exact ⟨u, (hD' u).2 (.inl hu), hs, rfl⟩
    · refine ⟨u0, (hD' u0).2 (.inr rfl), hu0, ?_⟩
      simpa using ht
  · rintro ⟨u, hu, hs, rfl⟩
    rcases (hD' u).1 hu with hu | rfl
    · exact .inl ⟨u, hu, hs, rfl⟩
    · exact .inr (by simp)

theorem Covers.congr {n : Nat} {acc s : VSet n} {perm : Array Nat} {D D' : Nat → Prop}
    (h : Covers acc s perm D) (hD : ∀ u, s.mem u = true → (D u ↔ D' u)) : Covers acc s perm D' :=
  fun t => (h t).trans ⟨fun ⟨u, hu, hs, ht⟩ => ⟨u, (hD u hs).1 hu, hs, ht⟩,
    fun ⟨u, hu, hs, ht⟩ => ⟨u, (hD u hs).2 hu, hs, ht⟩⟩

theorem covers_empty {n : Nat} (s : VSet n) (perm : Array Nat) :
    Covers (VSet.empty : VSet n) s perm (fun u => u < 0) := fun t => by
  simp

/-- Covering every member is the image. -/
theorem covers_image {n : Nat} {acc s : VSet n} {perm : Array Nat}
    (h : Covers acc s perm (fun _ => True)) (hp : ∀ u < n, perm[u]! < n) :
    acc = s.permset perm := by
  apply VSet.ext
  intro t
  rw [VSet.permset, VSet.mem_image]
  cases hac : acc.mem t with
  | true =>
    obtain ⟨u, -, hs, rfl⟩ := (h t).1 hac
    have hu := VSet.mem_lt hs
    symm
    rw [List.any_eq_true]
    exact ⟨u, List.mem_range.2 hu, by simp [hs, hp u hu]⟩
  | false =>
    symm
    rw [List.any_eq_false]
    intro u hu hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    have := (h t).2 ⟨u, trivial, hc.1.1, hc.1.2⟩
    rw [hac] at this; cases this

variable {xi : ExternalCalls}

/-- What `permset` reads: `set1` (words `w1`, representing `s`) and `perm`. -/
structure Frame {n : Nat} (m : mem) (le : temp_env) (b1 : block) (o1 : ptrofs)
    (w1 : Nat → Lib.Integers.int64) (s : VSet n) (bp : block) (po : ptrofs) (perm : Array Nat)
    (b2 : block) (o2 : ptrofs) (M : Nat) : Prop where
  hset1 : PTree.get id.set1 le = some (.Vptr b1 o1)
  hset2 : PTree.get id.set2 le = some (.Vptr b2 o2)
  hperm : PTree.get id.perm le = some (.Vptr bp po)
  hm : PTree.get id.m le = some (.Vint (ir M))
  arr1 : ArrayAt m .Mint64 b1 (intOfZ (Ptrofs.unsigned o1)) (longs w1) M
  rep1 : SetRep (fun w => bv64 (w1 w)) M s
  parr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned po)) (ints perm) n
  psmall : ∀ u < n, perm[u]! < n
  lb : LeftbitTable m
  bit : BitTable m E.nautilBit
  Mlt : M < 33554432
  b21 : b2 ≠ b1
  b2p : b2 ≠ bp
  b2bit : b2 ≠ E.nautilBit
  b2lb : b2 ≠ E.leftbit

theorem Frame.temps {n : Nat} {m : mem} {le le' : temp_env} {b1 : block} {o1 : ptrofs}
    {w1 : Nat → Lib.Integers.int64} {s : VSet n} {bp : block} {po : ptrofs} {perm : Array Nat}
    {b2 : block} {o2 : ptrofs} {M : Nat} (h : Frame m le b1 o1 w1 s bp po perm b2 o2 M)
    (hle : ∀ y, y ≠ id.setw → y ≠ id.pos → y ≠ id.b → y ≠ id.w → y ≠ id.es → y ≠ id.t1 →
      y ≠ id.t2 → y ≠ id.t3 → PTree.get y le' = PTree.get y le) :
    Frame m le' b1 o1 w1 s bp po perm b2 o2 M :=
  { h with
    hset1 := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact h.hset1
    hset2 := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact h.hset2
    hperm := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact h.hperm
    hm := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact h.hm }

theorem Frame.unch {n : Nat} {m m' : mem} {le : temp_env} {b1 : block} {o1 : ptrofs}
    {w1 : Nat → Lib.Integers.int64} {s : VSet n} {bp : block} {po : ptrofs} {perm : Array Nat}
    {b2 : block} {o2 : ptrofs} {M : Nat} (h : Frame m le b1 o1 w1 s bp po perm b2 o2 M)
    (hu : Unch m m' (· = b2)) : Frame m' le b1 o1 w1 s bp po perm b2 o2 M :=
  { h with
    arr1 := h.arr1.unch hu (Ne.symm h.b21)
    parr := h.parr.unch hu (Ne.symm h.b2p)
    lb := fun i hi => by rw [hu.load _ _ _ (Ne.symm h.b2lb)]; exact h.lb i hi
    bit := h.bit.unch hu (Ne.symm h.b2bit) }

/-- The members of word `w0` still to take, while `setw` holds `x`. -/
def Done (w0 : Nat) (x : Lib.Integers.int64) (u : Nat) : Prop :=
  u < 64 * w0 ∨ (u / 64 = w0 ∧ (bv64 x).getMsbD (u % 64) = false)

theorem Done.clear {w0 k : Nat} {x : Lib.Integers.int64} (hk : LeadBit (bv64 x) k) (u : Nat) :
    Done w0 (clearBit x k) u ↔ Done w0 x u ∨ u = 64 * w0 + k := by
  have hk64 := hk.1
  have hmod := Nat.mod_lt u (show 64 > 0 by decide)
  simp only [Done, getMsbD_clearBit x hk64 hmod hk.2.1, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Decidable.not_not]
  constructor
  · rintro (h | ⟨h1, h2 | h2⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr ⟨h1, h2⟩)
    · exact .inr (by omega)
  · rintro ((h | ⟨h1, h2⟩) | rfl)
    · exact .inl h
    · exact .inr ⟨h1, .inl h2⟩
    · exact .inr ⟨by omega, .inr (by omega)⟩

theorem wp_word {Q : Post} {f : function} {le : temp_env} {m : mem} {n : Nat} {b1 : block}
    {o1 : ptrofs} {w1 : Nat → Lib.Integers.int64} {s : VSet n} {bp : block} {po : ptrofs}
    {perm : Array Nat} {b2 : block} {o2 : ptrofs} {M w0 : Nat}
    (h : Frame m le b1 o1 w1 s bp po perm b2 o2 M) (w2 : Nat → Lib.Integers.int64) (acc : VSet n)
    (harr2 : ArrayAt m .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2) M)
    (hrep2 : SetRep (fun w => bv64 (w2 w)) M acc) (hcov : Covers acc s perm (fun u => u < 64 * w0))
    (hw : PTree.get id.w le = some (.Vint (ir w0))) (hw0 : w0 < M)
    (hQ : ∀ le' m' w2' acc', ArrayAt m' .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2') M →
      SetRep (fun w => bv64 (w2' w)) M acc' → Covers acc' s perm (fun u => u < 64 * (w0 + 1)) →
      Unch m m' (· = b2) →
      Outside m m' b2 (intOfZ (Ptrofs.unsigned o2)) (intOfZ (Ptrofs.unsigned o2) + 8 * M) →
      (∀ y, y ≠ id.setw → y ≠ id.pos → y ≠ id.b → y ≠ id.t3 → PTree.get y le' = PTree.get y le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge f word Q empty_env le m := by
  have hMlt := h.Mlt
  have hnM := h.rep1.1
  have hmem : ∀ u, s.mem u = true → u / 64 = w0 → (bv64 (w1 w0)).getMsbD (u % 64) = true := by
    intro u hu hu0
    have hun := VSet.mem_lt hu
    rw [← h.rep1.2 u (by omega)] at hu
    simpa [SetwordsMem, hu0] using hu
  have hw1 := Set.eval_word (e := empty_env) h.arr1 (by omega) id.set1 h.hset1 (tv id.w) w0 hw0 hw rfl
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ x w2' acc', v = (bv64 x).toNat ∧ PTree.get id.setw le' = some (.Vlong x) ∧
      (∀ j < 64, (bv64 x).getMsbD j = true → (bv64 (w1 w0)).getMsbD j = true) ∧
      ArrayAt m' .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2') M ∧
      SetRep (fun w => bv64 (w2' w)) M acc' ∧ Covers acc' s perm (Done w0 x) ∧ Unch m m' (· = b2) ∧
      Outside m m' b2 (intOfZ (Ptrofs.unsigned o2)) (intOfZ (Ptrofs.unsigned o2) + 8 * M) ∧
      ∀ y, y ≠ id.setw → y ≠ id.pos → y ≠ id.b → y ≠ id.t3 → PTree.get y le' = PTree.get y le
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [hw1]
  refine wp_loop (I := I) (J := fun v t e' le' m' => ∃ v', v' < v ∧ I v' t e' le' m') ?_ ?_
    (n := (bv64 (w1 w0)).toNat)
    ⟨rfl, rfl, w1 w0, w2, acc, rfl, temps_gss _ _ _, fun _ _ h => h, harr2, hrep2,
      hcov.congr fun u hu => ⟨fun h => .inl h, fun h => by
        rcases h with h | ⟨h1, h2⟩
        · exact h
        · rw [hmem u hu h1] at h2; cases h2⟩, Unch.refl _ _, Outside.refl _ _ _ _,
      fun y h1 _ _ _ => temps_gso _ _ h1⟩
  · rintro v t e' le' m' ⟨rfl, rfl, x, w2', acc', rfl, hsw, hsub, harr', hrep', hcov', hu, hout, ho⟩
    have hf := (h.temps fun y h1 h2 h3 _ _ _ _ h8 => ho y h1 h2 h3 h8).unch hu
    have hw' : PTree.get id.w le' = some (.Vint (ir w0)) := by
      rw [ho _ (by decide) (by decide) (by decide) (by decide)]; exact hw
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge empty_env le' m' sw = _ from hsw]
    simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩, bv64_eq,
      show bv64 (lr 0) = 0 by simp [intOfZ_zOfInt]]
    by_cases hx : bv64 x = 0
    · rw [hx]
      simp only [decide_true, Bool.not_true, cop, Bool.false_eq_true, ite_false]
      apply wp_break
      refine hQ le' m' w2' acc' harr' hrep' (hcov'.congr fun u hu => ?_) hu hout ho
      simp only [Done, hx]
      simp only [show ∀ i, (0 : BitVec 64).getMsbD i = false from fun i => BitVec.getMsbD_zero, and_true]
      omega
    · rw [ite_eq_left (by simpa using hx)]
      apply wp_skip
      wp_step
      refine wp_takebit id.t3 (by decide) x hsw hx rfl rfl hf.lb hf.bit ?_
      intro k le1 hk hsw1 hb1 ho1
      have hk64 := hk.1
      let u0 := 64 * w0 + k
      have hu0s : s.mem u0 = true := by
        have hb := hsub k hk64 hk.2.1
        rw [← h.rep1.2 u0 (by omega)]
        simp only [SetwordsMem, u0]
        rw [show (64 * w0 + k) / 64 = w0 by omega, show (64 * w0 + k) % 64 = k by omega]
        exact hb
      have hu0n := VSet.mem_lt hu0s
      have hpu := h.psmall u0 hu0n
      have hw1' : PTree.get id.w le1 = some (.Vint (ir w0)) := by
        rw [ho1 _ (by decide) (by decide) (by decide)]; exact hw'
      have hidx : Exec.evalExpr ge empty_env le1 m'
          (.Ebinop .Oadd (.Ebinop .Oshl (tv id.w) (ci 6 tint) tint) (tv id.b) tint) =
          some (.Vint (ir (u0 : Int))) := by
        simp only [Exec.evalExpr, hw1', hb1, typeof, cop]
        rw [show Lib.Integers.Int.ltu (ir 6) Lib.Integers.Int.iwordsize = true by decide,
          ite_eq_left rfl]
        simp only [cop]
        rw [ir_shl6 (by omega) (by omega), ir_add]
        congr 3; simp only [u0]; push_cast; omega
      have hpe := eval_at (ge := ge) (e := empty_env) hf.parr (by omega) id.perm
        (by rw [ho1 _ (by decide) (by decide) (by decide)]; exact hf.hperm) _ u0 hu0n hidx rfl
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [hpe]
      simp only [ints]
      refine Set.wp_addElement' (s := id.set2) harr' (by omega)
        (by rw [temps_gso _ _ (by decide), ho1 _ (by decide) (by decide) (by decide)]; exact hf.hset2)
        (by simp only [Exec.evalExpr]; rw [temps_gss]) rfl (by omega) (by omega) hf.bit rfl ?_
      intro m3 harr3 hu3 hout3
      refine ⟨(bv64 (clearBit x k)).toNat, clearBit_lt x hk, rfl, rfl, clearBit x k, _, _, rfl,
        by rw [temps_gso _ _ (by decide)]; exact hsw1, fun j hj hb => ?_, harr3,
        Set.setRep_add hrep' hpu, hcov'.insert hu0s hpu _ (Done.clear hk), hu.trans hu3,
        hout.trans hout3, ?_⟩
      · rw [getMsbD_clearBit x hk64 hj hk.2.1] at hb
        simp only [Bool.and_eq_true] at hb
        exact hsub j hj hb.1
      · intro y h1 h2 h3 h4
        rw [temps_gso _ _ h2, ho1 y h4 h3 h1, ho y h1 h2 h3 h4]
  · rintro v t e' le' m' hJ
    apply wp_skip
    simpa using hJ

end NautyVerified.Proofs.Permset
