import NautyVerified.Proofs.Prune.LongSyntax

/-!
# One workspace pair in `longprune`

`wp_pair`: with `bottom` at word `o` of the workspace, where the pair
`(fx, mc)` is stored (`fx` at `o`, `mc` at `o + M`), one pass of
`longprune`'s loop intersects `tcell` with `mc` when the fixed points lie in
`fx`, as HexGraphIso's `longprune` step does, and leaves `bottom` at `o + 2M`.
-/

namespace NautyVerified.Proofs.Prune.Long

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set
open Hex.GraphIso.Nauty (VSet)

variable {xi : ExternalCalls}

/-- Words `o .. o + len - 1` of an array, through a pointer to word `o`. -/
theorem slice_at {m : mem} {b : block} {base : Int} {ws : Nat → Lib.Integers.int64} {W : Nat}
    (h : ArrayAt m .Mint64 b base (longs ws) W) (o len : Nat) (hle : o + len ≤ W) :
    ArrayAt m .Mint64 b (intOfZ (Ptrofs.unsigned (ptrTo base 8 o))) (longs fun i => ws (o + i)) len := by
  have hf := h.fits
  have hb := h.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf
  rw [unsigned_ptrTo (by omega) (by omega)]
  have := h.slice o len hle
  rw [h8] at this
  exact this

theorem add_ptrTo8 (ce : Cfrontend.Ctypes.composite_env) (base : Int) (k j : Nat)
    (hj : (j : Int) < 2147483648) :
    Ptrofs.add (ptrTo base 8 k) (Ptrofs.mul (Ptrofs.repr (Cfrontend.Ctypes.sizeof ce tulong))
      (Ptrofs.of_ints (ir j))) = ptrTo base 8 (k + j) := by
  have h : intOfZ (Cfrontend.Ctypes.sizeof ce tulong) = 8 := rfl
  have := add_ptrTo_ptrTo base (Cfrontend.Ctypes.sizeof ce tulong) k j hj
  rw [h] at this
  exact this

theorem cmplu_lt_ptrTo {m : mem} {b : block} {base : Int} {vals : Nat → val} {W : Nat}
    (h : ArrayAt m .Mint64 b base vals W) (hW : 0 < W) {k K : Nat} (hk : k ≤ W) (hK : K ≤ W) :
    Val.cmplu_bool (Mem.valid_pointer m) .Clt (.Vptr b (ptrTo base 8 k)) (.Vptr b (ptrTo base 8 K)) =
      some (decide (k < K)) := by
  have hf := h.fits
  have hb := h.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf
  have hu : ∀ j, j ≤ W → intOfZ (Ptrofs.unsigned (ptrTo base 8 j)) = base + 8 * j := fun j hj => by
    apply unsigned_ptrTo <;> omega
  have hz : ∀ j, j ≤ W → Ptrofs.unsigned (ptrTo base 8 j) = zOfInt (base + 8 * j) := fun j hj => by
    rw [← hu j hj, zOfInt_intOfZ]
  rw [cmplu_same _ _ _ _ _ (by rw [hz k hk]; exact h.weak_valid hW (by omega) (by rw [h8]; omega))
    (by rw [hz K hK]; exact h.weak_valid hW (by omega) (by rw [h8]; omega)), cmpu_lt]
  congr 1
  have e1 := hu k hk
  have e2 := hu K hK
  rw [intOfZ_Ptrofs_unsigned] at e1 e2
  apply decide_eq_decide.2
  omega

theorem wp_advance {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bw : block}
    {wb : Int} {k M : Nat} (hM : M < 2147483648)
    (hbot : PTree.get id.bottom le = some (.Vptr bw (ptrTo wb 8 k)))
    (hm : PTree.get id.m le = some (.Vint (ir M)))
    (hQ : Q.normal E0 e (PTree.set id.bottom (.Vptr bw (ptrTo wb 8 (k + M))) le) m) :
    Wp xi ge f advance Q e le m := by
  wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hbot, hm, typeof, cop]
  rw [add_ptrTo8 _ _ _ _ (by omega)]
  exact hQ

/-- What `longprune` reads throughout: `tcell`, the fixed points `fix`
(words `wf`, representing `F`) and the workspace (words `ww`). -/
structure LFrame {n : Nat} (m : mem) (le : temp_env) (bt : block) (tofs : ptrofs) (bf : block)
    (fofs : ptrofs) (bw : block) (wb : Int) (ww : Nat → Lib.Integers.int64) (W M : Nat)
    (wf : Nat → Lib.Integers.int64) (F : VSet n) : Prop where
  htcell : PTree.get id.tcell le = some (.Vptr bt tofs)
  hfix : PTree.get id.fix le = some (.Vptr bf fofs)
  hm : PTree.get id.m le = some (.Vint (ir M))
  farr : ArrayAt m .Mint64 bf (intOfZ (Ptrofs.unsigned fofs)) (longs wf) M
  frep : SetRep (fun w => bv64 (wf w)) M F
  warr : ArrayAt m .Mint64 bw wb (longs ww) W
  Mlt : M < 2147483648
  tf : bt ≠ bf
  tw : bt ≠ bw

theorem LFrame.temps {n : Nat} {m : mem} {le le' : temp_env} {bt : block} {tofs : ptrofs}
    {bf : block} {fofs : ptrofs} {bw : block} {wb : Int} {ww : Nat → Lib.Integers.int64}
    {W M : Nat} {wf : Nat → Lib.Integers.int64} {F : VSet n}
    (h : LFrame m le bt tofs bf fofs bw wb ww W M wf F)
    (hle : ∀ k, k ≠ id.i → k ≠ id.bottom → PTree.get k le' = PTree.get k le) :
    LFrame m le' bt tofs bf fofs bw wb ww W M wf F :=
  { h with
    htcell := by rw [hle _ (by decide) (by decide)]; exact h.htcell
    hfix := by rw [hle _ (by decide) (by decide)]; exact h.hfix
    hm := by rw [hle _ (by decide) (by decide)]; exact h.hm }

theorem LFrame.unch {n : Nat} {m m' : mem} {le : temp_env} {bt : block} {tofs : ptrofs}
    {bf : block} {fofs : ptrofs} {bw : block} {wb : Int} {ww : Nat → Lib.Integers.int64}
    {W M : Nat} {wf : Nat → Lib.Integers.int64} {F : VSet n}
    (h : LFrame m le bt tofs bf fofs bw wb ww W M wf F) (hu : Unch m m' (· = bt)) :
    LFrame m' le bt tofs bf fofs bw wb ww W M wf F :=
  { h with farr := h.farr.unch hu (Ne.symm h.tf), warr := h.warr.unch hu (Ne.symm h.tw) }

theorem wp_pair {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {bt : block} {tofs : ptrofs} {bf : block} {fofs : ptrofs} {bw : block} {wb : Int}
    {ww : Nat → Lib.Integers.int64} {W M o : Nat} {wf wt : Nat → Lib.Integers.int64}
    {F T fx mc : VSet n}
    (h : LFrame m le bt tofs bf fofs bw wb ww W M wf F)
    (htarr : ArrayAt m .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) (longs wt) M)
    (htrep : SetRep (fun w => bv64 (wt w)) M T) (ho : o + M + M ≤ W)
    (hbot : PTree.get id.bottom le = some (.Vptr bw (ptrTo wb 8 o)))
    (hfx : SetRep (fun w => bv64 (ww (o + w))) M fx)
    (hmc : SetRep (fun w => bv64 (ww (o + M + w))) M mc)
    (hQ : ∀ le' m' wt', PTree.get id.bottom le' = some (.Vptr bw (ptrTo wb 8 (o + M + M))) →
      ArrayAt m' .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) (longs wt') M →
      SetRep (fun w => bv64 (wt' w)) M (if F.subset fx then T.inter mc else T) →
      Unch m m' (· = bt) →
      (∀ k, k ≠ id.i → k ≠ id.bottom → PTree.get k le' = PTree.get k le) →
      Q.normal E0 e le' m') :
    Wp xi ge f pair Q e le m := by
  have hM := h.Mlt
  wp_step
  refine wp_subsetLoop h.farr (slice_at h.warr o M (by omega)) h.Mlt h.hfix hbot h.hm
    (by decide) (by decide) (by decide) ?_
  intro le1 r hr hi1 hiff ho1
  have hsub : r = M ↔ F.subset fx = true := hiff.trans (setRep_subset h.frep hfx)
  have h1 := h.temps fun k h1 _ => ho1 k h1
  wp_step
  refine wp_advance hM (by rw [ho1 _ (by decide)]; exact hbot) h1.hm ?_
  let le2 := PTree.set id.bottom (.Vptr bw (ptrTo wb 8 (o + M))) le1
  have ho2 : ∀ k, k ≠ id.i → k ≠ id.bottom → PTree.get k le2 = PTree.get k le := fun k h1 h2 => by
    simp only [le2]; rw [temps_gso _ _ h2, ho1 k h1]
  have h2 := h.temps ho2
  have hi2 : PTree.get id.i le2 = some (.Vint (ir r)) := by
    simp only [le2]; rw [temps_gso _ _ (by decide)]; exact hi1
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, show Exec.evalExpr ge e le2 m (.Etempvar id.i tint) = _ from hi2,
    show Exec.evalExpr ge e le2 m (.Etempvar id.m tint) = _ from h2.hm]
  simp only [typeof, cop]
  rw [ir_eq (a := (r : Int)) (b := (M : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hrM : r = M
  · rw [ite_eq_left (by simp; omega)]
    have hs := hsub.1 hrM
    refine wp_interLoop htarr (slice_at h.warr (o + M) M (by omega)) (Ne.symm h.tw) hM h2.htcell
      (temps_gss _ _ _) h2.hm (by decide) (by decide) (by decide) ?_
    intro le3 m3 harr3 hu3 ho3
    refine wp_advance hM (by rw [ho3 _ (by decide)]; exact temps_gss _ _ _)
      (by rw [ho3 _ (by decide)]; exact h2.hm) ?_
    refine hQ _ m3 _ (temps_gss _ _ _) harr3 ?_ hu3 ?_
    · rw [ite_eq_left hs]; exact setRep_andW htrep hmc
    · intro k h1 h2'
      rw [temps_gso _ _ h2', ho3 k h1, ho2 k h1 h2']
  · rw [ite_eq_right (by simp; omega)]
    apply wp_skip
    refine wp_advance hM (temps_gss _ _ _) h2.hm ?_
    refine hQ _ m wt (temps_gss _ _ _) htarr ?_ (Unch.refl _ _) ?_
    · rw [ite_eq_right (fun hs => hrM (hsub.2 hs))]; exact htrep
    · intro k h1 h2'
      rw [temps_gso _ _ h2', ho2 k h1 h2']

end NautyVerified.Proofs.Prune.Long
