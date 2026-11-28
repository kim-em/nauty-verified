import NautyVerified.Program.Env
import NautyVerified.Proofs.Alloc.KeepV
import NautyVerified.Proofs.Fmptn.Scan
import NautyVerified.Logic.Rest

/-!
# The cells of `fmptn`

`wp_single` and `wp_cell`: one iteration of `fmptn`'s loop at the start `c` of
a cell adds, as HexGraphIso's `cellStep`, the vertex of a trivial cell to
`fix` and `mcr`, or the least vertex of a nontrivial cell to `mcr`.
-/

namespace NautyVerified.Proofs.Fmptn

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (longs addW BitTable)
open Hex.GraphIso.Nauty (VSet fmptn cells cellEnd)

variable {xi : ExternalCalls}

/-- The two result sets, `fix` (words `wf`, representing `fx`) and `mcr`
(words `wm`, representing `mc`), in their blocks, with the `bit` table. -/
structure Sets (m : mem) (le : temp_env) (bf : block) (fofs : ptrofs) (bm : block)
    (mofs : ptrofs) (n M : Nat) (wf wm : Nat → Lib.Integers.int64) (fx mc : VSet n) : Prop where
  hfix : PTree.get id.fix le = some (.Vptr bf fofs)
  hmcr : PTree.get id.mcr le = some (.Vptr bm mofs)
  farr : ArrayAt m .Mint64 bf (intOfZ (Ptrofs.unsigned fofs)) (longs wf) M
  marr : ArrayAt m .Mint64 bm (intOfZ (Ptrofs.unsigned mofs)) (longs wm) M
  frep : SetRep (fun w => bv64 (wf w)) M fx
  mrep : SetRep (fun w => bv64 (wm w)) M mc
  bit : BitTable m E.nautilBit
  Mlt : M < 2147483648
  nM : n ≤ 64 * M

/-- The blocks of `fmptn`'s arrays are distinct, except that `fix` and `mcr` may
share one (`Apart`). -/
structure Disjoint (bl bp bf bm : block) : Prop where
  fl : bf ≠ bl
  fp : bf ≠ bp
  ml : bm ≠ bl
  mp : bm ≠ bp
  bf : E.nautilBit ≠ bf
  bm : E.nautilBit ≠ bm

theorem Sets.temps {m : mem} {le le' : temp_env} {bf : block} {fofs : ptrofs} {bm : block}
    {mofs : ptrofs} {n M : Nat} {wf wm : Nat → Lib.Integers.int64} {fx mc : VSet n}
    (h : Sets m le bf fofs bm mofs n M wf wm fx mc)
    (hle : ∀ k, k ≠ id.i → k ≠ id.lmin → k ≠ id.t3 → k ≠ id.es → k ≠ id.es1 → k ≠ id.t1 →
      k ≠ id.t2 → PTree.get k le' = PTree.get k le) :
    Sets m le' bf fofs bm mofs n M wf wm fx mc :=
  { h with
    hfix := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.hfix
    hmcr := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.hmcr }

theorem wp_single {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bl : block}
    {lofs : ptrofs} {bp : block} {pofs : ptrofs} {bf : block} {fofs : ptrofs} {bm : block}
    {mofs : ptrofs} {lab ptn : Array Nat} {n level M c : Nat} {wf wm : Nat → Lib.Integers.int64}
    {fx mc : VSet n}
    (h : Frame m le bl lofs bp pofs lab ptn n level) (hs : Sets m le bf fofs bm mofs n M wf wm fx mc)
    (hd : Disjoint bl bp bf bm)
    (hfm : Apart bf (intOfZ (Ptrofs.unsigned fofs)) bm (intOfZ (Ptrofs.unsigned mofs)) M)
    (he : PTree.get Set.bit e = none) (hc : c < n)
    (hi : PTree.get id.i le = some (.Vint (ir c)))
    (hQ : ∀ m', Frame m' le bl lofs bp pofs lab ptn n level →
      Sets m' le bf fofs bm mofs n M (addW wf lab[c]!) (addW wm lab[c]!)
        (fx.insert lab[c]!) (mc.insert lab[c]!) →
      Unch m m' (fun b => b = bf ∨ b = bm) →
      Rest m m' bf (intOfZ (Ptrofs.unsigned fofs)) bm (intOfZ (Ptrofs.unsigned mofs)) M →
      Alloc.KeepA m m' → Q.normal E0 e le m') :
    Wp xi ge f single Q e le m := by
  have hlc := h.lsmall c hc
  have hn := h.nlt
  have hnM := hs.nM
  have hev : ∀ m', Frame m' le bl lofs bp pofs lab ptn n level →
      Exec.evalExpr ge e le m' (at_ id.lab (tv id.i)) = some (.Vint (ir (lab[c]! : Int))) :=
    fun m' hf => eval_at hf.larr hf.nlt id.lab hf.hlab (tv id.i) c hc hi rfl
  wp_step
  refine Set.wp_addElement' hs.farr hs.Mlt hs.hfix (hev m h) rfl (by omega) (by omega) hs.bit he ?_
  intro m1 harr1 hu1 hO1
  have hf1 := h.unch hu1 (Ne.symm hd.fl) (Ne.symm hd.fp)
  refine Set.wp_addElement' (hs.marr.acrossF hu1 hO1 hfm) hs.Mlt hs.hmcr (hev m1 hf1) rfl
    (by omega) (by omega) (hs.bit.unch hu1 hd.bf) he ?_
  intro m2 harr2 hu2 hO2
  apply hQ m2 (hf1.unch hu2 (Ne.symm hd.ml) (Ne.symm hd.mp))
    ⟨hs.hfix, hs.hmcr, harr1.acrossM hu2 hO2 hfm, harr2, Set.setRep_add hs.frep hlc,
      Set.setRep_add hs.mrep hlc, (hs.bit.unch hu1 hd.bf).unch hu2 hd.bm, hs.Mlt, hs.nM⟩
  · exact (hu1.mono fun b hb => .inl hb).trans (hu2.mono fun b hb => .inr hb)
  · exact (Rest.fix hu1 hO1).trans (Rest.mcr hu2 hO2)
  · exact (Alloc.KeepA.of_outside hu1 hO1 hs.farr.base_nonneg).trans
      (Alloc.KeepA.of_outside hu2 hO2 (hs.marr.acrossF hu1 hO1 hfm).base_nonneg)

theorem wp_cell {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bl : block}
    {lofs : ptrofs} {bp : block} {pofs : ptrofs} {bf : block} {fofs : ptrofs} {bm : block}
    {mofs : ptrofs} {lab ptn : Array Nat} {n level M c c2 : Nat} {wf wm : Nat → Lib.Integers.int64}
    {fx mc : VSet n}
    (h : Frame m le bl lofs bp pofs lab ptn n level) (hs : Sets m le bf fofs bm mofs n M wf wm fx mc)
    (hd : Disjoint bl bp bf bm)
    (hfm : Apart bf (intOfZ (Ptrofs.unsigned fofs)) bm (intOfZ (Ptrofs.unsigned mofs)) M)
    (he : PTree.get Set.bit e = none) (hc : c < c2) (hc2 : c2 < n)
    (hend : ptn[c2]! ≤ level) (hgt : ∀ k, c ≤ k → k < c2 → level < ptn[k]!)
    (hi : PTree.get id.i le = some (.Vint (ir c)))
    (hQ : ∀ le' m', PTree.get id.i le' = some (.Vint (ir c2)) →
      Frame m' le' bl lofs bp pofs lab ptn n level →
      Sets m' le' bf fofs bm mofs n M wf (addW wm (scanMin lab (List.range' (c + 1) (c2 - c)) lab[c]!))
        fx (mc.insert (scanMin lab (List.range' (c + 1) (c2 - c)) lab[c]!)) →
      Unch m m' (fun b => b = bf ∨ b = bm) →
      Rest m m' bf (intOfZ (Ptrofs.unsigned fofs)) bm (intOfZ (Ptrofs.unsigned mofs)) M →
      Alloc.KeepA m m' →
      (∀ k, k ≠ id.i → k ≠ id.lmin → k ≠ id.t3 → PTree.get k le' = PTree.get k le) →
      Q.normal E0 e le' m') :
    Wp xi ge f cell Q e le m := by
  have hn := h.nlt
  have hnM := hs.nM
  have hlc := eval_at (ge := ge) (e := e) h.larr h.nlt id.lab h.hlab (tv id.i) c (by omega) hi rfl
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [hlc]
  simp only [ints]
  let le1 := PTree.set id.lmin (.Vint (ir (lab[c]! : Int))) le
  have ho1 : ∀ k, k ≠ id.lmin → PTree.get k le1 = PTree.get k le := fun k hk => temps_gso _ _ hk
  have hf1 : Frame m le1 bl lofs bp pofs lab ptn n level :=
    h.temps fun k _ h2 _ _ _ _ _ => ho1 k h2
  wp_step
  refine wp_scan hf1 hc hc2 hend hgt (by rw [ho1 _ (by decide)]; exact hi) (temps_gss _ _ _) ?_
  intro le2 hi2 hl2 ho2
  have hs2 : Sets m le2 bf fofs bm mofs n M wf wm fx mc :=
    hs.temps fun k h1 h2 h3 _ _ _ _ => by rw [ho2 k h1 h2 h3, ho1 k h2]
  have hf2 : Frame m le2 bl lofs bp pofs lab ptn n level :=
    h.temps fun k h1 h2 h3 _ _ _ _ => by rw [ho2 k h1 h2 h3, ho1 k h2]
  have hsm := scanMin_lt (lab := lab) (B := n) (List.range' (c + 1) (c2 - c)) lab[c]!
    (fun x hx => h.lsmall x (by simp [List.mem_range'] at hx; omega)) (h.lsmall c (by omega))
  refine Set.wp_addElement' hs2.marr hs2.Mlt hs2.hmcr hl2 rfl (by omega) (by omega) hs2.bit he ?_
  intro m3 harr3 hu3 hO3
  refine hQ le2 m3 hi2 (hf2.unch hu3 (Ne.symm hd.ml) (Ne.symm hd.mp))
    ⟨hs2.hfix, hs2.hmcr, hs2.farr.acrossM hu3 hO3 hfm, harr3, hs2.frep, Set.setRep_add hs2.mrep hsm,
      hs2.bit.unch hu3 hd.bm, hs2.Mlt, hs2.nM⟩ (hu3.mono fun b hb => .inr hb) (Rest.mcr hu3 hO3)
    (Alloc.KeepA.of_outside hu3 hO3 hs2.marr.base_nonneg) ?_
  intro k h1 h2 h3
  rw [ho2 k h1 h2 h3, ho1 k h2]

theorem wp_loop_fmptn {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bl : block}
    {lofs : ptrofs} {bp : block} {pofs : ptrofs} {bf : block} {fofs : ptrofs} {bm : block}
    {mofs : ptrofs} {lab ptn : Array Nat} {n level M : Nat} {wf wm : Nat → Lib.Integers.int64}
    (h : Frame m le bl lofs bp pofs lab ptn n level)
    (hs : Sets m le bf fofs bm mofs n M wf wm VSet.empty VSet.empty)
    (hd : Disjoint bl bp bf bm)
    (hfm : Apart bf (intOfZ (Ptrofs.unsigned fofs)) bm (intOfZ (Ptrofs.unsigned mofs)) M)
    (he : PTree.get Set.bit e = none) (hsize : ptn.size = n)
    (hlast : ptn[n - 1]! ≤ level) (hi : PTree.get id.i le = some (.Vint (ir 0)))
    (hQ : ∀ le' m' wf' wm', Frame m' le' bl lofs bp pofs lab ptn n level →
      Sets m' le' bf fofs bm mofs n M wf' wm' (fmptn lab ptn level n).1 (fmptn lab ptn level n).2 →
      Unch m m' (fun b => b = bf ∨ b = bm) →
      Rest m m' bf (intOfZ (Ptrofs.unsigned fofs)) bm (intOfZ (Ptrofs.unsigned mofs)) M →
      Alloc.KeepA m m' →
      (∀ k, k ≠ id.i → k ≠ id.lmin → k ≠ id.t3 → PTree.get k le' = PTree.get k le) →
      Q.normal E0 e le' m') :
    Wp xi ge f loop Q e le m := by
  let R : VSet n × VSet n := (cells ptn level n).foldl (cellStep lab) (VSet.empty, VSet.empty)
  have hR : fmptn lab ptn level n = R := fmptn_eq lab ptn level n
  have hn := h.nlt
  let Oth := fun le' : temp_env =>
    ∀ k, k ≠ id.i → k ≠ id.lmin → k ≠ id.t3 → PTree.get k le' = PTree.get k le
  refine wp_loop
    (I := fun v t e' le' m' => t = E0 ∧ e = e' ∧ ∃ c wf wm fx mc F, c ≤ n ∧ v = n - c ∧
      n - c ≤ F ∧ (cells.go ptn level n F c).foldl (cellStep lab) (fx, mc) = R ∧
      PTree.get id.i le' = some (.Vint (ir c)) ∧ Frame m' le' bl lofs bp pofs lab ptn n level ∧
      Sets m' le' bf fofs bm mofs n M wf wm fx mc ∧ Unch m m' (fun b => b = bf ∨ b = bm) ∧
      Rest m m' bf (intOfZ (Ptrofs.unsigned fofs)) bm (intOfZ (Ptrofs.unsigned mofs)) M ∧
      Alloc.KeepA m m' ∧ Oth le')
    (J := fun v t e' le' m' => t = E0 ∧ e = e' ∧ ∃ c c2 wf wm fx mc F, c ≤ c2 ∧ c2 < n ∧
      v = n - c ∧ n - (c2 + 1) ≤ F ∧
      (cells.go ptn level n F (c2 + 1)).foldl (cellStep lab) (fx, mc) = R ∧
      PTree.get id.i le' = some (.Vint (ir c2)) ∧ Frame m' le' bl lofs bp pofs lab ptn n level ∧
      Sets m' le' bf fofs bm mofs n M wf wm fx mc ∧ Unch m m' (fun b => b = bf ∨ b = bm) ∧
      Rest m m' bf (intOfZ (Ptrofs.unsigned fofs)) bm (intOfZ (Ptrofs.unsigned mofs)) M ∧
      Alloc.KeepA m m' ∧ Oth le')
    ?_ ?_ (n := n - 0)
    ⟨rfl, rfl, 0, wf, wm, _, _, n, Nat.zero_le _, rfl, by omega, rfl, hi, h, hs, Unch.refl _ _,
      Rest.refl _ _ _ _ _ _, Alloc.KeepA.refl _, fun _ _ _ _ => rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, c, wf, wm, fx, mc, F, hcn, rfl, hF, hfold, hic, hf, hs', hu, hr, hk, ho⟩
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge e le' m' (tv id.i) = _ from hic,
      show Exec.evalExpr ge e le' m' (tv id.n) = _ from hf.hn]
    simp only [typeof, cop]
    rw [ir_lt (a := (c : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hc : c < n
    · rw [ite_eq_left (by simpa using hc)]
      apply wp_skip
      have hsp := cellEnd_spec hsize hc hlast
      obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [cells_go_succ _ _ _ _ _ hc, List.foldl_cons] at hfold
      have hpc := hf.psmall c hc
      have hlv := hf.levlt
      have hpe := eval_at (ge := ge) (e := e) hf.parr hf.nlt id.ptn hf.hptn (tv id.i) c hc hic rfl
      wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, hpe, show Exec.evalExpr ge e le' m' (tv id.level) = _ from hf.hlev]
      simp only [ints, typeof, cop]
      rw [ir_lt (a := (level : Int)) (b := (ptn[c]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      by_cases hle : ptn[c]! ≤ level
      · rw [ite_eq_left (by simp; omega)]
        have hce : cellEnd ptn level c = c := by
          rcases Nat.lt_or_ge c (cellEnd ptn level c) with hlt | hge
          · have := hsp.2.2.2 c (Nat.le_refl _) hlt; omega
          · omega
        rw [hce] at hfold
        simp only [cellStep, beq_self_eq_true, ite_true] at hfold
        refine wp_single hf hs' hd hfm he hc hic ?_
        intro m2 hf2 hs2 hu2 hr2 hk2
        exact ⟨by simp, rfl, c, c, _, _, _, _, F, Nat.le_refl _, hc, rfl, by omega, hfold, hic, hf2,
          hs2, hu.trans hu2, hr.trans hr2, hk.trans hk2, ho⟩
      · rw [ite_eq_right (by simp; omega)]
        have hce : c < cellEnd ptn level c := by
          rcases Nat.lt_or_ge c (cellEnd ptn level c) with hlt | hge
          · exact hlt
          · have h1 : cellEnd ptn level c = c := by have := hsp.1; omega
            have h2 := hsp.2.2.1
            rw [h1] at h2; omega
        have hne : (c == cellEnd ptn level c) = false := by simp; omega
        simp only [cellStep, hne] at hfold
        refine wp_cell hf hs' hd hfm he hce hsp.2.1 hsp.2.2.1 hsp.2.2.2 hic ?_
        intro le2 m3 hi2 hf2 hs2 hu3 hr3 hk3 ho2
        exact ⟨by simp, rfl, c, cellEnd ptn level c, _, _, _, _, F, Nat.le_of_lt hce, hsp.2.1, rfl, by omega,
          hfold, hi2, hf2, hs2, hu.trans hu3, hr.trans hr3, hk.trans hk3, fun k h1 h2 h3 => by rw [ho2 k h1 h2 h3, ho k h1 h2 h3]⟩
    · rw [ite_eq_right (by simpa using hc)]
      apply wp_break
      have hcn' : c = n := by omega
      subst hcn'
      rw [cells_go_ge _ _ _ _ _ hc, List.foldl_nil] at hfold
      have h1 : (fmptn lab ptn level c).1 = fx := by rw [hR, ← hfold]
      have h2 : (fmptn lab ptn level c).2 = mc := by rw [hR, ← hfold]
      have := hQ le' m' wf wm hf (by rw [h1, h2]; exact hs') hu hr hk ho
      simpa using this
  · rintro v t e' le' m' ⟨rfl, rfl, c, c2, wf, wm, fx, mc, F, hcc, hc2, rfl, hF, hfold, hic, hf, hs',
      hu, hr, hk, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge e le' m' (tv id.i) = _ from hic]
    simp only [Exec.evalExpr, typeof, cop, ir_add]
    have hoth : ∀ k, k ≠ id.i → PTree.get k (PTree.set id.i (.Vint (ir ((c2 : Int) + 1))) le') =
        PTree.get k le' := fun k hk => temps_gso _ _ hk
    refine ⟨n - (c2 + 1), by omega, by simp, trivial, c2 + 1, wf, wm, fx, mc, F, by omega, rfl, hF,
      hfold, by rw [temps_gss]; rfl, hf.temps fun k h1 _ _ _ _ _ _ => hoth k h1,
      hs'.temps fun k h1 _ _ _ _ _ _ => hoth k h1, hu, hr, hk, fun k h1 h2 h3 => by rw [hoth k h1, ho k h1 h2 h3]⟩

end NautyVerified.Proofs.Fmptn
