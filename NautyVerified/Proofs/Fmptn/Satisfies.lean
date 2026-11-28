import NautyVerified.Program.Env
import NautyVerified.Proofs.Fmptn.Loop
import NautyVerified.Proofs.Nextelement.Satisfies

/-!
# `fmptn` meets its specification

`fmptnSpec`: called with `lab` and `ptn` arrays holding `lab` and `ptn`
(`n` entries, `lab`'s below `n`, the last cell closed: `ptn[n-1] ≤ level`),
`level`, and sets `fix` and `mcr` of `M` words, nauty's `fmptn` leaves in
`fix` and `mcr` words representing HexGraphIso's `fmptn lab ptn level n`. It
changes only the two set blocks and emits no events.
-/

namespace NautyVerified.Proofs.Fmptn

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (longs BitTable)
open Hex.GraphIso.Nauty (VSet fmptn)

/-- The specification of `fmptn`. -/
def fmptnSpec (bl : block) (lofs : ptrofs) (bp : block) (pofs : ptrofs) (bf : block)
    (fofs : ptrofs) (bm : block) (mofs : ptrofs) (lab ptn : Array Nat) (n level M : Nat)
    (wf wm : Nat → Lib.Integers.int64) : FunSpec where
  pre args m := args = [.Vptr bl lofs, .Vptr bp pofs, .Vint (ir level), .Vptr bf fofs,
      .Vptr bm mofs, .Vint (ir M), .Vint (ir n)] ∧
    ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n ∧
    ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n ∧
    ArrayAt m .Mint64 bf (intOfZ (Ptrofs.unsigned fofs)) (longs wf) M ∧
    ArrayAt m .Mint64 bm (intOfZ (Ptrofs.unsigned mofs)) (longs wm) M ∧
    BitTable m E.nautilBit ∧ Disjoint bl bp bf bm ∧
    Apart bf (intOfZ (Ptrofs.unsigned fofs)) bm (intOfZ (Ptrofs.unsigned mofs)) M ∧
    ptn.size = n ∧ (∀ x < n, lab[x]! < n) ∧ (∀ x < n, ptn[x]! < 2147483648) ∧
    ptn[n - 1]! ≤ level ∧
    n < 2147483648 ∧ level < 2147483648 ∧ 0 < M ∧ M < 2147483648 ∧ n ≤ 64 * M
  post _ m t _ m' := t = E0 ∧ ∃ wf' wm',
    ArrayAt m' .Mint64 bf (intOfZ (Ptrofs.unsigned fofs)) (longs wf') M ∧
    ArrayAt m' .Mint64 bm (intOfZ (Ptrofs.unsigned mofs)) (longs wm') M ∧
    SetRep (fun w => bv64 (wf' w)) M (fmptn lab ptn level n).1 ∧
    SetRep (fun w => bv64 (wm' w)) M (fmptn lab ptn level n).2 ∧
    Unch m m' (fun b => b = bf ∨ b = bm) ∧
    Rest m m' bf (intOfZ (Ptrofs.unsigned fofs)) bm (intOfZ (Ptrofs.unsigned mofs)) M ∧
    Alloc.KeepA m m'

/-- The temporaries on entry. -/
def entryTemps (bl : block) (lofs : ptrofs) (bp : block) (pofs : ptrofs) (bf : block)
    (fofs : ptrofs) (bm : block) (mofs : ptrofs) (n level M : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.mcr (.Vptr bm mofs) (PTree.set id.fix (.Vptr bf fofs)
      (PTree.set id.level (.Vint (ir level)) (PTree.set id.ptn (.Vptr bp pofs)
        (PTree.set id.lab (.Vptr bl lofs) (create_undef_temps Source.dense.fn.fmptn.fn_temps)))))))

theorem fmptn_satisfies {xi : ExternalCalls} (bl : block) (lofs : ptrofs) (bp : block)
    (pofs : ptrofs) (bf : block) (fofs : ptrofs) (bm : block) (mofs : ptrofs)
    (lab ptn : Array Nat) (n level M : Nat) (wf wm : Nat → Lib.Integers.int64) :
    Satisfies xi ge (.Internal Source.dense.fn.fmptn)
      (fmptnSpec bl lofs bp pofs bf fofs bm mofs lab ptn n level M wf wm) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bl lofs bp pofs bf fofs bm mofs n level M ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bl lofs bp pofs bf fofs bm mofs n level M, m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hlarr, hparr, hfarr, hmarr, hbit, hd, hfm, hps, hls, hpl, hlast, hn, hlev, hM,
      hM2, hnM⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.fmptn.fn_body_eq, body_eq]
    simp only [body]
    wp_step
    refine Set.wp_emptySet' (vals := Set.longs wf) (by decide) (by decide) (by decide) hfarr hM hM2
      (by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]) ?_
    intro le1 m1 harr1 hu1 hO1 ho1
    wp_step
    refine Set.wp_emptySet' (vals := Set.longs wm) (by decide) (by decide) (by decide)
      (hmarr.acrossF hu1 hO1 hfm) hM hM2
      (by rw [ho1 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      (by rw [ho1 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]) ?_
    intro le2 m2 harr2 hu2 hO2 ho2
    wp_step; wp_step; wp_step; wp_step
    let le3 := PTree.set id.i (.Vint (ir 0)) le2
    have hT : ∀ k, k ≠ id.i → k ≠ id.es → k ≠ id.t1 → k ≠ id.es1 → k ≠ id.t2 →
        PTree.get k le3 = PTree.get k (entryTemps bl lofs bp pofs bf fofs bm mofs n level M) :=
      fun k h1 h2 h3 h4 h5 => by
        simp only [le3]; rw [temps_gso _ _ h1, ho2 k h4 h5, ho1 k h2 h3]
    have hf : Frame m2 le3 bl lofs bp pofs lab ptn n level :=
      { hlab := by rw [hT _ (by decide) (by decide) (by decide) (by decide) (by decide)]
                   simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hptn := by rw [hT _ (by decide) (by decide) (by decide) (by decide) (by decide)]
                   simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hlev := by rw [hT _ (by decide) (by decide) (by decide) (by decide) (by decide)]
                   simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hn := by rw [hT _ (by decide) (by decide) (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [entryTemps, temps_gss]
        larr := (hlarr.unch hu1 (Ne.symm hd.fl)).unch hu2 (Ne.symm hd.ml)
        parr := (hparr.unch hu1 (Ne.symm hd.fp)).unch hu2 (Ne.symm hd.mp)
        nlt := hn, levlt := hlev, lsmall := hls, psmall := hpl }
    have hs : Sets m2 le3 bf fofs bm mofs n M (fun _ => lr 0) (fun _ => lr 0) VSet.empty VSet.empty :=
      { hfix := by rw [hT _ (by decide) (by decide) (by decide) (by decide) (by decide)]
                   simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hmcr := by rw [hT _ (by decide) (by decide) (by decide) (by decide) (by decide)]
                   simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        farr := harr1.acrossM hu2 hO2 hfm
        marr := harr2
        frep := Set.setRep_zero hnM
        mrep := Set.setRep_zero hnM
        bit := (hbit.unch hu1 hd.bf).unch hu2 hd.bm
        Mlt := hM2, nM := hnM }
    refine wp_loop_fmptn hf hs hd hfm rfl hps hlast (temps_gss _ _ _) ?_
    intro le' m' wf' wm' hf' hs' hu' hr' hk' ho'
    exact ⟨m', Nextelement.free_empty m', rfl, wf', wm', hs'.farr, hs'.marr, hs'.frep, hs'.mrep,
      ((hu1.mono fun b hb => .inl hb).trans (hu2.mono fun b hb => .inr hb)).trans hu',
      ((Rest.fix hu1 hO1).trans (Rest.mcr hu2 hO2)).trans hr',
      ((Alloc.KeepA.of_outside hu1 hO1 hfarr.base_nonneg).trans (Alloc.KeepA.of_outside hu2 hO2
        (hmarr.acrossF hu1 hO1 hfm).base_nonneg)).trans hk'⟩

end NautyVerified.Proofs.Fmptn
