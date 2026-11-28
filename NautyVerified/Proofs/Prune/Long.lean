import NautyVerified.Program.Env
import NautyVerified.Proofs.Prune.LongPair
import NautyVerified.Proofs.Nextelement.Satisfies
import HexGraphIso.Nauty.Search.State

/-!
# `longprune` meets its specification

`PairsAt ww M o L`: from word `o` of the workspace, the pairs of `L` are
stored one after another, each as its `fix` set then its `mcr` set (`M` words
each). `longpruneSpec`: called with `tcell` (representing `T`), the fixed
points `fix` (representing `F`), and `bottom`, `top` delimiting `L` in the
workspace, nauty's `longprune` leaves `tcell` representing HexGraphIso's
`longprune T F L.toArray`. It changes only `tcell`'s block and emits no events.
-/

namespace NautyVerified.Proofs.Prune.Long

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set
open Hex.GraphIso.Nauty (VSet)

variable {xi : ExternalCalls}

/-- The pairs of `L`, stored from word `o` of `ww`. -/
def PairsAt {n : Nat} (ww : Nat → Lib.Integers.int64) (M : Nat) :
    Nat → List (VSet n × VSet n) → Prop
  | _, [] => True
  | o, (fx, mc) :: L => SetRep (fun w => bv64 (ww (o + w))) M fx ∧
      SetRep (fun w => bv64 (ww (o + M + w))) M mc ∧ PairsAt ww M (o + M + M) L

/-- HexGraphIso's `longprune` step. -/
def pruneStep {n : Nat} (F : VSet n) (T : VSet n) (p : VSet n × VSet n) : VSet n :=
  if F.subset p.1 then T.inter p.2 else T

theorem longprune_eq {n : Nat} (T F : VSet n) (L : List (VSet n × VSet n)) :
    Hex.GraphIso.Nauty.longprune T F L.toArray = L.foldl (pruneStep F) T := by
  rw [Hex.GraphIso.Nauty.longprune, List.foldl_toArray]
  rfl

theorem wp_body {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {bt : block} {tofs : ptrofs} {bf : block} {fofs : ptrofs} {bw : block} {wb : Int}
    {ww : Nat → Lib.Integers.int64} {W M o : Nat} {wf wt : Nat → Lib.Integers.int64}
    {F T : VSet n} {L : List (VSet n × VSet n)}
    (h : LFrame m le bt tofs bf fofs bw wb ww W M wf F)
    (htarr : ArrayAt m .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) (longs wt) M)
    (htrep : SetRep (fun w => bv64 (wt w)) M T) (hM : 0 < M) (hW : 0 < W)
    (ho : o + (M + M) * L.length ≤ W)
    (hbot : PTree.get id.bottom le = some (.Vptr bw (ptrTo wb 8 o)))
    (htop : PTree.get id.top le = some (.Vptr bw (ptrTo wb 8 (o + (M + M) * L.length))))
    (hL : PairsAt ww M o L)
    (hQ : ∀ le' m' wt', ArrayAt m' .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) (longs wt') M →
      SetRep (fun w => bv64 (wt' w)) M (L.foldl (pruneStep F) T) →
      Unch m m' (· = bt) → Alloc.KeepA m m' →
      (∀ k, k ≠ id.i → k ≠ id.bottom → PTree.get k le' = PTree.get k le) →
      Q.normal E0 e le' m') :
    Wp xi ge f body Q e le m := by
  let tp := o + (M + M) * L.length
  let R := L.foldl (pruneStep F) T
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    ∃ L' o' wt' T', v = L'.length ∧ o' + (M + M) * L'.length = tp ∧
      PTree.get id.bottom le' = some (.Vptr bw (ptrTo wb 8 o')) ∧ PairsAt ww M o' L' ∧
      L'.foldl (pruneStep F) T' = R ∧
      ArrayAt m' .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) (longs wt') M ∧
      SetRep (fun w => bv64 (wt' w)) M T' ∧ Unch m m' (· = bt) ∧ Alloc.KeepA m m' ∧
      ∀ k, k ≠ id.i → k ≠ id.bottom → PTree.get k le' = PTree.get k le
  refine wp_loop (I := I) (J := fun v t e' le' m' => ∃ v', v' < v ∧ I v' t e' le' m') ?_ ?_
    (n := L.length) ⟨rfl, rfl, L, o, wt, T, rfl, rfl, hbot, hL, rfl, htarr, htrep, Unch.refl _ _,
      Alloc.KeepA.refl _, fun _ _ _ => rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, L', o', wt', T', rfl, hoff, hbot', hL', hfold, harr', hrep', hu,
      hkp, hoth⟩
    have h' := (h.temps hoth).unch hu
    have htop' : PTree.get id.top le' = some (.Vptr bw (ptrTo wb 8 tp)) := by
      rw [hoth _ (by decide) (by decide)]; exact htop
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge e le' m' (pv id.bottom) = _ from hbot',
      show Exec.evalExpr ge e le' m' (pv id.top) = _ from htop']
    simp only [typeof, cop]
    rw [cmplu_lt_ptrTo h'.warr hW (by omega) (by omega)]
    simp only [Option.map, cop]
    cases L' with
    | nil =>
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hoff
      rw [ite_eq_right (by simp; omega)]
      apply wp_break
      simp only [List.foldl_nil] at hfold
      rw [hfold] at hrep'
      simpa using hQ le' m' wt' harr' hrep' hu hkp hoth
    | cons p L'' =>
      obtain ⟨fx, mc⟩ := p
      obtain ⟨hfx, hmc, hL''⟩ := hL'
      simp only [List.length_cons, Nat.mul_succ] at hoff
      rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      refine wp_pair h' harr' hrep' (by omega) hbot' hfx hmc ?_
      intro le2 m2 wt2 hbot2 harr2 hrep2 hu2 hk2 hoth2
      refine ⟨L''.length, by simp, by simp, rfl, L'', o' + M + M, wt2, _, rfl, by omega, hbot2,
        hL'', ?_, harr2, hrep2, hu.trans hu2, hkp.trans hk2, fun k h1 h2 => by rw [hoth2 k h1 h2, hoth k h1 h2]⟩
      rw [← hfold, List.foldl_cons]
      rfl
  · rintro v t e' le' m' hJ
    apply wp_skip
    simpa using hJ

/-- The specification of `longprune`. -/
def longpruneSpec {n : Nat} (bt : block) (tofs : ptrofs) (bf : block) (fofs : ptrofs) (bw : block)
    (wb : Int) (ww : Nat → Lib.Integers.int64) (W M o : Nat) (wf wt : Nat → Lib.Integers.int64)
    (F T : VSet n) (L : List (VSet n × VSet n)) : FunSpec where
  pre args m := args = [.Vptr bt tofs, .Vptr bf fofs, .Vptr bw (ptrTo wb 8 o),
      .Vptr bw (ptrTo wb 8 (o + (M + M) * L.length)), .Vint (ir M)] ∧
    ArrayAt m .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) (longs wt) M ∧
    ArrayAt m .Mint64 bf (intOfZ (Ptrofs.unsigned fofs)) (longs wf) M ∧
    ArrayAt m .Mint64 bw wb (longs ww) W ∧
    SetRep (fun w => bv64 (wt w)) M T ∧ SetRep (fun w => bv64 (wf w)) M F ∧ PairsAt ww M o L ∧
    bt ≠ bf ∧ bt ≠ bw ∧ 0 < M ∧ M < 2147483648 ∧ 0 < W ∧ o + (M + M) * L.length ≤ W
  post _ m t _ m' := t = E0 ∧ ∃ wt',
    ArrayAt m' .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) (longs wt') M ∧
    SetRep (fun w => bv64 (wt' w)) M (Hex.GraphIso.Nauty.longprune T F L.toArray) ∧
    Unch m m' (· = bt) ∧ Alloc.KeepA m m'

theorem longprune_satisfies {n : Nat} {xi : ExternalCalls} (bt : block) (tofs : ptrofs)
    (bf : block) (fofs : ptrofs) (bw : block) (wb : Int) (ww : Nat → Lib.Integers.int64)
    (W M o : Nat) (wf wt : Nat → Lib.Integers.int64) (F T : VSet n) (L : List (VSet n × VSet n)) :
    Satisfies xi ge (.Internal Source.dense.fn.longprune)
      (longpruneSpec bt tofs bf fofs bw wb ww W M o wf wt F T L) := by
  let le0 := PTree.set id.m (.Vint (ir M))
    (PTree.set id.top (.Vptr bw (ptrTo wb 8 (o + (M + M) * L.length)))
      (PTree.set id.bottom (.Vptr bw (ptrTo wb 8 o)) (PTree.set id.fix (.Vptr bf fofs)
        (PTree.set id.tcell (.Vptr bt tofs)
          (create_undef_temps Source.dense.fn.longprune.fn_temps)))))
  refine satisfies_internal (Entry := fun _ m₀ e le m => e = empty_env ∧ le = le0 ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, le0, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, htarr, hfarr, hwarr, htrep, hfrep, hL, htf, htw, hM, hM2, hW, ho⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.longprune.fn_body_eq, body_eq]
    have h : LFrame m le0 bt tofs bf fofs bw wb ww W M wf F :=
      { htcell := by simp (config := {decide := true}) only [le0, temps_gso, temps_gss]
        hfix := by simp (config := {decide := true}) only [le0, temps_gso, temps_gss]
        hm := by simp (config := {decide := true}) only [le0, temps_gss]
        farr := hfarr, frep := hfrep, warr := hwarr, Mlt := hM2, tf := htf, tw := htw }
    refine wp_body h htarr htrep hM hW ho
      (by simp (config := {decide := true}) only [le0, temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [le0, temps_gso, temps_gss]) hL ?_
    intro le' m' wt' harr' hrep' hu hk _
    rw [← longprune_eq] at hrep'
    exact ⟨m', Nextelement.free_empty m', rfl, wt', harr', hrep', hu, hk⟩

end NautyVerified.Proofs.Prune.Long
