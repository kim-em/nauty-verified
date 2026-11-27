import NautyVerified.Proofs.Breakout.Rotate
import NautyVerified.Proofs.Nextelement.Satisfies
import NautyVerified.Spec.Setwords

/-!
# `breakout` meets its specification

`breakoutSpec`: called with `lab` and `ptn` arrays holding `lab` and `ptn`
(`n` entries each, `lab`'s entries below `n`), `level`, a cell start `tc`, a
vertex `tv` held in `lab` at some position `≥ tc`, and an active set of `M`
words, nauty's `breakout` leaves `lab` and `ptn` holding the first two
components of HexGraphIso's `breakout n lab ptn level tc tv`, and the active
set representing the third (`SetRep`). It changes only those three blocks
and emits no events. It reads nautil.c's `bit` table.
-/

namespace NautyVerified.Proofs.Breakout

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec

theorem BitTable.unch {m m' : mem} {S : block → Prop} {b : block} (h : BitTable m b)
    (hu : Unch m m' S) (hb : ¬ S b) : BitTable m' b := fun i hi => by
  rw [hu.load _ _ _ hb]; exact h i hi

/-- The active set after `breakout`: `{tc}`. -/
def single (tc : Nat) : Nat → Lib.Integers.int64 :=
  upd (fun _ => lr 0) (tc / 64) (Int64.or (lr 0) (lr ((2 ^ (63 - tc % 64) : Nat) : Int)))

theorem setRep_single {n M tc : Nat} (hn : n ≤ 64 * M) (htc : tc < n) :
    SetRep (fun w => bv64 (single tc w)) M
      (Hex.GraphIso.Nauty.VSet.empty.insert tc : Hex.GraphIso.Nauty.VSet n) := by
  have h := setRep_insert (setRep_empty (n := n) hn) htc
  have he : (fun w => bv64 (single tc w)) =
      fun w => if w = tc / 64 then (fun _ => (0 : BitVec 64)) w ||| bitAt (tc % 64)
        else (fun _ => (0 : BitVec 64)) w := by
    funext w
    simp only [single, upd]
    split
    · simp only [bv64_or, bv64_repr, intOfZ_zOfInt, bitAt, BitVec.ofInt_natCast]
      simp
    · simp [intOfZ_zOfInt]
  rw [he]; exact h

/-- The specification of `breakout`. -/
def breakoutSpec (bl : block) (lofs : ptrofs) (bp : block) (pofs : ptrofs) (ba : block)
    (aofs : ptrofs) (lab ptn : Array Nat) (n level tc tv M : Nat)
    (ws : Nat → Lib.Integers.int64) : FunSpec where
  pre args m := args = [.Vptr bl lofs, .Vptr bp pofs, .Vint (ir level), .Vint (ir tc),
      .Vint (ir tv), .Vptr ba aofs, .Vint (ir M)] ∧
    ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n ∧
    ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n ∧
    ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned aofs)) (longs ws) M ∧
    BitTable m Block.nautilBit ∧
    bl ≠ bp ∧ bl ≠ ba ∧ bp ≠ ba ∧ Block.nautilBit ≠ ba ∧
    lab.size = n ∧ ptn.size = n ∧ (∀ x < n, lab[x]! < n) ∧
    (∃ j, tc ≤ j ∧ j < n ∧ lab[j]! = tv) ∧
    n < 2147483648 ∧ level < 2147483648 ∧ 0 < M ∧ M < 2147483648 ∧ n ≤ 64 * M
  post _ m t _ m' := t = E0 ∧
    ArrayAt m' .Mint32 bl (intOfZ (Ptrofs.unsigned lofs))
      (ints (Hex.GraphIso.Nauty.breakout n lab ptn level tc tv).1) n ∧
    ArrayAt m' .Mint32 bp (intOfZ (Ptrofs.unsigned pofs))
      (ints (Hex.GraphIso.Nauty.breakout n lab ptn level tc tv).2.1) n ∧
    ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned aofs)) (longs (single tc)) M ∧
    SetRep (fun w => bv64 (single tc w)) M (Hex.GraphIso.Nauty.breakout n lab ptn level tc tv).2.2 ∧
    Unch m m' (fun b => b = bl ∨ b = bp ∨ b = ba)

/-- The temporaries on entry. -/
def entryTemps (bl : block) (lofs : ptrofs) (bp : block) (pofs : ptrofs) (ba : block)
    (aofs : ptrofs) (level tc tv M : Nat) : temp_env :=
  PTree.set id.m (.Vint (ir M)) (PTree.set id.active (.Vptr ba aofs)
    (PTree.set id.tv (.Vint (ir tv)) (PTree.set id.tc (.Vint (ir tc))
      (PTree.set id.level (.Vint (ir level)) (PTree.set id.ptn (.Vptr bp pofs)
        (PTree.set id.lab (.Vptr bl lofs) (create_undef_temps Source.dense.fn.breakout.fn_temps)))))))

theorem breakout_satisfies {xi : ExternalCalls} (bl : block) (lofs : ptrofs) (bp : block)
    (pofs : ptrofs) (ba : block) (aofs : ptrofs) (lab ptn : Array Nat) (n level tc tv M : Nat)
    (ws : Nat → Lib.Integers.int64) :
    Satisfies xi ge (.Internal Source.dense.fn.breakout)
      (breakoutSpec bl lofs bp pofs ba aofs lab ptn n level tc tv M ws) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bl lofs bp pofs ba aofs level tc tv M ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bl lofs bp pofs ba aofs level tc tv M, m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hlarr, hparr, harr, hbit, hlp, hla, hpa, hba, hls, hps, hsmall,
      ⟨jt, htj, hjt, hat⟩, hn, hlev, hM, hM2, hnM⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.breakout.fn_body_eq, body_eq]
    simp only [body]
    wp_step
    refine wp_clear harr hM hM2 (by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [entryTemps, temps_gss]) ?_
    intro le1 m1 harr1 hu1 ho1
    wp_step
    have htcn : tc < n := by omega
    refine wp_add (c := tc) harr1 hM2
      (by rw [ho1 _ (by decide) (by decide)]; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      (by rw [ho1 _ (by decide) (by decide)]; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      (by omega) (by omega) (hbit.unch hu1 hba) rfl ?_
    intro m2 harr2 hu2
    have hT : ∀ k, k ≠ id.es → k ≠ id.t1 →
        PTree.get k le1 = PTree.get k (entryTemps bl lofs bp pofs ba aofs level tc tv M) := ho1
    have hu12 := hu1.trans hu2
    have htc1 : PTree.get id.tc le1 = some (.Vint (ir tc)) := by
      rw [hT _ (by decide) (by decide)]
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have htv1 : PTree.get id.tv le1 = some (.Vint (ir tv)) := by
      rw [hT _ (by decide) (by decide)]
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have hlab1 : PTree.get id.lab le1 = some (.Vptr bl lofs) := by
      rw [hT _ (by decide) (by decide)]
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    wp_step; wp_step; wp_step; wp_step
    rw [htc1]
    wp_step; wp_step; wp_step; wp_step
    rw [temps_gso _ _ (by decide), htv1]
    dsimp only
    wp_step
    refine wp_rotate (hlarr.unch hu12 hla) hn hls
      (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hlab1)
      (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact htv1)
      (by rw [temps_gso _ _ (by decide), temps_gss])
      (temps_gss _ _ _) htj hjt hat hsmall ?_
    intro le3 m3 harr3 hu3 ho3
    wp_step; wp_step
    have hparr3 := (hparr.unch hu12 hpa).unch hu3 (Ne.symm hlp)
    refine wp_store (ge := ge) hparr3 hn id.ptn ?_ (Breakout.tv id.tc) tc htcn ?_ rfl (Breakout.tv id.level) level ?_ rfl ?_
    · rw [ho3 _ (by decide) (by decide) (by decide) (by decide)]
      rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), hT _ (by decide) (by decide)]
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    · simp only [Exec.evalExpr]
      rw [ho3 _ (by decide) (by decide) (by decide) (by decide)]
      rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), hT _ (by decide) (by decide)]
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    · simp only [Exec.evalExpr]
      rw [ho3 _ (by decide) (by decide) (by decide) (by decide)]
      rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), hT _ (by decide) (by decide)]
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    intro m4 hparr4 hu4
    rw [← ints_set (by omega)] at hparr4
    refine ⟨m4, Nextelement.free_empty m4, rfl, ?_, hparr4, ?_, ?_, ?_⟩
    · have := harr3.unch hu4 hlp
      simpa [Hex.GraphIso.Nauty.breakout, hls] using this
    · exact (harr2.unch hu3 (Ne.symm hla)).unch hu4 (Ne.symm hpa)
    · exact setRep_single hnM htcn
    · refine ((hu12.mono ?_).trans (hu3.mono ?_)).trans (hu4.mono ?_) <;> intro b hb <;> simp_all

end NautyVerified.Proofs.Breakout
