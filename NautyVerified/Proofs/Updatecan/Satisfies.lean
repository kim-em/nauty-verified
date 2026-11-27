import NautyVerified.Proofs.Updatecan.Rows
import NautyVerified.Proofs.Alloc.Keep

/-!
# `updatecan` meets its specification

`updatecanSpec`: called with a graph `g` and the current best graph `canong`
(both `n` rows of `M` words, of which only `canong`'s first `samerows` need
represent anything, since `updatecan` overwrites the rest), a labelling `lab` hitting every vertex and
`samerows`, nauty's `updatecan` leaves `canong` holding HexGraphIso's
`updatecan ⟨g⟩ canong lab samerows`. `DYNALLOC1` may replace naugraph.c's
`workperm` (`DynAt`); nothing else changes.
-/

namespace NautyVerified.Proofs.Updatecan

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (BitTable longs)
open NautyVerified.Proofs.Nextelement (LeftbitTable)
open NautyVerified.Proofs.Graph (GraphAt)
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty (VSet invPerm)

abbrev WP := Block.naugraphWorkperm
abbrev WPS := Block.naugraphWorkpermSz

def updatecanSpec {n : Nat} (bg : block) (gofs : ptrofs) (gw : Nat → Lib.Integers.int64)
    (grows : Array (VSet n)) (bc : block) (cofs : ptrofs) (cw : Nat → Lib.Integers.int64)
    (canong : Array (VSet n)) (bl : block) (lofs : ptrofs) (lab : Array Nat) (samerows M cap : Nat)
    (b0 : block) : FunSpec where
  pre args m := args = [.Vptr bg gofs, .Vptr bc cofs, .Vptr bl lofs, .Vint (ir samerows),
      .Vint (ir M), .Vint (ir n)] ∧
    GraphAt m bg gofs gw grows M ∧ Graph.RowsAt m bc cofs cw canong samerows M ∧ canong.size = n ∧
    ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n ∧ lab.size = n ∧
    (∀ j < n, lab[j]! < n) ∧ (∀ p < n, ∃ j < n, lab[j]! = p) ∧
    DynAt m WP WPS 4 cap b0 ∧ LeftbitTable m ∧ BitTable m Block.nautilBit ∧
    Mem.valid_block m bg ∧ Mem.valid_block m bc ∧ Mem.valid_block m bl ∧
    bc ≠ bg ∧ bc ≠ bl ∧
    (∀ z, z = WP ∨ z = WPS ∨ z = Block.nautilBit ∨ z = Block.leftbit → z ≠ bc ∧ z ≠ bl ∧ z ≠ bg) ∧
    (0 < cap → b0 ≠ bc ∧ b0 ≠ bl ∧ b0 ≠ bg ∧ b0 ≠ Block.nautilBit ∧ b0 ≠ Block.leftbit) ∧
    samerows ≤ n ∧ 0 < M ∧ M < 33554432 ∧ n ≤ 64 * M
  post _ m t _ m' := t = E0 ∧ ∃ cw' cap' b',
    GraphAt m' bc cofs cw' (Hex.GraphIso.Nauty.updatecan ⟨grows⟩ canong lab samerows) M ∧
    DynAt m' WP WPS 4 cap' b' ∧ n ≤ cap' ∧ ((cap' = cap ∧ b' = b0) ∨ ¬ Mem.valid_block m b') ∧
    Unch m m' (fun z => z = bc ∨ z = WPS ∨ z = WP ∨ (0 < cap ∧ z = b0) ∨
      (¬ Mem.valid_block m b' ∧ z = b'))

def entryTemps (bg : block) (gofs : ptrofs) (bc : block) (cofs : ptrofs) (bl : block)
    (lofs : ptrofs) (samerows M n : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.samerows (.Vint (ir samerows)) (PTree.set id.lab (.Vptr bl lofs)
      (PTree.set id.canong (.Vptr bc cofs) (PTree.set id.g (.Vptr bg gofs)
        (create_undef_temps Source.dense.fn.updatecan.fn_temps))))))

theorem updatecan_satisfies {xi : ExternalCalls} {n : Nat} (bg : block) (gofs : ptrofs)
    (gw : Nat → Lib.Integers.int64) (grows : Array (VSet n)) (bc : block) (cofs : ptrofs)
    (cw : Nat → Lib.Integers.int64) (canong : Array (VSet n)) (bl : block) (lofs : ptrofs)
    (lab : Array Nat) (samerows M cap : Nat) (b0 : block) :
    Satisfies xi ge (.Internal Source.dense.fn.updatecan)
      (updatecanSpec bg gofs gw grows bc cofs cw canong bl lofs lab samerows M cap b0) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bg gofs bc cofs bl lofs samerows M n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bg gofs bc cofs bl lofs samerows M n, m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hg, hcg, hcsz, hlarr, hlsz, hls, hsurj, hD, hlb, hbit, hvg, hvc, hvl, hcgb, hclb,
      hglob, hb0, hsr, hM1, hM2, hnM⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.updatecan.fn_body_eq, body_eq]
    simp only [body]
    have hn : n < 2147483648 := by omega
    have hc4 : 4 * n < 2 ^ 62 := by omega
    have gWP := hglob WP (.inl rfl)
    have gWPS := hglob WPS (.inr (.inl rfl))
    have gBit := hglob Block.nautilBit (.inr (.inr (.inl rfl)))
    have gLb := hglob Block.leftbit (.inr (.inr (.inr rfl)))
    wp_step
    refine Alloc.wp_dynalloc1 find_naugraphWorkpermSz find_naugraphWorkperm rfl hD
      (by simp (config := {decide := true}) only [entryTemps, temps_gss]) hn hc4 ?_
    intro le1 m1 cap' b' hD' hcap hu1 hb' _ ho1
    have hout : ∀ z, Mem.valid_block m z → z ≠ WPS → z ≠ WP → ¬ (0 < cap ∧ z = b0) →
        ¬ (z = WPS ∨ z = WP ∨ (0 < cap ∧ z = b0) ∨ (¬ Mem.valid_block m b' ∧ z = b')) := by
      rintro z hv h1 h2 h3 (h | h | h | ⟨hb, rfl⟩)
      · exact h1 h
      · exact h2 h
      · exact h3 h
      · exact hb hv
    have hbD : 0 < cap' → b' ≠ bc ∧ b' ≠ bl ∧ b' ≠ bg := by
      intro hc0
      rcases hb' with ⟨hcc, rfl⟩ | hnv
      · have := hb0 (by omega); exact ⟨this.1, this.2.1, this.2.2.1⟩
      · exact ⟨fun h => hnv (h ▸ hvc), fun h => hnv (h ▸ hvl), fun h => hnv (h ▸ hvg)⟩
    have hvlb : Mem.valid_block m Block.leftbit := by
      obtain h0 := hlb 0 (by decide)
      exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h0)
    have hvbit : Mem.valid_block m Block.nautilBit := by
      obtain h0 := hbit 0 (by decide)
      exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h0)
    have oc := hout bc hvc gWPS.1.symm gWP.1.symm (fun ⟨h1, h2⟩ => (hb0 h1).1 h2.symm)
    have ol := hout bl hvl gWPS.2.1.symm gWP.2.1.symm (fun ⟨h1, h2⟩ => (hb0 h1).2.1 h2.symm)
    have og := hout bg hvg gWPS.2.2.symm gWP.2.2.symm (fun ⟨h1, h2⟩ => (hb0 h1).2.2.1 h2.symm)
    have obit := hout _ hvbit (by decide) (by decide) (fun ⟨h1, h2⟩ => (hb0 h1).2.2.2.1 h2.symm)
    have olb := hout _ hvlb (by decide) (by decide) (fun ⟨h1, h2⟩ => (hb0 h1).2.2.2.2 h2.symm)
    have hcg1 : Graph.RowsAt m1 bc cofs cw canong samerows M := ⟨hcg.arr.unch hu1 oc, hcg.rep⟩
    have hg1 : GraphAt m1 bg gofs gw grows M := ⟨hg.arr.unch hu1 og, hg.rep⟩
    have hlarr1 := hlarr.unch hu1 ol
    have hbit1 := hbit.unch hu1 obit
    have hlb1 : LeftbitTable m1 := fun i hi => by rw [hu1.load _ _ _ olb]; exact hlb i hi
    have hw1 : ∃ vals, ArrayAt m1 .Mint32 b' 0 vals n := by
      by_cases hn0 : n = 0
      · subst hn0
        exact ⟨fun _ => .Vundef, ⟨Int.le_refl _, by decide, fun _ h => absurd h (by omega),
          fun _ h => absurd h (by omega)⟩⟩
      · exact Alloc.malloced_array (hD'.mal (by omega)) .Mint32 4 rfl rfl n (Nat.mul_le_mul_left 4 hcap)
    obtain ⟨vals, hw1⟩ := hw1
    have hT1 : ∀ k, k ≠ Updatecan.id.t1 → k ≠ Updatecan.id.t2 →
        PTree.get k le1 = PTree.get k (entryTemps bg gofs bc cofs bl lofs samerows M n) := ho1
    wp_step
    refine wp_inv rfl
      (by rw [hT1 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      hlarr1 hls
      (by rw [hT1 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [entryTemps, temps_gss])
      hn (fun hn0 => hD'.ptr (by omega)) hw1 (fun hn0 => ((hbD (by omega)).2.1).symm)
      (fun hn0 => ((hD'.bne (by omega)).2).symm) ?_
    intro le2 m2 harr2 hu2 hk2 ho2
    have nb : ∀ z, (0 < cap' → b' ≠ z) → ¬ (0 < n ∧ z = b') := fun z hz ⟨h0, h⟩ =>
      hz (by omega) h.symm
    have hT2 : ∀ k, k ≠ Updatecan.id.t1 → k ≠ Updatecan.id.t2 → k ≠ Updatecan.id.i →
        PTree.get k le2 = PTree.get k (entryTemps bg gofs bc cofs bl lofs samerows M n) :=
      fun k h1 h2 h3 => by rw [ho2 k h3, hT1 k h1 h2]
    have hwarr2 : ArrayAt m2 .Mint32 b' 0 (ints (invPerm lab)) n :=
      harr2.congr fun p hp => written_full lab n vals hlsz hsurj hp
    have hf : Frame m2 le2 bg gofs gw grows bc cofs bl lofs lab b' M :=
      { hg := by rw [hT2 _ (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hcan := by rw [hT2 _ (by decide) (by decide) (by decide)]
                   simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hlab := by rw [hT2 _ (by decide) (by decide) (by decide)]
                   simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hm := by rw [hT2 _ (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hn := by rw [hT2 _ (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [entryTemps, temps_gss]
        graph := ⟨hg1.arr.unch hu2 (nb _ fun h => (hbD h).2.2), hg1.rep⟩
        larr := hlarr1.unch hu2 (nb _ fun h => (hbD h).2.1)
        lsmall := hls
        warr := hwarr2
        wsmall := invPerm_small lab n hlsz
        wptr := fun hn0 => by
          rw [hu2.load _ _ _ (nb _ fun h => (hD'.bne h).2)]; exact hD'.ptr (by omega)
        lb := fun i hi => by
          have hnS : ¬ (0 < n ∧ Block.leftbit = b') := fun ⟨h0, hh⟩ => by
            rcases hb' with ⟨_, hbb⟩ | hnv
            · exact (hb0 (by omega)).2.2.2.2 (hbb ▸ hh.symm)
            · exact hnv (hh ▸ hvlb)
          rw [hu2.load _ _ _ hnS]
          exact hlb1 i hi
        bit := hbit1.unch hu2 (fun ⟨h0, hh⟩ => by
            rcases hb' with ⟨_, hbb⟩ | hnv
            · exact (hb0 (by omega)).2.2.2.1 (hbb ▸ hh.symm)
            · exact hnv (hh ▸ hvbit))
        cg := hcgb, cl := hclb
        cW := fun hn0 => ((hbD (by omega)).1).symm
        cbit := gBit.1.symm, clb := gLb.1.symm, cwp := gWP.1.symm
        M1 := hM1, Mlt := hM2, nM := hnM }
    have hcg2 : Graph.RowsAt m2 bc cofs cw canong samerows M := ⟨hcg1.arr.unch hu2 (nb _ fun h => (hbD h).1), hcg1.rep⟩
    have hsrv : PTree.get Updatecan.id.samerows le2 = some (.Vint (ir samerows)) := by
      rw [hT2 _ (by decide) (by decide) (by decide)]
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    refine wp_rows hf hcg2 hcsz hsr hsrv ?_
    intro le3 m3 cw' hcg3 hu3 ho3
    refine ⟨m3, Nextelement.free_empty m3, rfl, cw', cap', b', hcg3, ?_, hcap, hb', ?_⟩
    · refine (hD'.keep hu2 (nb _ fun h => (hD'.bne h).2) (nb _ fun h => (hD'.bne h).1)
        fun _ => hk2).keep hu3 gWP.1 gWPS.1 fun hc0 => Keep.unch hu3 (hbD hc0).1
    · have hbS : ∀ z, 0 < n ∧ z = b' → (z = bc ∨ z = WPS ∨ z = WP ∨ (0 < cap ∧ z = b0) ∨
          (¬ Mem.valid_block m b' ∧ z = b')) := by
        rintro z ⟨h0, rfl⟩
        rcases hb' with ⟨hcc, hbb⟩ | hnv
        · exact .inr (.inr (.inr (.inl ⟨by omega, hbb⟩)))
        · exact .inr (.inr (.inr (.inr ⟨hnv, rfl⟩)))
      exact ((hu1.mono fun z hz => .inr hz).trans (hu2.mono fun z hz => hbS z hz)).trans
        (hu3.mono fun z hz => .inl hz)

end NautyVerified.Proofs.Updatecan
