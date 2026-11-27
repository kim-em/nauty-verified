import NautyVerified.Proofs.Testcanlab.Rows
import NautyVerified.Proofs.Updatecan.Satisfies

/-!
# `testcanlab` meets its specification

`testcanlabSpec`: called with a graph `g`, the best graph so far `canong`, a
labelling `lab` hitting every vertex and a cell `*samerows`, nauty's
`testcanlab` returns the first component of HexGraphIso's
`testcanlab ⟨g⟩ canong lab` and stores the second in `*samerows`.
`DYNALLOC1` may replace naugraph.c's `workperm` and `workset` (`DynAt`).
-/

namespace NautyVerified.Proofs.Testcanlab

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
abbrev WS := Block.naugraphWorkset
abbrev WSS := Block.naugraphWorksetSz

def testcanlabSpec {n : Nat} (bg : block) (gofs : ptrofs) (gw : Nat → Lib.Integers.int64)
    (grows : Array (VSet n)) (bc : block) (cofs : ptrofs) (cw : Nat → Lib.Integers.int64)
    (canong : Array (VSet n)) (bl : block) (lofs : ptrofs) (lab : Array Nat) (bs : block) (so : ptrofs)
    (svals : Nat → val) (M capP : Nat) (bP : block) (capS : Nat) (bS : block) : FunSpec where
  pre args m := args = [.Vptr bg gofs, .Vptr bc cofs, .Vptr bl lofs, .Vptr bs so, .Vint (ir M),
      .Vint (ir n)] ∧
    GraphAt m bg gofs gw grows M ∧ GraphAt m bc cofs cw canong M ∧
    ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n ∧ lab.size = n ∧
    (∀ j < n, lab[j]! < n) ∧ (∀ p < n, ∃ j < n, lab[j]! = p) ∧
    ArrayAt m .Mint32 bs (intOfZ (Ptrofs.unsigned so)) svals 1 ∧
    DynAt m WP WPS 4 capP bP ∧ DynAt m WS WSS 8 capS bS ∧ LeftbitTable m ∧ BitTable m Block.nautilBit ∧
    (∀ z, z = bg ∨ z = bc ∨ z = bl ∨ z = bs → Mem.valid_block m z ∧
      z ≠ WP ∧ z ≠ WPS ∧ z ≠ WS ∧ z ≠ WSS ∧ z ≠ Block.nautilBit ∧ z ≠ Block.leftbit ∧
      (0 < capP → z ≠ bP) ∧ (0 < capS → z ≠ bS)) ∧
    bs ≠ bg ∧ bs ≠ bc ∧ bs ≠ bl ∧
    (0 < capP → bP ≠ Block.nautilBit ∧ bP ≠ Block.leftbit ∧ bP ≠ WS ∧ bP ≠ WSS ∧
      (0 < capS → bP ≠ bS)) ∧
    (0 < capS → bS ≠ Block.nautilBit ∧ bS ≠ Block.leftbit ∧ bS ≠ WP ∧ bS ≠ WPS) ∧
    0 < M ∧ M < 33554432 ∧ n ≤ 64 * M
  post _ m t v m' := t = E0 ∧
    v = .Vint (ir (Hex.GraphIso.Nauty.testcanlab ⟨grows⟩ canong lab).1) ∧
    ArrayAt m' .Mint32 bs (intOfZ (Ptrofs.unsigned so))
      (fun _ => .Vint (ir ((Hex.GraphIso.Nauty.testcanlab ⟨grows⟩ canong lab).2 : Int))) 1 ∧ Alloc.Keep m m' bs ∧
    ∃ capP' bP' capS' bS', DynAt m' WP WPS 4 capP' bP' ∧ DynAt m' WS WSS 8 capS' bS' ∧
      n ≤ capP' ∧ M ≤ capS' ∧
      ((capP' = capP ∧ bP' = bP) ∨ ¬ Mem.valid_block m bP') ∧
      ((capS' = capS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS') ∧ (0 < capP' → bP' ≠ bS') ∧
      Unch m m' (fun z => z = bs ∨ z = WPS ∨ z = WP ∨ z = WSS ∨ z = WS ∨ (0 < capP ∧ z = bP) ∨
        (0 < capS ∧ z = bS) ∨ (¬ Mem.valid_block m bP' ∧ z = bP') ∨ (¬ Mem.valid_block m bS' ∧ z = bS'))

def entryTemps (bg : block) (gofs : ptrofs) (bc : block) (cofs : ptrofs) (bl : block)
    (lofs : ptrofs) (bs : block) (so : ptrofs) (M n : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.samerows (.Vptr bs so) (PTree.set Updatecan.id.lab (.Vptr bl lofs)
      (PTree.set id.canong (.Vptr bc cofs) (PTree.set id.g (.Vptr bg gofs)
        (create_undef_temps Source.dense.fn.testcanlab.fn_temps))))))

theorem Malloced.valid {m : mem} {b : block} {N : Nat} (h : Alloc.Malloced m b N) :
    Mem.valid_block m b :=
  Mem.perm_valid_block _ _ _ _ _ (h.perm (-1) (by decide) (by omega))

theorem testcanlab_satisfies {xi : ExternalCalls} {n : Nat} (bg : block) (gofs : ptrofs)
    (gw : Nat → Lib.Integers.int64) (grows : Array (VSet n)) (bc : block) (cofs : ptrofs)
    (cw : Nat → Lib.Integers.int64) (canong : Array (VSet n)) (bl : block) (lofs : ptrofs)
    (lab : Array Nat) (bs : block) (so : ptrofs) (svals : Nat → val) (M capP : Nat) (bP : block)
    (capS : Nat) (bS : block) :
    Satisfies xi ge (.Internal Source.dense.fn.testcanlab)
      (testcanlabSpec bg gofs gw grows bc cofs cw canong bl lofs lab bs so svals M capP bP capS bS) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bg gofs bc cofs bl lofs bs so M n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bg gofs bc cofs bl lofs bs so M n, m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hg, hcg, hlarr, hlsz, hls, hsurj, hsarr, hDP, hDS, hlb, hbit, hcall, hsg, hsc,
      hsl, hbP, hbS, hM1, hM2, hnM⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.testcanlab.fn_body_eq, body_eq]
    simp only [body]
    have hn : n < 2147483648 := by omega
    have cG := hcall bg (.inl rfl)
    have cC := hcall bc (.inr (.inl rfl))
    have cL := hcall bl (.inr (.inr (.inl rfl)))
    have cS := hcall bs (.inr (.inr (.inr rfl)))
    have hT0 : ∀ k, k ≠ id.t1 → k ≠ id.t2 → k ≠ id.t3 → k ≠ id.t4 → k ≠ Updatecan.id.i →
        PTree.get k (entryTemps bg gofs bc cofs bl lofs bs so M n) = PTree.get k (entryTemps bg gofs bc cofs bl lofs bs so M n) :=
      fun _ _ _ _ _ _ => rfl
    -- `DYNALLOC1(int, workperm, workperm_sz, n)`
    wp_step
    refine Alloc.wp_dynalloc1 (c := 4) find_naugraphWorkpermSz find_naugraphWorkperm rfl hDP
      (by simp (config := {decide := true}) only [entryTemps, temps_gss]) hn (by omega) ?_
    intro le1 m1 capP' bP' hDP' hcapP huP hbP' hgP ho1
    have hvWS : Mem.valid_block m WS := Alloc.valid_of_access hDS.bpW
    have hvWSS : Mem.valid_block m WSS := Alloc.valid_of_access hDS.bsW
    have hvWP : Mem.valid_block m WP := Alloc.valid_of_access hDP.bpW
    have hvWPS : Mem.valid_block m WPS := Alloc.valid_of_access hDP.bsW
    have notSP : ∀ z, Mem.valid_block m z → z ≠ WPS → z ≠ WP → (0 < capP → z ≠ bP) →
        ¬ (z = WPS ∨ z = WP ∨ (0 < capP ∧ z = bP) ∨ (¬ Mem.valid_block m bP' ∧ z = bP')) := by
      rintro z hv h1 h2 h3 (h | h | ⟨hc, h⟩ | ⟨hb, rfl⟩)
      · exact h1 h
      · exact h2 h
      · exact h3 hc h
      · exact hb hv
    have hDS1 : DynAt m1 WS WSS 8 capS bS :=
      hDS.keep huP (notSP _ hvWS (by decide) (by decide) fun hc h => (hbP hc).2.2.1 h.symm)
        (notSP _ hvWSS (by decide) (by decide) fun hc h => (hbP hc).2.2.2.1 h.symm)
        fun hc => Keep.unch huP (notSP _ (Malloced.valid (hDS.mal hc)) (hbS hc).2.2.2
          (hbS hc).2.2.1 fun hcP h => (hbP hcP).2.2.2.2 hc h.symm)
    have hT1 : ∀ k, k ≠ id.t1 → k ≠ id.t2 →
        PTree.get k le1 = PTree.get k (entryTemps bg gofs bc cofs bl lofs bs so M n) := ho1
    -- `DYNALLOC1(set, workset, workset_sz, m)`
    wp_step
    refine Alloc.wp_dynalloc1 (c := 8) (n := M) find_naugraphWorksetSz find_naugraphWorkset rfl hDS1
      (by rw [hT1 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]) (by omega) (by omega) ?_
    intro le2 m2 capS' bS' hDS' hcapS huS hbS' hgS ho2
    have notSS : ∀ z, Mem.valid_block m1 z → z ≠ WSS → z ≠ WS → (0 < capS → z ≠ bS) →
        ¬ (z = WSS ∨ z = WS ∨ (0 < capS ∧ z = bS) ∨ (¬ Mem.valid_block m1 bS' ∧ z = bS')) := by
      rintro z hv h1 h2 h3 (h | h | ⟨hc, h⟩ | ⟨hb, rfl⟩)
      · exact h1 h
      · exact h2 h
      · exact h3 hc h
      · exact hb hv
    have hvlb : Mem.valid_block m Block.leftbit := by
      obtain h0 := hlb 0 (by decide)
      exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h0)
    have hvbit : Mem.valid_block m Block.nautilBit := by
      obtain h0 := hbit 0 (by decide)
      exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h0)
    -- caller blocks and tables survive both allocations
    have both : ∀ z, Mem.valid_block m z → z ≠ WPS → z ≠ WP → z ≠ WSS → z ≠ WS →
        (0 < capP → z ≠ bP) → (0 < capS → z ≠ bS) →
        ¬ (z = WPS ∨ z = WP ∨ (0 < capP ∧ z = bP) ∨ (¬ Mem.valid_block m bP' ∧ z = bP')) ∧
        ¬ (z = WSS ∨ z = WS ∨ (0 < capS ∧ z = bS) ∨ (¬ Mem.valid_block m1 bS' ∧ z = bS')) :=
      fun z hv h1 h2 h3 h4 h5 h6 => ⟨notSP z hv h1 h2 h5, notSS z (hgP z hv) h3 h4 h6⟩
    have bG := both bg cG.1 cG.2.2.1 cG.2.1 cG.2.2.2.2.1 cG.2.2.2.1 cG.2.2.2.2.2.2.2.1 cG.2.2.2.2.2.2.2.2
    have bC := both bc cC.1 cC.2.2.1 cC.2.1 cC.2.2.2.2.1 cC.2.2.2.1 cC.2.2.2.2.2.2.2.1 cC.2.2.2.2.2.2.2.2
    have bL := both bl cL.1 cL.2.2.1 cL.2.1 cL.2.2.2.2.1 cL.2.2.2.1 cL.2.2.2.2.2.2.2.1 cL.2.2.2.2.2.2.2.2
    have bSr := both bs cS.1 cS.2.2.1 cS.2.1 cS.2.2.2.2.1 cS.2.2.2.1 cS.2.2.2.2.2.2.2.1 cS.2.2.2.2.2.2.2.2
    have bBit := both _ hvbit (by decide) (by decide) (by decide) (by decide)
      (fun hc h => (hbP hc).1 h.symm) (fun hc h => (hbS hc).1 h.symm)
    have bLb := both _ hvlb (by decide) (by decide) (by decide) (by decide)
      (fun hc h => (hbP hc).2.1 h.symm) (fun hc h => (hbS hc).2.1 h.symm)
    have hu12 : ∀ z, (¬ (z = WPS ∨ z = WP ∨ (0 < capP ∧ z = bP) ∨ (¬ Mem.valid_block m bP' ∧ z = bP')) ∧
        ¬ (z = WSS ∨ z = WS ∨ (0 < capS ∧ z = bS) ∨ (¬ Mem.valid_block m1 bS' ∧ z = bS'))) →
        ∀ chunk ofs, Mem.load chunk m2 z ofs = Mem.load chunk m z ofs := fun z hz chunk ofs => by
      rw [huS.load _ _ _ hz.2, huP.load _ _ _ hz.1]
    -- the `workperm` block `bP'`
    have hP' : 0 < capP' → (bP' ≠ WS ∧ bP' ≠ WSS ∧ (0 < capS → bP' ≠ bS)) ∧ Mem.valid_block m1 bP' :=
      fun hc => ⟨by
        rcases hbP' with ⟨hcc, rfl⟩ | hnv
        · have := hbP (by omega); exact ⟨this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
        · exact ⟨fun h => hnv (h ▸ hvWS), fun h => hnv (h ▸ hvWSS),
            fun hcS h => hnv (h ▸ Malloced.valid (hDS.mal hcS))⟩, Malloced.valid (hDP'.mal hc)⟩
    have hDP2 : DynAt m2 WP WPS 4 capP' bP' :=
      hDP'.keep huS (notSS _ (hgP _ hvWP) (by decide) (by decide) fun hc h => (hbS hc).2.2.1 h.symm)
        (notSS _ (hgP _ hvWPS) (by decide) (by decide) fun hc h => (hbS hc).2.2.2 h.symm)
        fun hc => Keep.unch huS (notSS _ (hP' hc).2 (hP' hc).1.2.1 (hP' hc).1.1 (hP' hc).1.2.2)
    have hT2 : ∀ k, k ≠ id.t1 → k ≠ id.t2 → k ≠ id.t3 → k ≠ id.t4 →
        PTree.get k le2 = PTree.get k (entryTemps bg gofs bc cofs bl lofs bs so M n) :=
      fun k h1 h2 h3 h4 => by rw [ho2 k h3 h4, hT1 k h1 h2]
    have hlarr2 : ArrayAt m2 .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n :=
      ⟨hlarr.base_nonneg, hlarr.fits, fun i hi => by rw [hu12 _ bL]; exact hlarr.load i hi,
       fun i hi => huS.access _ _ _ _ bL.2 (huP.access _ _ _ _ bL.1 (hlarr.writable i hi))⟩
    have hw2 : ∃ vals, ArrayAt m2 .Mint32 bP' 0 vals n := by
      by_cases hn0 : n = 0
      · subst hn0
        exact ⟨fun _ => .Vundef, ⟨Int.le_refl _, by decide, fun _ h => absurd h (by omega),
          fun _ h => absurd h (by omega)⟩⟩
      · exact Alloc.malloced_array (hDP2.mal (by omega)) .Mint32 4 rfl rfl n (Nat.mul_le_mul_left 4 hcapP)
    obtain ⟨vals, hw2⟩ := hw2
    have hblP : 0 < n → bl ≠ bP' := fun hn0 => by
      rcases hbP' with ⟨hcc, rfl⟩ | hnv
      · exact cL.2.2.2.2.2.2.2.1 (by omega)
      · exact fun h => hnv (h ▸ cL.1)
    wp_step
    refine Updatecan.wp_inv rfl
      (by rw [hT2 _ (by decide) (by decide) (by decide) (by decide)]
          simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      hlarr2 hls
      (by rw [hT2 _ (by decide) (by decide) (by decide) (by decide)]
          simp (config := {decide := true}) only [entryTemps, temps_gss])
      hn (fun hn0 => hDP2.ptr (by omega)) hw2 hblP (fun hn0 => ((hDP2.bne (by omega)).2).symm) ?_
    intro le3 m3 harr3 hu3 hk3 ho3
    have nb : ∀ z, (0 < capP' → bP' ≠ z) → ¬ (0 < n ∧ z = bP') := fun z hz ⟨h0, h⟩ =>
      hz (by omega) h.symm
    -- the `workset` block `bS'`
    have hS' : 0 < capS' → bS' ≠ bg ∧ bS' ≠ bc ∧ bS' ≠ bl ∧ bS' ≠ bs ∧ bS' ≠ Block.nautilBit ∧
        bS' ≠ Block.leftbit ∧ bS' ≠ WP ∧ (0 < n → bS' ≠ bP') := fun hc => by
      rcases hbS' with ⟨hcc, rfl⟩ | hnv
      · have hcS : 0 < capS := by omega
        refine ⟨fun h => cG.2.2.2.2.2.2.2.2 hcS h.symm, fun h => cC.2.2.2.2.2.2.2.2 hcS h.symm,
          fun h => cL.2.2.2.2.2.2.2.2 hcS h.symm, fun h => cS.2.2.2.2.2.2.2.2 hcS h.symm,
          (hbS hcS).1, (hbS hcS).2.1, (hbS hcS).2.2.1, fun hn0 h => ?_⟩
        exact (hP' (by omega)).1.2.2 hcS h.symm
      · exact ⟨fun h => hnv (h ▸ hgP _ cG.1), fun h => hnv (h ▸ hgP _ cC.1),
          fun h => hnv (h ▸ hgP _ cL.1), fun h => hnv (h ▸ hgP _ cS.1),
          fun h => hnv (h ▸ hgP _ hvbit), fun h => hnv (h ▸ hgP _ hvlb),
          fun h => hnv (h ▸ hgP _ hvWP), fun hn0 h => hnv (h ▸ (hP' (by omega)).2)⟩
    have hcS0 : 0 < capS' := by omega
    have hS := hS' hcS0
    have hT3 : ∀ k, k ≠ id.t1 → k ≠ id.t2 → k ≠ id.t3 → k ≠ id.t4 → k ≠ id.i →
        PTree.get k le3 = PTree.get k (entryTemps bg gofs bc cofs bl lofs bs so M n) :=
      fun k h1 h2 h3 h4 h5 => by rw [ho3 k h5, hT2 k h1 h2 h3 h4]
    have hl3 : ∀ z chunk ofs, (¬ (z = WPS ∨ z = WP ∨ (0 < capP ∧ z = bP) ∨ (¬ Mem.valid_block m bP' ∧ z = bP')) ∧
        ¬ (z = WSS ∨ z = WS ∨ (0 < capS ∧ z = bS) ∨ (¬ Mem.valid_block m1 bS' ∧ z = bS'))) →
        ¬ (0 < n ∧ z = bP') → Mem.load chunk m3 z ofs = Mem.load chunk m z ofs := fun z chunk ofs h1 h2 => by
      rw [hu3.load _ _ _ h2, hu12 z h1]
    have ha3 : ∀ z chunk ofs p, (¬ (z = WPS ∨ z = WP ∨ (0 < capP ∧ z = bP) ∨ (¬ Mem.valid_block m bP' ∧ z = bP')) ∧
        ¬ (z = WSS ∨ z = WS ∨ (0 < capS ∧ z = bS) ∨ (¬ Mem.valid_block m1 bS' ∧ z = bS'))) →
        ¬ (0 < n ∧ z = bP') → Mem.valid_access m chunk z ofs p → Mem.valid_access m3 chunk z ofs p :=
      fun z chunk ofs p h1 h2 hv => hu3.access _ _ _ _ h2 (huS.access _ _ _ _ h1.2 (huP.access _ _ _ _ h1.1 hv))
    have pDis : ∀ z, Mem.valid_block m z → (0 < capP → z ≠ bP) → ¬ (0 < n ∧ z = bP') :=
      fun z hv hz => nb z fun hc e => by
        rcases hbP' with ⟨hcc, hbb⟩ | hnv
        · exact hz (by omega) (hbb ▸ e).symm
        · exact hnv (e ▸ hv)
    have nG := pDis bg cG.1 cG.2.2.2.2.2.2.2.1
    have nC := pDis bc cC.1 cC.2.2.2.2.2.2.2.1
    have nL := pDis bl cL.1 cL.2.2.2.2.2.2.2.1
    have nS := pDis bs cS.1 cS.2.2.2.2.2.2.2.1
    have nBit := pDis _ hvbit fun hc h => (hbP hc).1 h.symm
    have nLb := pDis _ hvlb fun hc h => (hbP hc).2.1 h.symm
    have nWP : ¬ (0 < n ∧ WP = bP') := nb _ fun hc => (hDP2.bne hc).2
    have nWS : ¬ (0 < n ∧ WS = bP') := nb _ fun hc => (hP' hc).1.1
    have hwarr3 : ArrayAt m3 .Mint32 bP' 0 (ints (invPerm lab)) n :=
      harr3.congr fun p hp => Updatecan.written_full lab n vals hlsz hsurj hp
    obtain ⟨wsv, hws2⟩ := Alloc.malloced_array (hDS'.mal hcS0) .Mint64 8 rfl rfl M
      (Nat.mul_le_mul_left 8 hcapS)
    have hws3 := hws2.unch hu3 (fun ⟨h0, h⟩ => hS.2.2.2.2.2.2.2 h0 h)
    have hf : Frame m3 le3 bg gofs gw grows bc cofs cw canong bl lofs lab bP' bS' bs so M :=
      { hg := by rw [hT3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hcan := by rw [hT3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
                   simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hlab := by rw [hT3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
                   simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hsr := by rw [hT3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
                  simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hm := by rw [hT3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hn := by rw [hT3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [entryTemps, temps_gss]
        graph := ⟨⟨hg.arr.base_nonneg, hg.arr.fits, fun i hi => by rw [hl3 _ _ _ bG nG]; exact hg.arr.load i hi,
          fun i hi => ha3 _ _ _ _ bG nG (hg.arr.writable i hi)⟩, hg.rep⟩
        cgraph := ⟨⟨hcg.arr.base_nonneg, hcg.arr.fits, fun i hi => by rw [hl3 _ _ _ bC nC]; exact hcg.arr.load i hi,
          fun i hi => ha3 _ _ _ _ bC nC (hcg.arr.writable i hi)⟩, hcg.rep⟩
        larr := hlarr2.unch hu3 nL
        lsmall := hls
        warr := hwarr3
        wsmall := Updatecan.invPerm_small lab n hlsz
        wptr := fun hn0 => by rw [hu3.load _ _ _ nWP]; exact hDP2.ptr (by omega)
        wsptr := by rw [hu3.load _ _ _ nWS]; exact hDS'.ptr hcS0
        lb := fun i hi => by rw [hl3 _ _ _ bLb nLb]; exact hlb i hi
        bit := fun i hi => by rw [hl3 _ _ _ bBit nBit]; exact hbit i hi
        sg := hS.1, sc := hS.2.1, sl := hS.2.2.1
        sW := hS.2.2.2.2.2.2.2
        sbit := hS.2.2.2.2.1, slb := hS.2.2.2.2.2.1, swp := hS.2.2.2.2.2.2.1
        sws := (hDS'.bne hcS0).2
        M1 := hM1, Mlt := hM2, nM := hnM }
    have hsarr3 : ArrayAt m3 .Mint32 bs (intOfZ (Ptrofs.unsigned so)) svals 1 :=
      ⟨hsarr.base_nonneg, hsarr.fits, fun i hi => by rw [hl3 _ _ _ bSr nS]; exact hsarr.load i hi,
        fun i hi => ha3 _ _ _ _ bSr nS (hsarr.writable i hi)⟩
    -- the postcondition, from the final memory
    let Sfin := fun z => z = bs ∨ z = WPS ∨ z = WP ∨ z = WSS ∨ z = WS ∨ (0 < capP ∧ z = bP) ∨
        (0 < capS ∧ z = bS) ∨ (¬ Mem.valid_block m bP' ∧ z = bP') ∨ (¬ Mem.valid_block m bS' ∧ z = bS')
    have hmapP : ∀ z, 0 < n ∧ z = bP' → Sfin z := by
      rintro z ⟨h0, rfl⟩
      rcases hbP' with ⟨hcc, hbb⟩ | hnv
      · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨by omega, hbb⟩)))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨hnv, rfl⟩)))))))
    have hmapS : ∀ z, z = bS' → Sfin z := by
      rintro z rfl
      rcases hbS' with ⟨hcc, hbb⟩ | hnv
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨by omega, hbb⟩))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨fun hv => hnv (hgP _ hv), rfl⟩)))))))
    have hU3 : Unch m m3 Sfin := by
      refine ((huP.mono fun z hz => ?_).trans (huS.mono fun z hz => ?_)).trans (hu3.mono hmapP)
      · rcases hz with h | h | h | h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
      · rcases hz with h | h | h | ⟨hnv, h⟩
        · exact .inr (.inr (.inr (.inl h)))
        · exact .inr (.inr (.inr (.inr (.inl h))))
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨fun hv => hnv (hgP _ hv), h⟩)))))))
    have hDP3 : DynAt m3 WP WPS 4 capP' bP' :=
      hDP2.keep hu3 nWP (nb _ fun hc => (hDP2.bne hc).1) fun _ => hk3
    have hDS3 : DynAt m3 WS WSS 8 capS' bS' :=
      hDS'.keep hu3 nWS (nb _ fun hc => (hP' hc).1.2.1) fun hc => Keep.unch hu3 fun ⟨h0, h⟩ =>
        hS.2.2.2.2.2.2.2 h0 h
    have post : ∀ m4 (r : Int) c, Hex.GraphIso.Nauty.testcanlab ⟨grows⟩ canong lab = (r, c) →
        ArrayAt m4 .Mint32 bs (intOfZ (Ptrofs.unsigned so)) (fun _ => .Vint (ir c)) 1 →
        Unch m3 m4 (fun z => z = bS' ∨ z = bs) → Keep m3 m4 bS' → Keep m3 m4 bs →
        (testcanlabSpec bg gofs gw grows bc cofs cw canong bl lofs lab bs so svals M capP bP capS bS).post
          [.Vptr bg gofs, .Vptr bc cofs, .Vptr bl lofs, .Vptr bs so, .Vint (ir M), .Vint (ir n)] m E0
          (.Vint (ir r)) m4 := by
      intro m4 r c hR harr4 hu4 hk4 hk4s
      show _ ∧ _
      simp only [hR]
      have hPS : 0 < capP' → bP' ≠ bS' := fun hc h => by
        rcases hbS' with ⟨_, hbb⟩ | hnv
        · exact (hP' hc).1.2.2 (by omega) (h.trans hbb)
        · exact hnv (h ▸ (hP' hc).2)
      have hPs : 0 < capP' → bP' ≠ bs := fun hc h => by
        rcases hbP' with ⟨_, hbb⟩ | hnv
        · exact cS.2.2.2.2.2.2.2.1 (by omega) (h.symm.trans hbb)
        · exact hnv (h ▸ cS.1)
      have hSWPS : bS' ≠ WPS := fun h => by
        rcases hbS' with ⟨_, hbb⟩ | hnv
        · exact (hbS (by omega)).2.2.2 (hbb ▸ h)
        · exact hnv (h ▸ hgP _ hvWPS)
      refine ⟨trivial, trivial, harr4,
        (((Keep.unch huP bSr.1).trans (Keep.unch huS bSr.2)).trans (Keep.unch hu3 nS)).trans hk4s,
        capP', bP', capS', bS',
        hDP3.keep hu4 ?_ ?_ fun hc => Keep.unch hu4 ?_,
        hDS3.keep hu4 ?_ ?_ fun _ => hk4, hcapP, hcapS, hbP', ?_, hPS,
        hU3.trans (hu4.mono fun z hz => ?_)⟩
      · rintro (h | h)
        · exact hS.2.2.2.2.2.2.1 h.symm
        · exact cS.2.1 h.symm
      · rintro (h | h)
        · exact hSWPS h.symm
        · exact cS.2.2.1 h.symm
      · rintro (h | h)
        · exact hPS hc h
        · exact hPs hc h
      · rintro (h | h)
        · exact (hDS'.bne hcS0).2 h.symm
        · exact cS.2.2.2.1 h.symm
      · rintro (h | h)
        · exact (hDS'.bne hcS0).1 h.symm
        · exact cS.2.2.2.2.1 h.symm
      · rcases hbS' with h | hnv
        · exact .inl h
        · exact .inr fun hv => hnv (hgP _ hv)
      · rcases hz with h | h
        · exact hmapS z h
        · exact .inl h
    wp_step
    refine wp_rows hf hws3 hsarr3 (Ne.symm hS.2.2.2.1) ?_ ?_
    · intro hT le' m' ws' _ hu' hk' hle'
      have hsarr' := hsarr3.unch hu' (Ne.symm hS.2.2.2.1)
      obtain ⟨m5, hst, harr5, -⟩ := store_array hsarr' (show 0 < 1 by decide) (.Vint (ir n)) rfl
      have harr5' : ArrayAt m5 .Mint32 bs (intOfZ (Ptrofs.unsigned so)) (fun _ => .Vint (ir n)) 1 :=
        harr5.congr fun i hi => by simp [upd, show i = 0 by omega]
      have h1 : PTree.get id.samerows le' = some (.Vptr bs so) := by
        rw [hle' _ (by decide) (by decide) (by decide)]; exact hf.hsr
      have h2 : PTree.get id.n le' = some (.Vint (ir n)) := by
        rw [hle' _ (by decide) (by decide) (by decide)]; exact hf.hn
      simp only [final, Set.sk]
      wp_step; wp_step; wp_step
      apply wp_assign_eval
      simp only [Exec.evalLvalue, Exec.evalExpr, h1, h2, typeof, cop, Exec.assignLoc,
        Cfrontend.Ctypes.access_mode, Mem.storev]
      rw [show Ptrofs.unsigned so = elemOfs .Mint32 (intOfZ (Ptrofs.unsigned so)) 0 by
        unfold elemOfs
        rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ], hst]
      wp_step; wp_step
      apply wp_return_some_eval
      simp only [Exec.evalExpr, typeof, cop, Source.dense.fn.testcanlab.fn_return_eq,
        Nextelement.free_empty]
      have hu5 : Unch m' m5 (· = bs) := Unch.store hst rfl
      exact post m5 0 n (by rw [testcanlab_eq]; exact hT) harr5'
        ((hu'.mono fun z hz => .inl hz).trans (hu5.mono fun z hz => .inr hz))
        (hk'.trans (Keep.unch hu5 hS.2.2.2.1))
        ((Keep.unch hu' fun e => hS.2.2.2.1 e.symm).trans (Keep.store hst (by
          have := hsarr3.base_nonneg
          simp only [elemOfs, intOfZ_zOfInt]; omega)))
    · intro m4 r c hT harr4 hu4 hk4 hk4s
      exact post m4 r c (by rw [testcanlab_eq]; exact hT) harr4 hu4 hk4 hk4s

end NautyVerified.Proofs.Testcanlab
