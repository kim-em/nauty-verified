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
      (fun _ => .Vint (ir ((Hex.GraphIso.Nauty.testcanlab ⟨grows⟩ canong lab).2 : Int))) 1 ∧
    ∃ capP' bP' capS' bS', DynAt m' WP WPS 4 capP' bP' ∧ DynAt m' WS WSS 8 capS' bS' ∧
      n ≤ capP' ∧ M ≤ capS' ∧
      ((capP' = capP ∧ bP' = bP) ∨ ¬ Mem.valid_block m bP') ∧
      ((capS' = capS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS') ∧
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
    sorry

end NautyVerified.Proofs.Testcanlab
