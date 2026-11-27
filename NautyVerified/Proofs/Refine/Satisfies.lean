import NautyVerified.Proofs.Refine.Finish
import NautyVerified.Proofs.Alloc.Dyn3

/-!
# `refine` satisfies its specification

`refineSpec`: called on memory holding HexGraphIso's partition `lab`, `ptn`,
active set and cell count (with the graph, a `count` array and a `code` cell),
nauty's general `refine` leaves memory holding `refine ctx level lab ptn
active numcells`: its labelling, partition, active set and cell count, and its
code in `*code`. The three `DYNALLSTAT` arrays may have been reallocated.

`refine_satisfies_of` proves it from the two splitting passes
(`TrivialPass`, `NontrivialPass`).
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep dyn3Set)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

/-- The facts about `refine`'s locations before its allocations. -/
structure PreOk (n : Nat) (L : Loc) : Prop where
  distinct : L.blocks.Pairwise (· ≠ ·)
  n0 : 0 < n
  nM : n ≤ 64 * L.M
  M1 : 0 < L.M
  Mlt : L.M < 33554432
  levlt : L.level < 2147483648
  nlt : n < 1073741824

/-- The state HexGraphIso's `refine` starts from. -/
def initSt {n : Nat} (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) : RefineSt n :=
  { lab, ptn, active, numcells, hint := 0, maxpos := 0, longcode := numcells }

/-- `L` with new work blocks and capacities. -/
def Loc.withWork (L : Loc) (capW : Nat) (bW : block) (capS : Nat) (bS : block) (capB : Nat)
    (bB : block) : Loc :=
  { L with capW, bW, capS, bS, capB, bB }

def refineSpec {n : Nat} (L : Loc) (ctx : Ctx n) (lab ptn : Array Nat) (active : VSet n)
    (numcells : Nat) (aw : Nat → Lib.Integers.int64) : FunSpec where
  pre args m := args = [.Vptr L.bg L.gofs, .Vptr L.bl L.lofs, .Vptr L.bp L.pofs,
      .Vint (ir L.level), .Vptr L.bn L.nofs, .Vptr L.bc L.cofs, .Vptr L.ba L.aofs,
      .Vptr L.bk L.kofs, .Vint (ir L.M), .Vint (ir n)] ∧
    PreOk n L ∧ Mem m L ctx (initSt lab ptn active numcells) aw ∧
    (∃ kv, ArrayAt m .Mint32 L.bk L.kb kv 1) ∧
    (∀ z ∈ [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk], Mem.valid_block m z) ∧
    StOk n L.level (initSt lab ptn active numcells) ∧ (∀ i < n, ptn[i]! < 2147483648) ∧
    numcells ≤ n
  post _ m t _ m' := t = E0 ∧ ∃ capW bW capS bS capB bB aw',
    Mem m' (L.withWork capW bW capS bS capB bB) ctx
      (refine ctx L.level lab ptn active numcells) aw' ∧
    ArrayAt m' .Mint32 L.bk L.kb
      (fun _ => .Vint (ir (refine ctx L.level lab ptn active numcells).longcode)) 1 ∧
    n ≤ capW ∧ L.M ≤ capS ∧ n + 2 ≤ capB ∧
    ((capW = L.capW ∧ bW = L.bW) ∨ ¬ Mem.valid_block m bW) ∧
    ((capS = L.capS ∧ bS = L.bS) ∨ ¬ Mem.valid_block m bS) ∧
    ((capB = L.capB ∧ bB = L.bB) ∨ ¬ Mem.valid_block m bB) ∧
    Unch m m' (fun z => L.writes z ∨ z = L.bk ∨ dyn3Set m L.capW L.bW L.capS L.bS L.capB L.bB z)

/-- The temporaries on entry. -/
def entryTemps (L : Loc) (n : Nat) : temp_env :=
  PTree.set dense.id.n (.Vint (ir n)) (PTree.set dense.id.m (.Vint (ir L.M))
    (PTree.set dense.id.code (.Vptr L.bk L.kofs) (PTree.set dense.id.active (.Vptr L.ba L.aofs)
      (PTree.set dense.id.count (.Vptr L.bc L.cofs) (PTree.set dense.id.numcells (.Vptr L.bn L.nofs)
        (PTree.set dense.id.level (.Vint (ir L.level)) (PTree.set dense.id.ptn (.Vptr L.bp L.pofs)
          (PTree.set dense.id.lab (.Vptr L.bl L.lofs) (PTree.set dense.id.g (.Vptr L.bg L.gofs)
            (create_undef_temps dense.fn.refine.fn_temps))))))))))

theorem Loc.blocks_eq (L : Loc) : L.blocks = [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk] ++
    [L.bW, L.bS, L.bB] ++
    [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
     Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
     Block.naugraphBit, Block.naugraphBytecount, Block.leftbit] := rfl

/-- After the allocations: `Ok` for the new work blocks. -/
theorem PreOk.withWork {n : Nat} {L : Loc} {m : mem} (hp : PreOk n L)
    (hv : ∀ z ∈ [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk] ++
      [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
       Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
       Block.naugraphBit, Block.naugraphBytecount, Block.leftbit], Mem.valid_block m z)
    {capW capS capB : Nat} {bW bS bB : block} (hcW : n ≤ capW) (hcS : L.M ≤ capS)
    (hcB : n + 2 ≤ capB)
    (hbW : (capW = L.capW ∧ bW = L.bW) ∨ ¬ Mem.valid_block m bW)
    (hbS : (capS = L.capS ∧ bS = L.bS) ∨ ¬ Mem.valid_block m bS)
    (hbB : (capB = L.capB ∧ bB = L.bB) ∨ ¬ Mem.valid_block m bB)
    (hWS : bW ≠ bS) (hWB : bW ≠ bB) (hSB : bS ≠ bB) :
    Ok n (L.withWork capW bW capS bS capB bB) := by
  have d := hp.distinct
  rw [Loc.blocks_eq, List.pairwise_append, List.pairwise_append] at d
  obtain ⟨⟨dA, -, dAN⟩, dG, dANG⟩ := d
  have hn0 := hp.n0
  refine { hp with distinct := ?_, capW := hcW, capS := hcS, capB := hcB }
  rw [Loc.blocks_eq, List.pairwise_append, List.pairwise_append]
  have hnew : ∀ z ∈ [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk] ++
      [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
       Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
       Block.naugraphBit, Block.naugraphBytecount, Block.leftbit],
      z ≠ bW ∧ z ≠ bS ∧ z ≠ bB := by
    intro z hz
    have hzv := hv z hz
    have hold : z ≠ L.bW ∧ z ≠ L.bS ∧ z ≠ L.bB := by
      rcases List.mem_append.1 hz with hz | hz
      · exact ⟨dAN z hz _ (by simp), dAN z hz _ (by simp), dAN z hz _ (by simp)⟩
      · exact ⟨fun h => dANG _ (List.mem_append.2 (.inr (by simp))) z hz h.symm,
          fun h => dANG _ (List.mem_append.2 (.inr (by simp))) z hz h.symm,
          fun h => dANG _ (List.mem_append.2 (.inr (by simp))) z hz h.symm⟩
    exact ⟨Alloc.ne_new hbW hzv (fun _ => hold.1) (by omega),
      Alloc.ne_new hbS hzv (fun _ => hold.2.1) (by have := hp.M1; omega),
      Alloc.ne_new hbB hzv (fun _ => hold.2.2) (by omega)⟩
  refine ⟨⟨dA, ?_, fun a ha b hb => ?_⟩, dG, fun a ha b hb => ?_⟩
  · simp [Loc.withWork, hWS, hWB, hSB]
  · have := hnew a (List.mem_append.2 (.inl ha))
    simp only [Loc.withWork, List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  · rcases List.mem_append.1 ha with ha | ha
    · exact dANG a (List.mem_append.2 (.inl ha)) b hb
    · have := hnew b (List.mem_append.2 (.inr hb))
      simp only [Loc.withWork, List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact Ne.symm this.1
      · exact Ne.symm this.2.1
      · exact Ne.symm this.2.2

/-- Caller blocks and tables are none of the blocks the allocations change. -/
theorem PreOk.notDyn {n : Nat} {L : Loc} {m : mem} (hp : PreOk n L) {z : block}
    (hz : z ∈ [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk] ∨
      z = Block.naugraphBit ∨ z = Block.naugraphBytecount ∨ z = Block.leftbit)
    (hv : Mem.valid_block m z) : ¬ dyn3Set m L.capW L.bW L.capS L.bS L.capB L.bB z := by
  have d := hp.distinct
  rw [Loc.blocks_eq, List.pairwise_append, List.pairwise_append] at d
  obtain ⟨⟨-, -, dAN⟩, dG, dANG⟩ := d
  have hG : ∀ g ∈ [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
      Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz], z ≠ g := by
    intro g hg
    rcases hz with hz | hz
    · exact dANG z (List.mem_append.2 (.inl hz)) g (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg ⊢
        rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    · rcases hz with rfl | rfl | rfl <;> simp at hg <;>
        rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hN : ∀ b ∈ [L.bW, L.bS, L.bB], z ≠ b := by
    intro b hb
    rcases hz with hz | hz
    · exact dAN z hz b hb
    · intro h
      exact dANG b (List.mem_append.2 (.inr hb)) z (by rcases hz with rfl | rfl | rfl <;> simp)
        h.symm
  unfold dyn3Set
  rintro (h | h | h | h | h | h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | h)
  · exact hG _ (by simp) h
  · exact hG _ (by simp) h
  · exact hG _ (by simp) h
  · exact hG _ (by simp) h
  · exact hG _ (by simp) h
  · exact hG _ (by simp) h
  · exact hN _ (by simp) h
  · exact hN _ (by simp) h
  · exact hN _ (by simp) h
  · exact h hv

/-- `Mem` across the allocations, with the new work blocks. -/
theorem Mem.withWork {n : Nat} {m m' : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} (hp : PreOk n L) (hm : Mem m L ctx st aw)
    (hv : ∀ z ∈ [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk], Mem.valid_block m z)
    (hu : Unch m m' (dyn3Set m L.capW L.bW L.capS L.bS L.capB L.bB))
    {capW capS capB : Nat} {bW bS bB : block}
    (hW : DynAt m' Block.naugraphWorkperm Block.naugraphWorkpermSz 4 capW bW)
    (hS : DynAt m' Block.naugraphWorkset Block.naugraphWorksetSz 8 capS bS)
    (hB : DynAt m' Block.naugraphBucket Block.naugraphBucketSz 4 capB bB) :
    Mem m' (L.withWork capW bW capS bS capB bB) ctx st aw := by
  have nd : ∀ z, z ∈ [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk] →
      ¬ dyn3Set m L.capW L.bW L.capS L.bS L.capB L.bB z := fun z hz => hp.notDyn (.inl hz) (hv z hz)
  have vbit : Mem.valid_block m Block.naugraphBit := by
    obtain h0 := hm.bit 0 (by decide)
    exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h0)
  have vbytes : Mem.valid_block m Block.naugraphBytecount := by
    obtain h0 := hm.bytes 0 (by decide)
    exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h0)
  have vleft : Mem.valid_block m Block.leftbit := by
    obtain h0 := hm.left 0 (by decide)
    exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h0)
  obtain ⟨cv, hcv⟩ := hm.cnt
  exact
    { graph := ⟨hm.graph.arr.unch hu (nd _ (by simp)), hm.graph.rep⟩
      lab := hm.lab.unch hu (nd _ (by simp))
      ptn := hm.ptn.unch hu (nd _ (by simp))
      nc := hm.nc.unch hu (nd _ (by simp))
      act := hm.act.unch hu (nd _ (by simp))
      actRep := hm.actRep
      cnt := ⟨cv, hcv.unch hu (nd _ (by simp))⟩
      dW := hW, dS := hS, dB := hB
      bit := hm.bit.unch hu (hp.notDyn (.inr (.inl rfl)) vbit)
      bytes := BytecountTable.unch hm.bytes hu (hp.notDyn (.inr (.inr (.inl rfl))) vbytes)
      left := LeftbitTable.unch hm.left hu (hp.notDyn (.inr (.inr (.inr rfl))) vleft) }

/-- Only the `code` cell changed: `Mem` holds. -/
theorem Mem.unchCode {n : Nat} {m m' : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} (hok : Ok n L) (hm : Mem m L ctx st aw)
    (hu : Unch m m' (· = L.bk)) : Mem m' L ctx st aw := by
  have d := hok.distinct
  obtain ⟨cv, hcv⟩ := hm.cnt
  exact
    { graph := ⟨hm.graph.arr.unch hu (pw_ne d 0 6 (by decide) (by simp [Loc.blocks])), hm.graph.rep⟩
      lab := hm.lab.unch hu (pw_ne d 1 6 (by decide) (by simp [Loc.blocks]))
      ptn := hm.ptn.unch hu (pw_ne d 2 6 (by decide) (by simp [Loc.blocks]))
      nc := hm.nc.unch hu (pw_ne d 3 6 (by decide) (by simp [Loc.blocks]))
      act := hm.act.unch hu (pw_ne d 5 6 (by decide) (by simp [Loc.blocks]))
      actRep := hm.actRep
      cnt := ⟨cv, hcv.unch hu (pw_ne d 4 6 (by decide) (by simp [Loc.blocks]))⟩
      dW := hm.dW.keep hu (Ne.symm (pw_ne d 6 10 (by decide) (by simp [Loc.blocks])))
        (Ne.symm (pw_ne d 6 11 (by decide) (by simp [Loc.blocks])))
        fun _ => Keep.unch hu (Ne.symm (pw_ne d 6 7 (by decide) (by simp [Loc.blocks])))
      dS := hm.dS.keep hu (Ne.symm (pw_ne d 6 12 (by decide) (by simp [Loc.blocks])))
        (Ne.symm (pw_ne d 6 13 (by decide) (by simp [Loc.blocks])))
        fun _ => Keep.unch hu (Ne.symm (pw_ne d 6 8 (by decide) (by simp [Loc.blocks])))
      dB := hm.dB.keep hu (Ne.symm (pw_ne d 6 14 (by decide) (by simp [Loc.blocks])))
        (Ne.symm (pw_ne d 6 15 (by decide) (by simp [Loc.blocks])))
        fun _ => Keep.unch hu (Ne.symm (pw_ne d 6 9 (by decide) (by simp [Loc.blocks])))
      bit := hm.bit.unch hu (Ne.symm (pw_ne d 6 16 (by decide) (by simp [Loc.blocks])))
      bytes := BytecountTable.unch hm.bytes hu (Ne.symm (pw_ne d 6 17 (by decide) (by simp [Loc.blocks])))
      left := LeftbitTable.unch hm.left hu (Ne.symm (pw_ne d 6 18 (by decide) (by simp [Loc.blocks]))) }

theorem refine_satisfies_of {xi : ExternalCalls} (hT : TrivialPass xi) (hN : NontrivialPass xi)
    {n : Nat} (L : Loc) (ctx : Ctx n) (lab ptn : Array Nat) (active : VSet n) (numcells : Nat)
    (aw : Nat → Lib.Integers.int64) :
    Satisfies xi ge (.Internal dense.fn.refine) (refineSpec L ctx lab ptn active numcells aw) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps L n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps L n, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hp, hm, ⟨kv, hk⟩, hv, hok0, hps, hnc⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [dense.fn.refine.fn_body_eq, body_eq]
    simp only [body]
    have d := hp.distinct
    rw [Loc.blocks_eq, List.pairwise_append, List.pairwise_append] at d
    obtain ⟨⟨dA, dN, dAN⟩, dG, dANG⟩ := d
    have dNG : ∀ b ∈ [L.bW, L.bS, L.bB], ∀ g ∈ [Block.naugraphWorkperm, Block.naugraphWorkpermSz,
        Block.naugraphWorkset, Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
        Block.naugraphBit, Block.naugraphBytecount, Block.leftbit], b ≠ g :=
      fun b hb g hg => dANG b (List.mem_append.2 (.inr hb)) g hg
    simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true] at dN dNG
    have hn0 := hp.n0
    have hnl := hp.nlt
    have hMl := hp.Mlt
    refine Alloc.wp_dyn3 (xn := dense.id.n) (xm := dense.id.m) (n := n) (M := L.M) hm.dW hm.dS hm.dB
      (by simp (config := {decide := true}) only [entryTemps, temps_gss])
      (by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      (by omega) (by omega) (by decide) (by decide)
      (fun _ => ⟨dNG.1.2.2.1, dNG.1.2.2.2.1, dNG.1.2.2.2.2.1, dNG.1.2.2.2.2.2.1, fun _ => dN.1.1,
        fun _ => dN.1.2⟩)
      (fun _ => ⟨dNG.2.1.1, dNG.2.1.2.1, dNG.2.1.2.2.2.2.1, dNG.2.1.2.2.2.2.2.1, fun _ => dN.2.1⟩)
      (fun _ => ⟨dNG.2.2.1, dNG.2.2.2.1, dNG.2.2.2.2.1, dNG.2.2.2.2.2.1⟩) ?_
    intro le3 m3 capW bW capS bS capB bB hW hS hB hcW hcS hcB hbW hbS hbB hg3 ho3 hu3 hWS hWB hSB
    have hvG : ∀ z ∈ [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk] ++
        [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
         Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
         Block.naugraphBit, Block.naugraphBytecount, Block.leftbit], Mem.valid_block m z := by
      intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · exact hv z hz
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Alloc.valid_of_access hm.dW.bpW
        · exact Alloc.valid_of_access hm.dW.bsW
        · exact Alloc.valid_of_access hm.dS.bpW
        · exact Alloc.valid_of_access hm.dS.bsW
        · exact Alloc.valid_of_access hm.dB.bpW
        · exact Alloc.valid_of_access hm.dB.bsW
        · exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ (hm.bit 0 (by decide)))
        · exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ (hm.bytes 0 (by decide)))
        · exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ (hm.left 0 (by decide)))
    have hok : Ok n (L.withWork capW bW capS bS capB bB) :=
      hp.withWork hvG hcW hcS hcB hbW hbS hbB (hWS (by omega) (by have := hp.M1; omega))
        (hWB (by omega) (by omega)) (hSB (by have := hp.M1; omega) (by omega))
    have hm3 := hm.withWork hp hv hu3 hW hS hB
    have hT3 : ∀ k, k ≠ idOf 703 → k ≠ idOf 704 → k ≠ idOf 705 → k ≠ idOf 706 → k ≠ idOf 707 →
        k ≠ idOf 708 → PTree.get k le3 = PTree.get k (entryTemps L n) := ho3
    have hnc3 : Exec.evalExpr ge empty_env le3 m3 (.Ederef (pi dense.id.numcells) tint) =
        some (.Vint (ir numcells)) := by
      simp only [Exec.evalExpr, pi]
      rw [hT3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode]
      apply load_array hm3.nc (show 0 < 1 by decide)
      unfold elemOfs
      rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, Loc.withWork, Loc.nb,
        zOfInt_intOfZ]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, hnc3]
    simp only [typeof, cop, cast_int_long_ir (a := numcells) ⟨by omega, by omega⟩]
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop]
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr]
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr]
    simp only [seqPost, Post.after, E0_append]
    wp_step
    let st₀ : RefineSt n := initSt lab ptn active numcells
    have ht4 : Tmp (PTree.set dense.id.maxpos (.Vint (ir 0)) (PTree.set dense.id.hint (.Vint (ir 0))
        (PTree.set dense.id.split1 (.Vint (Lib.Integers.Int.neg (ir 1)))
          (PTree.set dense.id.longcode (.Vlong (lr numcells)) le3)))) (L.withWork capW bW capS bS capB bB)
        st₀ := by
      constructor <;>
        (simp (config := {decide := true}) only [temps_gso, temps_gss, Loc.withWork, st₀, initSt]) <;>
        (rw [hT3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]) <;>
        (simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
    have hi0 : StInv n (L.withWork capW bW capS bS capB bB) st₀ :=
      { ok := hok0, ptnSmall := hps, ncSmall := by simp [st₀, initSt]; omega
        hint := hn0, maxpos := hn0, code := by simp [st₀, initSt]; omega }
    refine wp_mainLoop hT hN hok ⟨aw, hm3, ht4, hi0⟩ ?_
    intro le5 m5 ⟨aw5, hm5, ht5, hi5⟩ hu5
    have hkn : ¬ dyn3Set m L.capW L.bW L.capS L.bS L.capB L.bB L.bk :=
      hp.notDyn (.inl (by simp)) (hv _ (by simp))
    have hkw : ¬ (L.withWork capW bW capS bS capB bB).writes L.bk := by
      have := hok.distinct
      rintro (h | h | h | h | h | h | h | h)
      · exact pw_ne this 1 6 (by decide) (by simp [Loc.blocks]) h.symm
      · exact pw_ne this 2 6 (by decide) (by simp [Loc.blocks]) h.symm
      · exact pw_ne this 3 6 (by decide) (by simp [Loc.blocks]) h.symm
      · exact pw_ne this 4 6 (by decide) (by simp [Loc.blocks]) h.symm
      · exact pw_ne this 5 6 (by decide) (by simp [Loc.blocks]) h.symm
      · exact pw_ne this 6 7 (by decide) (by simp [Loc.blocks]) h
      · exact pw_ne this 6 8 (by decide) (by simp [Loc.blocks]) h
      · exact pw_ne this 6 9 (by decide) (by simp [Loc.blocks]) h
    have hk5 : ArrayAt m5 .Mint32 L.bk L.kb kv 1 := (hk.unch hu3 hkn).unch hu5 hkw
    refine wp_finish hok hm5 ht5 hi5 (kv := kv) hk5 ?_
    intro m6 harr6 hu6
    have hpos : 0 < capW ∧ 0 < capS ∧ 0 < capB := ⟨by omega, by have := hp.M1; omega, by omega⟩
    have hnew : ∀ {cap cap' : Nat} {b b' : block}, 0 < cap' →
        ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') → ∀ z, z = b' →
        (0 < cap ∧ z = b) ∨ ¬ Mem.valid_block m z := by
      rintro cap cap' b b' hc (⟨rfl, rfl⟩ | hnv) z rfl
      · exact .inl ⟨hc, rfl⟩
      · exact .inr hnv
    refine ⟨m6, Nextelement.free_empty m6, by simp, capW, bW, capS, bS, capB, bB, aw5,
      (hm5.unchCode hok hu6).congr rfl rfl rfl rfl, harr6, hcW, hcS, hcB, hbW, hbS, hbB, ?_⟩
    refine ((hu3.mono fun z hz => .inr (.inr hz)).trans (hu5.mono fun z hz => ?_)).trans
      (hu6.mono fun z hz => .inr (.inl hz))
    unfold dyn3Set
    rcases hz with h | h | h | h | h | h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inl (.inr (.inr (.inl h)))
    · exact .inl (.inr (.inr (.inr (.inl h))))
    · exact .inl (.inr (.inr (.inr (.inr (.inl h)))))
    · rcases hnew hpos.1 hbW z h with h' | h'
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h'))))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h'))))))))))
    · rcases hnew hpos.2.1 hbS z h with h' | h'
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h')))))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h'))))))))))
    · rcases hnew hpos.2.2 hbB z h with h' | h'
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h'))))))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h'))))))))))

end NautyVerified.Proofs.Refine
