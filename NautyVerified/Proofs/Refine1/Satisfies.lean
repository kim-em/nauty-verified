import NautyVerified.Proofs.Refine.Satisfies
import NautyVerified.Proofs.Refine.Trivial
import NautyVerified.Proofs.Refine.Fn
import NautyVerified.Proofs.Alloc.Dyn2

/-!
# `refine1` satisfies `refine`'s specification

`refine1_satisfies_of`: for `m = 1`, `refine1` satisfies `refineSpec`, given
its nontrivial-splitter pass (`NontrivialPass1`). Its two allocations are
`wp_dyn2`; naugraph's `workset` is not touched, and when its capacity is 0
the proof works with a block not valid after the allocations in its place,
which `DynAt` allows. The loop is `wp_mainLoopG` in dialect `D1`, with the
trivial pass `wp_trivial1`. `refineFn_refine1`: `refine1` as a refinement
procedure for one-word sets.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs
open NautyVerified.Proofs.Set (longs BitTable)
open NautyVerified.Proofs.Alloc (DynAt Keep dyn3Set)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

/-- A `DYNALLSTAT` pair of capacity 0 says nothing about its block. -/
theorem _root_.NautyVerified.Proofs.Alloc.DynAt.reblock {m : mem} {bp bs : block} {c cap : Nat}
    {b : block} (h : DynAt m bp bs c cap b) (h0 : cap = 0) (b' : block) : DynAt m bp bs c cap b' :=
  { h with
    ptr := fun hc => absurd hc (by omega)
    mal := fun hc => absurd hc (by omega)
    bne := fun hc => absurd hc (by omega) }

/-- After the allocations: `Ok` for the new work blocks, with no condition on the
workset's capacity. -/
theorem PreOk.withWork' {n : Nat} {L : Loc} {m : mem} (hp : PreOk n L)
    (hv : ∀ z ∈ [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk] ++
      [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
       Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
       Block.naugraphBit, Block.naugraphBytecount, Block.leftbit], Mem.valid_block m z)
    {capW capS capB : Nat} {bW bS bB : block} (hcW : n ≤ capW) (hcB : n + 2 ≤ capB)
    (hbW : (capW = L.capW ∧ bW = L.bW) ∨ ¬ Mem.valid_block m bW)
    (hbS : (capS = L.capS ∧ bS = L.bS) ∨ ¬ Mem.valid_block m bS)
    (hbB : (capB = L.capB ∧ bB = L.bB) ∨ ¬ Mem.valid_block m bB)
    (hWS : bW ≠ bS) (hWB : bW ≠ bB) (hSB : bS ≠ bB) :
    Ok n (L.withWork capW bW capS bS capB bB) := by
  have d := hp.distinct
  rw [Loc.blocks_eq, List.pairwise_append, List.pairwise_append] at d
  obtain ⟨⟨dA, -, dAN⟩, dG, dANG⟩ := d
  have hn0 := hp.n0
  refine { hp with distinct := ?_, capW := hcW, capB := hcB }
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
    have side : ∀ {cap cap' : Nat} {b b' : block}, ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') →
        z ≠ b → z ≠ b' := by
      rintro cap cap' b b' (⟨-, rfl⟩ | hnv) hb
      · exact hb
      · exact fun h => hnv (h ▸ hzv)
    exact ⟨side hbW hold.1, side hbS hold.2.1, side hbB hold.2.2⟩
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

/-- `refine1`'s nontrivial-splitter pass, on every location with one-word sets. -/
def NontrivialPass1 (xi : ExternalCalls) : Prop :=
  ∀ {n : Nat} {L : Loc} {ctx : Ctx n}, Ok n L → L.M = 1 →
    NontrivialPassAt xi dense.fn.refine1 Refine1.nontrivial L ctx

/-- `refine1`'s temporaries on entry. -/
def entryTemps1 (L : Loc) (n : Nat) : temp_env :=
  PTree.set dense.id.n (.Vint (ir n)) (PTree.set dense.id.m (.Vint (ir L.M))
    (PTree.set dense.id.code (.Vptr L.bk L.kofs) (PTree.set dense.id.active (.Vptr L.ba L.aofs)
      (PTree.set dense.id.count (.Vptr L.bc L.cofs) (PTree.set dense.id.numcells (.Vptr L.bn L.nofs)
        (PTree.set dense.id.level (.Vint (ir L.level)) (PTree.set dense.id.ptn (.Vptr L.bp L.pofs)
          (PTree.set dense.id.lab (.Vptr L.bl L.lofs) (PTree.set dense.id.g (.Vptr L.bg L.gofs)
            (create_undef_temps dense.fn.refine1.fn_temps))))))))))

theorem refine1_satisfies_of {xi : ExternalCalls} (hN : NontrivialPass1 xi)
    {n : Nat} (L : Loc) (hL : L.M = 1) (ctx : Ctx n) (lab ptn : Array Nat) (active : VSet n)
    (numcells : Nat) (aw : Nat → Lib.Integers.int64) :
    Satisfies xi ge (.Internal dense.fn.refine1) (refineSpec L ctx lab ptn active numcells aw) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps1 L n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps1 L n, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hp, hm, ⟨kv, hk⟩, hv, hok0, hps, hnc⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [dense.fn.refine1.fn_body_eq, Refine1.body_eq]
    simp only [Refine1.body]
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
    refine Alloc.wp_dyn2 (xn := dense.id.n) (n := n) hm.dW hm.dS hm.dB
      (by simp (config := {decide := true}) only [entryTemps1, temps_gss])
      (by omega) (by decide)
      (fun _ => ⟨dNG.1.2.2.1, dNG.1.2.2.2.1, dNG.1.2.2.2.2.1, dNG.1.2.2.2.2.2.1, fun _ => dN.1.1,
        fun _ => dN.1.2⟩)
      (fun _ => ⟨dNG.2.1.1, dNG.2.1.2.1, dNG.2.1.2.2.2.2.1, dNG.2.1.2.2.2.2.2.1, fun _ => dN.2.1⟩)
      (fun _ => ⟨dNG.2.2.1, dNG.2.2.2.1, dNG.2.2.2.2.1, dNG.2.2.2.2.2.1⟩) ?_
    intro le3 m3 capW bW capB bB hW hS hB hcW hcB hbW hbB hg3 ho3 hu3 hWS hWB hSB
    -- the workset is not touched; when its capacity is 0 its block is any block, and a block
    -- not valid in `m3` keeps `Ok`'s distinctness
    let bS : block := if 0 < L.capS then L.bS else Mem.nextblock m3
    have hS' : DynAt m3 Block.naugraphWorkset Block.naugraphWorksetSz 8 L.capS bS := by
      by_cases hc : 0 < L.capS
      · rw [show bS = L.bS from ite_eq_left hc]; exact hS
      · rw [show bS = Mem.nextblock m3 from ite_eq_right hc]; exact hS.reblock (by omega) _
    have hnv : ¬ 0 < L.capS → ¬ Mem.valid_block m3 bS := fun hc => by
      rw [show bS = Mem.nextblock m3 from ite_eq_right hc]; exact CompCert4Lean.Lib.Coqlib.Plt_strict _
    have hbS : (L.capS = L.capS ∧ bS = L.bS) ∨ ¬ Mem.valid_block m bS := by
      by_cases hc : 0 < L.capS
      · exact .inl ⟨rfl, by simp [bS, hc]⟩
      · exact .inr fun h => hnv hc (hg3 _ h)
    have hWS' : bW ≠ bS := by
      by_cases hc : 0 < L.capS
      · have := hWS (by omega) hc; simpa [bS, hc] using this
      · exact fun h => hnv hc (h ▸ Alloc.Malloced.valid (hW.mal (by omega)))
    have hSB' : bS ≠ bB := by
      by_cases hc : 0 < L.capS
      · have := hSB hc (by omega); simpa [bS, hc] using this
      · exact fun h => hnv hc (h ▸ Alloc.Malloced.valid (hB.mal (by omega)))
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
    have hok : Ok n (L.withWork capW bW L.capS bS capB bB) :=
      hp.withWork' hvG hcW hcB hbW hbS hbB hWS' (hWB (by omega) (by omega)) hSB'
    have hm3 := hm.withWork hp hv hu3 hW hS' hB
    have hT3 : ∀ k, k ≠ idOf 703 → k ≠ idOf 704 → k ≠ idOf 705 → k ≠ idOf 706 →
        PTree.get k le3 = PTree.get k (entryTemps1 L n) := ho3
    have hnc3 : Exec.evalExpr ge empty_env le3 m3 (.Ederef (pi dense.id.numcells) tint) =
        some (.Vint (ir numcells)) := by
      simp only [Exec.evalExpr, pi]
      rw [hT3 _ (by decide) (by decide) (by decide) (by decide)]
      simp (config := {decide := true}) only [entryTemps1, temps_gso, temps_gss, Exec.derefLoc,
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
    have ht4 : Tmp (PTree.set dense.id.hint (.Vint (ir 0)) (PTree.set dense.id.maxpos (.Vint (ir 0))
        (PTree.set dense.id.split1 (.Vint (Lib.Integers.Int.neg (ir 1)))
          (PTree.set dense.id.longcode (.Vlong (lr numcells)) le3)))) (L.withWork capW bW L.capS bS capB bB)
        st₀ := by
      constructor <;>
        (simp (config := {decide := true}) only [temps_gso, temps_gss, Loc.withWork, st₀, initSt]) <;>
        (rw [hT3 _ (by decide) (by decide) (by decide) (by decide)]) <;>
        (simp (config := {decide := true}) only [entryTemps1, temps_gso, temps_gss])
    have hi0 : StInv n (L.withWork capW bW L.capS bS capB bB) st₀ :=
      { ok := hok0, ptnSmall := hps, ncSmall := by simp [st₀, initSt]; omega
        hint := hn0, maxpos := hn0, code := by simp [st₀, initSt]; omega }
    have hM1 : D1.okM (L.withWork capW bW L.capS bS capB bB).M := hL
    refine wp_mainLoopG D1_sem (by decide) hM1 hok (fun hm ht hi hnc hs hsp hQ =>
        wp_trivial1 hM1 hok hm ht hi hnc hs hsp hQ) (hN hok hL) ⟨aw, hm3, ht4, hi0⟩ ?_
    intro le5 m5 ⟨aw5, hm5, ht5, hi5⟩ hu5 hkA5
    have hkn : ¬ dyn3Set m L.capW L.bW L.capS L.bS L.capB L.bB L.bk :=
      hp.notDyn (.inl (by simp)) (hv _ (by simp))
    have hkw : ¬ (L.withWork capW bW L.capS bS capB bB).writes L.bk := by
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
    intro m6 harr6 hu6 hkA6
    have hpos : 0 < capW ∧ 0 < capB := ⟨by omega, by omega⟩
    have hnew : ∀ {cap cap' : Nat} {b b' : block}, 0 < cap' →
        ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') → ∀ z, z = b' →
        (0 < cap ∧ z = b) ∨ ¬ Mem.valid_block m z := by
      rintro cap cap' b b' hc (⟨rfl, rfl⟩ | hnv) z rfl
      · exact .inl ⟨hc, rfl⟩
      · exact .inr hnv
    refine ⟨m6, Nextelement.free_empty m6, by simp, capW, bW, L.capS, bS, capB, bB, aw5,
      (hm5.unchCode hok hu6).congr rfl rfl rfl rfl, harr6, hcW, hcB, hbW, hbS, hbB,
      hWS', hWB (by omega) (by omega), hSB', ?_,
      fun z hz => ((Keep.unch hu3 (hp.notDyn (.inl (List.mem_cons_of_mem _ hz))
        (hv z (List.mem_cons_of_mem _ hz))) : Keep m m3 z).trans (hkA5 z)).trans (hkA6 z)⟩
    refine ((hu3.mono fun z hz => .inr (.inr hz)).trans (hu5.mono fun z hz => ?_)).trans
      (hu6.mono fun z hz => .inr (.inl hz))
    unfold dyn3Set
    rcases hz with h | h | h | h | h | h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inl (.inr (.inr (.inl h)))
    · exact .inl (.inr (.inr (.inr (.inl h))))
    · exact .inl (.inr (.inr (.inr (.inr h))))
    · rcases hnew hpos.1 hbW z h with h' | h'
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h'))))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h'))))))))))
    · by_cases hc : 0 < L.capS
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
          ⟨hc, h.trans (show bS = L.bS from ite_eq_left hc)⟩)))))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (h ▸ fun hv => hnv hc (hg3 _ hv))))))))))))
    · rcases hnew hpos.2 hbB z h with h' | h'
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h'))))))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h'))))))))))


/-- `refine1` is a refinement procedure for one-word sets. -/
theorem refineFn_refine1 {xi : ExternalCalls} (hN : NontrivialPass1 xi) :
    RefineFn xi 1 (.Vptr Block.refine1 Ptrofs.zero) :=
  ⟨_, by simp [Genv.find_funct, funct_refine1], rfl,
    fun L hL ctx lab ptn active numcells aw => refine1_satisfies_of hN L hL ctx lab ptn active numcells aw⟩

end NautyVerified.Proofs.Refine
