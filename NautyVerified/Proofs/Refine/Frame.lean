import NautyVerified.Proofs.Refine.Step

/-!
# Frame facts for the nontrivial pass

`WDist L`: the blocks a pass writes (`L.writes`) are pairwise distinct, and
distinct from the graph, the globals and the tables. `Mem.frame` rebuilds
`Mem` after a pass from the new contents of the written blocks, given that
every other block is unchanged and the three work blocks keep their headers.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs NautyVerified.Proofs.Alloc
open NautyVerified.Proofs.Set (longs BitTable)
open Hex.GraphIso.Nauty

/-- Distinctness of the written blocks among themselves and from the rest. -/
structure WDist (L : Loc) : Prop where
  bl_bp : L.bl ≠ L.bp
  bl_bn : L.bl ≠ L.bn
  bl_bc : L.bl ≠ L.bc
  bl_ba : L.bl ≠ L.ba
  bl_bW : L.bl ≠ L.bW
  bl_bS : L.bl ≠ L.bS
  bl_bB : L.bl ≠ L.bB
  bp_bn : L.bp ≠ L.bn
  bp_bc : L.bp ≠ L.bc
  bp_ba : L.bp ≠ L.ba
  bp_bW : L.bp ≠ L.bW
  bp_bS : L.bp ≠ L.bS
  bp_bB : L.bp ≠ L.bB
  bn_bc : L.bn ≠ L.bc
  bn_ba : L.bn ≠ L.ba
  bn_bW : L.bn ≠ L.bW
  bn_bS : L.bn ≠ L.bS
  bn_bB : L.bn ≠ L.bB
  bc_ba : L.bc ≠ L.ba
  bc_bW : L.bc ≠ L.bW
  bc_bS : L.bc ≠ L.bS
  bc_bB : L.bc ≠ L.bB
  ba_bW : L.ba ≠ L.bW
  ba_bS : L.ba ≠ L.bS
  ba_bB : L.ba ≠ L.bB
  bW_bS : L.bW ≠ L.bS
  bW_bB : L.bW ≠ L.bB
  bS_bB : L.bS ≠ L.bB
  bg_bl : L.bg ≠ L.bl
  bl_g0 : L.bl ≠ Block.naugraphWorkperm
  bl_g1 : L.bl ≠ Block.naugraphWorkpermSz
  bl_g2 : L.bl ≠ Block.naugraphWorkset
  bl_g3 : L.bl ≠ Block.naugraphWorksetSz
  bl_g4 : L.bl ≠ Block.naugraphBucket
  bl_g5 : L.bl ≠ Block.naugraphBucketSz
  bl_g6 : L.bl ≠ Block.naugraphBit
  bl_g7 : L.bl ≠ Block.naugraphBytecount
  bl_g8 : L.bl ≠ Block.leftbit
  bg_bp : L.bg ≠ L.bp
  bp_g0 : L.bp ≠ Block.naugraphWorkperm
  bp_g1 : L.bp ≠ Block.naugraphWorkpermSz
  bp_g2 : L.bp ≠ Block.naugraphWorkset
  bp_g3 : L.bp ≠ Block.naugraphWorksetSz
  bp_g4 : L.bp ≠ Block.naugraphBucket
  bp_g5 : L.bp ≠ Block.naugraphBucketSz
  bp_g6 : L.bp ≠ Block.naugraphBit
  bp_g7 : L.bp ≠ Block.naugraphBytecount
  bp_g8 : L.bp ≠ Block.leftbit
  bg_bn : L.bg ≠ L.bn
  bn_g0 : L.bn ≠ Block.naugraphWorkperm
  bn_g1 : L.bn ≠ Block.naugraphWorkpermSz
  bn_g2 : L.bn ≠ Block.naugraphWorkset
  bn_g3 : L.bn ≠ Block.naugraphWorksetSz
  bn_g4 : L.bn ≠ Block.naugraphBucket
  bn_g5 : L.bn ≠ Block.naugraphBucketSz
  bn_g6 : L.bn ≠ Block.naugraphBit
  bn_g7 : L.bn ≠ Block.naugraphBytecount
  bn_g8 : L.bn ≠ Block.leftbit
  bg_bc : L.bg ≠ L.bc
  bc_g0 : L.bc ≠ Block.naugraphWorkperm
  bc_g1 : L.bc ≠ Block.naugraphWorkpermSz
  bc_g2 : L.bc ≠ Block.naugraphWorkset
  bc_g3 : L.bc ≠ Block.naugraphWorksetSz
  bc_g4 : L.bc ≠ Block.naugraphBucket
  bc_g5 : L.bc ≠ Block.naugraphBucketSz
  bc_g6 : L.bc ≠ Block.naugraphBit
  bc_g7 : L.bc ≠ Block.naugraphBytecount
  bc_g8 : L.bc ≠ Block.leftbit
  bg_ba : L.bg ≠ L.ba
  ba_g0 : L.ba ≠ Block.naugraphWorkperm
  ba_g1 : L.ba ≠ Block.naugraphWorkpermSz
  ba_g2 : L.ba ≠ Block.naugraphWorkset
  ba_g3 : L.ba ≠ Block.naugraphWorksetSz
  ba_g4 : L.ba ≠ Block.naugraphBucket
  ba_g5 : L.ba ≠ Block.naugraphBucketSz
  ba_g6 : L.ba ≠ Block.naugraphBit
  ba_g7 : L.ba ≠ Block.naugraphBytecount
  ba_g8 : L.ba ≠ Block.leftbit
  bg_bW : L.bg ≠ L.bW
  bW_g0 : L.bW ≠ Block.naugraphWorkperm
  bW_g1 : L.bW ≠ Block.naugraphWorkpermSz
  bW_g2 : L.bW ≠ Block.naugraphWorkset
  bW_g3 : L.bW ≠ Block.naugraphWorksetSz
  bW_g4 : L.bW ≠ Block.naugraphBucket
  bW_g5 : L.bW ≠ Block.naugraphBucketSz
  bW_g6 : L.bW ≠ Block.naugraphBit
  bW_g7 : L.bW ≠ Block.naugraphBytecount
  bW_g8 : L.bW ≠ Block.leftbit
  bg_bS : L.bg ≠ L.bS
  bS_g0 : L.bS ≠ Block.naugraphWorkperm
  bS_g1 : L.bS ≠ Block.naugraphWorkpermSz
  bS_g2 : L.bS ≠ Block.naugraphWorkset
  bS_g3 : L.bS ≠ Block.naugraphWorksetSz
  bS_g4 : L.bS ≠ Block.naugraphBucket
  bS_g5 : L.bS ≠ Block.naugraphBucketSz
  bS_g6 : L.bS ≠ Block.naugraphBit
  bS_g7 : L.bS ≠ Block.naugraphBytecount
  bS_g8 : L.bS ≠ Block.leftbit
  bg_bB : L.bg ≠ L.bB
  bB_g0 : L.bB ≠ Block.naugraphWorkperm
  bB_g1 : L.bB ≠ Block.naugraphWorkpermSz
  bB_g2 : L.bB ≠ Block.naugraphWorkset
  bB_g3 : L.bB ≠ Block.naugraphWorksetSz
  bB_g4 : L.bB ≠ Block.naugraphBucket
  bB_g5 : L.bB ≠ Block.naugraphBucketSz
  bB_g6 : L.bB ≠ Block.naugraphBit
  bB_g7 : L.bB ≠ Block.naugraphBytecount
  bB_g8 : L.bB ≠ Block.leftbit

theorem Ok.wd {n : Nat} {L : Loc} (h : Ok n L) : WDist L where
  bl_bp := pw_ne h.distinct 1 2 (by decide) (by simp [Loc.blocks])
  bl_bn := pw_ne h.distinct 1 3 (by decide) (by simp [Loc.blocks])
  bl_bc := pw_ne h.distinct 1 4 (by decide) (by simp [Loc.blocks])
  bl_ba := pw_ne h.distinct 1 5 (by decide) (by simp [Loc.blocks])
  bl_bW := pw_ne h.distinct 1 7 (by decide) (by simp [Loc.blocks])
  bl_bS := pw_ne h.distinct 1 8 (by decide) (by simp [Loc.blocks])
  bl_bB := pw_ne h.distinct 1 9 (by decide) (by simp [Loc.blocks])
  bp_bn := pw_ne h.distinct 2 3 (by decide) (by simp [Loc.blocks])
  bp_bc := pw_ne h.distinct 2 4 (by decide) (by simp [Loc.blocks])
  bp_ba := pw_ne h.distinct 2 5 (by decide) (by simp [Loc.blocks])
  bp_bW := pw_ne h.distinct 2 7 (by decide) (by simp [Loc.blocks])
  bp_bS := pw_ne h.distinct 2 8 (by decide) (by simp [Loc.blocks])
  bp_bB := pw_ne h.distinct 2 9 (by decide) (by simp [Loc.blocks])
  bn_bc := pw_ne h.distinct 3 4 (by decide) (by simp [Loc.blocks])
  bn_ba := pw_ne h.distinct 3 5 (by decide) (by simp [Loc.blocks])
  bn_bW := pw_ne h.distinct 3 7 (by decide) (by simp [Loc.blocks])
  bn_bS := pw_ne h.distinct 3 8 (by decide) (by simp [Loc.blocks])
  bn_bB := pw_ne h.distinct 3 9 (by decide) (by simp [Loc.blocks])
  bc_ba := pw_ne h.distinct 4 5 (by decide) (by simp [Loc.blocks])
  bc_bW := pw_ne h.distinct 4 7 (by decide) (by simp [Loc.blocks])
  bc_bS := pw_ne h.distinct 4 8 (by decide) (by simp [Loc.blocks])
  bc_bB := pw_ne h.distinct 4 9 (by decide) (by simp [Loc.blocks])
  ba_bW := pw_ne h.distinct 5 7 (by decide) (by simp [Loc.blocks])
  ba_bS := pw_ne h.distinct 5 8 (by decide) (by simp [Loc.blocks])
  ba_bB := pw_ne h.distinct 5 9 (by decide) (by simp [Loc.blocks])
  bW_bS := pw_ne h.distinct 7 8 (by decide) (by simp [Loc.blocks])
  bW_bB := pw_ne h.distinct 7 9 (by decide) (by simp [Loc.blocks])
  bS_bB := pw_ne h.distinct 8 9 (by decide) (by simp [Loc.blocks])
  bg_bl := pw_ne h.distinct 0 1 (by decide) (by simp [Loc.blocks])
  bl_g0 := pw_ne h.distinct 1 10 (by decide) (by simp [Loc.blocks])
  bl_g1 := pw_ne h.distinct 1 11 (by decide) (by simp [Loc.blocks])
  bl_g2 := pw_ne h.distinct 1 12 (by decide) (by simp [Loc.blocks])
  bl_g3 := pw_ne h.distinct 1 13 (by decide) (by simp [Loc.blocks])
  bl_g4 := pw_ne h.distinct 1 14 (by decide) (by simp [Loc.blocks])
  bl_g5 := pw_ne h.distinct 1 15 (by decide) (by simp [Loc.blocks])
  bl_g6 := pw_ne h.distinct 1 16 (by decide) (by simp [Loc.blocks])
  bl_g7 := pw_ne h.distinct 1 17 (by decide) (by simp [Loc.blocks])
  bl_g8 := pw_ne h.distinct 1 18 (by decide) (by simp [Loc.blocks])
  bg_bp := pw_ne h.distinct 0 2 (by decide) (by simp [Loc.blocks])
  bp_g0 := pw_ne h.distinct 2 10 (by decide) (by simp [Loc.blocks])
  bp_g1 := pw_ne h.distinct 2 11 (by decide) (by simp [Loc.blocks])
  bp_g2 := pw_ne h.distinct 2 12 (by decide) (by simp [Loc.blocks])
  bp_g3 := pw_ne h.distinct 2 13 (by decide) (by simp [Loc.blocks])
  bp_g4 := pw_ne h.distinct 2 14 (by decide) (by simp [Loc.blocks])
  bp_g5 := pw_ne h.distinct 2 15 (by decide) (by simp [Loc.blocks])
  bp_g6 := pw_ne h.distinct 2 16 (by decide) (by simp [Loc.blocks])
  bp_g7 := pw_ne h.distinct 2 17 (by decide) (by simp [Loc.blocks])
  bp_g8 := pw_ne h.distinct 2 18 (by decide) (by simp [Loc.blocks])
  bg_bn := pw_ne h.distinct 0 3 (by decide) (by simp [Loc.blocks])
  bn_g0 := pw_ne h.distinct 3 10 (by decide) (by simp [Loc.blocks])
  bn_g1 := pw_ne h.distinct 3 11 (by decide) (by simp [Loc.blocks])
  bn_g2 := pw_ne h.distinct 3 12 (by decide) (by simp [Loc.blocks])
  bn_g3 := pw_ne h.distinct 3 13 (by decide) (by simp [Loc.blocks])
  bn_g4 := pw_ne h.distinct 3 14 (by decide) (by simp [Loc.blocks])
  bn_g5 := pw_ne h.distinct 3 15 (by decide) (by simp [Loc.blocks])
  bn_g6 := pw_ne h.distinct 3 16 (by decide) (by simp [Loc.blocks])
  bn_g7 := pw_ne h.distinct 3 17 (by decide) (by simp [Loc.blocks])
  bn_g8 := pw_ne h.distinct 3 18 (by decide) (by simp [Loc.blocks])
  bg_bc := pw_ne h.distinct 0 4 (by decide) (by simp [Loc.blocks])
  bc_g0 := pw_ne h.distinct 4 10 (by decide) (by simp [Loc.blocks])
  bc_g1 := pw_ne h.distinct 4 11 (by decide) (by simp [Loc.blocks])
  bc_g2 := pw_ne h.distinct 4 12 (by decide) (by simp [Loc.blocks])
  bc_g3 := pw_ne h.distinct 4 13 (by decide) (by simp [Loc.blocks])
  bc_g4 := pw_ne h.distinct 4 14 (by decide) (by simp [Loc.blocks])
  bc_g5 := pw_ne h.distinct 4 15 (by decide) (by simp [Loc.blocks])
  bc_g6 := pw_ne h.distinct 4 16 (by decide) (by simp [Loc.blocks])
  bc_g7 := pw_ne h.distinct 4 17 (by decide) (by simp [Loc.blocks])
  bc_g8 := pw_ne h.distinct 4 18 (by decide) (by simp [Loc.blocks])
  bg_ba := pw_ne h.distinct 0 5 (by decide) (by simp [Loc.blocks])
  ba_g0 := pw_ne h.distinct 5 10 (by decide) (by simp [Loc.blocks])
  ba_g1 := pw_ne h.distinct 5 11 (by decide) (by simp [Loc.blocks])
  ba_g2 := pw_ne h.distinct 5 12 (by decide) (by simp [Loc.blocks])
  ba_g3 := pw_ne h.distinct 5 13 (by decide) (by simp [Loc.blocks])
  ba_g4 := pw_ne h.distinct 5 14 (by decide) (by simp [Loc.blocks])
  ba_g5 := pw_ne h.distinct 5 15 (by decide) (by simp [Loc.blocks])
  ba_g6 := pw_ne h.distinct 5 16 (by decide) (by simp [Loc.blocks])
  ba_g7 := pw_ne h.distinct 5 17 (by decide) (by simp [Loc.blocks])
  ba_g8 := pw_ne h.distinct 5 18 (by decide) (by simp [Loc.blocks])
  bg_bW := pw_ne h.distinct 0 7 (by decide) (by simp [Loc.blocks])
  bW_g0 := pw_ne h.distinct 7 10 (by decide) (by simp [Loc.blocks])
  bW_g1 := pw_ne h.distinct 7 11 (by decide) (by simp [Loc.blocks])
  bW_g2 := pw_ne h.distinct 7 12 (by decide) (by simp [Loc.blocks])
  bW_g3 := pw_ne h.distinct 7 13 (by decide) (by simp [Loc.blocks])
  bW_g4 := pw_ne h.distinct 7 14 (by decide) (by simp [Loc.blocks])
  bW_g5 := pw_ne h.distinct 7 15 (by decide) (by simp [Loc.blocks])
  bW_g6 := pw_ne h.distinct 7 16 (by decide) (by simp [Loc.blocks])
  bW_g7 := pw_ne h.distinct 7 17 (by decide) (by simp [Loc.blocks])
  bW_g8 := pw_ne h.distinct 7 18 (by decide) (by simp [Loc.blocks])
  bg_bS := pw_ne h.distinct 0 8 (by decide) (by simp [Loc.blocks])
  bS_g0 := pw_ne h.distinct 8 10 (by decide) (by simp [Loc.blocks])
  bS_g1 := pw_ne h.distinct 8 11 (by decide) (by simp [Loc.blocks])
  bS_g2 := pw_ne h.distinct 8 12 (by decide) (by simp [Loc.blocks])
  bS_g3 := pw_ne h.distinct 8 13 (by decide) (by simp [Loc.blocks])
  bS_g4 := pw_ne h.distinct 8 14 (by decide) (by simp [Loc.blocks])
  bS_g5 := pw_ne h.distinct 8 15 (by decide) (by simp [Loc.blocks])
  bS_g6 := pw_ne h.distinct 8 16 (by decide) (by simp [Loc.blocks])
  bS_g7 := pw_ne h.distinct 8 17 (by decide) (by simp [Loc.blocks])
  bS_g8 := pw_ne h.distinct 8 18 (by decide) (by simp [Loc.blocks])
  bg_bB := pw_ne h.distinct 0 9 (by decide) (by simp [Loc.blocks])
  bB_g0 := pw_ne h.distinct 9 10 (by decide) (by simp [Loc.blocks])
  bB_g1 := pw_ne h.distinct 9 11 (by decide) (by simp [Loc.blocks])
  bB_g2 := pw_ne h.distinct 9 12 (by decide) (by simp [Loc.blocks])
  bB_g3 := pw_ne h.distinct 9 13 (by decide) (by simp [Loc.blocks])
  bB_g4 := pw_ne h.distinct 9 14 (by decide) (by simp [Loc.blocks])
  bB_g5 := pw_ne h.distinct 9 15 (by decide) (by simp [Loc.blocks])
  bB_g6 := pw_ne h.distinct 9 16 (by decide) (by simp [Loc.blocks])
  bB_g7 := pw_ne h.distinct 9 17 (by decide) (by simp [Loc.blocks])
  bB_g8 := pw_ne h.distinct 9 18 (by decide) (by simp [Loc.blocks])

theorem notW_bg {L : Loc} (d : WDist L) : ¬ L.writes L.bg := by
  rintro (h | h | h | h | h | h | h | h)
  · exact d.bg_bl h
  · exact d.bg_bp h
  · exact d.bg_bn h
  · exact d.bg_bc h
  · exact d.bg_ba h
  · exact d.bg_bW h
  · exact d.bg_bS h
  · exact d.bg_bB h

theorem notW_glob {L : Loc} {g : block} (h0 : L.bl ≠ g) (h1 : L.bp ≠ g)
    (h2 : L.bn ≠ g) (h3 : L.bc ≠ g) (h4 : L.ba ≠ g) (h5 : L.bW ≠ g) (h6 : L.bS ≠ g)
    (h7 : L.bB ≠ g) : ¬ L.writes g := by
  rintro (h | h | h | h | h | h | h | h)
  · exact h0 h.symm
  · exact h1 h.symm
  · exact h2 h.symm
  · exact h3 h.symm
  · exact h4 h.symm
  · exact h5 h.symm
  · exact h6 h.symm
  · exact h7 h.symm

/-- `Mem` after a pass. -/
theorem Mem.frame {n : Nat} {m m' : mem} {L : Loc} {ctx : Ctx n} {st st' : RefineSt n}
    {aw aw' : Nat → Lib.Integers.int64} (hok : Ok n L) (hm : Mem m L ctx st aw)
    (hu : Unch m m' L.writes) (hkW : Keep m m' L.bW) (hkS : Keep m m' L.bS) (hkB : Keep m m' L.bB)
    (hl : ArrayAt m' .Mint32 L.bl L.lb (ints st'.lab) n)
    (hp : ArrayAt m' .Mint32 L.bp L.pb (ints st'.ptn) n)
    (hn : ArrayAt m' .Mint32 L.bn L.nb (fun _ => .Vint (ir st'.numcells)) 1)
    (ha : ArrayAt m' .Mint64 L.ba L.ab (longs aw') L.M)
    (har : SetRep (fun w => bv64 (aw' w)) L.M st'.active)
    (hc : ∃ v, ArrayAt m' .Mint32 L.bc L.cb v n) : Mem m' L ctx st' aw' :=
  have d := hok.wd
  { graph := ⟨hm.graph.arr.unch hu (notW_bg d), hm.graph.rep⟩
    lab := hl
    ptn := hp
    nc := hn
    act := ha
    actRep := har
    cnt := hc
    dW := hm.dW.keep hu (notW_glob d.bl_g0 d.bp_g0 d.bn_g0 d.bc_g0 d.ba_g0 d.bW_g0 d.bS_g0 d.bB_g0)
      (notW_glob d.bl_g1 d.bp_g1 d.bn_g1 d.bc_g1 d.ba_g1 d.bW_g1 d.bS_g1 d.bB_g1) fun _ => hkW
    dS := hm.dS.keep hu (notW_glob d.bl_g2 d.bp_g2 d.bn_g2 d.bc_g2 d.ba_g2 d.bW_g2 d.bS_g2 d.bB_g2)
      (notW_glob d.bl_g3 d.bp_g3 d.bn_g3 d.bc_g3 d.ba_g3 d.bW_g3 d.bS_g3 d.bB_g3) fun _ => hkS
    dB := hm.dB.keep hu (notW_glob d.bl_g4 d.bp_g4 d.bn_g4 d.bc_g4 d.ba_g4 d.bW_g4 d.bS_g4 d.bB_g4)
      (notW_glob d.bl_g5 d.bp_g5 d.bn_g5 d.bc_g5 d.ba_g5 d.bW_g5 d.bS_g5 d.bB_g5) fun _ => hkB
    bit := hm.bit.unch hu
      (notW_glob d.bl_g6 d.bp_g6 d.bn_g6 d.bc_g6 d.ba_g6 d.bW_g6 d.bS_g6 d.bB_g6)
    bytes := BytecountTable.unch hm.bytes hu
      (notW_glob d.bl_g7 d.bp_g7 d.bn_g7 d.bc_g7 d.ba_g7 d.bW_g7 d.bS_g7 d.bB_g7)
    left := LeftbitTable.unch hm.left hu
      (notW_glob d.bl_g8 d.bp_g8 d.bn_g8 d.bc_g8 d.ba_g8 d.bW_g8 d.bS_g8 d.bB_g8) }

end NautyVerified.Proofs.Refine
