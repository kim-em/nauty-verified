import NautyVerified.Proofs.Refine.Frame

/-!
# Updating `Mem` and `Tmp` one field at a time

`Mem.setPtn` and `Mem.setNc`: after a write to `ptn` or `*numcells` alone.
`Mem.away`: after writes to the work blocks `count`, `bucket` and `workperm`,
which `Mem` does not describe beyond their headers. `Tmp.setHint`,
`Tmp.setMaxpos`: after `hint = …`, `maxpos = …`.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs NautyVerified.Proofs.Alloc
open NautyVerified.Proofs.Set (longs BitTable)
open Hex.GraphIso.Nauty

theorem Mem.setPtn {n : Nat} {m m' : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} {p : Array Nat} (hok : Ok n L) (hm : Mem m L ctx st aw)
    (hu : Unch m m' (· = L.bp)) (harr : ArrayAt m' .Mint32 L.bp L.pb (ints p) n) :
    Mem m' L ctx { st with ptn := p } aw := by
  have d := hok.wd
  have hu' : Unch m m' L.writes := hu.mono fun z hz => .inr (.inl hz)
  obtain ⟨cv, hcv⟩ := hm.cnt
  exact hm.frame hok hu' (Keep.unch hu (Ne.symm d.bp_bW)) (Keep.unch hu (Ne.symm d.bp_bS))
    (Keep.unch hu (Ne.symm d.bp_bB)) (hm.lab.unch hu d.bl_bp) harr (hm.nc.unch hu (Ne.symm d.bp_bn))
    (hm.act.unch hu (Ne.symm d.bp_ba)) hm.actRep ⟨cv, hcv.unch hu (Ne.symm d.bp_bc)⟩

theorem Mem.setNc {n : Nat} {m m' : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} {c : Nat} (hok : Ok n L) (hm : Mem m L ctx st aw)
    (hu : Unch m m' (· = L.bn)) (harr : ArrayAt m' .Mint32 L.bn L.nb (fun _ => .Vint (ir c)) 1) :
    Mem m' L ctx { st with numcells := c } aw := by
  have d := hok.wd
  have hu' : Unch m m' L.writes := hu.mono fun z hz => .inr (.inr (.inl hz))
  obtain ⟨cv, hcv⟩ := hm.cnt
  exact hm.frame hok hu' (Keep.unch hu (Ne.symm d.bn_bW)) (Keep.unch hu (Ne.symm d.bn_bS))
    (Keep.unch hu (Ne.symm d.bn_bB)) (hm.lab.unch hu d.bl_bn) (hm.ptn.unch hu d.bp_bn) harr
    (hm.act.unch hu (Ne.symm d.bn_ba)) hm.actRep ⟨cv, hcv.unch hu (Ne.symm d.bn_bc)⟩

theorem Mem.away {n : Nat} {m m' : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} (hok : Ok n L) (hm : Mem m L ctx st aw)
    (hu : Unch m m' (fun z => z = L.bc ∨ z = L.bB ∨ z = L.bW)) (hkB : Keep m m' L.bB)
    (hkW : Keep m m' L.bW) (hc : ∃ v, ArrayAt m' .Mint32 L.bc L.cb v n) :
    Mem m' L ctx st aw := by
  have d := hok.wd
  have nS : ∀ {z}, L.bc ≠ z → L.bB ≠ z → L.bW ≠ z → ¬ (z = L.bc ∨ z = L.bB ∨ z = L.bW) :=
    fun h1 h2 h3 h => by
      rcases h with h | h | h
      · exact h1 h.symm
      · exact h2 h.symm
      · exact h3 h.symm
  have hu' : Unch m m' L.writes := hu.mono fun z hz => by
    rcases hz with h | h | h
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
  exact hm.frame hok hu' hkW (Keep.unch hu (nS d.bc_bS d.bS_bB.symm d.bW_bS))
    hkB (hm.lab.unch hu (nS d.bl_bc.symm d.bl_bB.symm d.bl_bW.symm))
    (hm.ptn.unch hu (nS d.bp_bc.symm d.bp_bB.symm d.bp_bW.symm))
    (hm.nc.unch hu (nS d.bn_bc.symm d.bn_bB.symm d.bn_bW.symm))
    (hm.act.unch hu (nS d.bc_ba d.ba_bB.symm d.ba_bW.symm)) hm.actRep hc

theorem Mem.setLab {n : Nat} {m m' : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} {T : Array Nat} (hok : Ok n L) (hm : Mem m L ctx st aw)
    (hu : Unch m m' (· = L.bl)) (harr : ArrayAt m' .Mint32 L.bl L.lb (ints T) n) :
    Mem m' L ctx { st with lab := T } aw := by
  have d := hok.wd
  have hu' : Unch m m' L.writes := hu.mono fun z hz => .inl hz
  obtain ⟨cv, hcv⟩ := hm.cnt
  exact hm.frame hok hu' (Keep.unch hu (Ne.symm d.bl_bW)) (Keep.unch hu (Ne.symm d.bl_bS))
    (Keep.unch hu (Ne.symm d.bl_bB)) harr (hm.ptn.unch hu (Ne.symm d.bl_bp))
    (hm.nc.unch hu (Ne.symm d.bl_bn)) (hm.act.unch hu (Ne.symm d.bl_ba)) hm.actRep
    ⟨cv, hcv.unch hu (Ne.symm d.bl_bc)⟩

theorem Tmp.setHint {n : Nat} {le : temp_env} {L : Loc} {st : RefineSt n} (h : Tmp le L st)
    (c : Nat) : Tmp (PTree.set dense.id.hint (.Vint (ir c)) le) L { st with hint := c } where
  g := by rw [temps_gso _ _ (by decide)]; exact h.g
  lab := by rw [temps_gso _ _ (by decide)]; exact h.lab
  ptn := by rw [temps_gso _ _ (by decide)]; exact h.ptn
  level := by rw [temps_gso _ _ (by decide)]; exact h.level
  numcells := by rw [temps_gso _ _ (by decide)]; exact h.numcells
  count := by rw [temps_gso _ _ (by decide)]; exact h.count
  active := by rw [temps_gso _ _ (by decide)]; exact h.active
  code := by rw [temps_gso _ _ (by decide)]; exact h.code
  m := by rw [temps_gso _ _ (by decide)]; exact h.m
  n := by rw [temps_gso _ _ (by decide)]; exact h.n
  longcode := by rw [temps_gso _ _ (by decide)]; exact h.longcode
  hint := temps_gss _ _ _
  maxpos := by rw [temps_gso _ _ (by decide)]; exact h.maxpos

theorem Tmp.setMaxpos {n : Nat} {le : temp_env} {L : Loc} {st : RefineSt n} (h : Tmp le L st)
    (c : Nat) : Tmp (PTree.set dense.id.maxpos (.Vint (ir c)) le) L { st with maxpos := c } where
  g := by rw [temps_gso _ _ (by decide)]; exact h.g
  lab := by rw [temps_gso _ _ (by decide)]; exact h.lab
  ptn := by rw [temps_gso _ _ (by decide)]; exact h.ptn
  level := by rw [temps_gso _ _ (by decide)]; exact h.level
  numcells := by rw [temps_gso _ _ (by decide)]; exact h.numcells
  count := by rw [temps_gso _ _ (by decide)]; exact h.count
  active := by rw [temps_gso _ _ (by decide)]; exact h.active
  code := by rw [temps_gso _ _ (by decide)]; exact h.code
  m := by rw [temps_gso _ _ (by decide)]; exact h.m
  n := by rw [temps_gso _ _ (by decide)]; exact h.n
  longcode := by rw [temps_gso _ _ (by decide)]; exact h.longcode
  hint := by rw [temps_gso _ _ (by decide)]; exact h.hint
  maxpos := temps_gss _ _ _

end NautyVerified.Proofs.Refine
