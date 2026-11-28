import NautyVerified.Proofs.Dispatch.DenseRep
import NautyVerified.Proofs.Isautom.Satisfies
import NautyVerified.Proofs.Testcanlab.Satisfies
import NautyVerified.Proofs.Updatecan.Satisfies
import NautyVerified.Proofs.Targetcell.Satisfies
import NautyVerified.Proofs.Refine1.Nontrivial
import NautyVerified.Proofs.Cheapautom.Satisfies
import NautyVerified.Proofs.Top.Freedyn
import NautyVerified.Proofs.Top.Check
import NautyVerified.Logic.Grow
import NautyVerified.Spec.Processnode

/-!
# naugraph.c's dispatch procedures

`dense`: `denseRep` (`Dispatch/DenseRep.lean`) with the specifications, from
the proofs of naugraph.c's procedures.
-/

namespace NautyVerified.Proofs.Dispatch

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep Slot InUse SlotsOk)
open NautyVerified.Proofs.Set (BitTable longs)
open NautyVerified.Proofs.Graph (GraphAt RowsAt)
open NautyVerified.Proofs.Init (BytecountTable)
open Hex.GraphIso.Nauty

local notation "WP" => Block.naugraphWorkperm
local notation "WPS" => Block.naugraphWorkpermSz
local notation "WS" => Block.naugraphWorkset
local notation "WSS" => Block.naugraphWorksetSz
local notation "BK" => Block.naugraphBucket
local notation "BKS" => Block.naugraphBucketSz

/-- A call's `Step`, from its frame and the scratch state after it. -/
theorem denseStep {m m' : mem} {out : block → Prop}
    (hw' : denseRep.Work m' ∧ ∀ z, denseRep.IsWork m' z → denseRep.IsWork m z ∨ ¬ Mem.valid_block m z)
    {W : block → Prop} (hu : Unch m m' W)
    (hW : ∀ z, W z → out z ∨ z ∈ denseWGlobs ∨ InUse m denseSlots z ∨ ¬ Mem.valid_block m z)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hk : ∀ z, out z → Mem.valid_block m z → Keep m m' z) : denseRep.Step m m' out :=
  ⟨hu.mono hW, hv, hw'.1, hw'.2, hk⟩

/-- A shared table or nautil.c's `workperm` pair is none of naugraph.c's scratch blocks in use. -/
theorem dense_env_notWork {m : mem} (hw : denseRep.Work m) {z b : block} (hz : z ∈ envAvoid)
    (hb : InUse m denseSlots b) : z ≠ b := by
  rintro rfl
  exact hw.1.notin _ hb (List.mem_append_right _ hz)

theorem dense_globs_notWork {m : mem} (hw : denseRep.Work m) {z b : block} (hz : z ∈ denseGlobs)
    (hb : InUse m denseSlots b) : z ≠ b := by
  rintro rfl
  exact hw.1.notin _ hb (List.mem_append_left _ hz)

/-! ### The procedures -/

kernel_rfl type_isautomD : type_of_fundef (.Internal dense.fn.«isautom») = isautomType
kernel_rfl type_testcanlabD : type_of_fundef (.Internal dense.fn.«testcanlab») = testcanlabType
kernel_rfl type_updatecanD : type_of_fundef (.Internal dense.fn.«updatecan») = updatecanType
kernel_rfl type_refineD : type_of_fundef (.Internal dense.fn.«refine») = refineType
kernel_rfl type_refine1D : type_of_fundef (.Internal dense.fn.«refine1») = refineType
kernel_rfl type_cheapautomD : type_of_fundef (.Internal dense.fn.«cheapautom») = cheapautomType
kernel_rfl type_targetcellD : type_of_fundef (.Internal dense.fn.«targetcell») = targetcellType
kernel_rfl type_checkD : type_of_fundef (.Internal dense.fn.naugraph_check) = checkType
kernel_rfl type_freedynD : type_of_fundef (.Internal dense.fn.naugraph_freedyn) = freedynType

theorem dense_isautom (xi : ExternalCalls) : denseRep.IsautomFn xi denseRep.isautom := by
  refine ⟨_, by simp [Genv.find_funct, denseRep, Search.funct_isautomFn], type_isautomD,
    fun G _ bg gofs bpm pofs perm M => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hc, ⟨gw, hg⟩, _, hp, hps, _⟩ =>
    ⟨_, Isautom.isautom_satisfies bg gofs gw G.g bpm pofs perm M,
      ⟨hargs, hg, hp, hps, hc.tables.1, hc.etables.left, hc.M1, by have := hc.Mlt; omega, hc.nM⟩, ?_⟩
  rintro t v m' ⟨rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, DispatchRep.Step.refl _ hc.work _⟩

theorem dense_cheapautom (xi : ExternalCalls) : denseRep.CheapautomFn xi denseRep.cheapautom := by
  refine ⟨_, by simp [Genv.find_funct, denseRep, Search.funct_cheapautomFn], type_cheapautomD,
    fun bp pofs ptn level n => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hw, ha, hs, hsm, hl, hn, hlev⟩ =>
    ⟨_, Cheapautom.cheapautom_satisfies bp pofs ptn level n, ⟨hargs, ha, hs, hsm, hl, hn, hlev⟩, ?_⟩
  rintro t v m' ⟨rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, DispatchRep.Step.refl _ hw _⟩

theorem dense_check (xi : ExternalCalls) : @DispatchRep.CheckFn Program.ge xi denseRep.check :=
  ⟨_, by simp [Genv.find_funct, denseRep, Top.funct_naugraphCheck], type_checkD,
    fun mv nv => Top.naugraph_check_satisfies mv nv⟩

/-! ### Separation facts -/

/-- A block that is none of naugraph.c's globals. -/
theorem ne_globs {z : block} (h : z ∉ denseGlobs) :
    z ≠ WP ∧ z ≠ WPS ∧ z ≠ WS ∧ z ≠ WSS ∧ z ≠ BK ∧ z ≠ BKS ∧ z ≠ Block.naugraphBit ∧
      z ≠ Block.naugraphBytecount := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact h (by simp [denseGlobs, denseWGlobs])

/-- A scratch block in use is none of the globals. -/
theorem work_ne {m : mem} (hw : denseRep.Work m) {b : block} (hb : InUse m denseSlots b) :
    (b ≠ WP ∧ b ≠ WPS ∧ b ≠ WS ∧ b ≠ WSS ∧ b ≠ BK ∧ b ≠ BKS ∧ b ≠ Block.naugraphBit ∧
      b ≠ Block.naugraphBytecount) ∧ b ≠ Block.nautilBit ∧ b ≠ Block.leftbit ∧
      b ≠ Block.nautyBit := by
  have h := hw.1.notin b hb
  simp only [denseL, List.mem_append, not_or] at h
  refine ⟨ne_globs h.1, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact h.2 (by simp [NautyEnv.blocks])

theorem work_sep {m : mem} (hw : denseRep.Work m) {p q : Slot} (hp : p ∈ denseSlots)
    (hq : q ∈ denseSlots) (hpq : p ≠ q) {c c' : Nat} {b b' : block} (hc : 0 < c) (hc' : 0 < c')
    (d : p.At m c b) (d' : q.At m c' b') : b ≠ b' := by
  rintro rfl
  exact hpq (hw.1.sep p hp q hq c c' b hc hc' d d')

/-- The facts the separation of a call's arguments gives. -/
theorem sep_ne {m : mem} (hw : denseRep.Work m) {bs : List block} (h : denseRep.Sep m bs) {z : block}
    (hz : z ∈ bs) :
    Mem.valid_block m z ∧ (z ≠ WP ∧ z ≠ WPS ∧ z ≠ WS ∧ z ≠ WSS ∧ z ≠ BK ∧ z ≠ BKS ∧
      z ≠ Block.naugraphBit ∧ z ≠ Block.naugraphBytecount) ∧
    z ≠ Block.nautilBit ∧ z ≠ Block.leftbit ∧ z ≠ Block.nautyBit ∧
    ∀ {b}, InUse m denseSlots b → z ≠ b := by
  have hT := h.notTab z hz
  exact ⟨h.valid z hz, ne_globs (h.notGlobs z hz), hT.2.1, hT.2.2, hT.1,
    fun hb e => h.notWork z hz (e ▸ hb)⟩

theorem pw2 {a b : block} {l : List block} (h : (a :: b :: l).Pairwise (· ≠ ·)) : a ≠ b :=
  List.rel_of_pairwise_cons h (by simp)

theorem pw4 {a b c d : block} (h : [a, b, c, d].Pairwise (· ≠ ·)) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false] at h
  exact ⟨h.1 _ (.inl rfl), h.1 _ (.inr (.inl rfl)), h.1 _ (.inr (.inr rfl)), h.2.1 _ (.inl rfl),
    h.2.1 _ (.inr rfl), h.2.2.1 _ rfl⟩

theorem pw3 {a b c : block} (h : [a, b, c].Pairwise (· ≠ ·)) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false] at h
  exact ⟨h.1 _ (.inl rfl), h.1 _ (.inr rfl), h.2.1 _ rfl⟩

theorem pw3_mk {a b c : block} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) :
    [a, b, c].Pairwise (· ≠ ·) := by
  refine .cons ?_ (.cons ?_ (.cons (fun _ h => absurd h List.not_mem_nil) .nil))
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx; exact h3

theorem new_ne {m : mem} {z b : block} (hz : Mem.valid_block m z) (hb : ¬ Mem.valid_block m b) :
    z ≠ b := fun e => hb (e ▸ hz)

theorem dense_testcanlab (xi : ExternalCalls) : denseRep.TestcanlabFn xi denseRep.testcanlab := by
  refine ⟨_, by simp [Genv.find_funct, denseRep, Search.funct_testcanlabFn], type_testcanlabD,
    fun G _ bg gofs c _ bc cofs bl lofs lab bs so M => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hc, ⟨gw, hg⟩, _, ⟨cw, hcr⟩, _, hl, hls, hlsm, hsurj,
    _, ⟨sv, hs⟩, hsep⟩ => ?_
  have hw := hc.work
  obtain ⟨⟨cP, bP, dP⟩, ⟨cS, bS, dS⟩, ⟨cB, bB, dB⟩⟩ := dense_dyn hw
  have wP := fun h => work_ne hw (dense_inUseW dP h)
  have wS := fun h => work_ne hw (dense_inUseS dS h)
  have wB := fun h => work_ne hw (dense_inUseB dB h)
  have sPS : 0 < cP → 0 < cS → bP ≠ bS := fun h1 h2 =>
    work_sep hw (p := (WP, WPS, 4)) (q := (WS, WSS, 8)) (by simp [denseSlots]) (by simp [denseSlots])
      (by decide) h1 h2 dP dS
  have sPB : 0 < cP → 0 < cB → bP ≠ bB := fun h1 h2 =>
    work_sep hw (p := (WP, WPS, 4)) (q := (BK, BKS, 4)) (by simp [denseSlots]) (by simp [denseSlots])
      (by decide) h1 h2 dP dB
  have sSB : 0 < cS → 0 < cB → bS ≠ bB := fun h1 h2 =>
    work_sep hw (p := (WS, WSS, 8)) (q := (BK, BKS, 4)) (by simp [denseSlots]) (by simp [denseSlots])
      (by decide) h1 h2 dS dB
  have zg := sep_ne hw hsep (z := bg) (by simp)
  have zc := sep_ne hw hsep (z := bc) (by simp)
  have zl := sep_ne hw hsep (z := bl) (by simp)
  have zs := sep_ne hw hsep (z := bs) (by simp)
  have hd := pw4 hsep.distinct
  refine ⟨_, Satisfies.grow (Testcanlab.testcanlab_satisfies bg gofs gw G.g bc cofs cw c bl lofs lab
    bs so sv M cP bP cS bS), ⟨hargs, hg, hcr.graphAt, hl, hls, hlsm, hsurj, hs, dP, dS,
    hc.etables.left, hc.etables.nautilBit, ?_, hd.2.2.1.symm, hd.2.2.2.2.1.symm, hd.2.2.2.2.2.symm, ?_, ?_,
    hc.M1, hc.Mlt, hc.nM⟩, ?_⟩
  · rintro z (rfl | rfl | rfl | rfl)
    all_goals first
      | exact ⟨zg.1, zg.2.1.1, zg.2.1.2.1, zg.2.1.2.2.1, zg.2.1.2.2.2.1, zg.2.2.1, zg.2.2.2.1,
          fun h => zg.2.2.2.2.2 (dense_inUseW dP h), fun h => zg.2.2.2.2.2 (dense_inUseS dS h)⟩
      | exact ⟨zc.1, zc.2.1.1, zc.2.1.2.1, zc.2.1.2.2.1, zc.2.1.2.2.2.1, zc.2.2.1, zc.2.2.2.1,
          fun h => zc.2.2.2.2.2 (dense_inUseW dP h), fun h => zc.2.2.2.2.2 (dense_inUseS dS h)⟩
      | exact ⟨zl.1, zl.2.1.1, zl.2.1.2.1, zl.2.1.2.2.1, zl.2.1.2.2.2.1, zl.2.2.1, zl.2.2.2.1,
          fun h => zl.2.2.2.2.2 (dense_inUseW dP h), fun h => zl.2.2.2.2.2 (dense_inUseS dS h)⟩
      | exact ⟨zs.1, zs.2.1.1, zs.2.1.2.1, zs.2.1.2.2.1, zs.2.1.2.2.2.1, zs.2.2.1, zs.2.2.2.1,
          fun h => zs.2.2.2.2.2 (dense_inUseW dP h), fun h => zs.2.2.2.2.2 (dense_inUseS dS h)⟩
  · exact fun h => ⟨(wP h).2.1, (wP h).2.2.1, (wP h).1.2.2.1, (wP h).1.2.2.2.1, sPS h⟩
  · exact fun h => ⟨(wS h).2.1, (wS h).2.2.1, (wS h).1.1, (wS h).1.2.1⟩
  rintro t v m' ⟨⟨rfl, hv, harr, hkeep, cP', bP', cS', bS', dP', dS', -, -, rP, rS, hne, hu⟩, hval⟩
  have nB : ∀ z, z = BK ∨ z = BKS ∨ (0 < cB ∧ z = bB) → ¬ (z = bs ∨ z = WPS ∨ z = WP ∨ z = WSS ∨
      z = WS ∨ (0 < cP ∧ z = bP) ∨ (0 < cS ∧ z = bS) ∨ (¬ Mem.valid_block m bP' ∧ z = bP') ∨
      (¬ Mem.valid_block m bS' ∧ z = bS')) := by
    have vBK : Mem.valid_block m BK := hw.2 _ (by simp [denseGlobs, denseWGlobs])
    have vBKS : Mem.valid_block m BKS := hw.2 _ (by simp [denseGlobs, denseWGlobs])
    rintro z (rfl | rfl | ⟨hcB, ez⟩)
    · rintro (e | e | e | e | e | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩)
      · exact zs.2.1.2.2.2.2.1 e.symm
      all_goals first
        | exact absurd e (by decide)
        | exact (wP h).1.2.2.2.2.1 e.symm
        | exact (wS h).1.2.2.2.2.1 e.symm
        | exact h (e ▸ vBK)
    · rintro (e | e | e | e | e | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩)
      · exact zs.2.1.2.2.2.2.2.1 e.symm
      all_goals first
        | exact absurd e (by decide)
        | exact (wP h).1.2.2.2.2.2.1 e.symm
        | exact (wS h).1.2.2.2.2.2.1 e.symm
        | exact h (e ▸ vBKS)
    · rw [ez]
      have vb : Mem.valid_block m bB := Alloc.Malloced.valid (dB.mal hcB)
      rintro (e | e | e | e | e | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩)
      · exact zs.2.2.2.2.2 (dense_inUseB dB hcB) e.symm
      · exact (wB hcB).1.2.1 e
      · exact (wB hcB).1.1 e
      · exact (wB hcB).1.2.2.2.1 e
      · exact (wB hcB).1.2.2.1 e
      · exact sPB h hcB e.symm
      · exact sSB h hcB e.symm
      · exact h (e ▸ vb)
      · exact h (e ▸ vb)
  have dB' := dB.keep hu (nB _ (.inl rfl)) (nB _ (.inr (.inl rfl)))
    fun h => Keep.unch hu (nB _ (.inr (.inr ⟨h, rfl⟩)))
  have hw' := denseWork_next hw hval dP dS dB dP' dS' dB' rP rS (.inl ⟨rfl, rfl⟩)
    (fun _ _ h1 h2 => hne h1) (fresh_r dB) (fresh_r dB)
  refine ⟨rfl, hv, harr, denseStep hw' hu ?_ hval fun z e _ => e ▸ hkeep⟩
  rintro z (e | e | e | e | e | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩)
  · exact .inl e
  all_goals first
    | exact .inr (.inr (.inl (e ▸ dense_inUseW dP h)))
    | exact .inr (.inr (.inl (e ▸ dense_inUseS dS h)))
    | exact .inr (.inr (.inr (e ▸ h)))
    | (subst e; exact .inr (.inl (by simp [denseWGlobs])))

theorem dense_updatecan (xi : ExternalCalls) : denseRep.UpdatecanFn xi denseRep.updatecan := by
  refine ⟨_, by simp [Genv.find_funct, denseRep, Search.funct_updatecanFn], type_updatecanD,
    fun G _ bg gofs c _ bc cofs bl lofs lab sr M => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hc, ⟨gw, hg⟩, _, ⟨cw, hcr⟩, hok, hl, hls, hlsm, hsurj,
    _, hsr, hsep, _⟩ => ?_
  have hw := hc.work
  obtain ⟨⟨cP, bP, dP⟩, ⟨cS, bS, dS⟩, ⟨cB, bB, dB⟩⟩ := dense_dyn hw
  have wP := fun h => work_ne hw (dense_inUseW dP h)
  have wS := fun h => work_ne hw (dense_inUseS dS h)
  have wB := fun h => work_ne hw (dense_inUseB dB h)
  have sPS : 0 < cP → 0 < cS → bP ≠ bS := fun h1 h2 =>
    work_sep hw (p := (WP, WPS, 4)) (q := (WS, WSS, 8)) (by simp [denseSlots]) (by simp [denseSlots])
      (by decide) h1 h2 dP dS
  have sPB : 0 < cP → 0 < cB → bP ≠ bB := fun h1 h2 =>
    work_sep hw (p := (WP, WPS, 4)) (q := (BK, BKS, 4)) (by simp [denseSlots]) (by simp [denseSlots])
      (by decide) h1 h2 dP dB
  have zg := sep_ne hw hsep (z := bg) (by simp)
  have zc := sep_ne hw hsep (z := bc) (by simp)
  have zl := sep_ne hw hsep (z := bl) (by simp)
  have hd := pw3 hsep.distinct
  refine ⟨_, Satisfies.grow (Updatecan.updatecan_satisfies bg gofs gw G.g bc cofs cw c bl lofs lab
    sr M cP bP), ⟨hargs, hg, hcr, hok, hl, hls, hlsm, hsurj, dP, hc.etables.left,
    hc.etables.nautilBit, zg.1, zc.1, zl.1, hd.1.symm, hd.2.2, ?_, ?_, hsr, hc.M1, hc.Mlt, hc.nM⟩, ?_⟩
  · rintro z (rfl | rfl | rfl | rfl)
    · exact ⟨fun e => zc.2.1.1 e.symm, fun e => zl.2.1.1 e.symm, fun e => zg.2.1.1 e.symm⟩
    · exact ⟨fun e => zc.2.1.2.1 e.symm, fun e => zl.2.1.2.1 e.symm, fun e => zg.2.1.2.1 e.symm⟩
    · exact ⟨fun e => zc.2.2.1 e.symm, fun e => zl.2.2.1 e.symm, fun e => zg.2.2.1 e.symm⟩
    · exact ⟨fun e => zc.2.2.2.1 e.symm, fun e => zl.2.2.2.1 e.symm, fun e => zg.2.2.2.1 e.symm⟩
  · exact fun h => ⟨fun e => zc.2.2.2.2.2 (dense_inUseW dP h) e.symm,
      fun e => zl.2.2.2.2.2 (dense_inUseW dP h) e.symm, fun e => zg.2.2.2.2.2 (dense_inUseW dP h) e.symm,
      (wP h).2.1, (wP h).2.2.1⟩
  rintro t v m' ⟨⟨rfl, cw', cP', bP', hg', dP', -, rP, hu, hkeep⟩, hval⟩
  have vWS : Mem.valid_block m WS := hw.2 _ (by simp [denseGlobs, denseWGlobs])
  have vWSS : Mem.valid_block m WSS := hw.2 _ (by simp [denseGlobs, denseWGlobs])
  have vBK : Mem.valid_block m BK := hw.2 _ (by simp [denseGlobs, denseWGlobs])
  have vBKS : Mem.valid_block m BKS := hw.2 _ (by simp [denseGlobs, denseWGlobs])
  have nU : ∀ z, Mem.valid_block m z → z ≠ bc → z ≠ WPS → z ≠ WP → (0 < cP → z ≠ bP) →
      ¬ (z = bc ∨ z = WPS ∨ z = WP ∨ (0 < cP ∧ z = bP) ∨ (¬ Mem.valid_block m bP' ∧ z = bP')) := by
    rintro z hz h1 h2 h3 h4 (e | e | e | ⟨h, e⟩ | ⟨h, e⟩)
    · exact h1 e
    · exact h2 e
    · exact h3 e
    · exact h4 h e
    · exact h (e ▸ hz)
  have dS' := dS.keep hu (nU _ vWS (fun e => zc.2.1.2.2.1 e.symm) (by decide) (by decide)
      fun h e => (wP h).1.2.2.1 e.symm)
    (nU _ vWSS (fun e => zc.2.1.2.2.2.1 e.symm) (by decide) (by decide) fun h e => (wP h).1.2.2.2.1 e.symm)
    fun hs => Keep.unch hu (nU _ (Alloc.Malloced.valid (dS.mal hs))
      (fun e => zc.2.2.2.2.2 (dense_inUseS dS hs) e.symm) (wS hs).1.2.1 (wS hs).1.1
      fun h e => sPS h hs e.symm)
  have dB' := dB.keep hu (nU _ vBK (fun e => zc.2.1.2.2.2.2.1 e.symm) (by decide) (by decide)
      fun h e => (wP h).1.2.2.2.2.1 e.symm)
    (nU _ vBKS (fun e => zc.2.1.2.2.2.2.2.1 e.symm) (by decide) (by decide)
      fun h e => (wP h).1.2.2.2.2.2.1 e.symm)
    fun hs => Keep.unch hu (nU _ (Alloc.Malloced.valid (dB.mal hs))
      (fun e => zc.2.2.2.2.2 (dense_inUseB dB hs) e.symm) (wB hs).1.2.1 (wB hs).1.1
      fun h e => sPB h hs e.symm)
  have hw' := denseWork_next hw hval dP dS dB dP' dS' dB' rP (.inl ⟨rfl, rfl⟩) (.inl ⟨rfl, rfl⟩)
    (fresh_r dS) (fresh_r dB) (fresh_l dS)
  refine ⟨rfl, ⟨cw', hg'.arr, hg'.rep⟩, (Spec.updatecan_size _ _ _ _).trans hok,
    denseStep hw' hu ?_ hval fun z e _ => (by simpa using e : z = bc) ▸ hkeep⟩
  rintro z (e | e | e | ⟨h, e⟩ | ⟨h, e⟩)
  · exact .inl (by simpa using e)
  · subst e; exact .inr (.inl (by simp [denseWGlobs]))
  · subst e; exact .inr (.inl (by simp [denseWGlobs]))
  · exact .inr (.inr (.inl (e ▸ dense_inUseW dP h)))
  · exact .inr (.inr (.inr (e ▸ h)))

/-- A call that may reallocate all three pairs, changing only `dyn3Set` and its
outputs. -/
theorem dense_step3 {m m' : mem} {out : block → Prop} (hw : denseRep.Work m)
    (hval : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    {cP cS cB cP' cS' cB' : Nat} {bP bS bB bP' bS' bB' : block}
    (dP : DynAt m WP WPS 4 cP bP) (dS : DynAt m WS WSS 8 cS bS) (dB : DynAt m BK BKS 4 cB bB)
    (dP' : DynAt m' WP WPS 4 cP' bP') (dS' : DynAt m' WS WSS 8 cS' bS')
    (dB' : DynAt m' BK BKS 4 cB' bB')
    (rP : (cP' = cP ∧ bP' = bP) ∨ ¬ Mem.valid_block m bP')
    (rS : (cS' = cS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS')
    (rB : (cB' = cB ∧ bB' = bB) ∨ ¬ Mem.valid_block m bB')
    (fPS : 0 < cP' → 0 < cS' → bP' ≠ bS') (fPB : 0 < cP' → 0 < cB' → bP' ≠ bB')
    (fSB : 0 < cS' → 0 < cB' → bS' ≠ bB')
    {W : block → Prop} (hu : Unch m m' W)
    (hW : ∀ z, W z → out z ∨ Alloc.dyn3Set m cP bP cS bS cB bB z)
    (hk : ∀ z, out z → Mem.valid_block m z → Keep m m' z) : denseRep.Step m m' out := by
  have hw' := denseWork_next hw hval dP dS dB dP' dS' dB' rP rS rB (fun _ _ => fPS)
    (fun _ _ => fPB) (fun _ _ => fSB)
  refine denseStep hw' hu (fun z hz => ?_) hval hk
  rcases hW z hz with h | h
  · exact .inl h
  rcases h with e | e | e | e | e | e | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | h
  · subst e; exact .inr (.inl (by simp [denseWGlobs]))
  · subst e; exact .inr (.inl (by simp [denseWGlobs]))
  · subst e; exact .inr (.inl (by simp [denseWGlobs]))
  · subst e; exact .inr (.inl (by simp [denseWGlobs]))
  · subst e; exact .inr (.inl (by simp [denseWGlobs]))
  · subst e; exact .inr (.inl (by simp [denseWGlobs]))
  · exact .inr (.inr (.inl (e ▸ dense_inUseW dP h)))
  · exact .inr (.inr (.inl (e ▸ dense_inUseS dS h)))
  · exact .inr (.inr (.inl (e ▸ dense_inUseB dB h)))
  · exact .inr (.inr (.inr h))

/-- What `targetcell` and `refine` need of the three pairs, from the scratch state
and the arguments' separation. -/
theorem dense_pre3 {m : mem} (hw : denseRep.Work m) {bs : List block} (hsep : denseRep.Sep m bs)
    {cP cS cB : Nat} {bP bS bB : block}
    (dP : DynAt m WP WPS 4 cP bP) (dS : DynAt m WS WSS 8 cS bS) (dB : DynAt m BK BKS 4 cB bB) :
    (∀ z ∈ bs, Mem.valid_block m z ∧ z ≠ WP ∧ z ≠ WPS ∧ z ≠ WS ∧ z ≠ WSS ∧ z ≠ BK ∧ z ≠ BKS ∧
      z ≠ Block.naugraphBit ∧ (0 < cP → z ≠ bP) ∧ (0 < cS → z ≠ bS) ∧ (0 < cB → z ≠ bB)) ∧
    (0 < cP → bP ≠ WS ∧ bP ≠ WSS ∧ bP ≠ BK ∧ bP ≠ BKS ∧ bP ≠ Block.naugraphBit ∧
      (0 < cS → bP ≠ bS) ∧ (0 < cB → bP ≠ bB)) ∧
    (0 < cS → bS ≠ WP ∧ bS ≠ WPS ∧ bS ≠ BK ∧ bS ≠ BKS ∧ bS ≠ Block.naugraphBit ∧
      (0 < cB → bS ≠ bB)) ∧
    (0 < cB → bB ≠ WP ∧ bB ≠ WPS ∧ bB ≠ WS ∧ bB ≠ WSS ∧ bB ≠ Block.naugraphBit) := by
  have wP := fun h => work_ne hw (dense_inUseW dP h)
  have wS := fun h => work_ne hw (dense_inUseS dS h)
  have wB := fun h => work_ne hw (dense_inUseB dB h)
  have sPS : 0 < cP → 0 < cS → bP ≠ bS := fun h1 h2 =>
    work_sep hw (p := (WP, WPS, 4)) (q := (WS, WSS, 8)) (by simp [denseSlots]) (by simp [denseSlots])
      (by decide) h1 h2 dP dS
  have sPB : 0 < cP → 0 < cB → bP ≠ bB := fun h1 h2 =>
    work_sep hw (p := (WP, WPS, 4)) (q := (BK, BKS, 4)) (by simp [denseSlots]) (by simp [denseSlots])
      (by decide) h1 h2 dP dB
  have sSB : 0 < cS → 0 < cB → bS ≠ bB := fun h1 h2 =>
    work_sep hw (p := (WS, WSS, 8)) (q := (BK, BKS, 4)) (by simp [denseSlots]) (by simp [denseSlots])
      (by decide) h1 h2 dS dB
  refine ⟨fun z hz => ?_, fun h => ⟨(wP h).1.2.2.1, (wP h).1.2.2.2.1, (wP h).1.2.2.2.2.1,
    (wP h).1.2.2.2.2.2.1, (wP h).1.2.2.2.2.2.2.1, sPS h, sPB h⟩,
    fun h => ⟨(wS h).1.1, (wS h).1.2.1, (wS h).1.2.2.2.2.1, (wS h).1.2.2.2.2.2.1,
      (wS h).1.2.2.2.2.2.2.1, sSB h⟩,
    fun h => ⟨(wB h).1.1, (wB h).1.2.1, (wB h).1.2.2.1, (wB h).1.2.2.2.1, (wB h).1.2.2.2.2.2.2.1⟩⟩
  have z := sep_ne hw hsep hz
  exact ⟨z.1, z.2.1.1, z.2.1.2.1, z.2.1.2.2.1, z.2.1.2.2.2.1, z.2.1.2.2.2.2.1, z.2.1.2.2.2.2.2.1,
    z.2.1.2.2.2.2.2.2.1, fun h => z.2.2.2.2.2 (dense_inUseW dP h),
    fun h => z.2.2.2.2.2 (dense_inUseS dS h), fun h => z.2.2.2.2.2 (dense_inUseB dB h)⟩

theorem dense_targetcell (xi : ExternalCalls) : denseRep.TargetcellFn xi denseRep.targetcell := by
  refine ⟨_, by simp [Genv.find_funct, denseRep, Search.funct_targetcellFn], type_targetcellD,
    fun G _ bg gofs bl lofs lab bp pofs ptn level tcLevel dg hint M => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hc, ⟨gw, hg⟩, _, hl, hlsm, _, hp, hps, hpsm, hpl, hlev,
    hh, hh0, htc, hsep⟩ => ?_
  have hw := hc.work
  obtain ⟨⟨cP, bP, dP⟩, ⟨cS, bS, dS⟩, ⟨cB, bB, dB⟩⟩ := dense_dyn hw
  obtain ⟨hz, sP, sS, sB⟩ := dense_pre3 hw hsep dP dS dB
  refine ⟨_, Satisfies.grow (Targetcell.targetcell_satisfies bg gofs gw G.g bl lofs lab bp pofs ptn
    level tcLevel dg hint M cP bP cS bS cB bB),
    ⟨hargs, ⟨hg, hl, hlsm, hp, hps, hpsm, hpl, hlev, dP, dS, dB, hc.tables.1,
      fun z h => hz z (by rcases h with rfl | rfl | rfl <;> simp), sP, sS, sB, hc.n0, hc.nlt, hc.M1,
      hc.Mlt, hc.nM⟩, hh, hh0, htc⟩, ?_⟩
  rintro t v m' ⟨⟨rfl, hv, cP', bP', cS', bS', cB', bB', dP', dS', dB', rP, rS, rB, hu, fPS, fPB,
    fSB⟩, hval⟩
  exact ⟨rfl, hv, dense_step3 hw hval dP dS dB dP' dS' dB' rP rS rB fPS fPB fSB hu
    (fun z h => .inr h) (fun _ h => h.elim)⟩

/-- naugraph.c's globals `refine` reads, and `leftbit`. -/
abbrev refineGlobs : List block :=
  [WP, WPS, WS, WSS, BK, BKS, Block.naugraphBit, Block.naugraphBytecount, Block.leftbit]

kernel_rfl refineGlobs_dec : decide (refineGlobs.Pairwise (· ≠ ·) ∧
  Block.naugraphDnwork ∉ refineGlobs ∧ Block.naugraphDnworkSz ∉ refineGlobs ∧
  Block.nautyBit ∉ refineGlobs ∧ Block.naugraphDnwork ≠ Block.naugraphDnworkSz ∧
  Block.naugraphDnwork ≠ Block.nautyBit ∧ Block.naugraphDnworkSz ≠ Block.nautyBit ∧
  Block.naugraphDnwork ∈ denseGlobs ∧ Block.naugraphDnworkSz ∈ denseGlobs) = true

/-- A pair's block for `refine`'s `Loc`: its block in use, or the stand-in `d`
when its capacity is 0. -/
abbrev SlotBlk (m : mem) (c : Nat) (b b' d : block) : Prop :=
  (0 < c ∧ b' = b ∧ InUse m denseSlots b) ∨ (c = 0 ∧ b' = d)

theorem slotBlk {m : mem} {bp bs : block} {k c : Nat} {b : block} (dd : DynAt m bp bs k c b)
    (hu : 0 < c → InUse m denseSlots b) (d : block) :
    ∃ b', DynAt m bp bs k c b' ∧ SlotBlk m c b b' d := by
  rcases Nat.eq_zero_or_pos c with h0 | hc
  · exact ⟨d, dd.reblock h0 d, .inr ⟨h0, rfl⟩⟩
  · exact ⟨b, dd, .inl ⟨hc, rfl, hu hc⟩⟩

/-- `refine` as naugraph.c implements it meets the dispatch specification. -/
theorem dense_refineFn {xi : ExternalCalls} {M : Nat} {vf : val} (h : Refine.RefineFn xi M vf) :
    denseRep.RefineFn xi M vf := by
  obtain ⟨fd, hfd, hty, hsat⟩ := h
  refine ⟨fd, hfd, hty, fun G _ bg gofs bl lofs lab bp pofs ptn level bn nofs numcells bc cofs ba
    aofs active bk kofs => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hc, ⟨gw, hg⟩, _, hl, hp, hnc, hcnt, ⟨aw, ha, har⟩, hk,
    hok, hps, hncl, hlev, hsep⟩ => ?_
  have hw := hc.work
  obtain ⟨⟨cP, bP, dP⟩, ⟨cS, bS, dS⟩, ⟨cB, bB, dB⟩⟩ := dense_dyn hw
  obtain ⟨bP', dP', eP⟩ := slotBlk dP (dense_inUseW dP) Block.naugraphDnwork
  obtain ⟨bS', dS', eS⟩ := slotBlk dS (dense_inUseS dS) Block.naugraphDnworkSz
  obtain ⟨bB', dB', eB⟩ := slotBlk dB (dense_inUseB dB) Block.nautyBit
  have G0 := of_decide_eq_true refineGlobs_dec
  -- the stand-ins and the blocks in use, against the arguments and the globals
  have argNe : ∀ z ∈ [bg, bl, bp, bn, bc, ba, bk], ∀ {c b b' d}, SlotBlk m c b b' d →
      (d = Block.naugraphDnwork ∨ d = Block.naugraphDnworkSz ∨ d = Block.nautyBit) → z ≠ b' := by
    intro z hz c b b' d e hd
    have zz := sep_ne hw hsep hz
    rcases e with ⟨_, rfl, hu⟩ | ⟨_, rfl⟩
    · exact zz.2.2.2.2.2 hu
    · rcases hd with rfl | rfl | rfl
      · exact fun e => hsep.notGlobs z hz (e ▸ G0.2.2.2.2.2.2.2.1)
      · exact fun e => hsep.notGlobs z hz (e ▸ G0.2.2.2.2.2.2.2.2)
      · exact zz.2.2.2.2.1
  have globNe : ∀ {c b b' d}, SlotBlk m c b b' d →
      (d = Block.naugraphDnwork ∨ d = Block.naugraphDnworkSz ∨ d = Block.nautyBit) →
      ∀ y ∈ refineGlobs, b' ≠ y := by
    intro c b b' d e hd y hy
    rcases e with ⟨_, rfl, hu⟩ | ⟨_, rfl⟩
    · have ww := work_ne hw hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ww.1.1
      · exact ww.1.2.1
      · exact ww.1.2.2.1
      · exact ww.1.2.2.2.1
      · exact ww.1.2.2.2.2.1
      · exact ww.1.2.2.2.2.2.1
      · exact ww.1.2.2.2.2.2.2.1
      · exact ww.1.2.2.2.2.2.2.2
      · exact ww.2.2.1
    · rcases hd with rfl | rfl | rfl
      · exact fun e => G0.2.1 (e ▸ hy)
      · exact fun e => G0.2.2.1 (e ▸ hy)
      · exact fun e => G0.2.2.2.1 (e ▸ hy)
  have workNe : ∀ {c b b' d c₂ b₂ b₂' d₂ : _} {p q : Slot}, p ∈ denseSlots → q ∈ denseSlots → p ≠ q →
      p.At m c b → q.At m c₂ b₂ → SlotBlk m c b b' d → SlotBlk m c₂ b₂ b₂' d₂ → d ≠ d₂ →
      (d = Block.naugraphDnwork ∨ d = Block.naugraphDnworkSz ∨ d = Block.nautyBit) →
      (d₂ = Block.naugraphDnwork ∨ d₂ = Block.naugraphDnworkSz ∨ d₂ = Block.nautyBit) → b' ≠ b₂' := by
    intro c b b' d c₂ b₂ b₂' d₂ p q hp hq hpq dp dq e1 e2 hdd hd1 hd2
    rcases e1 with ⟨h1, rfl, hu1⟩ | ⟨_, rfl⟩ <;> rcases e2 with ⟨h2, rfl, hu2⟩ | ⟨_, rfl⟩
    · exact work_sep hw hp hq hpq h1 h2 dp dq
    · intro e; subst e
      have := hw.1.notin _ hu1
      rcases hd2 with rfl | rfl | rfl
      · exact this (List.mem_append_left _ G0.2.2.2.2.2.2.2.1)
      · exact this (List.mem_append_left _ G0.2.2.2.2.2.2.2.2)
      · exact (work_ne hw hu1).2.2.2 rfl
    · intro e; subst e
      have := hw.1.notin _ hu2
      rcases hd1 with rfl | rfl | rfl
      · exact this (List.mem_append_left _ G0.2.2.2.2.2.2.2.1)
      · exact this (List.mem_append_left _ G0.2.2.2.2.2.2.2.2)
      · exact (work_ne hw hu2).2.2.2 rfl
    · exact hdd
  let L : Refine.Loc := ⟨bg, gofs, gw, bl, lofs, bp, pofs, bn, nofs, bc, cofs, ba, aofs, bk, kofs,
    bP', cP, bS', cS, bB', cB, level, M⟩
  have hd : L.blocks.Pairwise (· ≠ ·) := by
    rw [Refine.Loc.blocks_eq, List.pairwise_append, List.pairwise_append]
    refine ⟨⟨hsep.distinct, ?_, ?_⟩, G0.1, ?_⟩
    · exact pw3_mk (workNe (p := (WP, WPS, 4)) (q := (WS, WSS, 8)) (by simp [denseSlots])
          (by simp [denseSlots]) (by decide) dP dS eP eS G0.2.2.2.2.1 (.inl rfl) (.inr (.inl rfl)))
        (workNe (p := (WP, WPS, 4)) (q := (BK, BKS, 4)) (by simp [denseSlots])
          (by simp [denseSlots]) (by decide) dP dB eP eB G0.2.2.2.2.2.1 (.inl rfl) (.inr (.inr rfl)))
        (workNe (p := (WS, WSS, 8)) (q := (BK, BKS, 4)) (by simp [denseSlots])
          (by simp [denseSlots]) (by decide) dS dB eS eB G0.2.2.2.2.2.2.1 (.inr (.inl rfl))
          (.inr (.inr rfl)))
    · intro z hz y hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · exact argNe z hz eP (.inl rfl)
      · exact argNe z hz eS (.inr (.inl rfl))
      · exact argNe z hz eB (.inr (.inr rfl))
    · intro z hz y hy
      rcases List.mem_append.1 hz with hz | hz
      · have zz := sep_ne hw hsep hz
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact zz.2.1.1
        · exact zz.2.1.2.1
        · exact zz.2.1.2.2.1
        · exact zz.2.1.2.2.2.1
        · exact zz.2.1.2.2.2.2.1
        · exact zz.2.1.2.2.2.2.2.1
        · exact zz.2.1.2.2.2.2.2.2.1
        · exact zz.2.1.2.2.2.2.2.2.2
        · exact zz.2.2.2.1
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl
        · exact globNe eP (.inl rfl) y hy
        · exact globNe eS (.inr (.inl rfl)) y hy
        · exact globNe eB (.inr (.inr rfl)) y hy
  have hvA : ∀ z ∈ [bg, bl, bp, bn, bc, ba, bk], Mem.valid_block m z := hsep.valid
  refine ⟨_, Satisfies.grow (hsat L rfl G lab ptn active numcells aw),
    ⟨hargs, ⟨hd, hc.n0, hc.nM, hc.M1, hc.Mlt, hlev, hc.nlt⟩,
      ⟨hg, hl, hp, hnc, ha, har, hcnt, dP', dS', dB', hc.tables.1, hc.tables.2, hc.etables.left⟩,
      hk, hvA, hok, hps, hncl⟩, ?_⟩
  rintro t v m' ⟨⟨rfl, cW₁, bW₁, cS₁, bS₁, cB₁, bB₁, aw', hm', hk', -, -, rW, rS, rB, nWS, nWB, nSB, hu,
    hkeep⟩, hval⟩
  -- the relations to the pairs before, through the stand-ins
  have rel : ∀ {bp bs : block} {k c c' : Nat} {b b' b'' d : block}, DynAt m bp bs k c b →
      SlotBlk m c b b' d → ((c' = c ∧ b'' = b') ∨ ¬ Mem.valid_block m b'') →
      (c' = c ∧ (0 < c → b'' = b)) ∨ ¬ Mem.valid_block m b'' := by
    intro bp bs k c c' b b' b'' d _ e r
    rcases r with ⟨rfl, rfl⟩ | r
    · rcases e with ⟨_, rfl, _⟩ | ⟨h0, _⟩
      · exact .inl ⟨rfl, fun _ => rfl⟩
      · exact .inl ⟨rfl, fun hc => absurd h0 (by omega)⟩
    · exact .inr r
  have toNext : ∀ {bp bs : block} {k c c' : Nat} {b b'' : block}, DynAt m bp bs k c b →
      DynAt m' bp bs k c' b'' → ((c' = c ∧ (0 < c → b'' = b)) ∨ ¬ Mem.valid_block m b'') →
      (c' = c ∧ b'' = b) ∨ ¬ Mem.valid_block m b'' ∨ (c' = 0 ∧ c = 0) := by
    intro bp bs k c c' b b'' _ _ r
    rcases r with ⟨rfl, h⟩ | r
    · rcases Nat.eq_zero_or_pos c' with h0 | hc
      · exact .inr (.inr ⟨h0, h0⟩)
      · exact .inl ⟨rfl, h hc⟩
    · exact .inr (.inl r)
  -- a capacity-0 pair after the call holds its old block too
  have fix : ∀ {bp bs : block} {k c c' : Nat} {b b'' : block}, DynAt m bp bs k c b →
      DynAt m' bp bs k c' b'' → ((c' = c ∧ (0 < c → b'' = b)) ∨ ¬ Mem.valid_block m b'') →
      ∃ b₃, DynAt m' bp bs k c' b₃ ∧ ((c' = c ∧ b₃ = b) ∨ ¬ Mem.valid_block m b₃) ∧
        (0 < c' → b₃ = b'') := by
    intro bp bs k c c' b b'' d d' r
    rcases toNext d d' r with h | h | ⟨h0, h0'⟩
    · exact ⟨b'', d', .inl h, fun _ => rfl⟩
    · exact ⟨b'', d', .inr h, fun _ => rfl⟩
    · exact ⟨b, d'.reblock h0 b, .inl ⟨by omega, rfl⟩, fun hc => absurd h0 (by omega)⟩
  obtain ⟨bW₃, dW₃, rW₃, eW₃⟩ := fix dP hm'.dW (rel dP eP rW)
  obtain ⟨bS₃, dS₃, rS₃, eS₃⟩ := fix dS hm'.dS (rel dS eS rS)
  obtain ⟨bB₃, dB₃, rB₃, eB₃⟩ := fix dB hm'.dB (rel dB eB rB)
  have nPS : 0 < cW₁ → 0 < cS₁ → bW₃ ≠ bS₃ := fun h1 h2 => by rw [eW₃ h1, eS₃ h2]; exact nWS
  have nPB : 0 < cW₁ → 0 < cB₁ → bW₃ ≠ bB₃ := fun h1 h2 => by rw [eW₃ h1, eB₃ h2]; exact nWB
  have nSB' : 0 < cS₁ → 0 < cB₁ → bS₃ ≠ bB₃ := fun h1 h2 => by rw [eS₃ h1, eB₃ h2]; exact nSB
  -- `dyn3Set` with the stand-ins is `dyn3Set` with the old blocks
  have d3 : ∀ z, Alloc.dyn3Set m cP bP' cS bS' cB bB' z → Alloc.dyn3Set m cP bP cS bS cB bB z := by
    intro z h
    rcases h with e | e | e | e | e | e | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | h
    · exact .inl e
    · exact .inr (.inl e)
    · exact .inr (.inr (.inl e))
    · exact .inr (.inr (.inr (.inl e)))
    · exact .inr (.inr (.inr (.inr (.inl e))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl e)))))
    · rcases eP with ⟨_, e2, _⟩ | ⟨h0, _⟩
      · rw [e2] at e; exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h, e⟩))))))
      · omega
    · rcases eS with ⟨_, e2, _⟩ | ⟨h0, _⟩
      · rw [e2] at e; exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h, e⟩)))))))
      · omega
    · rcases eB with ⟨_, e2, _⟩ | ⟨h0, _⟩
      · rw [e2] at e; exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h, e⟩))))))))
      · omega
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))))
  refine ⟨rfl, hm'.lab, hm'.ptn, hm'.nc, hm'.cnt, ⟨aw', hm'.act, hm'.actRep⟩, hk',
    dense_step3 hw hval dP dS dB dW₃ dS₃ dB₃ rW₃ rS₃ rB₃ nPS nPB nSB' hu ?_ ?_⟩
  · rintro z ((e | e | e | e | e) | e | h)
    · subst e; exact .inl (by simp)
    · subst e; exact .inl (by simp)
    · subst e; exact .inl (by simp)
    · subst e; exact .inl (by simp)
    · subst e; exact .inl (by simp)
    · subst e; exact .inl (by simp)
    · exact .inr (d3 z h)
  · intro z hz _
    exact hkeep z (by simpa using hz)

theorem dense_refine (xi : ExternalCalls) (M : Nat) :
    denseRep.RefineFn xi M (.Vptr (denseRep.refineAt M) Ptrofs.zero) := by
  unfold DispatchRep.refineAt
  by_cases h : M = 1
  · subst h; simp only [ite_true]; exact dense_refineFn Refine.refineFn_refine1'
  · simp only [h, ite_false]; exact dense_refineFn (Refine.refineFn_refine' M)

theorem dense_freedyn (xi : ExternalCalls) : denseRep.FreedynFn xi denseRep.freedyn := by
  refine ⟨_, by simp [Genv.find_funct, denseRep, Search.funct_naugraphFreedyn], type_freedynD,
    fun capD bD => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hw, dD, hbD⟩ => ?_
  obtain ⟨⟨cP, bP, dP⟩, ⟨cS, bS, dS⟩, ⟨cB, bB, dB⟩⟩ := dense_dyn hw
  have wP := fun h => work_ne hw (dense_inUseW dP h)
  have wS := fun h => work_ne hw (dense_inUseS dS h)
  have wB := fun h => work_ne hw (dense_inUseB dB h)
  have sPS : 0 < cP → 0 < cS → bP ≠ bS := fun h1 h2 =>
    work_sep hw (p := (WP, WPS, 4)) (q := (WS, WSS, 8)) (by simp [denseSlots]) (by simp [denseSlots])
      (by decide) h1 h2 dP dS
  have sPB : 0 < cP → 0 < cB → bP ≠ bB := fun h1 h2 =>
    work_sep hw (p := (WP, WPS, 4)) (q := (BK, BKS, 4)) (by simp [denseSlots]) (by simp [denseSlots])
      (by decide) h1 h2 dP dB
  have sSB : 0 < cS → 0 < cB → bS ≠ bB := fun h1 h2 =>
    work_sep hw (p := (WS, WSS, 8)) (q := (BK, BKS, 4)) (by simp [denseSlots]) (by simp [denseSlots])
      (by decide) h1 h2 dS dB
  have hok : Alloc.FreeD.Ok m (Top.naugraphDs cS bS cP bP cB bB capD bD) := by
    refine ⟨fun d hd => ?_, fun d hd => ?_, by simp [Alloc.FreeD.globals, Top.naugraphDs]; decide,
      fun d hd hc => ?_, ?_⟩
    · simp only [Top.naugraphDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact ⟨Program.find_naugraphWorksetSz, Program.find_naugraphWorkset⟩
      · exact ⟨Program.find_naugraphWorkpermSz, Program.find_naugraphWorkperm⟩
      · exact ⟨Program.find_naugraphBucketSz, Program.find_naugraphBucket⟩
      · exact ⟨Program.find_naugraphDnworkSz, Program.find_naugraphDnwork⟩
    · simp only [Top.naugraphDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact dS
      · exact dP
      · exact dB
      · exact dD
    · simp only [Top.naugraphDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
      simp only [Alloc.FreeD.globals, Top.naugraphDs, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
        or_false, not_or]
      rcases hd with rfl | rfl | rfl | rfl
      · have w := (wS hc).1
        exact ⟨w.2.2.2.1, w.2.2.1, w.2.1, w.1, w.2.2.2.2.2.1, w.2.2.2.2.1,
          fun e => (hw.1.notin _ (dense_inUseS dS hc)) (by simp only at e; rw [e]; simp [denseL, denseGlobs]),
          fun e => (hw.1.notin _ (dense_inUseS dS hc)) (by simp only at e; rw [e]; simp [denseL, denseGlobs])⟩
      · have w := (wP hc).1
        exact ⟨w.2.2.2.1, w.2.2.1, w.2.1, w.1, w.2.2.2.2.2.1, w.2.2.2.2.1,
          fun e => (hw.1.notin _ (dense_inUseW dP hc)) (by simp only at e; rw [e]; simp [denseL, denseGlobs]),
          fun e => (hw.1.notin _ (dense_inUseW dP hc)) (by simp only at e; rw [e]; simp [denseL, denseGlobs])⟩
      · have w := (wB hc).1
        exact ⟨w.2.2.2.1, w.2.2.1, w.2.1, w.1, w.2.2.2.2.2.1, w.2.2.2.2.1,
          fun e => (hw.1.notin _ (dense_inUseB dB hc)) (by simp only at e; rw [e]; simp [denseL, denseGlobs]),
          fun e => (hw.1.notin _ (dense_inUseB dB hc)) (by simp only at e; rw [e]; simp [denseL, denseGlobs])⟩
      · have w := ne_globs (hbD hc).2
        exact ⟨w.2.2.2.1, w.2.2.1, w.2.1, w.1, w.2.2.2.2.2.1, w.2.2.2.2.1, (dD.bne hc).1,
          (dD.bne hc).2⟩
    · simp only [Top.naugraphDs, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
        forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
      exact ⟨⟨fun h1 h2 => (sPS h2 h1).symm, sSB,
          fun h1 h2 e => (hbD h2).1 (e ▸ dense_inUseS dS h1)⟩,
        ⟨sPB, fun h1 h2 e => (hbD h2).1 (e ▸ dense_inUseW dP h1)⟩,
        fun h1 h2 e => (hbD h2).1 (e ▸ dense_inUseB dB h1)⟩
  refine ⟨_, Top.naugraphFreedyn_satisfies cS bS cP bP cB bB capD bD, ⟨hargs, hok⟩, ?_⟩
  rintro t v m' ⟨rfl, hD, hu, hnb⟩
  refine ⟨rfl, hu.mono fun z hz => ?_, fun b => hD ⟨dense.id.«naugraph:dnwork», dense.id.«naugraph:dnwork_sz», Block.naugraphDnwork,
    Block.naugraphDnworkSz, tulong, 8, capD, bD⟩ (by simp [Top.naugraphDs]) 8 b, hnb⟩
  rcases hz with hz | ⟨d, hd, hc, rfl⟩
  · simp only [Alloc.FreeD.globals, Top.naugraphDs, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact .inr (.inl rfl)
      | exact .inr (.inr (.inl rfl))
      | exact .inl (by simp [denseRep, denseWGlobs])
  · simp only [Top.naugraphDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact .inr (.inr (.inr (.inl (dense_inUseS dS hc))))
    · exact .inr (.inr (.inr (.inl (dense_inUseW dP hc))))
    · exact .inr (.inr (.inr (.inl (dense_inUseB dB hc))))
    · exact .inr (.inr (.inr (.inr ⟨hc, rfl⟩)))

/-- naugraph.c's `dispatch_graph`, with its procedures' specifications. -/
def dense : DispatchC Program.ge denseOps where
  toDispatchRep := denseRep
  isautom_fn := dense_isautom
  testcanlab_fn := dense_testcanlab
  updatecan_fn := dense_updatecan
  refine_fn := dense_refine
  cheapautom_fn := dense_cheapautom
  targetcell_fn := dense_targetcell
  check_fn := dense_check
  freedyn_fn := dense_freedyn
  init_fn _ h := absurd rfl h

end NautyVerified.Proofs.Dispatch
