import NautyVerified.Proofs.Dispatch.Spec
import NautyVerified.Proofs.Doref.Satisfies

/-!
# `doref` calling a dispatch `refine`

`DispatchRep.refinePre_unch`: `refineSpec`'s precondition survives a step
that changes none of its argument blocks, the procedures' globals, their
scratch blocks in use or the shared tables.

`DispatchRep.doref_refine`: with `refproc` a dispatch refinement procedure,
the two conditions `dorefSpecR` places on it hold: `refineSpec`'s
precondition after nautil.c's `DYNALLOC1` of `workperm`, and a call leaving
`*qinvar` and nautil.c's `workperm` pair alone.
-/

namespace NautyVerified.Proofs.Dispatch

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program
open NautyVerified.Proofs.Alloc (DynAt)
open Hex.GraphIso.Nauty

variable {ge : genv} [E : NautyEnv ge] {O : Ops} (R : DispatchRep ge O)

namespace DispatchRep

theorem refinePre_unch {n : Nat} {G : O.Gr n} {gl : R.GLoc} {bg : block} {gofs : ptrofs} {bl : block}
    {lofs : ptrofs} {lab : Array Nat} {bp : block} {pofs : ptrofs} {ptn : Array Nat} {level : Nat}
    {bn : block} {nofs : ptrofs} {numcells : Nat} {bc : block} {cofs : ptrofs} {ba : block}
    {aofs : ptrofs} {active : VSet n} {bk : block} {kofs : ptrofs} {M : Nat} {args : List val}
    {m m₁ : mem}
    (h : (R.refineSpec G gl bg gofs bl lofs lab bp pofs ptn level bn nofs numcells bc cofs ba aofs
      active bk kofs M).pre args m)
    {W : block → Prop} (hu : Unch m m₁ W) (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m₁ z)
    (hW : ∀ z, W z → z ∉ R.graphBlocks gl bg ++ [bl, bp, bn, bc, ba, bk] ∧ z ∉ R.globs ∧
      ¬ R.IsWork m z ∧ z ≠ E.nautyBit ∧ z ≠ E.nautilBit ∧ z ≠ E.leftbit) :
    (R.refineSpec G gl bg gofs bl lofs lab bp pofs ptn level bn nofs numcells bc cofs ba aofs active bk
      kofs M).pre args m₁ := by
  obtain ⟨hargs, hc, hg, hgo, hl, hp, hnc, ⟨v, hcnt⟩, ⟨aw, ha, har⟩, ⟨kv, hk⟩, hok, hps, hncl, hlev,
    hsep⟩ := h
  have hwk := R.work_unch hc.work hu (fun z hz hWz => (hW z hWz).2.1 (R.wglobs_sub z hz))
    (fun z hz hWz => (hW z hWz).2.2.1 hz) hv
  have nA : ∀ z ∈ R.graphBlocks gl bg ++ [bl, bp, bn, bc, ba, bk], ¬ W z :=
    fun z hz hWz => (hW z hWz).1 hz
  refine ⟨hargs, ⟨hwk.1, R.tables_unch hc.tables hu fun z hz _ hWz => (hW z hWz).2.1 hz,
    hc.etables.unch hu (fun hWz => (hW _ hWz).2.2.2.1 rfl) (fun hWz => (hW _ hWz).2.2.2.2.1 rfl)
      (fun hWz => (hW _ hWz).2.2.2.2.2 rfl), hc.n0, hc.nlt, hc.M1, hc.Mlt, hc.nM⟩,
    R.graph_unch hg hu (fun z hz => nA z (List.mem_append_left _ hz)), hgo, hl.unch hu (nA bl (by simp)),
    hp.unch hu (nA bp (by simp)), hnc.unch hu (nA bn (by simp)),
    ⟨v, hcnt.unch hu (nA bc (by simp))⟩, ⟨aw, ha.unch hu (nA ba (by simp)), har⟩,
    ⟨kv, hk.unch hu (nA bk (by simp))⟩, hok, hps, hncl, hlev,
    ⟨hsep.distinct, fun z hz => hv z (hsep.valid z hz),
      fun z hz hw => hsep.notWork z hz (hwk.2 z hw), hsep.notGlobs, hsep.notTab⟩⟩

local notation "NWP" => E.nautilWorkperm
local notation "NWPS" => E.nautilWorkpermSz

/-- The conditions `dorefSpecR` places on a dispatch refinement procedure. -/
theorem doref_refine {n : Nat} (G : O.Gr n) (gl : R.GLoc) (L : Refine.Loc) (lab ptn : Array Nat) (numcells : Nat)
    (active : VSet n) {m : mem} {bq : block} {capN : Nat} {bN : block}
    (h : (R.refineSpec G gl L.bg L.gofs L.bl L.lofs lab L.bp L.pofs ptn L.level L.bn L.nofs numcells
      L.bc L.cofs L.ba L.aofs active L.bk L.kofs L.M).pre (Doref.refArgs L n) m)
    (hN : ∀ z ∈ (R.graphBlocks gl L.bg ++ [L.bl, L.bp, L.bn, L.bc, L.ba, L.bk]), z ≠ NWP ∧ z ≠ NWPS ∧ (0 < capN → z ≠ bN))
    (hbN : 0 < capN → bN ∉ R.globs ∧ ¬ R.IsWork m bN ∧ bN ∉ E.blocks)
    (hgv : ∀ z ∈ R.globs, Mem.valid_block m z)
    (hEv : ∀ z ∈ [E.nautyBit, E.nautilBit, E.leftbit], Mem.valid_block m z)
    (hq : bq ∉ (R.graphBlocks gl L.bg ++ [L.bl, L.bp, L.bn, L.bc, L.ba, L.bk]) ∧ bq ∉ R.globs ∧ ¬ R.IsWork m bq ∧
      Mem.valid_block m bq) :
    (∀ m₁, Unch m m₁ (Doref.NSet m capN bN) → (∀ z, Mem.valid_block m z → Mem.valid_block m₁ z) →
      (R.refineSpec G gl L.bg L.gofs L.bl L.lofs lab L.bp L.pofs ptn L.level L.bn L.nofs numcells
        L.bc L.cofs L.ba L.aofs active L.bk L.kofs L.M).pre (Doref.refArgs L n) m₁) ∧
    (∀ m₁ c' b', Unch m m₁ (Doref.NSet m capN bN) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m₁ z) →
      DynAt m₁ NWP NWPS 4 c' b' → ((c' = capN ∧ b' = bN) ∨ ¬ Mem.valid_block m b') →
      ∀ t v m₂, (R.refineSpec G gl L.bg L.gofs L.bl L.lofs lab L.bp L.pofs ptn L.level L.bn L.nofs
        numcells L.bc L.cofs L.ba L.aofs active L.bk L.kofs L.M).post (Doref.refArgs L n) m₁ t v m₂ →
        t = E0 ∧ ∃ W : block → Prop, Unch m₁ m₂ W ∧ ¬ W bq ∧ ¬ W NWP ∧ ¬ W NWPS ∧
          (0 < c' → ¬ W b')) := by
  have hc := h.2.1
  have hsep := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have eB : NWP ∈ E.blocks ∧ NWPS ∈ E.blocks := by simp [NautyEnv.blocks]
  have eA : NWP ∈ envAvoid ∧ NWPS ∈ envAvoid := by simp
  -- what the `DYNALLOC1` may change
  have nset : ∀ z, Doref.NSet m capN bN z → z ∉ (R.graphBlocks gl L.bg ++ [L.bl, L.bp, L.bn, L.bc, L.ba, L.bk]) ∧
      z ∉ R.globs ∧ ¬ R.IsWork m z ∧ z ≠ E.nautyBit ∧ z ≠ E.nautilBit ∧ z ≠ E.leftbit := by
    rintro z (rfl | rfl | ⟨hc', rfl⟩ | hnv)
    · refine ⟨fun hz => (hN _ hz).2.1 rfl, fun hz => R.globs_env _ hz eB.2,
        fun hw => (R.isWork_globs hc.work hw).2 eA.2, by env_ne, by env_ne, by env_ne⟩
    · refine ⟨fun hz => (hN _ hz).1 rfl, fun hz => R.globs_env _ hz eB.1,
        fun hw => (R.isWork_globs hc.work hw).2 eA.1, by env_ne, by env_ne, by env_ne⟩
    · have hb := hbN hc'
      refine ⟨fun hz => (hN _ hz).2.2 hc' rfl, hb.1, hb.2.1, fun e => hb.2.2 (e ▸ ?_),
        fun e => hb.2.2 (e ▸ ?_), fun e => hb.2.2 (e ▸ ?_)⟩ <;> simp [NautyEnv.blocks]
    · refine ⟨fun hz => hnv (hsep.valid z hz), fun hz => hnv (hgv z hz),
        fun hw => hnv (R.isWork_valid hw), fun e => hnv (e ▸ hEv _ (by simp)),
        fun e => hnv (e ▸ hEv _ (by simp)), fun e => hnv (e ▸ hEv _ (by simp))⟩
  refine ⟨fun m₁ hu hv => R.refinePre_unch h hu hv nset, ?_⟩
  intro m₁ c' b' hu hv hD1 hb' t v m₂ hpost
  have h₁ := R.refinePre_unch h hu hv nset
  have hwk := R.work_unch hc.work hu (fun z hz hz' => (nset z hz').2.1 (R.wglobs_sub z hz))
    (fun z hz hz' => (nset z hz').2.2.1 hz) hv
  obtain ⟨rfl, -, -, -, -, -, -, hstep⟩ := hpost
  refine ⟨rfl, _, hstep.unch, ?_, ?_, ?_, ?_⟩
  · rintro (h1 | h1 | h1 | h1)
    · exact hq.1 (List.mem_append_right _ h1)
    · exact hq.2.1 (R.wglobs_sub _ h1)
    · exact hq.2.2.1 (hwk.2 _ h1)
    · exact h1 (hv _ hq.2.2.2)
  · rintro (h1 | h1 | h1 | h1)
    · exact (hN _ (List.mem_append_right _ h1)).1 rfl
    · exact R.globs_env _ (R.wglobs_sub _ h1) eB.1
    · exact (R.isWork_globs hwk.1 h1).2 eA.1
    · exact h1 (Alloc.valid_of_access hD1.bpW)
  · rintro (h1 | h1 | h1 | h1)
    · exact (hN _ (List.mem_append_right _ h1)).2.1 rfl
    · exact R.globs_env _ (R.wglobs_sub _ h1) eB.2
    · exact (R.isWork_globs hwk.1 h1).2 eA.2
    · exact h1 (Alloc.valid_of_access hD1.bsW)
  · intro hc' hW
    have hvb : Mem.valid_block m₁ b' := Alloc.Malloced.valid (hD1.mal hc')
    rcases hb' with ⟨rfl, rfl⟩ | hnv
    · have hb := hbN hc'
      rcases hW with h1 | h1 | h1 | h1
      · exact (hN _ (List.mem_append_right _ h1)).2.2 hc' rfl
      · exact hb.1 (R.wglobs_sub _ h1)
      · exact hb.2.1 (hwk.2 _ h1)
      · exact h1 hvb
    · rcases hW with h1 | h1 | h1 | h1
      · exact hnv (hsep.valid _ (List.mem_append_right _ h1))
      · exact hnv (hgv _ (R.wglobs_sub _ h1))
      · exact hnv (R.isWork_valid (hwk.2 _ h1))
      · exact h1 hvb

end DispatchRep

end NautyVerified.Proofs.Dispatch
