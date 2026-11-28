import NautyVerified.Proofs.Search.Frame
import NautyVerified.Proofs.Search.Valid
import NautyVerified.Proofs.Alloc.Dyn3

/-!
# `SearchAt` across a reallocation of naugraph.c's work arrays

A callee such as `maketargetcell`, `testcanlab` or `refine` may reallocate
naugraph.c's `workperm`, `workset` and `bucket`: it changes only `dyn3Set`
(the six globals, the old arrays in use, and blocks not valid before) and
blocks `X` outside `S`. `SearchAt.realloc` rebuilds the search state from the
callee's new `DynAt`s, its freshness disjunctions, and the distinctness of
the new arrays.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep dyn3Set)
open Hex.GraphIso.Nauty

/-- `z` is one of naugraph.c's six work globals. -/
abbrev G6 (z : block) : Prop :=
  z = Block.naugraphWorkpermSz ∨ z = Block.naugraphWorkperm ∨ z = Block.naugraphWorksetSz ∨
    z = Block.naugraphWorkset ∨ z = Block.naugraphBucketSz ∨ z = Block.naugraphBucket

set_option maxHeartbeats 2000000 in
theorem SearchAt.realloc {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    (hvU : Mem.valid_block m S.bUA)
    (hvT : Mem.valid_block m Block.tcnode0)
    {cW cS cB cN : Nat} {bW bS bB bN : block}
    (dN : DynAt m Block.nautilWorkperm Block.nautilWorkpermSz 4 cN bN)
    (nW : 0 < cW → bW ∉ S.blocks) (nS : 0 < cS → bS ∉ S.blocks) (nB : 0 < cB → bB ∉ S.blocks)
    (nN : 0 < cN → bN ∉ S.blocks)
    (pNW : 0 < cN → 0 < cW → bN ≠ bW) (pNS : 0 < cN → 0 < cS → bN ≠ bS)
    (pNB : 0 < cN → 0 < cB → bN ≠ bB)
    {X : block → Prop} (hu : Unch m m' (fun z => dyn3Set m cW bW cS bS cB bB z ∨ X z))
    (hX : ∀ z ∈ S.blocks, ¬ X z) (hXN : 0 < cN → ¬ X bN)
    {cW' cS' cB' : Nat} {bW' bS' bB' : block}
    (dW' : DynAt m' Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW' bW')
    (dS' : DynAt m' Block.naugraphWorkset Block.naugraphWorksetSz 8 cS' bS')
    (dB' : DynAt m' Block.naugraphBucket Block.naugraphBucketSz 4 cB' bB')
    (fW : (cW' = cW ∧ bW' = bW) ∨ ¬ Mem.valid_block m bW')
    (fS : (cS' = cS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS')
    (fB : (cB' = cB ∧ bB' = bB) ∨ ¬ Mem.valid_block m bB')
    (pWS : 0 < cW' → 0 < cS' → bW' ≠ bS') (pWB : 0 < cW' → 0 < cB' → bW' ≠ bB')
    (pSB : 0 < cS' → 0 < cB' → bS' ≠ bB') :
    SearchAt m' S ctx st pre nsp := by
  have hv := h.valid_all hvU hvT
  have hd := h.distinct
  -- blocks of `S` other than the six globals are untouched
  have key : ∀ z ∈ S.blocks, ¬ G6 z → ¬ (dyn3Set m cW bW cS bS cB bB z ∨ X z) := by
    intro z hz hg
    rintro (h6 | hx)
    · unfold dyn3Set at h6
      rcases h6 with e | e | e | e | e | e | ⟨hc, e⟩ | ⟨hc, e⟩ | ⟨hc, e⟩ | hnv
      · exact hg (.inl e)
      · exact hg (.inr (.inl e))
      · exact hg (.inr (.inr (.inl e)))
      · exact hg (.inr (.inr (.inr (.inl e))))
      · exact hg (.inr (.inr (.inr (.inr (.inl e)))))
      · exact hg (.inr (.inr (.inr (.inr (.inr e)))))
      · exact nW hc (e ▸ hz)
      · exact nS hc (e ▸ hz)
      · exact nB hc (e ▸ hz)
      · exact hnv (hv z hz)
    · exact hX z hz hx
  have notIn : ∀ {b : block} {c c' : Nat} {b₀ : block}, (0 < c → b₀ ∉ S.blocks) →
      ((c' = c ∧ b = b₀) ∨ ¬ Mem.valid_block m b) → 0 < c' → b ∉ S.blocks := by
    intro b c c' b₀ hn hf hc hb
    rcases hf with ⟨rfl, rfl⟩ | hnv
    · exact hn hc hb
    · exact hnv (hv b hb)
  have neN : ∀ {b : block} {c c' : Nat} {b₀ : block}, (0 < cN → 0 < c → bN ≠ b₀) →
      ((c' = c ∧ b = b₀) ∨ ¬ Mem.valid_block m b) → 0 < cN → 0 < c' → bN ≠ b := by
    intro b c c' b₀ hp hf hcN hc e
    rcases hf with ⟨rfl, rfl⟩ | hnv
    · exact hp hcN hc e
    · exact hnv (e ▸ Alloc.Malloced.valid (dN.mal hcN))
  have gN : ∀ z ∈ [Block.nautilWorkperm, Block.nautilWorkpermSz],
      ¬ (dyn3Set m cW bW cS bS cB bB z ∨ X z) := by
    intro z hz
    apply key z (by revert z; simp [SLoc.blocks])
    revert z hz
    sep_all hd
  have kN : 0 < cN → ¬ (dyn3Set m cW bW cS bS cB bB bN ∨ X bN) := by
    intro hc
    rintro (h6 | hx)
    · unfold dyn3Set at h6
      have hbn := nN hc
      have hG : ∀ g ∈ S.blocks, bN ≠ g := fun g hg e => hbn (e ▸ hg)
      rcases h6 with e | e | e | e | e | e | ⟨hc', e⟩ | ⟨hc', e⟩ | ⟨hc', e⟩ | hnv
      · exact hG _ (by simp [SLoc.blocks]) e
      · exact hG _ (by simp [SLoc.blocks]) e
      · exact hG _ (by simp [SLoc.blocks]) e
      · exact hG _ (by simp [SLoc.blocks]) e
      · exact hG _ (by simp [SLoc.blocks]) e
      · exact hG _ (by simp [SLoc.blocks]) e
      · exact pNW hc hc' e
      · exact pNS hc hc' e
      · exact pNB hc hc' e
      · exact hnv (Alloc.Malloced.valid (dN.mal hc))
    · exact hXN hc hx
  refine
    { h with
      fixed := h.fixed.unch hu fun z hz => key z (by revert z hz; simp [SLoc.blocks])
        (by revert z hz; sep_all hd)
      scalars := h.scalars.unch hu fun z hz => key z (by revert z hz; simp [SLoc.blocks])
        (by revert z hz; sep_all hd)
      stats := h.stats.unch hu (key _ (by simp [SLoc.blocks]) (by
        show ¬ G6 S.bst
        simp only [not_or]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sep_ne hd))
      arrays := h.arrays.unch hu fun z hz => key z (by revert z hz; simp [SLoc.blocks])
        (by revert z hz; sep_all hd)
      dyns := h.dyns.unch hu fun z hz => key z (by revert z hz; simp [SLoc.blocks])
        (by revert z hz; sep_all hd)
      tables := h.tables.unch hu fun z hz => key z (by revert z hz; simp [SLoc.blocks])
        (by revert z hz; sep_all hd)
      work := ⟨⟨cW', bW', cS', bS', cB', bB', cN, bN, dW', dS', dB',
        dN.keep hu (gN _ (by simp)) (gN _ (by simp)) fun hc => Keep.unch hu (kN hc),
        notIn nW fW, notIn nS fS, notIn nB fB, nN, pWS, pWB, pSB,
        neN pNW fW, neN pNS fS, neN pNB fB⟩⟩ }

end NautyVerified.Proofs.Search
