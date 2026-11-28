import NautyVerified.Proofs.Search.Node.Realloc
import NautyVerified.Proofs.Search.Node.Rebuild
import NautyVerified.Proofs.Search.Valid

/-!
# `SearchAt` after writes and work-array reallocation together

`SearchAt.reallocW`: after a callee that writes some of `S`'s own blocks (all
within `S.wr`, keeping the `DYNALLSTAT` targets' headers) and reallocates any of
naugraph.c's and nautil.c's work arrays, `SearchAt` holds for the new state. It
combines `SearchAt.rebuild` (writes) and `SearchAt.realloc` (work arrays), as
`doref` needs: nautil.c's `workperm`, then refinement's writes and naugraph.c's
work arrays, then the `qinvar` cell.
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

/-- naugraph.c's six work globals and nautil.c's two. -/
abbrev G8 (z : block) : Prop :=
  G6 z ∨ z = Block.nautilWorkpermSz ∨ z = Block.nautilWorkperm

/-- What a nautil.c `DYNALLOC1` of `workperm` may change. -/
abbrev nautilSet (m : mem) (cN : Nat) (bN : block) (z : block) : Prop :=
  z = Block.nautilWorkpermSz ∨ z = Block.nautilWorkperm ∨ (0 < cN ∧ z = bN) ∨
    ¬ Mem.valid_block m z

/-- A global of `S.blocks` that the search's statements do not write is not in `S.wr`. -/
theorem SLoc.glob_not_wr {S : SLoc} (hv : ∀ a ∈ S.vars, ∀ b ∈ globs, a ≠ b) {z : block}
    (h1 : z ∉ wrG) (h2 : z ∈ globs) : z ∉ S.wr := by
  intro hz
  rcases List.mem_append.1 hz with h | h
  · exact h1 h
  · exact hv _ (SLoc.wrV_sub _ _ h) _ h2 rfl

theorem Dyns.keepW {n : Nat} {m m' : mem} {S : SLoc} {W : block → Prop} (h : Dyns n m S)
    (hu : Unch m m' W)
    (hW : ∀ z ∈ [Program.Block.nautyActive, Program.Block.nautyActiveSz,
      Program.Block.nautyFixedpts, Program.Block.nautyFixedptsSz, Program.Block.nautyWorkperm,
      Program.Block.nautyWorkpermSz, Program.Block.nautyFirstlab, Program.Block.nautyFirstlabSz,
      Program.Block.nautyCanonlab, Program.Block.nautyCanonlabSz, Program.Block.nautyFirstcode,
      Program.Block.nautyFirstcodeSz, Program.Block.nautyCanoncode,
      Program.Block.nautyCanoncodeSz, Program.Block.nautyFirsttc, Program.Block.nautyFirsttcSz,
      Block.naugraphDnwork, Block.naugraphDnworkSz],
      ¬ W z)
    (hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws], Keep m m' z) :
    Dyns n m' S := by
  simp only [List.forall_mem_cons] at hW hK
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, -⟩ := hW
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, -⟩ := hK
  exact { h with
    workspace := h.workspace.keep hu g17 g18 fun _ => k9
    active := h.active.keep hu g1 g2 fun _ => k1
    fixedpts := h.fixedpts.keep hu g3 g4 fun _ => k2
    workperm := h.workperm.keep hu g5 g6 fun _ => k3
    firstlab := h.firstlab.keep hu g7 g8 fun _ => k4
    canonlab := h.canonlab.keep hu g9 g10 fun _ => k5
    firstcode := h.firstcode.keep hu g11 g12 fun _ => k6
    canoncode := h.canoncode.keep hu g13 g14 fun _ => k7
    firsttc := h.firsttc.keep hu g15 g16 fun _ => k8 }

set_option maxHeartbeats 2000000 in
/-- `SearchAt` after a callee writes blocks of `S.wr` and reallocates work arrays. -/
theorem SearchAt.reallocW {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st st' : Search n}
    {pre nsp pre' nsp' : Bool} (h : SearchAt m S ctx st pre nsp)
    (hvU : Mem.valid_block m S.bUA) (hvT : Mem.valid_block m Block.tcnode0)
    {cW cS cB cN : Nat} {bW bS bB bN : block}
    (nW : 0 < cW → bW ∉ S.blocks) (nS : 0 < cS → bS ∉ S.blocks) (nB : 0 < cB → bB ∉ S.blocks)
    (nN : 0 < cN → bN ∉ S.blocks)
    {X : block → Prop}
    (hu : Unch m m' (fun z => dyn3Set m cW bW cS bS cB bB z ∨ nautilSet m cN bN z ∨ X z))
    (hX : ∀ z ∈ S.blocks, X z → z ∈ S.wr)
    (hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws], Keep m m' z)
    {cW' cS' cB' cN' : Nat} {bW' bS' bB' bN' : block}
    (dW' : DynAt m' Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW' bW')
    (dS' : DynAt m' Block.naugraphWorkset Block.naugraphWorksetSz 8 cS' bS')
    (dB' : DynAt m' Block.naugraphBucket Block.naugraphBucketSz 4 cB' bB')
    (dN' : DynAt m' Block.nautilWorkperm Block.nautilWorkpermSz 4 cN' bN')
    (fW : (cW' = cW ∧ bW' = bW) ∨ ¬ Mem.valid_block m bW')
    (fS : (cS' = cS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS')
    (fB : (cB' = cB ∧ bB' = bB) ∨ ¬ Mem.valid_block m bB')
    (fN : (cN' = cN ∧ bN' = bN) ∨ ¬ Mem.valid_block m bN')
    (pWS : 0 < cW' → 0 < cS' → bW' ≠ bS') (pWB : 0 < cW' → 0 < cB' → bW' ≠ bB')
    (pSB : 0 < cS' → 0 < cB' → bS' ≠ bB') (pNW : 0 < cN' → 0 < cW' → bN' ≠ bW')
    (pNS : 0 < cN' → 0 < cS' → bN' ≠ bS') (pNB : 0 < cN' → 0 < cB' → bN' ≠ bB')
    (hsc : Scalars m' st' nsp') (hst : Stats m' S st' pre') (har : Arrays m' S ctx st')
    (hinv : SInv st') : SearchAt m' S ctx st' pre' nsp' := by
  have hv := h.valid_all hvU hvT
  have hd := h.distinct
  have hvn := SLoc.vars_ne hd
  -- a block of `S` outside `S.wr` and the eight work globals is untouched
  have key : ∀ z ∈ S.blocks, z ∉ S.wr → ¬ G8 z →
      ¬ (dyn3Set m cW bW cS bS cB bB z ∨ nautilSet m cN bN z ∨ X z) := by
    intro z hz hw hg
    rintro (h6 | hN | hx)
    · unfold dyn3Set at h6
      rcases h6 with e | e | e | e | e | e | ⟨hc, e⟩ | ⟨hc, e⟩ | ⟨hc, e⟩ | hnv
      · exact hg (.inl (.inl e))
      · exact hg (.inl (.inr (.inl e)))
      · exact hg (.inl (.inr (.inr (.inl e))))
      · exact hg (.inl (.inr (.inr (.inr (.inl e)))))
      · exact hg (.inl (.inr (.inr (.inr (.inr (.inl e))))))
      · exact hg (.inl (.inr (.inr (.inr (.inr (.inr e))))))
      · exact nW hc (e ▸ hz)
      · exact nS hc (e ▸ hz)
      · exact nB hc (e ▸ hz)
      · exact hnv (hv z hz)
    · rcases hN with e | e | ⟨hc, e⟩ | hnv
      · exact hg (.inr (.inl e))
      · exact hg (.inr (.inr e))
      · exact nN hc (e ▸ hz)
      · exact hnv (hv z hz)
    · exact hw (hX z hz hx)
  -- the same for a constant global not written by the search's statements
  have keyG : ∀ z, z ∈ globs → z ∉ wrG → ¬ G8 z →
      ¬ (dyn3Set m cW bW cS bS cB bB z ∨ nautilSet m cN bN z ∨ X z) := fun z h1 h2 h3 =>
    key z (by rw [SLoc.blocks_split]; exact List.mem_append.2 (.inr h1))
      (SLoc.glob_not_wr hvn h2 h1) h3
  have notIn : ∀ {b : block} {c c' : Nat} {b₀ : block}, (0 < c → b₀ ∉ S.blocks) →
      ((c' = c ∧ b = b₀) ∨ ¬ Mem.valid_block m b) → 0 < c' → b ∉ S.blocks := by
    intro b c c' b₀ hn hf hc hb
    rcases hf with ⟨rfl, rfl⟩ | hnv
    · exact hn hc hb
    · exact hnv (hv b hb)
  exact
    { h with
      fixed := h.fixed.unch hu fun z hz => keyG z (by revert z hz; decide) (by revert z hz; decide)
        (by revert z hz; decide)
      scalars := hsc
      stats := hst
      arrays := har
      dyns := h.dyns.keepW hu (fun z hz => keyG z (by revert z hz; decide)
        (by revert z hz; decide) (by revert z hz; decide)) hK
      tables := h.tables.unch hu fun z hz => keyG z (by revert z hz; decide)
        (by revert z hz; decide) (by revert z hz; decide)
      work := ⟨⟨cW', bW', cS', bS', cB', bB', cN', bN', dW', dS', dB', dN',
        notIn nW fW, notIn nS fS, notIn nB fB, notIn nN fN, pWS, pWB, pSB, pNW, pNS, pNB⟩⟩
      inv := hinv }

end NautyVerified.Proofs.Search
