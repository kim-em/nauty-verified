import NautyVerified.Proofs.Search.Node.Steps

/-!
# The blocks of `refine`'s locations at a search node

`loc_distinct`: the `Refine.Loc` a node builds for `doref` (the caller's arrays
from `S`, the node's locals, and the work blocks, each in use or replaced by a
nauty.c static) has pairwise distinct blocks.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Common.Values
open NautyVerified NautyVerified.Program

theorem ne_of_notin {l : List block} {z y : block} (hz : z ∉ l) (hy : y ∈ l) : z ≠ y :=
  fun e => hz (e ▸ hy)

/-- What a work block of refine's `Loc` is: a nauty.c static standing in for an
empty array, or a block in use, apart from `S` and the node's locals. -/
def WorkBlk (S : SLoc) (c bnc bq bk : block) (w : block) : Prop :=
  w = c ∨ (w ∉ S.blocks ∧ w ≠ bnc ∧ w ≠ bq ∧ w ≠ bk)

set_option maxHeartbeats 4000000 in
/-- The blocks of refine's `Loc` for a node are distinct. -/
theorem loc_distinct {S : SLoc} {bnc bq bk bW bS bB : block} (hd : S.blocks.Pairwise (· ≠ ·))
    (hloc : [bnc, bq, bk].Pairwise (· ≠ ·)) (hlocS : ∀ z ∈ [bnc, bq, bk], z ∉ S.blocks)
    (hW : WorkBlk S Block.gcaFirst bnc bq bk bW) (hS : WorkBlk S Block.gcaCanon bnc bq bk bS)
    (hB : WorkBlk S Block.noncheaplevel bnc bq bk bB)
    (hWS : bW ∉ S.blocks → bS ∉ S.blocks → bW ≠ bS) (hWB : bW ∉ S.blocks → bB ∉ S.blocks → bW ≠ bB)
    (hSB : bS ∉ S.blocks → bB ∉ S.blocks → bS ≠ bB) :
    [S.bg, S.bl, S.bp, bnc, S.bWP, S.bA, bk, bW, bS, bB,
     Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
     Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
     Block.naugraphBit, Block.naugraphBytecount, Block.leftbit].Pairwise (· ≠ ·) := by
  have h1 := hlocS bnc (by simp)
  have h3 := hlocS bk (by simp)
  have hnq : bnc ≠ bq := List.rel_of_pairwise_cons hloc (by simp)
  have hnk : bnc ≠ bk := List.rel_of_pairwise_cons hloc (by simp)
  have hqk : bq ≠ bk := List.rel_of_pairwise_cons (List.Pairwise.of_cons hloc) (by simp)
  rcases hW with rfl | ⟨hWn, hW1, hW2, hW3⟩ <;> rcases hS with rfl | ⟨hSn, hS1, hS2, hS3⟩ <;>
    rcases hB with rfl | ⟨hBn, hB1, hB2, hB3⟩ <;>
    simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true] <;>
    (repeat' constructor) <;>
    first
      | sep_ne hd
      | assumption
      | exact Ne.symm (by assumption)
      | (apply ne_of_notin h1; simp [SLoc.blocks]; done)
      | (apply Ne.symm; apply ne_of_notin h1; simp [SLoc.blocks]; done)
      | (apply ne_of_notin h3; simp [SLoc.blocks]; done)
      | (apply Ne.symm; apply ne_of_notin h3; simp [SLoc.blocks]; done)
      | (apply ne_of_notin hWn; simp [SLoc.blocks]; done)
      | (apply Ne.symm; apply ne_of_notin hWn; simp [SLoc.blocks]; done)
      | (apply ne_of_notin hSn; simp [SLoc.blocks]; done)
      | (apply Ne.symm; apply ne_of_notin hSn; simp [SLoc.blocks]; done)
      | (apply ne_of_notin hBn; simp [SLoc.blocks]; done)
      | (apply Ne.symm; apply ne_of_notin hBn; simp [SLoc.blocks]; done)
      | exact hWS hWn hSn
      | exact hWB hWn hBn
      | exact hSB hSn hBn

set_option maxHeartbeats 4000000 in
/-- The blocks of `refine`'s `Loc` for a node are apart from `qinvar` and nautil.c's
`workperm`. -/
theorem loc_sep {S : SLoc} {bnc bq bk bW bS bB bN : block} {cN : Nat}
    (hd : S.blocks.Pairwise (· ≠ ·))
    (hloc : [bnc, bq, bk].Pairwise (· ≠ ·)) (hlocS : ∀ z ∈ [bnc, bq, bk], z ∉ S.blocks)
    (hW : WorkBlk S Block.gcaFirst bnc bq bk bW) (hS : WorkBlk S Block.gcaCanon bnc bq bk bS)
    (hB : WorkBlk S Block.noncheaplevel bnc bq bk bB)
    (hNS : 0 < cN → bN ∉ S.blocks) (hNl : 0 < cN → bN ≠ bnc ∧ bN ≠ bq ∧ bN ≠ bk)
    (hNW : 0 < cN → bW ∉ S.blocks → bN ≠ bW) (hNS' : 0 < cN → bS ∉ S.blocks → bN ≠ bS)
    (hNB : 0 < cN → bB ∉ S.blocks → bN ≠ bB) :
    ∀ z ∈ [S.bg, S.bl, S.bp, bnc, S.bWP, S.bA, bk, bW, bS, bB,
     Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
     Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
     Block.naugraphBit, Block.naugraphBytecount, Block.leftbit],
      z ≠ bq ∧ z ≠ Block.nautilWorkperm ∧ z ≠ Block.nautilWorkpermSz ∧ (0 < cN → z ≠ bN) := by
  have h1 := hlocS bnc (by simp)
  have h2 := hlocS bq (by simp)
  have h3 := hlocS bk (by simp)
  have hnq : bnc ≠ bq := List.rel_of_pairwise_cons hloc (by simp)
  have hnk : bnc ≠ bk := List.rel_of_pairwise_cons hloc (by simp)
  have hqk : bq ≠ bk := List.rel_of_pairwise_cons (List.Pairwise.of_cons hloc) (by simp)
  rcases hW with rfl | ⟨hWn, hW1, hW2, hW3⟩ <;> rcases hS with rfl | ⟨hSn, hS1, hS2, hS3⟩ <;>
    rcases hB with rfl | ⟨hBn, hB1, hB2, hB3⟩ <;>
    simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] <;>
    (repeat' constructor) <;>
    first
      | sep_ne hd
      | assumption
      | exact Ne.symm (by assumption)
      | (intro hc; exact (by assumption : _ → _ ≠ _) hc)
      | (apply ne_of_notin h1; simp [SLoc.blocks]; done)
      | (apply Ne.symm; apply ne_of_notin h1; simp [SLoc.blocks]; done)
      | (apply ne_of_notin h2; simp [SLoc.blocks]; done)
      | (apply Ne.symm; apply ne_of_notin h2; simp [SLoc.blocks]; done)
      | (apply ne_of_notin h3; simp [SLoc.blocks]; done)
      | (apply Ne.symm; apply ne_of_notin h3; simp [SLoc.blocks]; done)
      | (apply ne_of_notin hWn; simp [SLoc.blocks]; done)
      | (apply Ne.symm; apply ne_of_notin hWn; simp [SLoc.blocks]; done)
      | (apply ne_of_notin hSn; simp [SLoc.blocks]; done)
      | (apply Ne.symm; apply ne_of_notin hSn; simp [SLoc.blocks]; done)
      | (apply ne_of_notin hBn; simp [SLoc.blocks]; done)
      | (apply Ne.symm; apply ne_of_notin hBn; simp [SLoc.blocks]; done)
      | (intro hc; apply Ne.symm; apply ne_of_notin (hNS hc); simp [SLoc.blocks]; done)
      | (intro hc; exact Ne.symm (hNl hc).1)
      | (intro hc; exact Ne.symm (hNl hc).2.1)
      | (intro hc; exact Ne.symm (hNl hc).2.2)
      | (intro hc; exact Ne.symm (hNW hc hWn))
      | (intro hc; exact Ne.symm (hNS' hc hSn))
      | (intro hc; exact Ne.symm (hNB hc hBn))

end NautyVerified.Proofs.Search
