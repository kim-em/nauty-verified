import NautyVerified.Proofs.Alloc.Dynfree
import NautyVerified.Proofs.Alloc.Blocks
import NautyVerified.Proofs.Top.Init

/-!
# naugraph.c's and nautil.c's `*_freedyn`

`dynfreeSpec ds`: a function that only runs `DYNFREE` on the pairs `ds`
(`nautil_freedyn`: nautil.c's `workperm`; `naugraph_freedyn`: naugraph.c's
`workset`, `workperm`, `bucket` and `dnwork`) leaves every pair at capacity 0
with a `NULL` pointer, freeing exactly the allocated blocks.
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt FreeD dynfree seqR wp_dynfrees)

variable {xi : ExternalCalls}

/-- A function running `DYNFREE` on the pairs `ds`. -/
def dynfreeSpec (ds : List FreeD) : FunSpec where
  pre args m := args = [] ∧ FreeD.Ok m ds
  post _ m t _ m' := t = E0 ∧ (∀ d ∈ ds, ∀ c b', DynAt m' d.bp d.bs c 0 b') ∧
    Unch m m' (fun z => z ∈ FreeD.globals ds ∨ ∃ d ∈ ds, 0 < d.cap ∧ z = d.blk) ∧
    Mem.nextblock m' = Mem.nextblock m

/-- nautil.c's pair. -/
def nautilDs (cap : Nat) (b : block) : List FreeD :=
  [⟨dense.id.«nautil:workperm», dense.id.«nautil:workperm_sz», Block.nautilWorkperm,
    Block.nautilWorkpermSz, tint, 4, cap, b⟩]

/-- naugraph.c's pairs: `workset`, `workperm`, `bucket`, `dnwork`. -/
def naugraphDs (cS : Nat) (bS : block) (cW : Nat) (bW : block) (cB : Nat) (bB : block)
    (cD : Nat) (bD : block) : List FreeD :=
  [⟨dense.id.«naugraph:workset», dense.id.«naugraph:workset_sz», Block.naugraphWorkset,
     Block.naugraphWorksetSz, tulong, 8, cS, bS⟩,
   ⟨dense.id.«naugraph:workperm», dense.id.«naugraph:workperm_sz», Block.naugraphWorkperm,
     Block.naugraphWorkpermSz, tint, 4, cW, bW⟩,
   ⟨dense.id.«naugraph:bucket», dense.id.«naugraph:bucket_sz», Block.naugraphBucket,
     Block.naugraphBucketSz, tint, 4, cB, bB⟩,
   ⟨dense.id.«naugraph:dnwork», dense.id.«naugraph:dnwork_sz», Block.naugraphDnwork,
     Block.naugraphDnworkSz, tulong, 8, cD, bD⟩]

kernel_rfl body_nautilFreedyn : dense.body.nautil_freedyn =
  seqR [dynfree dense.id.«nautil:workperm» dense.id.«nautil:workperm_sz» tint]

kernel_rfl body_naugraphFreedyn : dense.body.naugraph_freedyn =
  seqR [dynfree dense.id.«naugraph:workset» dense.id.«naugraph:workset_sz» tulong,
    dynfree dense.id.«naugraph:workperm» dense.id.«naugraph:workperm_sz» tint,
    dynfree dense.id.«naugraph:bucket» dense.id.«naugraph:bucket_sz» tint,
    dynfree dense.id.«naugraph:dnwork» dense.id.«naugraph:dnwork_sz» tulong]

theorem nautilFreedyn_satisfies (cap : Nat) (b : block) :
    Satisfies xi ge (.Internal dense.fn.nautil_freedyn) (dynfreeSpec (nautilDs cap b)) := by
  let le0 := create_undef_temps dense.fn.nautil_freedyn.fn_temps
  refine satisfies_internal (Entry := fun _ m₀ e le m => e = empty_env ∧ le = le0 ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, le0, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hok⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [dense.fn.nautil_freedyn.fn_body_eq, body_nautilFreedyn]
    exact wp_dynfrees Alloc.noShadow_empty (nautilDs cap b) _ hok
      (fun m' hD hu hnb => ⟨m', rfl, rfl, hD, hu, hnb⟩)

theorem naugraphFreedyn_satisfies (cS : Nat) (bS : block) (cW : Nat) (bW : block) (cB : Nat)
    (bB : block) (cD : Nat) (bD : block) :
    Satisfies xi ge (.Internal dense.fn.naugraph_freedyn)
      (dynfreeSpec (naugraphDs cS bS cW bW cB bB cD bD)) := by
  let le0 := create_undef_temps dense.fn.naugraph_freedyn.fn_temps
  refine satisfies_internal (Entry := fun _ m₀ e le m => e = empty_env ∧ le = le0 ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, le0, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hok⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [dense.fn.naugraph_freedyn.fn_body_eq, body_naugraphFreedyn]
    exact wp_dynfrees Alloc.noShadow_empty (naugraphDs cS bS cW bW cB bB cD bD) _ hok
      (fun m' hD hu hnb => ⟨m', rfl, rfl, hD, hu, hnb⟩)

end NautyVerified.Proofs.Top
