import NautyVerified.Proofs.Search.Processnode.Tail
import NautyVerified.Logic.Grow
import NautyVerified.Proofs.Search.Node.Env

/-!
# Leaving `processnode`

`PAt.finish`: freeing `sr` succeeds, and afterwards memory holds the search
state, the changes since entry are an `SFrame`, and the work blocks in use
were in use at entry or are new.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word
open NautyVerified.Source
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

variable {n : Nat} {m₀ m₁ m : mem} {S : SLoc} {ctx : Ctx n} {e : env} {bsr : block}
  {st : Search n} {nsp : Bool}

theorem blocks_sr (bsr : block) :
    blocks_of_env ge (PTree.set dense.id.sr (bsr, tint) empty_env) =
      [(bsr, zOfInt 0, sizeof ge.genv_cenv tint)] := rfl

theorem PAt.finish (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp) :
    ∃ mf, Mem.free_list m (blocks_of_env ge e) = some mf ∧ SearchAt mf S ctx st false nsp ∧
      SFrame m₀ mf S ∧ (∀ z, IsWork mf z → IsWork m₀ z ∨ ¬ Mem.valid_block m₀ z) := by
  obtain ⟨mf, hfree, hu⟩ := free_ints [bsr] m (by simp) (by simpa using h.srW)
  rw [c.eEq, blocks_sr]
  refine ⟨mf, by simpa using hfree, ?_⟩
  have hu' : Unch m mf (· = bsr) := hu.mono fun z hz => by simpa using hz
  have hwk : ∀ z, IsWork m z → ¬ z = bsr := fun z hz => h.work_ne c hz
  have hv : ∀ z, Mem.valid_block m z → Mem.valid_block mf z :=
    fun z hz => free_list_valid (by simpa using hfree) z hz
  have hwm : WorkMono m mf := WorkMono.of_unch h.search.work hu'
    (fun z hz hzb => c.ne_blocks (workG_blocks S hz) hzb) hwk
  refine ⟨h.search.unch hu' (fun z hz => c.ne_blocks hz) hwk,
    ⟨h.frame.1.trans (hu'.mono fun z hz => .inr (.inl (hz ▸ c.fresh))),
      fun z hz => hv _ (h.frame.2 z hz)⟩, fun z hz => ?_⟩
  rcases hwm z hz with h1 | h1
  · rcases h.work z h1 with h2 | h2
    · exact .inl (c.work10 z h2)
    · exact .inr fun hv0 => h2 (c.grow01 _ hv0)
  · exact .inr fun hv0 => h1 (h.frame.2 _ hv0)

end NautyVerified.Proofs.Search.Processnode
