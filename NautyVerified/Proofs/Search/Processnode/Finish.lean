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

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}
variable {n : Nat} {D : DispatchC ge O} {m₀ m₁ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
  {G : O.Gr n} {e : env} {bsr : block} {st : SearchState n (O.Canon n)} {nsp : Bool}

theorem blocks_sr (bsr : block) :
    blocks_of_env ge (PTree.set dense.id.sr (bsr, tint) empty_env) =
      [(bsr, zOfInt 0, sizeof ge.genv_cenv tint)] := rfl

theorem PAt.finish (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp) :
    ∃ mf, Mem.free_list m (blocks_of_env ge e) = some mf ∧
      SearchAtG D.toDispatchRep mf S gl cl G st false nsp ∧
      SFrameG D.toDispatchRep m₀ mf S gl cl ∧
      (∀ z, IsWorkG D.toDispatchRep mf z → IsWorkG D.toDispatchRep m₀ z ∨ ¬ Mem.valid_block m₀ z) := by
  obtain ⟨mf, hfree, hu⟩ := free_ints [bsr] m (by simp) (by simpa using h.srW)
  rw [c.eEq, blocks_sr]
  refine ⟨mf, by simpa using hfree, ?_⟩
  have hs := h.search
  have hu' : Unch m mf (· = bsr) := hu.mono fun z hz => by simpa using hz
  have hS : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, ¬ z = bsr := fun z hz => c.ne_blocks hz
  have hwk : ∀ z, IsWorkG D.toDispatchRep m z → ¬ z = bsr := fun z hz => h.work_ne c hz
  have hv : ∀ z, Mem.valid_block m z → Mem.valid_block mf z :=
    fun z hz => free_list_valid (by simpa using hfree) z hz
  have back := (hs.work.unch hu' (fun z hz => hS z (SLoc.mem_blocksG_of _
      (.inr (.inr (.inr (.inr (.inr (D.wglobs_sub z hz))))))))
    ⟨hS _ (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp))))))),
      hS _ (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp)))))))⟩ hwk hv).2
  refine ⟨hs.unch hu' hS hwk hv,
    ⟨h.frame.1.trans (hu'.mono fun z hz => .inr (.inl (hz ▸ c.fresh))),
      fun z hz => hv _ (h.frame.2 z hz)⟩, fun z hz => ?_⟩
  rcases h.work z (back z hz) with h2 | h2
  · exact .inl (c.work10 z h2)
  · exact .inr fun hv0 => h2 (c.grow01 _ hv0)

end NautyVerified.Proofs.Search.Processnode
