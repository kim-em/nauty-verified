import NautyVerified.Proofs.Search.Node.OtherIter

/-!
# `Keep` and access permissions

`Keep.access'`: a kept block keeps its access permissions. (`CarryG.step`, in
`OtherIter.lean`, moves `CarryG` across a step of `othernode0`'s body.)
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified NautyVerified.Logic NautyVerified.Program
open NautyVerified.Proofs.Alloc (Keep)
open Hex.GraphIso.Nauty

variable {n : Nat}

theorem Keep.access' {m m' : mem} {b : block} (hk : Keep m m' b)
    {chunk : Common.AST.memory_chunk} {ofs : Z} {p : Common.Memtype.permission}
    (h : Mem.valid_access m chunk b ofs p) : Mem.valid_access m' chunk b ofs p :=
  ⟨fun o ho => hk.perm _ _ (h.1 o ho), h.2⟩

end NautyVerified.Proofs.Search
