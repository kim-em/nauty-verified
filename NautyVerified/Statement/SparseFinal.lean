import NautyVerified.Statement.Sparse

/-!
# The end-to-end theorem for sparse nauty

`sparsenauty_binary_correct`: the x86-64 program that CompCert4Lean compiles
from the linked C sources (`sparse_main.c`, nauty 2.9.3's sparse code and
`zalloc.c`; the binary `scripts/build_binary.sh --sparse` produces), run on the
input encoding a coloured sparse graph `G`, terminates, and writes exactly what
HexGraphIso's sparse search computes on `G` (`expectedSparse G`): the same
generators in the same order, canonical labelling, orbits, canonical graph
(with nauty's neighbour order) and statistics.

It is `binary_of_backward` through `sparse_backward`, given one execution of
the pinned Clight that reads `sparseInput G` and writes `expectedSparse G`.
That execution is not proved yet (Phase 7 of docs/PLAN.md); it comes from a
specification of `sparse_main`'s `main`, as `exec_of_main` and `main_ok`
give the dense one.
-/

namespace NautyVerified.Statement

open CompCert4Lean CompCert4Lean.Common.Behaviors
open Hex.GraphIso

theorem sparsenauty_binary_correct {n k : Nat} (G : Sparse.Colored n k) (hn : 0 < n)
    (hmax : n ≤ maxN) (hk : k ≤ maxN) {ins : List Int} (hins : SparseEncodes G ins)
    {tp : X86.Asm.program} (hc : SparseCompiled tp) :
    ∀ beh, program_behaves (X86.Asm.semantics Build.config xi tp) beh → Consistent ins beh →
      ∃ t, beh = .Terminates t (Lib.Integers.Int.repr .Z0) ∧ writes t = expectedSparse G :=
  binary_of_backward (sparse_backward tp hc xi) sorry

end NautyVerified.Statement
