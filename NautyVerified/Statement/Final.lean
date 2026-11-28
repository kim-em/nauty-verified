import NautyVerified.Statement.DenseOf

/-!
# The end-to-end theorem for dense nauty

`densenauty_binary_correct`: the x86-64 program that CompCert4Lean compiles
from the linked C sources (`dense_main.c`, nauty 2.9.3's dense code and
`zalloc.c`; the binary `scripts/build_binary.sh` produces), run on any input
encoding a coloured graph `G`, terminates, and writes exactly what
HexGraphIso's search computes on `G` (`expected G`): the same generators in
the same order, canonical labelling, orbits, canonical graph and statistics.

It is `densenauty_binary_correct_of` applied to the emission hypotheses, which
are not proved yet (Phase 6 of docs/PLAN.md: they need the re-pin of
hex-graph-iso that adds `TraceRun.emitted`).
-/

namespace NautyVerified.Statement

open CompCert4Lean CompCert4Lean.Common.Events CompCert4Lean.Common.Behaviors
open CompCert4Lean.Lib.Integers
open Hex.GraphIso

theorem densenauty_binary_correct {n k : Nat} (G : Colored n k) (hn : 0 < n) (hmax : n ≤ maxN)
    (hk : k ≤ maxN) {ins : List Int} (hins : Encodes G ins) {tp : X86.Asm.program} (hc : Compiled tp) :
    ∀ beh, program_behaves (X86.Asm.semantics Build.config xi tp) beh → Consistent ins beh →
      ∃ t, beh = .Terminates t (Lib.Integers.Int.repr .Z0) ∧ writes t = expected G :=
  densenauty_binary_correct_of G hn hmax hk hins hc (gens := sorry) (Em := sorry)
    sorry sorry sorry sorry

end NautyVerified.Statement
