import NautyVerified.Statement.Compose
import NautyVerified.Source.Sparse

/-!
# The sparse harness: input, output and the binary

The verified sparse program is `sparse_main.c` linked with nauty's sparse
sources (`Source.sparse`). It talks to its environment as `dense_main.c` does,
through `nv_read` and `nv_write` under the same environment `xi`, so
`reads`, `writes` and `Consistent` (`Statement/Harness.lean`) apply unchanged.
This module fixes

* `sparseInput G`: the numbers `sparse_main` reads for the coloured sparse
  graph `G`: `n`, the colour of each vertex, the degree of each vertex, then
  each vertex's neighbours in the order `G` stores them;
* `expectedSparse G`: the numbers it writes when nauty computes what
  HexGraphIso's sparse search computes on `G`;
* `SparseCompiled tp`: `tp` is the binary CompCert4Lean compiles from the
  linked sparse program, and `sparse_backward`, Phase 3's backward simulation
  for it.
-/

namespace NautyVerified.Statement

open CompCert4Lean CompCert4Lean.Common.Smallstep
open Hex.GraphIso

/-! ## Input -/

/-- The numbers `sparse_main` reads for `G`: `n`, the colour of each vertex,
the degree of each vertex, and the neighbour lists in vertex order (each in
`G`'s order, which is increasing). The harness lays the lists out
contiguously, so its offsets are `G`'s. -/
def sparseInput {n k : Nat} (G : Sparse.Colored n k) : List Int :=
  [(n : Int)] ++ (List.finRange n).map (fun v => ((G.coloring.cells.get v).val : Int)) ++
    (List.finRange n).map (fun v => ((G.graph.nbrs v).size : Int)) ++
    (List.finRange n).flatMap (fun v => (G.graph.nbrs v).toList.map (fun u => (u.val : Int)))

/-- The numbers `sparse_main` reads encode `G`. -/
def SparseEncodes {n k : Nat} (G : Sparse.Colored n k) (ins : List Int) : Prop :=
  ins = sparseInput G

/-! ## Output -/

/-- Row `i` of a canonical store as `sparse_main` writes it: the degree, then
the neighbours in stored order. -/
def sparseRow {n : Nat} (r : Nauty.Sparse.Rows n) (i : Nat) : List Int :=
  (r.degree i : Int) :: ((r.neighbors.extract r.offsets[i]! r.offsets[i + 1]!).toList.map
    (fun (u : Nat) => (u : Int)))

/-- What `sparse_main` writes for a final state of HexGraphIso's sparse search:
each generator (tag 1), the canonical labelling (2), the orbits (3), the
canonical graph's rows (4) and the statistics (5), the last of which,
`errstatus`, is 0. As for `expected`, the statistics are written as the C
types hold them. -/
def sparseOutput {n : Nat} (st : Nauty.Sparse.State n) : List Int :=
  st.genTrace.toList.flatMap (fun p => 1 :: p.toList.map (fun (i : Nat) => (i : Int))) ++
  (2 :: st.canonlab.toList.map (fun (i : Nat) => (i : Int))) ++
  (3 :: st.orbits.toList.map (fun (i : Nat) => (i : Int))) ++
  (4 :: (List.range n).flatMap (sparseRow st.canong.toRows)) ++
  [5, asInt st.numorbits, asInt st.numgenerators, asLong st.numnodes,
    asLong st.numbadleaves, asInt st.maxlevel, asLong st.tctotal,
    asLong st.canupdates, 0]

/-- What `sparse_main` writes when nauty computes what HexGraphIso's sparse
search computes on `G`. -/
def expectedSparse {n k : Nat} (G : Sparse.Colored n k) : List Int :=
  sparseOutput (Nauty.Sparse.runColored G)

/-! ## The binary -/

/-- The binary compiled from the linked sparse program. -/
abbrev SparseCompiled (tp : X86.Asm.program) : Prop :=
  Build.compile Source.sparse.fresh Source.sparse.program = .ok tp

/-- Every behaviour of the compiled sparse binary is an improvement of a
behaviour of `sparse.locals`, as `dense_backward` for the dense program. -/
theorem sparse_backward (tp : X86.Asm.program) (hc : SparseCompiled tp)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls) :
    backward_simulation (Cfrontend.Clight.semantics2 xi Source.sparse.locals)
      (X86.Asm.semantics Build.config xi tp) := by
  have hcomp : Driver.Compiler.transf_c_program Build.config (Prototype.selectionFor Build.config)
      Build.inlining (Allocator.regalloc Build.config .empty) Prototype.enumeration
      (Source.freshContext Source.sparse.fresh) Source.sparse.program = .OK tp := by
    have hc : Build.compile Source.sparse.fresh Source.sparse.program = .ok tp := hc
    unfold Build.compile at hc
    split at hc
    · cases hc; assumption
    · cases hc
  have hlocals := Source.sparse.locals_eq Build.config.options Build.config.x86_64ABI
    Build.config.relocation
  exact Driver.Compiler.transf_c_program_clight_correct Build.config _ _ _ _ _ xi _ _ _ tp hcomp
    Source.sparse.clight_eq hlocals

end NautyVerified.Statement
