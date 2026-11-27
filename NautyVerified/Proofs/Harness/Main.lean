import NautyVerified.Proofs.Harness.Loop

/-!
# `dense_main`'s `main`, relative to `densenautySpec`

`main_satisfies`: from the program's initial memory, reading the numbers
`ins` that encode `G` (`EncodesB`, `Statement.Encodes` with the edge list
short enough for an `int` count), `main` returns 0 with a trace whose reads
are `ins` and whose writes are `Statement.expected G`, given that
`densenauty` satisfies `densenautySpec` and the facts `HexFacts G` about
HexGraphIso's result (sizes, and counters that fit the C types they are
stored in).
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search (Writes FieldAt gensWords)
open NautyVerified.Proofs.Alloc (Fresh zb)
open Hex.GraphIso Hex.GraphIso.Nauty

/-- `Statement.Encodes`, with an edge list whose length fits in an `int`. -/
def EncodesB {n k : Nat} (G : Colored n k) (ins : List Int) : Prop :=
  ∃ es : List (Fin n × Fin n), es.length < 2147483648 ∧
    ins = [(n : Int)] ++ (List.finRange n).map (fun v => ((G.coloring.cells.get v).val : Int)) ++
      [(es.length : Int)] ++ es.flatMap (fun e => [(e.1.val : Int), (e.2.val : Int)]) ∧
    (∀ e ∈ es, e.1 ≠ e.2) ∧
    ∀ u v : Fin n, G.graph.adj u v = true ↔ ((u, v) ∈ es ∨ (v, u) ∈ es)

/-- HexGraphIso facts the harness's output needs: the result arrays have `n`
entries, and every number written fits the C type it is stored in. -/
structure HexFacts {n k : Nat} (G : Colored n k) : Prop where
  autos : ∀ p ∈ (runColoredTraced G).autos.toList, p.size = n
  canonlab : (runColoredTraced G).result.canonlab.size = n
  canonlabSmall : ∀ i < n, (runColoredTraced G).result.canonlab[i]! < 2147483648
  orbits : (Statement.finalState G).orbits.size = n
  orbitsSmall : ∀ i < n, (Statement.finalState G).orbits[i]! < 2147483648
  canong : (runColoredTraced G).result.canong.size = n
  numorbits : (runColoredTraced G).result.numorbits < 2147483648
  numgenerators : (runColoredTraced G).result.numgenerators < 2147483648
  maxlevel : (runColoredTraced G).result.maxlevel < 2147483648
  numnodes : (runColoredTraced G).result.numnodes < 2 ^ 63
  numbadleaves : (runColoredTraced G).result.numbadleaves < 2 ^ 63
  tctotal : (runColoredTraced G).result.tctotal < 2 ^ 63
  canupdates : (runColoredTraced G).result.canupdates < 2 ^ 63

/-- Every event of `t` is a call of `nv_read` or `nv_write` (so `t` has no
volatile loads). -/
def IOOnly (t : trace) : Prop :=
  ∀ ev ∈ (show List event from t), ∃ name args res, ev = .Event_syscall name args res

/-- `main` from the initial memory. -/
def mainSpec {n k : Nat} (G : Colored n k) (ins : List Int) : FunSpec where
  pre args m := args = [] ∧ Genv.init_mem Init.prog = some m
  post _ _ t v _ := v = .Vint (ir 0) ∧ Statement.reads t = ins.map some ∧
    Statement.writes t = Statement.expected G ∧ IOOnly t

end NautyVerified.Proofs.Harness
