import NautyVerified.Proofs.Search.Spec
import NautyVerified.Proofs.Init.Tables
import NautyVerified.Statement.Harness

/-!
# What the harness needs from `densenauty`

`densenautySpec G gens bg bl bp bo bst bc`: `dense_main` calls
`densenauty(g, lab, ptn, orbits, &options, &stats, m, n, canong)` with

- memory equal to the program's initial memory except in the `options`
  global (whose fields `OptionsAt` gives: `DEFAULTOPTIONS_GRAPH` with
  `getcanon`, no default partition, the harness's `emit_generator` and the
  dummy `outfile`) and in blocks the harness allocated since;
- `g` holding HexGraphIso's rows of `G` (`m = SETWORDSNEEDED(n)` words each);
- `lab`, `ptn` holding `initialPartition G` as the harness builds it
  (`ptn` 1 inside a cell and 0 at its end, `harnessPtn`);
- `orbits`, `canong` and the `statsblk` `stats` writable.

Afterwards the trace writes the generators `gens`, in order (`gensWords
gens`, which is what `emit_generator` writes for them). `gens` is a
parameter: it is the list of generators nauty emits (one each time
`numgenerators` increases), which `main` forwards to its output and the
caller relates to `Statement.expected`'s first block. Memory holds the
canonical labelling in `lab`, the orbits of HexGraphIso's final search state
in `orbits`, the canonical graph's rows in `canong`, and the result's
counters as their C types hold them (and `errstatus = 0`) in `stats`. The
block `stats` keeps its permissions, so `main` can free it.
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Graph (GraphAt)
open NautyVerified.Proofs.Search (FieldAt Writes gensWords)
open Hex.GraphIso Hex.GraphIso.Nauty

namespace Block
def options : Common.Values.block := PArith.BinPos.Pos.of_nat 111
def emitGenerator : Common.Values.block := PArith.BinPos.Pos.of_nat 23
def dummyfile : Common.Values.block := PArith.BinPos.Pos.of_nat 67
def main : Common.Values.block := PArith.BinPos.Pos.of_nat 77
def densenauty : Common.Values.block := PArith.BinPos.Pos.of_nat 175
def nvRead : Common.Values.block := PArith.BinPos.Pos.of_nat 309
def nvWrite : Common.Values.block := PArith.BinPos.Pos.of_nat 2
def dispatchGraph : Common.Values.block := PArith.BinPos.Pos.of_nat 243
end Block

kernel_rfl find_options : Genv.find_symbol ge.genv_genv dense.id.«dense_main:options» = some Block.options
kernel_rfl find_emitGenerator :
  Genv.find_symbol ge.genv_genv dense.id.«dense_main:emit_generator» = some Block.emitGenerator
kernel_rfl find_dummyfile :
  Genv.find_symbol ge.genv_genv dense.id.«dense_main:dummyfile» = some Block.dummyfile
kernel_rfl find_main : Genv.find_symbol ge.genv_genv dense.id.main = some Block.main
kernel_rfl find_densenauty : Genv.find_symbol ge.genv_genv dense.id.densenauty = some Block.densenauty
kernel_rfl find_nvRead : Genv.find_symbol ge.genv_genv dense.id.nv_read = some Block.nvRead
kernel_rfl find_nvWrite : Genv.find_symbol ge.genv_genv dense.id.nv_write = some Block.nvWrite
kernel_rfl find_dispatchGraph :
  Genv.find_symbol ge.genv_genv dense.id.dispatch_graph = some Block.dispatchGraph
kernel_rfl funct_densenauty :
  Genv.find_funct_ptr ge.genv_genv Block.densenauty = some (.Internal dense.fn.densenauty)
kernel_rfl funct_main : Genv.find_funct_ptr ge.genv_genv Block.main = some (.Internal dense.fn.main)

/-- `SETWORDSNEEDED(n)`, the `m` the harness computes. -/
abbrev wordsOf (n : Nat) : Nat := Statement.setwordsNeeded n

/-- The `ptn` the harness builds: 1 inside a cell, 0 at its end. -/
def harnessPtn (n : Nat) (ends : List Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => if i.val ∈ ends then 0 else 1

/-- The `options` global as `main` leaves it (`optionstruct`, x86-64 layout). -/
structure OptionsAt (m : mem) : Prop where
  getcanon : FieldAt m .Mint32 Block.options 0 (.Vint (ir 1))
  digraph : FieldAt m .Mint32 Block.options 4 (.Vint (ir 0))
  writeautoms : FieldAt m .Mint32 Block.options 8 (.Vint (ir 0))
  writemarkers : FieldAt m .Mint32 Block.options 12 (.Vint (ir 0))
  defaultptn : FieldAt m .Mint32 Block.options 16 (.Vint (ir 0))
  cartesian : FieldAt m .Mint32 Block.options 20 (.Vint (ir 0))
  linelength : FieldAt m .Mint32 Block.options 24 (.Vint (ir 78))
  outfile : FieldAt m .Mint64 Block.options 32 (.Vptr Block.dummyfile Ptrofs.zero)
  userrefproc : FieldAt m .Mint64 Block.options 40 Vnullptr
  userautomproc : FieldAt m .Mint64 Block.options 48 (.Vptr Block.emitGenerator Ptrofs.zero)
  userlevelproc : FieldAt m .Mint64 Block.options 56 Vnullptr
  usernodeproc : FieldAt m .Mint64 Block.options 64 Vnullptr
  usercanonproc : FieldAt m .Mint64 Block.options 72 Vnullptr
  invarproc : FieldAt m .Mint64 Block.options 80 Vnullptr
  tcLevel : FieldAt m .Mint32 Block.options 88 (.Vint (ir 100))
  mininvarlevel : FieldAt m .Mint32 Block.options 92 (.Vint (ir 0))
  maxinvarlevel : FieldAt m .Mint32 Block.options 96 (.Vint (ir 1))
  invararg : FieldAt m .Mint32 Block.options 100 (.Vint (ir 0))
  dispatch : FieldAt m .Mint64 Block.options 104 (.Vptr Block.dispatchGraph Ptrofs.zero)
  schreier : FieldAt m .Mint32 Block.options 112 (.Vint (ir 0))
  extraOptions : FieldAt m .Mint64 Block.options 120 Vnullptr

/-- `densenauty(g, lab, ptn, orbits, &options, &stats, m, n, canong)` as
`dense_main` calls it on the coloured graph `G`. -/
def densenautySpec {n k : Nat} (G : Colored n k) (gens : List (Array Nat)) (bg bl bp bo bst bc : block) : FunSpec where
  pre args m := args = [.Vptr bg Ptrofs.zero, .Vptr bl Ptrofs.zero, .Vptr bp Ptrofs.zero,
      .Vptr bo Ptrofs.zero, .Vptr Block.options Ptrofs.zero, .Vptr bst Ptrofs.zero,
      .Vint (ir (wordsOf n)), .Vint (ir n), .Vptr bc Ptrofs.zero] ∧
    (∃ m₀, Genv.init_mem Init.prog = some m₀ ∧
      Unch m₀ m (fun z => z = Block.options ∨ ¬ Mem.valid_block m₀ z) ∧
      ∀ z ∈ [bg, bl, bp, bo, bst, bc], ¬ Mem.valid_block m₀ z ∧ Mem.valid_block m z) ∧
    OptionsAt m ∧
    (∃ gw, GraphAt m bg Ptrofs.zero gw (rowsOf G) (wordsOf n)) ∧
    ArrayAt m .Mint32 bl 0 (ints (initialPartition G).1) n ∧
    ArrayAt m .Mint32 bp 0 (ints (harnessPtn n (initialPartition G).2)) n ∧
    (∃ v, ArrayAt m .Mint32 bo 0 v n) ∧
    (∃ v, ArrayAt m .Mint64 bc 0 v (wordsOf n * n)) ∧
    Mem.range_perm m bst (zOfInt 0) (zOfInt 88) .Cur .Freeable ∧
    [bg, bl, bp, bo, bst, bc].Pairwise (· ≠ ·) ∧
    0 < n ∧ n ≤ 65536
  post _ m t _ m' :=
    let r := runColoredTraced G
    Writes t (gensWords gens n) ∧
    ArrayAt m' .Mint32 bl 0 (ints r.result.canonlab) n ∧
    ArrayAt m' .Mint32 bo 0 (ints (Statement.finalState G).orbits) n ∧
    (∃ cw, ArrayAt m' .Mint64 bc 0 (longs cw) (wordsOf n * n) ∧
      ∀ v < n, SetRep (fun w => bv64 (cw (wordsOf n * v + w))) (wordsOf n) r.result.canong[v]!) ∧
    FieldAt m' .Mint32 bst 12 (.Vint (ir r.result.numorbits)) ∧
    FieldAt m' .Mint32 bst 16 (.Vint (ir r.result.numgenerators)) ∧
    FieldAt m' .Mint32 bst 20 (.Vint (ir 0)) ∧
    FieldAt m' .Mint64 bst 24 (.Vlong (lr r.result.numnodes)) ∧
    FieldAt m' .Mint64 bst 32 (.Vlong (lr r.result.numbadleaves)) ∧
    FieldAt m' .Mint32 bst 40 (.Vint (ir r.result.maxlevel)) ∧
    FieldAt m' .Mint64 bst 48 (.Vlong (lr r.result.tctotal)) ∧
    FieldAt m' .Mint64 bst 56 (.Vlong (lr r.result.canupdates)) ∧
    Mem.range_perm m' bst (zOfInt 0) (zOfInt 88) .Cur .Freeable ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z)

end NautyVerified.Proofs.Harness
