import NautyVerified.Proofs.Harness.Spec
import NautyVerified.Proofs.Top.DensenautySyntax

/-!
# What `densenauty` needs from `nauty`

`nautySpec G gens bg bl bp bo bst bc capD bD`: `densenauty` calls
`nauty(g, lab, ptn, NULL, orbits, options, stats, dnwork, 2 * 500 * m, m, n,
canong)` in the memory `densenautySpec` describes, except that `densenauty`
has (re)allocated its workspace `dnwork` (naugraph.c's `DYNALLSTAT` pair
holding `capD ≥ 1000 * m` setwords at `bD`). Its postcondition is
`densenautySpec`'s, and `options->digraph` stays writable (`densenauty`
writes it back afterwards).
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Graph (GraphAt)
open NautyVerified.Proofs.Alloc (DynAt)
open NautyVerified.Proofs.Search (FieldAt Writes gensWords)
open NautyVerified.Proofs.Harness (OptionsAt wordsOf harnessPtn densenautySpec)
open Hex.GraphIso Hex.GraphIso.Nauty

/-- The `NULL` that `densenauty` passes as `active`, as a `set *` argument. -/
def nullArg : val :=
  .Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir 0)))

def nautySpec {n k : Nat} (G : Colored n k) (gens : List (Array Nat)) (bg bl bp bo bst bc : block)
    (capD : Nat) (bD : block) :
    FunSpec where
  pre args m := args = [.Vptr bg Ptrofs.zero, .Vptr bl Ptrofs.zero, .Vptr bp Ptrofs.zero, nullArg,
      .Vptr bo Ptrofs.zero, .Vptr Harness.Block.options Ptrofs.zero, .Vptr bst Ptrofs.zero,
      .Vptr bD Ptrofs.zero, .Vint (ir (2 * 500 * wordsOf n)), .Vint (ir (wordsOf n)), .Vint (ir n),
      .Vptr bc Ptrofs.zero] ∧
    (∃ m₀, Genv.init_mem Init.prog = some m₀ ∧
      Unch m₀ m (fun z => z = Harness.Block.options ∨ z = Block.naugraphDnwork ∨
        z = Block.naugraphDnworkSz ∨ ¬ Mem.valid_block m₀ z) ∧
      (∀ z, Mem.valid_block m₀ z → Mem.valid_block m z) ∧
      (∀ z ∈ [bg, bl, bp, bo, bst, bc], ¬ Mem.valid_block m₀ z ∧ Mem.valid_block m z) ∧
      ¬ Mem.valid_block m₀ bD ∧ bD ∉ [bg, bl, bp, bo, bst, bc]) ∧
    DynAt m Block.naugraphDnwork Block.naugraphDnworkSz 8 capD bD ∧ 2 * 500 * wordsOf n ≤ capD ∧
    OptionsAt m ∧
    (∃ gw, GraphAt m bg Ptrofs.zero gw (rowsOf G) (wordsOf n)) ∧
    ArrayAt m .Mint32 bl 0 (ints (initialPartition G).1) n ∧
    ArrayAt m .Mint32 bp 0 (ints (harnessPtn n (initialPartition G).2)) n ∧
    (∃ v, ArrayAt m .Mint32 bo 0 v n) ∧
    (∃ cw, ArrayAt m .Mint64 bc 0 (longs cw) (wordsOf n * n)) ∧
    Mem.range_perm m bst (zOfInt 0) (zOfInt 88) .Cur .Freeable ∧
    [bg, bl, bp, bo, bst, bc].Pairwise (· ≠ ·) ∧
    0 < n ∧ n ≤ 65536
  post args m t v m' := (densenautySpec G gens bg bl bp bo bst bc).post args m t v m' ∧
    Mem.valid_access m' .Mint32 Harness.Block.options (zOfInt 4) .Writable

end NautyVerified.Proofs.Top
