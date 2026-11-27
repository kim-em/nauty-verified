import NautyVerified.Proofs.Fmperm.Loop
import NautyVerified.Proofs.Nextelement.Satisfies

/-!
# `fmperm` meets its specification

`fmpermSpec`: called with a permutation `perm` of `0 .. n-1` and sets `fix`,
`mcr` of `M` words, nauty's `fmperm` leaves in `fix` and `mcr` words
representing HexGraphIso's `fmperm perm n`. Along the way `DYNALLOC1` may
replace nautil.c's `workperm` array (`DynAt`); nothing else changes.
-/

namespace NautyVerified.Proofs.Fmperm

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Spec
open NautyVerified.Proofs.Set (longs addW BitTable)
open NautyVerified.Proofs.Alloc (DynAt)
open Hex.GraphIso.Nauty (VSet)

/-- The blocks nautil.c's `workperm` pair occupies. -/
abbrev WP := Block.nautilWorkperm
abbrev WPS := Block.nautilWorkpermSz

/-- The specification of `fmperm`. -/
def fmpermSpec (bpm : block) (pofs : ptrofs) (bf : block) (fofs : ptrofs) (bm : block)
    (mofs : ptrofs) (perm : Array Nat) (n M : Nat) (wf wm : Nat → Lib.Integers.int64)
    (cap : Nat) (b0 : block) : FunSpec where
  pre args m := args = [.Vptr bpm pofs, .Vptr bf fofs, .Vptr bm mofs, .Vint (ir M), .Vint (ir n)] ∧
    ArrayAt m .Mint32 bpm (intOfZ (Ptrofs.unsigned pofs)) (ints perm) n ∧
    ArrayAt m .Mint64 bf (intOfZ (Ptrofs.unsigned fofs)) (longs wf) M ∧
    ArrayAt m .Mint64 bm (intOfZ (Ptrofs.unsigned mofs)) (longs wm) M ∧
    BitTable m Block.nautilBit ∧ DynAt m WP WPS 4 cap b0 ∧
    Mem.valid_block m bpm ∧ Mem.valid_block m bf ∧ Mem.valid_block m bm ∧
    bf ≠ bm ∧ bf ≠ bpm ∧ bm ≠ bpm ∧
    (∀ z, z = WP ∨ z = WPS ∨ z = Block.nautilBit → z ≠ bpm ∧ z ≠ bf ∧ z ≠ bm) ∧
    (0 < cap → b0 ≠ bpm ∧ b0 ≠ bf ∧ b0 ≠ bm ∧ b0 ≠ Block.nautilBit) ∧
    perm.size = n ∧ (∀ x, x < n → perm[x]! < n) ∧
    (∀ x y, x < n → y < n → perm[x]! = perm[y]! → x = y) ∧
    n < 2147483648 ∧ 0 < M ∧ M < 2147483648 ∧ n ≤ 64 * M
  post _ m t _ m' := t = E0 ∧ ∃ wf' wm' cap' b',
    ArrayAt m' .Mint64 bf (intOfZ (Ptrofs.unsigned fofs)) (longs wf') M ∧
    ArrayAt m' .Mint64 bm (intOfZ (Ptrofs.unsigned mofs)) (longs wm') M ∧
    SetRep (fun w => bv64 (wf' w)) M (Hex.GraphIso.Nauty.fmperm perm n).1 ∧
    SetRep (fun w => bv64 (wm' w)) M (Hex.GraphIso.Nauty.fmperm perm n).2 ∧
    DynAt m' WP WPS 4 cap' b' ∧ n ≤ cap' ∧ (b' = b0 ∨ ¬ Mem.valid_block m b') ∧
    Unch m m' (fun z => z = bf ∨ z = bm ∨ z = WPS ∨ z = WP ∨ z = b0 ∨ z = b')

end NautyVerified.Proofs.Fmperm
