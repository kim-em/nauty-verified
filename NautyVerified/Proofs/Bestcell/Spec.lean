import NautyVerified.Proofs.Bestcell.Frame
import NautyVerified.Proofs.Alloc.Dyn3

/-!
# `bestcell`'s specification

`bestcellSpec`: called with a graph, a labelling `lab` and a partition `ptn`
whose last cell is closed at `level`, naugraph.c's `bestcell` returns
HexGraphIso's `bestcell ⟨g⟩ lab ptn level`. Its three `DYNALLOC1`s may replace
`workperm`, `workset` and `bucket` (`DynAt`); nothing else visible changes
(`dyn3Set`).
-/

namespace NautyVerified.Proofs.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (BitTable)
open NautyVerified.Proofs.Graph (GraphAt)
open NautyVerified.Proofs.Alloc (DynAt dyn3Set)
open Hex.GraphIso.Nauty (VSet)

/-- What `bestcell` and `targetcell` need of the caller's memory: the graph,
`lab`, `ptn`, the three `DYNALLSTAT` pairs and naugraph.c's `bit`, with the
caller's blocks apart from the globals and the old arrays. -/
structure Pre {n : Nat} (m : mem) (bg : block) (gofs : ptrofs) (gw : Nat → Lib.Integers.int64)
    (grows : Array (VSet n)) (bl : block) (lofs : ptrofs) (lab : Array Nat) (bp : block)
    (pofs : ptrofs) (ptn : Array Nat) (level M capP : Nat) (bP : block) (capS : Nat) (bS : block)
    (capB : Nat) (bB : block) : Prop where
  graph : GraphAt m bg gofs gw grows M
  larr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n
  lsmall : ∀ j < n, lab[j]! < n
  parr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n
  psize : ptn.size = n
  psmall : ∀ x < n, ptn[x]! < 2147483648
  plast : ptn[n - 1]! ≤ level
  levlt : level < 2147483648
  dP : DynAt m WP WPS 4 capP bP
  dS : DynAt m WS WSS 8 capS bS
  dB : DynAt m BK BKS 4 capB bB
  bit : BitTable m BIT
  caller : ∀ z, z = bg ∨ z = bl ∨ z = bp → Mem.valid_block m z ∧ z ≠ WP ∧ z ≠ WPS ∧ z ≠ WS ∧
    z ≠ WSS ∧ z ≠ BK ∧ z ≠ BKS ∧ z ≠ BIT ∧ (0 < capP → z ≠ bP) ∧ (0 < capS → z ≠ bS) ∧
    (0 < capB → z ≠ bB)
  sP : 0 < capP → bP ≠ WS ∧ bP ≠ WSS ∧ bP ≠ BK ∧ bP ≠ BKS ∧ bP ≠ BIT ∧ (0 < capS → bP ≠ bS) ∧
    (0 < capB → bP ≠ bB)
  sS : 0 < capS → bS ≠ WP ∧ bS ≠ WPS ∧ bS ≠ BK ∧ bS ≠ BKS ∧ bS ≠ BIT ∧ (0 < capB → bS ≠ bB)
  sB : 0 < capB → bB ≠ WP ∧ bB ≠ WPS ∧ bB ≠ WS ∧ bB ≠ WSS ∧ bB ≠ BIT
  n0 : 0 < n
  nlt : n < 1073741824
  M1 : 0 < M
  Mlt : M < 33554432
  nM : n ≤ 64 * M

/-- What `bestcell` and `targetcell` leave: the three `DYNALLSTAT` pairs, each
either as before or a block not valid before, and only `dyn3Set` changed. -/
def Post (m m' : mem) (capP : Nat) (bP : block) (capS : Nat) (bS : block) (capB : Nat)
    (bB : block) : Prop :=
  ∃ capP' bP' capS' bS' capB' bB', DynAt m' WP WPS 4 capP' bP' ∧ DynAt m' WS WSS 8 capS' bS' ∧
    DynAt m' BK BKS 4 capB' bB' ∧
    ((capP' = capP ∧ bP' = bP) ∨ ¬ Mem.valid_block m bP') ∧
    ((capS' = capS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS') ∧
    ((capB' = capB ∧ bB' = bB) ∨ ¬ Mem.valid_block m bB') ∧
    Unch m m' (dyn3Set m capP bP capS bS capB bB)

theorem Post.refl {m : mem} {capP capS capB : Nat} {bP bS bB : block}
    (hP : DynAt m WP WPS 4 capP bP) (hS : DynAt m WS WSS 8 capS bS) (hB : DynAt m BK BKS 4 capB bB) :
    Post m m capP bP capS bS capB bB :=
  ⟨capP, bP, capS, bS, capB, bB, hP, hS, hB, .inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩,
    Unch.refl _ _⟩

def bestcellSpec {n : Nat} (bg : block) (gofs : ptrofs) (gw : Nat → Lib.Integers.int64)
    (grows : Array (VSet n)) (bl : block) (lofs : ptrofs) (lab : Array Nat) (bp : block)
    (pofs : ptrofs) (ptn : Array Nat) (level tcLevel M capP : Nat) (bP : block) (capS : Nat)
    (bS : block) (capB : Nat) (bB : block) : FunSpec where
  pre args m := args = [.Vptr bg gofs, .Vptr bl lofs, .Vptr bp pofs, .Vint (ir level),
      .Vint (ir tcLevel), .Vint (ir M), .Vint (ir n)] ∧
    Pre m bg gofs gw grows bl lofs lab bp pofs ptn level M capP bP capS bS capB bB
  post _ m t v m' := t = E0 ∧
    v = .Vint (ir (Hex.GraphIso.Nauty.bestcell ⟨grows⟩ lab ptn level : Int)) ∧
    Post m m' capP bP capS bS capB bB

end NautyVerified.Proofs.Bestcell
