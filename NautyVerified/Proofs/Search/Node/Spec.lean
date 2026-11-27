import NautyVerified.Proofs.Search.Spec
import NautyVerified.Spec.NodeOk

/-!
# Specifications of nauty.c's search nodes

`firstpathnode0(lab, ptn, level, numcells, tcnode_parent)` and
`othernode0(…)` are HexGraphIso's `node true` and `node false` at `level`,
with node fuel `n + 3 - level` (so `n + 2` at the root, level 1) and the
pinned `inf = nautyInf`, `tcLevel = 100`:

- the returned `int` and `needshortprune` encode the `Exit` (`exitValue`);
- memory holds the resulting search state (after the first leaf, so
  `pre = false`);
- the trace writes `Em first level numcells st`, what nauty emits below the
  node (the `genWords` of `workperm` at each leaf where `numgenerators`
  increases, as `processnodeSpec` states it; `Em` is a parameter, to be
  instantiated by the emitted sequence of the re-pinned HexGraphIso run), and
  reads `nauty_kill_request` as 0 (`Emits`):
  `Satisfies` asks for one execution, and the one chosen is the one whose
  volatile reads return 0, as the end-to-end theorem assumes (`VloadsZero`);
- the target-cell list keeps its first `level - 1` nodes, and has at least
  `level` nodes afterwards (node `level - 1`, allocated if missing, owns
  this level's target cell).

`TcOk m S chain` says the list's blocks are valid, pairwise distinct, and
none of them is a block of `S` or a work block.

`NodeOk ctx first level numcells st` collects the HexGraphIso facts the C
needs at a node, beyond `SearchAt`: the fuel bound is never reached, and the
cell count is the one `refine` expects. It is a parameter of the
specifications here; `firstpathnodeSpecG`/`othernodeSpecG` instantiate it
with `SearchInf.NodeOk G` (`Spec/NodeOk.lean`).

`NodeFrame m m' S chain level`: the blocks a node at `level` may change: those
of `SFrame`, the list's nodes from index `level - 2` (the parent's `next`
field) and their target cells from index `level - 1`. The parent's own
target cell (index `level - 2`) is unchanged.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open Hex.GraphIso.Nauty

/-- `t` writes the values `l`, reads no input, and reads 0 from every volatile
location. -/
def Emits (t : trace) (l : List Int) : Prop :=
  Statement.writes t = l ∧ Statement.reads t = [] ∧ Statement.VloadsZero t

theorem Writes.writes {t : trace} {l : List Int} (h : Writes t l) : Statement.writes t = l := by
  induction h with
  | nil => rfl
  | cons x r _ ih => simp [Statement.writes, ih]

theorem Writes.reads {t : trace} {l : List Int} (h : Writes t l) : Statement.reads t = [] := by
  induction h with
  | nil => rfl
  | cons x r _ ih => simpa [Statement.reads] using ih

theorem Writes.vloadsZero {t : trace} {l : List Int} (h : Writes t l) : Statement.VloadsZero t := by
  induction h with
  | nil => intro _ _ _ _ hm; cases hm
  | cons x r _ ih =>
    intro c i o ev hm
    cases hm with
    | tail _ hm => exact ih c i o ev hm

theorem Writes.emits {t : trace} {l : List Int} (h : Writes t l) : Emits t l :=
  ⟨h.writes, h.reads, h.vloadsZero⟩

/-- The node fuel HexGraphIso uses at `level`. -/
abbrev nodeFuel (n level : Nat) : Nat := n + 3 - level

/-- HexGraphIso's node at `level`, as nauty.c runs it. -/
abbrev hexNode {n : Nat} (first : Bool) (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    Exit × Search n :=
  node first ctx nautyInf 100 (nodeFuel n level) level numcells st

/-- The tcnode that `level`'s call receives as `tcnode_parent`: `tcnode0` at
level 1, else node `level - 2` of the list. -/
def tcParent (chain : List (block × block)) (level : Nat) : block :=
  if level ≤ 1 then Block.tcnode0 else (chain[level - 2]?.map Prod.fst).getD Block.tcnode0

/-- The list's blocks are valid, distinct, and apart from `S` and the work blocks. -/
structure TcOk (m : mem) (S : SLoc) (chain : List (block × block)) : Prop where
  pairwise : (chain.flatMap fun p => [p.1, p.2]).Pairwise (· ≠ ·)
  valid : ∀ p ∈ chain, Mem.valid_block m p.1 ∧ Mem.valid_block m p.2
  apart : ∀ p ∈ chain, p.1 ∉ S.blocks ∧ p.2 ∉ S.blocks ∧ ¬ IsWork m p.1 ∧ ¬ IsWork m p.2

/-- What a node at `level` may change. -/
def NodeFrame (m m' : mem) (S : SLoc) (chain : List (block × block)) (level : Nat) : Prop :=
  Unch m m' (fun z => z ∈ S.blocks ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨ z = Block.tcnode0 ∨
      (∃ i p, chain[i]? = some p ∧ level ≤ i + 2 ∧ z = p.1) ∨
      (∃ i p, chain[i]? = some p ∧ level ≤ i + 1 ∧ z = p.2)) ∧
    ∀ z, Mem.valid_block m z → Mem.valid_block m' z

/-- The node specification, for `first = true` (`firstpathnode0`, entered
before the first leaf) and `first = false` (`othernode0`). -/
def nodeSpec {n : Nat} (xi : ExternalCalls) (NodeOk : Bool → Nat → Nat → Search n → Prop)
    (Em : Bool → Nat → Nat → Search n → List Int) (first : Bool) (S : SLoc) (ctx : Ctx n) (st : Search n) (level numcells : Nat)
    (chain : List (block × block)) : FunSpec where
  pre args m := args = [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level),
      .Vint (ir numcells), .Vptr (tcParent chain level) Ptrofs.zero] ∧
    SearchAt m S ctx st first false ∧ TcChain m S.M Block.tcnode0 chain ∧ TcOk m S chain ∧
    level - 1 ≤ chain.length ∧ AutomCb xi S.bUA ∧ 1 ≤ level ∧ level ≤ n ∧ numcells ≤ n ∧
    NodeOk first level numcells st
  post _ m t v m' :=
    let r := hexNode first ctx level numcells st
    v = .Vint (ir (exitValue level r.1).1) ∧
    SearchAt m' S ctx r.2 false (exitValue level r.1).2 ∧
    Emits t (Em first level numcells st) ∧
    (∃ chain', TcChain m' S.M Block.tcnode0 chain' ∧ TcOk m' S chain' ∧ level ≤ chain'.length ∧
      chain'.take (level - 1) = chain.take (level - 1)) ∧
    NodeFrame m m' S chain level

/-- `firstpathnode0`. -/
abbrev firstpathnodeSpec {n : Nat} (xi : ExternalCalls)
    (NodeOk : Bool → Nat → Nat → Search n → Prop) (Em : Bool → Nat → Nat → Search n → List Int)
    (S : SLoc) (ctx : Ctx n) (st : Search n)
    (level numcells : Nat) (chain : List (block × block)) : FunSpec :=
  nodeSpec xi NodeOk Em true S ctx st level numcells chain

/-- `othernode0`. -/
abbrev othernodeSpec {n : Nat} (xi : ExternalCalls)
    (NodeOk : Bool → Nat → Nat → Search n → Prop) (Em : Bool → Nat → Nat → Search n → List Int)
    (S : SLoc) (ctx : Ctx n) (st : Search n)
    (level numcells : Nat) (chain : List (block × block)) : FunSpec :=
  nodeSpec xi NodeOk Em false S ctx st level numcells chain

/-- `firstpathnode0` on the graph `G`, with `NodeOk` the HexGraphIso facts of
`Spec/NodeOk.lean`. -/
abbrev firstpathnodeSpecG {n k : Nat} (xi : ExternalCalls) (G : Hex.GraphIso.Colored n k)
    (Em : Bool → Nat → Nat → Search n → List Int) (S : SLoc) (st : Search n)
    (level numcells : Nat) (chain : List (block × block)) : FunSpec :=
  firstpathnodeSpec xi (SearchInf.NodeOk G) Em S ⟨rowsOf G⟩ st level numcells chain

/-- `othernode0` on the graph `G`, with `NodeOk` the HexGraphIso facts of
`Spec/NodeOk.lean`. -/
abbrev othernodeSpecG {n k : Nat} (xi : ExternalCalls) (G : Hex.GraphIso.Colored n k)
    (Em : Bool → Nat → Nat → Search n → List Int) (S : SLoc) (st : Search n)
    (level numcells : Nat) (chain : List (block × block)) : FunSpec :=
  othernodeSpec xi (SearchInf.NodeOk G) Em S ⟨rowsOf G⟩ st level numcells chain

end NautyVerified.Proofs.Search
