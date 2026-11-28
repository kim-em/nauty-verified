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
  this level's target cell); every node of the new list was in the old one or
  is newly allocated, so the caller's locals never join the list.

`TcOk m S chain` says the list's blocks are valid, pairwise distinct, and
none of them is a block of `S` or a work block. The precondition also asks
for `userautomproc`'s block `S.bUA` to be valid and readable at offset 0 (it is emit_generator's
function block, valid from the initial memory): a block a node allocates is
then not `S.bUA`.

`NodeOk ctx first level numcells st` collects the HexGraphIso facts the C
needs at a node, beyond `SearchAt`: the fuel bound is never reached, and the
cell count is the one `refine` expects. It is a parameter of the
specifications here; `firstpathnodeSpecG`/`othernodeSpecG` instantiate it
with `denseNodeOk G`: `SearchInf.NodeOk G` (`Spec/NodeOk.lean`) and the
active set's `ActiveOk`.

`NodeFrame m m' S chain level`: the blocks a node at `level` may change: those
of `SFrame`, the list's nodes from index `level - 2` (the parent's `next`
field) and their target cells from index `level - 1`. The parent's own
target cell (index `level - 2`) is unchanged. A work block afterwards was a work
block before or is newly allocated. Every unwind goes strictly above the node.
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

theorem writes_app : ∀ t₁ t₂ : List event, Statement.writes (List.append t₁ t₂) =
    Statement.writes t₁ ++ Statement.writes t₂
  | [], _ => rfl
  | ev :: t₁, t₂ => by
    have ih : Statement.writes (t₁ ++ t₂) = _ := writes_app t₁ t₂
    show Statement.writes (ev :: List.append t₁ t₂) = _
    rcases ev with ⟨name, args, res⟩ | _ | _ | _
    · rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · simpa [Statement.writes] using ih
      · rcases a <;> simp only [Statement.writes] <;> (try split) <;> simp [ih]
      · simpa [Statement.writes] using ih
    all_goals simpa [Statement.writes] using ih

theorem reads_app : ∀ t₁ t₂ : List event, Statement.reads (List.append t₁ t₂) =
    Statement.reads t₁ ++ Statement.reads t₂
  | [], _ => rfl
  | ev :: t₁, t₂ => by
    have ih : Statement.reads (t₁ ++ t₂) = _ := reads_app t₁ t₂
    show Statement.reads (ev :: List.append t₁ t₂) = _
    rcases ev with ⟨name, args, res⟩ | _ | _ | _
    · rcases args with _ | ⟨a, rest⟩
      · simp only [Statement.reads]; split <;> simp [ih]
      · simpa [Statement.reads] using ih
    all_goals simpa [Statement.reads] using ih

theorem Emits.append {t₁ t₂ : trace} {l₁ l₂ : List Int} (h₁ : Emits t₁ l₁) (h₂ : Emits t₂ l₂) :
    Emits (t₁ ++ t₂) (l₁ ++ l₂) := by
  obtain ⟨w1, r1, v1⟩ := h₁
  obtain ⟨w2, r2, v2⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · exact (writes_app t₁ t₂).trans (by rw [w1, w2])
  · exact (reads_app t₁ t₂).trans (by rw [r1, r2]; rfl)
  · intro c i o ev hm
    rcases List.mem_append.1 hm with hm | hm
    · exact v1 c i o ev hm
    · exact v2 c i o ev hm

theorem Emits.nil : Emits [] [] := Writes.nil.emits

/-- The node fuel HexGraphIso uses at `level`. -/
abbrev nodeFuel (n level : Nat) : Nat := n + 3 - level

/-- HexGraphIso's node at `level`, as nauty.c runs it. -/
abbrev hexNode {n : Nat} (first : Bool) (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    Exit × Search n :=
  node first ctx nautyInf 100 (nodeFuel n level) level numcells st

/-- The tcnode that `level`'s call receives as `tcnode_parent`: `tcnode0` at
level 1, else node `level - 2` of the list. -/
def tcParent {ge : genv} [E : NautyEnv ge] (chain : List (block × block)) (level : Nat) : block :=
  if level ≤ 1 then E.tcnode0 else (chain[level - 2]?.map Prod.fst).getD E.tcnode0

/-- The list's blocks are valid, distinct, and apart from `S` and the work blocks. -/
structure TcOk (m : mem) (S : SLoc) (chain : List (block × block)) : Prop where
  pairwise : (chain.flatMap fun p => [p.1, p.2]).Pairwise (· ≠ ·)
  valid : ∀ p ∈ chain, Mem.valid_block m p.1 ∧ Mem.valid_block m p.2
  apart : ∀ p ∈ chain, p.1 ∉ S.blocks ∧ p.2 ∉ S.blocks ∧ ¬ IsWork m p.1 ∧ ¬ IsWork m p.2

/-- What a node at `level` may change. -/
def NodeFrame (m m' : mem) (S : SLoc) (chain : List (block × block)) (level : Nat) : Prop :=
  Unch m m' (fun z => S.Chg z ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨
      z = Block.tcnode0 ∨
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
    NodeOk first level numcells st ∧ Mem.valid_block m S.bUA ∧
    Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty
  post _ m t v m' :=
    let r := hexNode first ctx level numcells st
    v = .Vint (ir (exitValue level r.1).1) ∧
    SearchAt m' S ctx r.2 false (exitValue level r.1).2 ∧
    Emits t (Em first level numcells st) ∧
    (∃ chain', TcChain m' S.M Block.tcnode0 chain' ∧ TcOk m' S chain' ∧ level ≤ chain'.length ∧
      chain'.take (level - 1) = chain.take (level - 1) ∧
      ∀ p ∈ chain', p ∈ chain ∨ (¬ Mem.valid_block m p.1 ∧ ¬ Mem.valid_block m p.2)) ∧
    NodeFrame m m' S chain level ∧ (∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z) ∧
    ∀ tg sh, r.1 = .unwind tg sh → tg < level

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

/-- The dense node precondition: the HexGraphIso facts of `Spec/NodeOk.lean`
and the active set `ActiveOk`, which the dispatch `refine` takes. -/
def denseNodeOk {n k : Nat} (G : Hex.GraphIso.Colored n k) (first : Bool) (level numcells : Nat)
    (st : Search n) : Prop :=
  SearchInf.NodeOk G first level numcells st ∧
    NautyVerified.Proofs.Dispatch.ActiveOk st.ptn level numcells st.active

/-- nauty()'s initial active set, one position per cell start, is `ActiveOk`
at the root. -/
theorem activeOk_root {n k : Nat} (G : Hex.GraphIso.Colored n k) (hn0 : 0 < n) :
    NautyVerified.Proofs.Dispatch.ActiveOk
      (SearchInf.initialC n (initialPartition G).1 (initialPartition G).2).ptn 1
      (initialPartition G).2.length
      (SearchInf.initialC n (initialPartition G).1 (initialPartition G).2).active := by
  have hok := Hex.GraphIso.Nauty.initial_nodeOk G hn0
  refine ⟨fun v hv => ?_, initActive_card n _⟩
  rcases hok.starts v hv with h | h
  · exact .inl h
  · right
    show (initPtn n SearchInf.nautyInfinity (initialPartition G).2)[v - 1]! ≤ 1
    have h' : (initPtn n (n + 2) (initialPartition G).2)[v - 1]! ≤ 1 := h
    rw [← SearchInf.initPtn_map (a := n + 2) (b := SearchInf.nautyInfinity) (by omega),
      SearchInf.getElem!_map_phi (by omega),
      SearchInf.phi_ne (show (initPtn n (n + 2) (initialPartition G).2)[v - 1]! ≠ n + 2 by omega)]
    exact h'

/-- `firstpathnode0` on the graph `G`, with `NodeOk` the HexGraphIso facts of
`Spec/NodeOk.lean` and `ActiveOk` (`denseNodeOk`). -/
abbrev firstpathnodeSpecG {n k : Nat} (xi : ExternalCalls) (G : Hex.GraphIso.Colored n k)
    (Em : Bool → Nat → Nat → Search n → List Int) (S : SLoc) (st : Search n)
    (level numcells : Nat) (chain : List (block × block)) : FunSpec :=
  firstpathnodeSpec xi (denseNodeOk G) Em S ⟨rowsOf G⟩ st level numcells chain

/-- `othernode0` on the graph `G`, with `NodeOk` `denseNodeOk`. -/
abbrev othernodeSpecG {n k : Nat} (xi : ExternalCalls) (G : Hex.GraphIso.Colored n k)
    (Em : Bool → Nat → Nat → Search n → List Int) (S : SLoc) (st : Search n)
    (level numcells : Nat) (chain : List (block × block)) : FunSpec :=
  othernodeSpec xi (denseNodeOk G) Em S ⟨rowsOf G⟩ st level numcells chain

/-! ### For any dispatch representation

The node specification over `SearchAtG D`, against HexGraphIso's
`Generic.node` for a search policy on `D`'s state (`hexNodeG`); `TcOkG`
and `NodeFrameG` are `TcOk` and `NodeFrame` for `D`. At `denseRep` with
HexGraphIso's nauty policy they give the dense forms (`TcOk.toG`,
`TcOkG.dense`, `NodeFrameG.dense`, `nodeSpec_ofG`, through
`node_eq_generic`). -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} (D : DispatchRep ge O)

/-- `hexNode` for the policy `P` on `D`'s search state. -/
abbrev hexNodeG {n : Nat} [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]
    (first : Bool) (G : O.Gr n) (level numcells : Nat) (st : SearchState n (O.Canon n)) :
    Exit × SearchState n (O.Canon n) :=
  Generic.node first G nautyInf 100 (nodeFuel n level) level numcells st

/-- `TcOk` for `D`. -/
structure TcOkG (m : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) (chain : List (block × block)) :
    Prop where
  pairwise : (chain.flatMap fun p => [p.1, p.2]).Pairwise (· ≠ ·)
  valid : ∀ p ∈ chain, Mem.valid_block m p.1 ∧ Mem.valid_block m p.2
  apart : ∀ p ∈ chain, p.1 ∉ S.blocksG D gl cl ∧ p.2 ∉ S.blocksG D gl cl ∧
    ¬ IsWorkG D m p.1 ∧ ¬ IsWorkG D m p.2

/-- `NodeFrame` for `D`. -/
def NodeFrameG (m m' : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) (chain : List (block × block))
    (level : Nat) : Prop :=
  Unch m m' (fun z => S.ChgG D gl cl z ∨ ¬ Mem.valid_block m z ∨ IsWorkG D m z ∨
      z = E.tcnode0 ∨
      (∃ i p, chain[i]? = some p ∧ level ≤ i + 2 ∧ z = p.1) ∨
      (∃ i p, chain[i]? = some p ∧ level ≤ i + 1 ∧ z = p.2)) ∧
    ∀ z, Mem.valid_block m z → Mem.valid_block m' z

/-- `nodeSpec` for `D` and the policy `P`. -/
def nodeSpecG {n : Nat} [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]
    (xi : ExternalCalls) (NodeOk : Bool → Nat → Nat → SearchState n (O.Canon n) → Prop)
    (Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int) (first : Bool) (S : SLoc)
    (gl : D.GLoc) (cl : D.CLoc) (G : O.Gr n) (st : SearchState n (O.Canon n))
    (level numcells : Nat) (chain : List (block × block)) : FunSpec where
  pre args m := args = [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level),
      .Vint (ir numcells), .Vptr (tcParent chain level) Ptrofs.zero] ∧
    SearchAtG D m S gl cl G st first false ∧ TcChain m S.M E.tcnode0 chain ∧
    TcOkG D m S gl cl chain ∧ level - 1 ≤ chain.length ∧ AutomCb xi S.bUA ∧ 1 ≤ level ∧
    level ≤ n ∧ numcells ≤ n ∧ NodeOk first level numcells st ∧ Mem.valid_block m S.bUA ∧
    Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty
  post _ m t v m' :=
    let r := hexNodeG first G level numcells st
    v = .Vint (ir (exitValue level r.1).1) ∧
    SearchAtG D m' S gl cl G r.2 false (exitValue level r.1).2 ∧
    Emits t (Em first level numcells st) ∧
    (∃ chain', TcChain m' S.M E.tcnode0 chain' ∧ TcOkG D m' S gl cl chain' ∧
      level ≤ chain'.length ∧ chain'.take (level - 1) = chain.take (level - 1) ∧
      ∀ p ∈ chain', p ∈ chain ∨ (¬ Mem.valid_block m p.1 ∧ ¬ Mem.valid_block m p.2)) ∧
    NodeFrameG D m m' S gl cl chain level ∧
    (∀ z, IsWorkG D m' z → IsWorkG D m z ∨ ¬ Mem.valid_block m z) ∧
    ∀ tg sh, r.1 = .unwind tg sh → tg < level

end Generic

section Dense

open NautyVerified.Proofs.Dispatch

theorem TcOk.toG {m : mem} {S : SLoc} {chain : List (block × block)} (h : TcOk m S chain) :
    TcOkG denseRep m S () () chain :=
  ⟨h.pairwise, h.valid, fun p hp =>
    let ⟨a, b, c, d⟩ := h.apart p hp
    ⟨fun e => a (SLoc.mem_blocksG.1 e), fun e => b (SLoc.mem_blocksG.1 e),
      fun e => c (isWork_dense.1 e), fun e => d (isWork_dense.1 e)⟩⟩

theorem TcOkG.dense {m : mem} {S : SLoc} {chain : List (block × block)}
    (h : TcOkG denseRep m S () () chain) : TcOk m S chain :=
  ⟨h.pairwise, h.valid, fun p hp =>
    let ⟨a, b, c, d⟩ := h.apart p hp
    ⟨fun e => a (SLoc.mem_blocksG.2 e), fun e => b (SLoc.mem_blocksG.2 e),
      fun e => c (isWork_dense.2 e), fun e => d (isWork_dense.2 e)⟩⟩

theorem NodeFrameG.dense {m m' : mem} {S : SLoc} {chain : List (block × block)} {level : Nat}
    (h : NodeFrameG denseRep m m' S () () chain level) : NodeFrame m m' S chain level :=
  ⟨h.1.mono fun _ hz => by
    rcases hz with hz | hz | hz | hz
    · exact .inl (SLoc.chgG_dense.1 hz)
    · exact .inr (.inl hz)
    · exact .inr (.inr (.inl (isWork_dense.1 hz)))
    · exact .inr (.inr (.inr hz)), h.2⟩

theorem hexNodeG_dense {n : Nat} (first : Bool) (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    hexNodeG (O := denseOps) first ctx level numcells st = hexNode first ctx level numcells st :=
  (node_eq_generic _ _ _ _ _ _ _ _).symm

theorem nodeSpec_ofG {xi : ExternalCalls} {fd : fundef} {n : Nat}
    {NodeOk : Bool → Nat → Nat → Search n → Prop} {Em : Bool → Nat → Nat → Search n → List Int}
    {first : Bool} {S : SLoc} {ctx : Ctx n} {st : Search n} {level numcells : Nat}
    {chain : List (block × block)}
    (h : Satisfies xi Program.ge fd
      (nodeSpecG denseRep xi NodeOk Em first S () () ctx st level numcells chain)) :
    Satisfies xi Program.ge fd (nodeSpec xi NodeOk Em first S ctx st level numcells chain) := by
  refine Satisfies.mono ?_ ?_ h
  · rintro _ _ ⟨ha, hs, hc, hok, h1, hu, h2, h3, h4, h5, h6, h7⟩
    exact ⟨ha, hs.toG, hc, hok.toG, h1, hu, h2, h3, h4, h5, h6, h7⟩
  · rintro _ _ _ _ _ ⟨_, hs, _⟩ hp
    simp only [nodeSpecG, hexNodeG_dense] at hp
    obtain ⟨hv, hs', hem, ⟨chain', hc', hok', h1, h2, h3⟩, hf, hw, hu⟩ := hp
    exact ⟨hv, hs'.dense hs.gw, hem, ⟨chain', hc', hok'.dense, h1, h2, h3⟩, hf.dense,
      workMonoG_dense hw, hu⟩

theorem NodeFrame.toG {m m' : mem} {S : SLoc} {chain : List (block × block)} {level : Nat}
    (h : NodeFrame m m' S chain level) : NodeFrameG denseRep m m' S () () chain level :=
  ⟨h.1.mono fun _ hz => by
    rcases hz with hz | hz | hz | hz
    · exact .inl (SLoc.chgG_dense.2 hz)
    · exact .inr (.inl hz)
    · exact .inr (.inr (.inl (isWork_dense.2 hz)))
    · exact .inr (.inr (.inr hz)), h.2⟩

/-- The dense node specification gives the generic one at `denseRep`, given the
graph's words (memory-independent, from the caller's `SearchAt`). -/
theorem nodeSpec_toG {xi : ExternalCalls} {fd : fundef} {n : Nat}
    {NodeOk : Bool → Nat → Nat → Search n → Prop} {Em : Bool → Nat → Nat → Search n → List Int}
    {first : Bool} {S : SLoc} {ctx : Ctx n} {st : Search n} {level numcells : Nat}
    {chain : List (block × block)}
    (hgw : ∀ v < n, SetRep (fun w => bv64 (S.gw (S.M * v + w))) S.M ctx.g[v]!)
    (h : Satisfies xi Program.ge fd (nodeSpec xi NodeOk Em first S ctx st level numcells chain)) :
    Satisfies xi Program.ge fd
      (nodeSpecG denseRep xi NodeOk Em first S () () ctx st level numcells chain) := by
  refine Satisfies.mono ?_ ?_ h
  · rintro _ _ ⟨ha, hs, hc, hok, h1, hu, h2, h3, h4, h5, h6, h7⟩
    exact ⟨ha, hs.dense hgw, hc, hok.dense, h1, hu, h2, h3, h4, h5, h6, h7⟩
  · rintro _ _ _ _ _ - hp
    simp only [nodeSpecG, hexNodeG_dense]
    obtain ⟨hv, hs', hem, ⟨chain', hc', hok', h1, h2, h3⟩, hf, hw, hu⟩ := hp
    exact ⟨hv, hs'.toG, hem, ⟨chain', hc', hok'.toG, h1, h2, h3⟩, hf.toG,
      fun z hz => (hw z (isWork_dense.1 hz)).imp isWork_dense.2 id, hu⟩

end Dense

end NautyVerified.Proofs.Search
