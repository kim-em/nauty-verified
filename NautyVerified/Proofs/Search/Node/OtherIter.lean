import NautyVerified.Proofs.Search.Node.OtherFrame
import NautyVerified.Proofs.Search.Node.LoopShape
import NautyVerified.Proofs.Search.Node.OkOff
import NautyVerified.Proofs.Search.Node.Prune
import NautyVerified.Proofs.Search.Node.ProcFacts
import NautyVerified.Spec.NodeBound
import NautyVerified.Proofs.Search.Node.UaFrame
import NautyVerified.Proofs.Search.Valid
import NautyVerified.Proofs.Search.Node.Laws

/-!
# One child of `othernode0`'s sweep

`OAtG`: the state of `othernode0` at the head of its child loop, for the
cursor `tv`: `SearchAtG` for the sweep's state, the temporaries, the locals'
values, the target cell, and `CarryG`: the target-cell list (whose entry
`level - 1` is this node's), the locals' blocks and the frame since entry.
`OEnvG`: the locals' bindings and freshness.

`wp_otherIterG`: the loop body after its test, from `OAtG` with the cursor at
a vertex, is `oChildG`, HexGraphIso's `otherChildG` for a search policy `P`
with link `K` and laws `Lw`. A child that continues the sweep ends in `OAtG`
for the pruned cell and the recovered state; one that unwinds below `level`
returns its target.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Set (sk longs)
open NautyVerified.Proofs.Refine (tv)
open Hex.GraphIso Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

/-- `othernode0`'s addressable locals. -/
structure OLocs where
  bnc : block
  bk : block
  bz : block
  bc : block
  bq : block

/-- The locals, as a list. -/
abbrev OLocs.list (L : OLocs) : List block := [L.bnc, L.bk, L.bz, L.bc, L.bq]

theorem TcChain.headValid {m : mem} {M : Nat} {prev : block} :
    ∀ {chain : List (block × block)}, TcChain m M prev chain → Mem.valid_block m prev
  | [], h => FieldAt.valid h
  | _ :: _, h => FieldAt.valid h.1

theorem SLoc.vars_blocks {S : SLoc} {z : block} (h : z ∈ S.vars) : z ∈ S.blocks := by
  rw [SLoc.blocks_split]; exact List.mem_append_left _ h

theorem workG_globs : ∀ z ∈ workG, z ∈ globs := by decide

theorem tcnode0_globs : Block.tcnode0 ∈ globs := by decide

/-! ### For any dispatch representation

`CarryG.step` moves `CarryG` across any step confined to blocks of `S` a
search function may change, blocks not valid before, scratch blocks in use,
the locals and the target cell; `CarryG.chg` is the case that keeps the
locals and the target cell. `SearchAtG.wmono` and `SearchAtG.chgL`: a step
writing only blocks the search's own statements write (`SearchAtG.not_wr`)
keeps the scratch blocks in use, and its blocks are blocks of `S` a search
function may change. -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

/-- The locals' bindings and freshness, and the globals' absence from `e`. -/
structure OEnvG (D : DispatchRep ge O) (e : env) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc)
    (m₀ : mem) (L : OLocs) : Prop where
  enc : PTree.get dense.id.numcells e = some (L.bnc, tint)
  ek : PTree.get dense.id.refcode e = some (L.bk, tint)
  ez : PTree.get dense.id.tcellsize e = some (L.bz, tint)
  ec : PTree.get dense.id.tc e = some (L.bc, tint)
  eq : PTree.get dense.id.qinvar e = some (L.bq, tint)
  glob : ∀ x, x ∉ [dense.id.numcells, dense.id.refcode, dense.id.tcellsize, dense.id.tc,
    dense.id.qinvar] → PTree.get x e = none
  fresh : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z
  nodup : L.list.Pairwise (· ≠ ·)
  notS : ∀ z ∈ L.list, z ∉ S.blocksG D gl cl

theorem OEnvG.gl {e : env} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {m₀ : mem} {L : OLocs}
    (hE : OEnvG D e S gl cl m₀ L) (l : List ident)
    (h : ∀ x ∈ l, x ∉ [dense.id.numcells, dense.id.refcode, dense.id.tcellsize, dense.id.tc,
      dense.id.qinvar] := by decide) : ∀ x ∈ l, PTree.get x e = none :=
  fun x hx => hE.glob x (h x hx)

/-- What `othernode0` carries through its child loop besides `SearchAtG`, the
temporaries and the target cell's contents: the values of `numcells` and `tc`,
the target-cell list (entry `level - 1` is this node's), the locals' blocks,
the frame since entry `m₀`, and the callback's block. -/
structure CarryG (D : DispatchRep ge O) (m₀ m : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc)
    (chain₀ chain : List (block × block)) (level : Nat) (ncw tcw : val) (nd bt : block)
    (L : OLocs) : Prop where
  ncv : Mem.load .Mint32 m L.bnc (zOfInt 0) = some ncw
  tcv : Mem.load .Mint32 m L.bc (zOfInt 0) = some tcw
  tcc : TcChain m S.M E.tcnode0 chain
  tco : TcOkG D m S gl cl chain
  own : chain[level - 1]? = some (nd, bt)
  take : chain.take (level - 1) = chain₀.take (level - 1)
  old : ∀ p ∈ chain, p ∈ chain₀ ∨ (¬ Mem.valid_block m₀ p.1 ∧ ¬ Mem.valid_block m₀ p.2)
  locs : ∀ z ∈ L.list, Mem.valid_access m .Mint32 z (zOfInt 0) .Freeable ∧ ¬ IsWorkG D m z ∧
    ∀ p ∈ chain, p.1 ≠ z ∧ p.2 ≠ z
  frame : NodeFrameG D m₀ m S gl cl chain₀ level
  wm : WorkMonoG D m₀ m
  uaV : Mem.valid_block m S.bUA
  uaP : Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty
  l1 : 1 ≤ level

/-- `othernode0` at the head of its child loop, the cursor holding `tvv`. -/
structure OAtG (D : DispatchRep ge O) {n : Nat} (m₀ m : mem) (le : temp_env) (S : SLoc)
    (gl : D.GLoc) (cl : D.CLoc) (G : O.Gr n) (st : SearchState n (O.Canon n))
    (cell : VSet n) (chain₀ chain : List (block × block)) (level nc tc tv1 : Nat) (tvv : Int)
    (nd bt : block) (L : OLocs) : Prop where
  search : SearchAtG D m S gl cl G st false false
  lab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs)
  ptn : PTree.get dense.id.ptn le = some (.Vptr S.bp S.pofs)
  lev : PTree.get dense.id.level le = some (.Vint (ir level))
  this : PTree.get dense.id.tcnode_this le = some (.Vptr nd Ptrofs.zero)
  tcell : PTree.get dense.id.tcell le = some (.Vptr bt Ptrofs.zero)
  tv1 : PTree.get dense.id.tv1 le = some (.Vint (ir tv1))
  tv : PTree.get dense.id.tv le = some (.Vint (ir tvv))
  cellA : ∃ tw, ArrayAt m .Mint64 bt 0 (longs tw) S.M ∧ SetRep (fun w => bv64 (tw w)) S.M cell
  carry : CarryG D m₀ m S gl cl chain₀ chain level (.Vint (ir nc)) (.Vint (ir tc)) nd bt L

theorem tcnode0_memG {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} : E.tcnode0 ∈ S.blocksG D gl cl :=
  SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl (by simp))))))

theorem bUA_memG {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} : S.bUA ∈ S.blocksG D gl cl :=
  SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inl (by simp)))))

/-- A step writing only blocks the search's own statements write keeps the
scratch blocks in use. -/
theorem SearchAtG.wmono {n : Nat} {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {L : List block} (hu : Unch m m' (· ∈ L))
    (hL : ∀ z ∈ L, z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) : WorkMonoG D m m' := by
  obtain ⟨nK, nG, nW⟩ := h.not_wr hL
  exact fun z hz => .inl ((h.work.unch hu (fun z hz => nG z (D.wglobs_sub z hz))
    ⟨nK _ (by simp), nK _ (by simp)⟩ nW hv).2 z hz)

/-- `SearchAtG.wmono` with one more written block outside `S` and not in use. -/
theorem SearchAtG.wmonoB {n : Nat} {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {L : List block} {b : block}
    (hu : Unch m m' (fun z => z ∈ L ∨ z = b))
    (hL : ∀ z ∈ L, z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc)
    (hbS : b ∉ S.blocksG D gl cl) (hbW : ¬ IsWorkG D m b)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) : WorkMonoG D m m' := by
  obtain ⟨nK, nG, nW⟩ := h.not_wr hL
  have mN : E.nautilWorkperm ∈ S.blocksG D gl cl ∧ E.nautilWorkpermSz ∈ S.blocksG D gl cl :=
    ⟨SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl (by simp)))))),
      SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl (by simp))))))⟩
  refine fun z hz => .inl ((h.work.unch hu (fun z hz hw => ?_) ⟨fun hw => ?_, fun hw => ?_⟩
    (fun z hz hw => ?_) hv).2 z hz)
  · rcases hw with hw | rfl
    · exact nG _ (D.wglobs_sub _ hz) hw
    · exact hbS (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inr (D.wglobs_sub _ hz)))))))
  · rcases hw with hw | e
    · exact nK _ (by simp) hw
    · exact hbS (e ▸ mN.1)
  · rcases hw with hw | e
    · exact nK _ (by simp) hw
    · exact hbS (e ▸ mN.2)
  · rcases hw with hw | rfl
    · exact nW _ hz hw
    · exact hbW hz

/-- A block the search's own statements write is a block of `S` a search
function may change. -/
theorem SearchAtG.chgL {n : Nat} {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {L : List block}
    (hL : ∀ z ∈ L, z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc) {z : block}
    (hz : z ∈ L) : S.ChgG D gl cl z := by
  obtain ⟨nK, -, -⟩ := h.not_wr hL
  refine ⟨SLoc.mem_blocksG_of D ?_, fun e => nK _ (by simp) (e ▸ hz),
    fun e => nK _ (by simp) (e ▸ hz)⟩
  rcases SLoc.wr_mem (hL z hz) with hz | hz | hz | hz
  · exact .inr (.inl hz)
  · exact .inr (.inr (.inl hz))
  · exact .inr (.inr (.inr (.inl hz)))
  · exact .inr (.inr (.inr (.inr (.inl hz))))

theorem CarryG.ntc {m₀ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {chain₀ chain : List (block × block)} {level : Nat} {ncw tcw : val}
    {nd bt : block} {L : OLocs} (c : CarryG D m₀ m S gl cl chain₀ chain level ncw tcw nd bt L) :
    bt ∉ S.blocksG D gl cl ∧ ¬ IsWorkG D m bt ∧ Mem.valid_block m bt ∧
      nd ∉ S.blocksG D gl cl ∧ Mem.valid_block m nd :=
  have hp := List.mem_of_getElem? c.own
  ⟨(c.tco.apart _ hp).2.1, (c.tco.apart _ hp).2.2.2, (c.tco.valid _ hp).2, (c.tco.apart _ hp).1,
    (c.tco.valid _ hp).1⟩

/-- `CarryG` across a step confined to blocks of `S` a search function may
change, blocks not valid before, scratch blocks in use, the locals and the
target cell. -/
theorem CarryG.step {n : Nat} {m₀ m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {chain₀ chain : List (block × block)} {level : Nat} {ncw tcw ncw' tcw' : val}
    {nd bt : block} {L : OLocs}
    (hLS : ∀ z ∈ L.list, z ∉ S.blocksG D gl cl) (hLF : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z)
    (h : SearchAtG D m S gl cl G st pre nsp)
    (c : CarryG D m₀ m S gl cl chain₀ chain level ncw tcw nd bt L)
    {W : block → Prop} (hu : Unch m m' W) (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hwm : WorkMonoG D m m')
    (hW : ∀ z, W z → S.ChgG D gl cl z ∨ ¬ Mem.valid_block m z ∨ IsWorkG D m z ∨ z ∈ L.list ∨
      z = bt)
    (hK : ∀ z ∈ L.list, Keep m m' z) (hbt : ∃ vals, ArrayAt m' .Mint64 bt 0 vals S.M)
    (hkb : Keep m m' bt)
    (hnc : Mem.load .Mint32 m' L.bnc (zOfInt 0) = some ncw')
    (htc : Mem.load .Mint32 m' L.bc (zOfInt 0) = some tcw') :
    CarryG D m₀ m' S gl cl chain₀ chain level ncw' tcw' nd bt L := by
  obtain ⟨btS, btW, btV, -, -⟩ := c.ntc
  have hpw := c.tco.pairwise
  have h0S : E.tcnode0 ∈ S.blocksG D gl cl := tcnode0_memG
  have keep : ∀ z, (z ∉ S.blocksG D gl cl ∨ z = E.tcnode0 ∨ z = S.bUA) → Mem.valid_block m z →
      ¬ IsWorkG D m z → z ∉ L.list → z ≠ bt → ¬ W z := by
    intro z hz hv hw hl hb hW'
    rcases hW z hW' with ⟨h1, h2, h3⟩ | h1 | h1 | h1 | h1
    · rcases hz with hz | hz | hz
      · exact hz h1
      · exact h3 hz
      · exact h2 hz
    · exact h1 hv
    · exact hw h1
    · exact hl h1
    · exact hb h1
  have locS : ∀ z, z ∈ S.blocksG D gl cl → z ∉ L.list := fun z hz hl => hLS z hl hz
  refine ⟨hnc, htc, ?_, TcOkG.mono c.tco hg hwm, c.own, c.take, c.old, ?_, ?_,
    WorkMonoG.trans c.wm c.frame.grow hwm, hg _ c.uaV, ?_, c.l1⟩
  · refine TcChain.setCell hu hbt hkb c.tcc ?_ ?_ ?_
    · intro z hz hzb
      simp only [tcBlocks, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact keep _ (.inr (.inl rfl)) (TcChain.headValid c.tcc) (fun hw => h.work_not hw h0S)
          (locS _ h0S) hzb
      · obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        obtain ⟨a1, a2, a3, a4⟩ := c.tco.apart p hp
        obtain ⟨v1, v2⟩ := c.tco.valid p hp
        rcases hz with rfl | rfl
        · exact keep _ (.inl a1) v1 a3 (fun hl => ((c.locs _ hl).2.2 p hp).1 rfl) hzb
        · exact keep _ (.inl a2) v2 a4 (fun hl => ((c.locs _ hl).2.2 p hp).2 rfl) hzb
    · intro e; exact btS (e ▸ h0S)
    · intro p hp; exact chain_cross hpw hp (List.mem_of_getElem? c.own)
  · intro z hz
    obtain ⟨ha, hw, hc⟩ := c.locs z hz
    refine ⟨⟨fun o ho => (hK z hz).perm _ _ (ha.1 o ho), ha.2⟩, fun hw' => ?_, hc⟩
    rcases hwm z hw' with h1 | h1
    · exact hw h1
    · exact h1 (Alloc.valid_of_access ha)
  · refine NodeFrameG.mk' (c.frame.nset.trans (hu.mono fun z hz => ?_))
      fun z hz => hg _ (c.frame.grow _ hz)
    rcases hW z hz with h1 | h1 | h1 | h1 | rfl
    · exact nset_stepG c.frame.grow c.wm (.inl h1)
    · exact nset_stepG c.frame.grow c.wm (.inr (.inl h1))
    · exact nset_stepG c.frame.grow c.wm (.inr (.inr h1))
    · exact .inr (.inl (hLF z h1))
    · exact nset_ownG hpw c.take c.old c.own
  · have hbU : S.bUA ∈ S.blocksG D gl cl := bUA_memG
    exact (Keep.unch hu (keep _ (.inr (.inr rfl)) c.uaV (fun hw => h.work_not hw hbU)
      (locS _ hbU) (fun e => btS (e ▸ hbU)))).perm _ _ c.uaP

/-- `CarryG` across a step that keeps the locals and the target cell. -/
theorem CarryG.chg {n : Nat} {m₀ m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {chain₀ chain : List (block × block)} {level : Nat} {ncw tcw : val}
    {nd bt : block} {L : OLocs}
    (hLS : ∀ z ∈ L.list, z ∉ S.blocksG D gl cl) (hLF : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z)
    (h : SearchAtG D m S gl cl G st pre nsp)
    (c : CarryG D m₀ m S gl cl chain₀ chain level ncw tcw nd bt L)
    {W : block → Prop} (hu : Unch m m' W) (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hwm : WorkMonoG D m m')
    (hW : ∀ z, W z → S.ChgG D gl cl z ∨ ¬ Mem.valid_block m z ∨ IsWorkG D m z)
    (hbt : ∃ vals, ArrayAt m .Mint64 bt 0 vals S.M) :
    CarryG D m₀ m' S gl cl chain₀ chain level ncw tcw nd bt L ∧ ¬ W bt := by
  obtain ⟨btS, btW, btV, -, -⟩ := c.ntc
  have nW : ∀ z, z ∉ S.blocksG D gl cl → Mem.valid_block m z → ¬ IsWorkG D m z → ¬ W z :=
    fun z hz hv hw hW' => by
      rcases hW z hW' with h1 | h1 | h1
      · exact hz h1.1
      · exact h1 hv
      · exact hw h1
  have nL : ∀ z ∈ L.list, ¬ W z := fun z hz =>
    nW z (hLS z hz) (Alloc.valid_of_access (c.locs z hz).1) (c.locs z hz).2.1
  have nB : ¬ W bt := nW bt btS btV btW
  obtain ⟨vals, hv⟩ := hbt
  refine ⟨c.step hLS hLF h hu hg hwm (fun z hz => ?_) (fun z hz => Keep.unch hu (nL z hz))
    ⟨vals, hv.unch hu nB⟩ (Keep.unch hu nB) (by rw [hu.load _ _ _ (nL _ (by simp))]; exact c.ncv)
    (by rw [hu.load _ _ _ (nL _ (by simp))]; exact c.tcv), nB⟩
  rcases hW z hz with h1 | h1 | h1
  · exact .inl h1
  · exact .inr (.inl h1)
  · exact .inr (.inr (.inl h1))

/-- `CarryG` across a step writing blocks the search's own statements write and
the target cell. -/
theorem CarryG.cell {n : Nat} {m₀ m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {chain₀ chain : List (block × block)} {level : Nat} {ncw tcw : val}
    {nd bt : block} {L : OLocs}
    (hLS : ∀ z ∈ L.list, z ∉ S.blocksG D gl cl) (hLF : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z)
    (h : SearchAtG D m S gl cl G st pre nsp)
    (c : CarryG D m₀ m S gl cl chain₀ chain level ncw tcw nd bt L)
    {W : List block} (hu : Unch m m' (fun z => z ∈ W ∨ z = bt))
    (hL : ∀ z ∈ W, z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc)
    (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hbt : ∃ vals, ArrayAt m' .Mint64 bt 0 vals S.M) (hkb : Keep m m' bt) :
    CarryG D m₀ m' S gl cl chain₀ chain level ncw tcw nd bt L ∧ WorkMonoG D m m' := by
  obtain ⟨btS, btW, -, -, -⟩ := c.ntc
  have hwm := h.wmonoB hu hL btS btW hg
  have nL : ∀ z ∈ L.list, ¬ (z ∈ W ∨ z = bt) := fun z hz => by
    rintro (hw | e)
    · exact hLS z hz (h.chgL hL hw).1
    · exact ((c.locs z hz).2.2 _ (List.mem_of_getElem? c.own)).2 e.symm
  refine ⟨c.step hLS hLF h hu hg hwm (fun z hz => ?_) (fun z hz => Keep.unch hu (nL z hz)) hbt hkb
    (by rw [hu.load _ _ _ (nL _ (by simp))]; exact c.ncv)
    (by rw [hu.load _ _ _ (nL _ (by simp))]; exact c.tcv), hwm⟩
  rcases hz with hz | rfl
  · exact .inl (h.chgL hL hz)
  · exact .inr (.inr (.inr (.inr rfl)))

/-- A local is none of the blocks a child may change. -/
theorem CarryG.loc_out {m₀ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {chain₀ chain : List (block × block)} {level : Nat} {ncw tcw : val}
    {nd bt : block} {L : OLocs} (hLS : ∀ z ∈ L.list, z ∉ S.blocksG D gl cl)
    (c : CarryG D m₀ m S gl cl chain₀ chain level ncw tcw nd bt L) {z : block} (hz : z ∈ L.list)
    (k : Nat) : ¬ NSetG D m S gl cl chain k z := by
  obtain ⟨ha, hw, hc⟩ := c.locs z hz
  have hzS := hLS z hz
  rintro (h | h | h | h | ⟨i, p, hp, -, rfl⟩ | ⟨i, p, hp, -, rfl⟩)
  · exact hzS h.1
  · exact h (Alloc.valid_of_access ha)
  · exact hw h
  · exact hzS (h ▸ tcnode0_memG)
  · exact (hc p (List.mem_of_getElem? hp)).1 rfl
  · exact (hc p (List.mem_of_getElem? hp)).2 rfl

/-- The node's target cell is none of the blocks its child may change. -/
theorem CarryG.own_out {m₀ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {chain₀ chain : List (block × block)} {level : Nat} {ncw tcw : val}
    {nd bt : block} {L : OLocs} (c : CarryG D m₀ m S gl cl chain₀ chain level ncw tcw nd bt L) :
    ¬ NSetG D m S gl cl chain (level + 1) bt := by
  obtain ⟨btS, btW, btV, -, -⟩ := c.ntc
  rintro (h | h | h | h | ⟨i, p, hp, -, e⟩ | ⟨i, p, hp, hi, e⟩)
  · exact btS h.1
  · exact h btV
  · exact btW h
  · exact btS (h ▸ tcnode0_memG)
  · exact chain_cross c.tco.pairwise (List.mem_of_getElem? hp) (List.mem_of_getElem? c.own) e.symm
  · have := chain_inj c.tco.pairwise hp c.own (.inr (by simpa using e.symm))
    have := c.l1; omega

/-- `CarryG` across a child, which hands back the list `chain'`. -/
theorem CarryG.child {n : Nat} {m₀ m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {chain₀ chain chain' : List (block × block)} {level : Nat} {ncw tcw : val} {nd bt : block}
    {L : OLocs} (hLS : ∀ z ∈ L.list, z ∉ S.blocksG D gl cl)
    (h : SearchAtG D m S gl cl G st pre nsp)
    (c : CarryG D m₀ m S gl cl chain₀ chain level ncw tcw nd bt L)
    (hF : NodeFrameG D m m' S gl cl chain (level + 1)) (hW : WorkMonoG D m m')
    (hTc : TcChain m' S.M E.tcnode0 chain') (hTo : TcOkG D m' S gl cl chain')
    (htk : chain'.take level = chain.take level)
    (hold : ∀ p ∈ chain', p ∈ chain ∨ (¬ Mem.valid_block m p.1 ∧ ¬ Mem.valid_block m p.2)) :
    CarryG D m₀ m' S gl cl chain₀ chain' level ncw tcw nd bt L := by
  have hpw := c.tco.pairwise
  have hlt : level - 1 < chain.length := by
    have := c.own; rw [List.getElem?_eq_some_iff] at this; exact this.1
  refine ⟨?_, ?_, hTc, hTo, ?_, ?_, ?_, ?_, ?_, WorkMonoG.trans c.wm c.frame.grow hW,
    hF.grow _ c.uaV, ?_, c.l1⟩
  · rw [hF.nset.load _ _ _ (c.loc_out hLS (by simp) _)]; exact c.ncv
  · rw [hF.nset.load _ _ _ (c.loc_out hLS (by simp) _)]; exact c.tcv
  · have := c.l1
    rw [getElem?_take_of htk (by omega)]; exact c.own
  · have := congrArg (List.take (level - 1)) htk
    simp only [List.take_take, Nat.min_eq_left (Nat.sub_le level 1)] at this
    exact this.trans c.take
  · intro p hp
    rcases hold p hp with hp' | ⟨h1, h2⟩
    · exact c.old p hp'
    · exact .inr ⟨fun hv => h1 (c.frame.grow _ hv), fun hv => h2 (c.frame.grow _ hv)⟩
  · intro z hz
    obtain ⟨ha, hw, hc⟩ := c.locs z hz
    have hzv := Alloc.valid_of_access ha
    refine ⟨hF.nset.access _ _ _ _ (c.loc_out hLS hz _) ha, fun hw' => ?_, fun p hp => ?_⟩
    · rcases hW z hw' with h1 | h1
      · exact hw h1
      · exact h1 hzv
    · rcases hold p hp with hp' | ⟨h1, h2⟩
      · exact hc p hp'
      · exact ⟨fun e => h1 (e ▸ hzv), fun e => h2 (e ▸ hzv)⟩
  · exact NodeFrameG.mk' (c.frame.nset.trans (hF.nset.mono fun z hz =>
      nset_childG c.frame.grow c.wm hpw c.take c.old hz)) fun z hz => hF.grow _ (c.frame.grow _ hz)
  · exact NodeFrameG.perm_bUA h c.tco hF c.uaV c.uaP

/-- `CarryG` across a search call (`SFrameG`) whose scratch blocks are old or new. -/
theorem CarryG.sframe {n : Nat} {m₀ m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {chain₀ chain : List (block × block)} {level : Nat} {ncw tcw : val} {nd bt : block}
    {L : OLocs} (hLS : ∀ z ∈ L.list, z ∉ S.blocksG D gl cl)
    (h : SearchAtG D m S gl cl G st pre nsp)
    (c : CarryG D m₀ m S gl cl chain₀ chain level ncw tcw nd bt L)
    (hF : SFrameG D m m' S gl cl) (hW : WorkMonoG D m m') :
    CarryG D m₀ m' S gl cl chain₀ chain level ncw tcw nd bt L := by
  have hout : ∀ z, z ∉ S.blocksG D gl cl → Mem.valid_block m z → ¬ IsWorkG D m z →
      ¬ (S.ChgG D gl cl z ∨ ¬ Mem.valid_block m z ∨ IsWorkG D m z) := fun z h1 h2 h3 => by
    rintro (h | h | h)
    · exact h1 h.1
    · exact h h2
    · exact h3 h
  have hloc : ∀ z ∈ L.list, ¬ (S.ChgG D gl cl z ∨ ¬ Mem.valid_block m z ∨ IsWorkG D m z) :=
    fun z hz => hout z (hLS z hz) (Alloc.valid_of_access (c.locs z hz).1) (c.locs z hz).2.1
  refine ⟨?_, ?_, ?_, TcOkG.mono c.tco hF.2 hW, c.own, c.take, c.old, ?_, ?_,
    WorkMonoG.trans c.wm c.frame.grow hW, hF.2 _ c.uaV, ?_, c.l1⟩
  · rw [hF.1.load _ _ _ (hloc _ (by simp))]; exact c.ncv
  · rw [hF.1.load _ _ _ (hloc _ (by simp))]; exact c.tcv
  · refine TcChain.unch hF.1 c.tcc fun z hz => ?_
    simp only [tcBlocks, List.mem_cons] at hz
    rcases hz with rfl | hz
    · rintro (⟨-, -, h1⟩ | h1 | h1)
      · exact h1 rfl
      · exact h1 (TcChain.headValid c.tcc)
      · exact h.work_not h1 tcnode0_memG
    · obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      obtain ⟨a1, a2, a3, a4⟩ := c.tco.apart p hp
      obtain ⟨v1, v2⟩ := c.tco.valid p hp
      rcases hz with rfl | rfl
      · exact hout _ a1 v1 a3
      · exact hout _ a2 v2 a4
  · intro z hz
    obtain ⟨ha, hw, hc⟩ := c.locs z hz
    refine ⟨hF.1.access _ _ _ _ (hloc z hz) ha, fun hw' => ?_, hc⟩
    rcases hW z hw' with h1 | h1
    · exact hw h1
    · exact h1 (Alloc.valid_of_access ha)
  · exact NodeFrameG.mk' (c.frame.nset.trans (hF.1.mono fun z hz =>
      nset_stepG c.frame.grow c.wm hz)) fun z hz => hF.2 _ (c.frame.grow _ hz)
  · exact SFrameG.perm_bUA h hF c.uaV c.uaP

end Generic

/-- The loop body after its test. -/
abbrev iterBody : statement :=
  .Ssequence breakCall
    (.Ssequence (Set.addElementG dense.id.«nauty:fixedpts» dense.id.«nauty:bit» (Refine.tv dense.id.«tv»))
      (.Ssequence childCall
        (.Ssequence (Set.delElementG dense.id.«nauty:fixedpts» dense.id.«nauty:bit» (Refine.tv dense.id.«tv»))
          (.Ssequence (Set.sk earlyRet)
            (.Ssequence (Set.sk Othernode.prune0)
              (.Ssequence (Set.sk longIf) recCall))))))

end NautyVerified.Proofs.Search

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Set (sk longs)
open Hex.GraphIso Hex.GraphIso.Nauty
open NautyVerified.Spec.SearchInf (SweepOkOff)

variable {xi : ExternalCalls} {n : Nat}

end NautyVerified.Proofs.Search

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Set (sk longs)
open Hex.GraphIso Hex.GraphIso.Nauty
open NautyVerified.Spec.SearchInf (SweepOkOff)

variable {xi : ExternalCalls} {n : Nat}

/-! ### For any dispatch representation and search policy -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

theorem tcParent_succG {chain : List (block × block)} {level : Nat} {nd bt : block}
    (hl : 1 ≤ level) (h : chain[level - 1]? = some (nd, bt)) :
    tcParent (E := E) chain (level + 1) = nd := by
  unfold tcParent
  rw [if_neg (show ¬ level + 1 ≤ 1 by omega), show level + 1 - 2 = level - 1 by omega, h]; rfl

/-- The temporaries `OAtG` reads, when only others change. -/
theorem OAtG.temps {m₀ m : mem} {le le' : temp_env} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {cell : VSet n} {chain₀ chain : List (block × block)} {level nc tc tv1 : Nat} {tvv : Int}
    {nd bt : block} {L : OLocs}
    (h : OAtG D m₀ m le S gl cl G st cell chain₀ chain level nc tc tv1 tvv nd bt L)
    (ht : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.tcnode_this, dense.id.tcell,
      dense.id.tv1, dense.id.tv], PTree.get x le' = PTree.get x le) :
    OAtG D m₀ m le' S gl cl G st cell chain₀ chain level nc tc tv1 tvv nd bt L := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ht
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := ht
  exact ⟨h.search, t1 ▸ h.lab, t2 ▸ h.ptn, t3 ▸ h.lev, t4 ▸ h.this, t5 ▸ h.tcell, t6 ▸ h.tv1,
    t7 ▸ h.tv, h.cellA, h.carry⟩

/-- `OAtG` with the store replaced by one with the same rows (`Same`). -/
theorem OAtG.same {m₀ m : mem} {le : temp_env} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st st' : SearchState n (O.Canon n)}
    {cell : VSet n} {chain₀ chain : List (block × block)} {level nc tc tv1 : Nat} {tvv : Int}
    {nd bt : block} {L : OLocs}
    (h : OAtG D m₀ m le S gl cl G st cell chain₀ chain level nc tc tv1 tvv nd bt L)
    (hs : Same O st st') :
    OAtG D m₀ m le S gl cl G st' cell chain₀ chain level nc tc tv1 tvv nd bt L :=
  { h with search := h.search.same hs }

variable [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]

/-- The child step of `othernode0`'s sweep at `tv`, for the policy `P`. -/
abbrev oChildG (G : O.Gr n) (level nc tc tv1 tv : Nat) (cell : VSet n)
    (st : SearchState n (O.Canon n)) : Exit × VSet n × SearchState n (O.Canon n) :=
  otherChildG G nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv cell st

set_option maxHeartbeats 8000000 in
/-- The loop body after its test, for the policy `P` with link `K` and laws `Lw`. -/
theorem wp_otherIterG (K : PolicyLink O n) {G : O.Gr n} (Lw : NodeLaws K G)
    {Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int}
    {f : function} {Q : Post} {e : env} {le : temp_env} {m₀ m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {st : SearchState n (O.Canon n)}
    {cell : VSet n} {chain₀ chain : List (block × block)} {level nc tc tv1 tv : Nat}
    {nd bt : block} {L : OLocs}
    (hE : OEnvG D e S gl cl m₀ L) (hfr : f.fn_return = tint)
    (hI : OAtG D m₀ m le S gl cl G st cell chain₀ chain level nc tc tv1 tv nd bt L)
    (hsw : Lw.SweepOff level nc tc cell (some tv) st) (hnc : nc < n) (htv1 : tv1 < n)
    (hcb : AutomCb xi S.bUA)
    (hRec : ∀ s ch, Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (nodeSpecG D xi Lw.NodeOk Em false S gl cl G s (level + 1) (nc + 1) ch))
    (hNext : ∀ t le' m' chain', (oChildG G level nc tc tv1 tv cell st).1 = .done →
      Emits t (Em false (level + 1) (nc + 1) (P.child false level tc tv st)) →
      OAtG D m₀ m' le' S gl cl G (oChildG G level nc tc tv1 tv cell st).2.2
        (oChildG G level nc tc tv1 tv cell st).2.1 chain₀ chain' level nc tc tv1 tv nd bt L →
      Q.normal t e le' m')
    (hRet : ∀ t m' tg s chain', (oChildG G level nc tc tv1 tv cell st).1 = .unwind tg s →
      tg < level →
      SearchAtG D m' S gl cl G (oChildG G level nc tc tv1 tv cell st).2.2 false s →
      (s = true → 0 < (oChildG G level nc tc tv1 tv cell st).2.2.autos.size) →
      Emits t (Em false (level + 1) (nc + 1) (P.child false level tc tv st)) →
      CarryG D m₀ m' S gl cl chain₀ chain' level (.Vint (ir nc)) (.Vint (ir tc)) nd bt L →
      match Mem.free_list m' (blocks_of_env ge e) with
      | some m'' => Q.ret t (.Vint (ir tg)) m''
      | none => False) :
    Wp xi ge f iterBody Q e le m := by
  have hS := hI.search
  have c := hI.carry
  have hLS := hE.notS
  have hLF := hE.fresh
  have hl := hS.lit
  have hnl := hS.nlt
  have hl1 := c.l1
  obtain ⟨htvn, htcn, hj⟩ := Lw.off_args hsw
  have hok := Lw.off_child hsw
  have hl2 : level + 1 ≤ n := Lw.level_le hok
  obtain ⟨tw, htw, hrep⟩ := hI.cellA
  obtain ⟨btS, btW, btV, -, -⟩ := c.ntc
  have wr4 : ∀ z ∈ [S.bl, S.bp, S.bA, S.bF],
      z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc := fun z hz => .inr (.inl (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl <;> simp))
  -- breakout
  wp_step
  refine wp_nodeBreakoutG hS hE.ec c.tcv (hE.gl _) hI.lab hI.ptn hI.lev hI.tv (by omega) htcn hj
    (Lw.off_broken hS.inv hsw) ?_
  intro m1 h1 hu1 hg1
  -- ADDELEMENT
  wp_step
  refine wp_fixAddG h1 (hE.glob _ (by decide)) (hE.glob _ (by decide)) hI.tv htvn ?_
  intro m2 h2 hu2 hg2
  have hch : child false level tc tv st =
      { brokenSt level tc tv st with fixedpts := (brokenSt level tc tv st).fixedpts.insert tv } := by
    simp [child, brokenSt]
  have h2' : SearchAtG D m2 S gl cl G (P.child false level tc tv st) false false := by
    refine SearchAtG.same ?_ (K.child_same false level tc tv st)
    rw [hch]; exact h2
  have hu12 : Unch m m2 (· ∈ [S.bl, S.bp, S.bA, S.bF]) :=
    (hu1.mono fun z hz => by rcases hz with h | h | h <;> simp [h]).trans
      (hu2.mono fun z hz => by simp [hz])
  have hg12 : ∀ z, Mem.valid_block m z → Mem.valid_block m2 z := fun z hz => hg2 _ (hg1 _ hz)
  obtain ⟨c2, bt12⟩ := c.chg hLS hLF hS hu12 hg12 (hS.wmono hu12 wr4 hg12)
    (fun z hz => .inl (hS.chgL wr4 hz)) ⟨_, htw⟩
  have htw2 := htw.unch hu12 bt12
  have hlen : level ≤ chain.length := by
    have := c.own; rw [List.getElem?_eq_some_iff] at this; obtain ⟨hlt, -⟩ := this; omega
  -- the child
  wp_step
  refine wp_nodeChildG (hRec _ chain) h2' c2.tcc c2.tco hlen hcb hl2 (by omega) hok c2.uaV c2.uaP
    hE.enc c2.ncv (hE.glob _ (by decide)) hI.lab hI.ptn hI.lev
    (by rw [tcParent_succG hl1 c.own]; exact hI.this) ?_
  intro t m3 h3 hEm hC3 hF3 hW3 _
  obtain ⟨c', hTc3, hTo3, -, htk3, hold3⟩ := hC3
  have c3 := c2.child hLS h2' hF3 hW3 hTc3 hTo3 htk3 hold3
  have htw3 := htw2.unch hF3.nset c2.own_out
  have hnf := Lw.noFuel hok hl2
  generalize hr : hexNodeG false G (level + 1) (nc + 1) (P.child false level tc tv st) = r at h3 ⊢
  have hoc : oChildG G level nc tc tv1 tv cell st = (match r.1 with
      | .fuel => (.fuel, cell, { r.2 with fixedpts := r.2.fixedpts.erase tv })
      | .unwind target short =>
        if target < level then
          (.unwind target short, cell, { r.2 with fixedpts := r.2.fixedpts.erase tv }) else
          let tcell := if short then shortprune cell { r.2 with fixedpts := r.2.fixedpts.erase tv }
            else cell
          let tcell := if tv == tv1 then longprune tcell (r.2.fixedpts.erase tv) r.2.autos
            else tcell
          (.done, tcell, P.recover nautyInf level { r.2 with fixedpts := r.2.fixedpts.erase tv })
      | .done =>
        let tcell := if tv == tv1 then longprune cell (r.2.fixedpts.erase tv) r.2.autos else cell
        (.done, tcell, P.recover nautyInf level { r.2 with fixedpts := r.2.fixedpts.erase tv })) := by
    rw [← hr]
    simp only [oChildG, otherChildG, K.leaveChild_eq, K.shortprune_eq, K.longprune_eq]
    rfl
  -- DELELEMENT
  have hle3 : ∀ x, x ≠ idOf 717 → x ≠ dense.id.rtnlevel →
      PTree.get x (PTree.set dense.id.rtnlevel (.Vint (ir (exitValue (level + 1) r.1).1))
        (PTree.set (idOf 717) (.Vint (ir (exitValue (level + 1) r.1).1)) le)) = PTree.get x le :=
    fun x h1 h2 => by rw [temps_gso _ _ h2, temps_gso _ _ h1]
  have hI3 := hI.temps (le' := PTree.set dense.id.rtnlevel (.Vint (ir (exitValue (level + 1) r.1).1))
        (PTree.set (idOf 717) (.Vint (ir (exitValue (level + 1) r.1).1)) le))
    (fun x hx => hle3 x (by revert x; decide) (by revert x; decide))
  wp_step
  refine wp_fixDelG h3 (hE.glob _ (by decide)) (hE.glob _ (by decide)) hI3.tv htvn ?_
  intro m4 h4 hu4 hg4
  have wrF : ∀ z ∈ [S.bF], z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc :=
    fun z hz => wr4 z (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢; simp [hz])
  have hu4' : Unch m3 m4 (· ∈ [S.bF]) := hu4.mono fun z hz => by simp [hz]
  obtain ⟨c4, bt4⟩ := c3.chg hLS hLF h3 hu4' hg4 (h3.wmono hu4' wrF hg4)
    (fun z hz => .inl (h3.chgL wrF hz)) ⟨_, htw3⟩
  have htw4 := htw3.unch hu4' bt4
  have hcap : 0 < r.2.wsCap := by rw [h3.inv.wsCap]; decide
  have hshort : ∀ tg, r.1 = .unwind tg true → 0 < r.2.autos.size := fun tg he => by
    rw [← hr] at he hcap ⊢; exact Lw.short_autos _ _ _ _ _ hcap he
  -- the steps after `earlyRet`, for a child that does not unwind below `level`
  have tail : ∀ (rv : Int) (sh : Bool) (Q' : Post), (sh = true → 0 < r.2.autos.size) →
      SearchAtG D m4 S gl cl G { r.2 with fixedpts := r.2.fixedpts.erase tv } false sh →
      (∀ m', OAtG D m₀ m' (PTree.set dense.id.rtnlevel (.Vint (ir rv))
          (PTree.set (idOf 717) (.Vint (ir rv)) le)) S gl cl G
          (P.recover nautyInf level { r.2 with fixedpts := r.2.fixedpts.erase tv })
          (if tv == tv1 then longprune (if sh then shortprune cell
              { r.2 with fixedpts := r.2.fixedpts.erase tv } else cell) (r.2.fixedpts.erase tv)
              r.2.autos
            else (if sh then shortprune cell { r.2 with fixedpts := r.2.fixedpts.erase tv }
              else cell))
          chain₀ c' level nc tc tv1 tv nd bt L →
        Q'.normal E0 e (PTree.set dense.id.rtnlevel (.Vint (ir rv))
          (PTree.set (idOf 717) (.Vint (ir rv)) le)) m') →
      Wp xi ge f (.Ssequence (Set.sk Othernode.prune0) (.Ssequence (Set.sk longIf) recCall)) Q' e
        (PTree.set dense.id.rtnlevel (.Vint (ir rv))
          (PTree.set (idOf 717) (.Vint (ir rv)) le)) m4 := by
    intro rv sh Q' hsa h4' hQ'
    have hI3 := hI.temps (le' := PTree.set dense.id.rtnlevel (.Vint (ir rv))
        (PTree.set (idOf 717) (.Vint (ir rv)) le))
      (fun x hx => by
        rw [temps_gso _ _ (by revert x; decide), temps_gso _ _ (by revert x; decide)])
    obtain ⟨-, btW4, -, -, -⟩ := c4.ntc
    wp_step; wp_step; wp_step
    refine wp_prune0G h4' (hE.glob _ (by decide)) (hE.glob _ (by decide)) (hE.glob _ (by decide))
      (hE.glob _ (by decide)) hI3.tcell htw4 hrep btS btW4 hsa ?_
    intro m5 tw5 h5 htw5 hrep5 hu5 hg5 hk5
    have wrN : ∀ z ∈ [E.needshortprune], z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc :=
      fun z hz => .inl (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; simp [hz])
    obtain ⟨c5, -⟩ := c4.cell hLS hLF h4' (hu5.mono fun z hz => by
      rcases hz with rfl | rfl
      · exact .inl (by simp)
      · exact .inr rfl) wrN hg5 ⟨_, htw5⟩ hk5
    obtain ⟨-, btW5, -, -, -⟩ := c5.ntc
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine wp_nodeLongG h5 (hE.gl _) hI3.tcell htw5 hrep5 btS btW5 hI3.tv hI3.tv1 htvn htv1 ?_
    intro m6 tw6 h6 htw6 hrep6 hu6 hg6 hk6
    obtain ⟨c6, -⟩ := c5.cell (W := []) hLS hLF h5 (hu6.mono fun z hz => .inr hz)
      (fun z hz => by simp at hz) hg6 ⟨_, htw6⟩ hk6
    obtain ⟨-, btW6, btV6, -, -⟩ := c6.ntc
    simp only [seqPost, Post.after, E0_append]
    refine wp_nodeRecoverG h6 (hE.glob _ (by decide)) hI3.ptn hI3.lev hl1 (by omega) ?_
    intro m7 h7 hF7 hW7
    have c7 := c6.sframe hLS h6 hF7 hW7
    have htw7 := htw6.unch hF7.1 (by
      rintro (h | h | h)
      · exact btS h.1
      · exact h btV6
      · exact btW6 h)
    exact hQ' m7 (OAtG.same ⟨h7, hI3.lab, hI3.ptn, hI3.lev, hI3.this, hI3.tcell, hI3.tv1, hI3.tv,
      ⟨tw6, htw7, hrep6⟩, c7⟩ (K.recover_same nautyInf level _))
  have hrl : PTree.get dense.id.rtnlevel (PTree.set dense.id.rtnlevel
      (.Vint (ir (exitValue (level + 1) r.1).1)) (PTree.set (idOf 717)
        (.Vint (ir (exitValue (level + 1) r.1).1)) le)) =
      some (.Vint (ir (exitValue (level + 1) r.1).1)) :=
    temps_gss _ _ _
  have hlev3 := hI3.lev
  wp_step
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hrl, hlev3, Refine.tv, typeof, cop]
  rcases hx : r.1 with _ | ⟨tg, sh⟩ | _
  · -- the child returned normally
    simp only [exitValue]
    simp only [ir_lt (a := ((level + 1 : Nat) : Int)) (b := level) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩, show ¬ ((level + 1 : Nat) : Int) < level by omega, decide_false,
      Bool.false_eq_true, ite_false]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    rw [hx] at h4
    simp only [exitValue] at h4
    refine tail _ false _ (fun h => absurd h (by decide)) h4 fun m' hO => ?_
    simp only [hx, exitValue, Bool.false_eq_true, ite_false, append_E0] at hO ⊢
    have hd' : (oChildG G level nc tc tv1 tv cell st).1 = .done := by rw [hoc, hx]
    refine hNext t _ m' c' hd' hEm ?_
    rw [hoc, hx]
    exact hO
  · -- an unwind
    have htgl : tg < level + 1 := by
      rw [← hr] at hx; exact Lw.unwind_lt hok _ tg sh hx
    simp only [exitValue]
    simp only [ir_lt (a := (tg : Int)) (b := level) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    rw [hx] at h4
    simp only [exitValue] at h4
    by_cases htg : tg < level
    · simp only [show (tg : Int) < level by omega, decide_true, ite_true]
      wp_step; wp_step
      apply wp_return_some_eval
      simp only [Exec.evalExpr, hrl, Refine.tv, typeof, hfr, cop, hx, exitValue]
      have hoc' : oChildG G level nc tc tv1 tv cell st =
          (.unwind tg sh, cell, { r.2 with fixedpts := r.2.fixedpts.erase tv }) := by
        rw [hoc, hx]; simp [htg]
      have := hRet t m4 tg sh c' (by rw [hoc']) htg (by rw [hoc']; exact h4)
        (by rw [hoc']; exact hshort tg ∘ fun h => h ▸ hx) hEm c4
      revert this
      rcases Mem.free_list m4 (blocks_of_env ge e) with _ | m'' <;> simp [Post.after]
    · simp only [show ¬ (tg : Int) < level by omega, decide_false, Bool.false_eq_true, ite_false]
      apply wp_skip
      simp only [seqPost, Post.after, E0_append]
      refine tail _ sh _ (fun h => hshort tg (h ▸ hx)) h4 fun m' hO => ?_
      simp only [append_E0]
      have hoc' : oChildG G level nc tc tv1 tv cell st =
          (.done, (if tv == tv1 then longprune (if sh then shortprune cell
              { r.2 with fixedpts := r.2.fixedpts.erase tv } else cell) (r.2.fixedpts.erase tv)
              r.2.autos
            else (if sh then shortprune cell { r.2 with fixedpts := r.2.fixedpts.erase tv }
              else cell)),
            P.recover nautyInf level { r.2 with fixedpts := r.2.fixedpts.erase tv }) := by
        rw [hoc, hx]; simp [htg]
      refine hNext t _ m' c' (by rw [hoc']) hEm ?_
      rw [hoc']
      simp only [hx] at hO
      exact hO
  · rw [← hr] at hx; exact absurd hx hnf

end Generic

end NautyVerified.Proofs.Search
