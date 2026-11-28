import NautyVerified.Proofs.Search.Node.OtherFrame
import NautyVerified.Proofs.Search.Node.LoopShape
import NautyVerified.Proofs.Search.Node.OkOff
import NautyVerified.Proofs.Search.Node.Prune
import NautyVerified.Proofs.Search.Node.ProcFacts
import NautyVerified.Spec.NodeBound
import NautyVerified.Proofs.Search.Node.UaFrame
import NautyVerified.Proofs.Search.Valid

/-!
# One child of `othernode0`'s sweep

`OAt`: the state of `othernode0` at the head of its child loop, for the
cursor `tv`: `SearchAt` for the sweep's state, the temporaries, the locals'
values, the target cell, the target-cell list (whose entry `level - 1` is this
node's), and the frame since entry.

`wp_otherIter`: the loop body after its test, from `OAt` with the cursor at
a vertex, is HexGraphIso's `otherChild`. A child that continues the sweep
ends in `OAt` for the pruned cell and the recovered state; one that unwinds
below `level` returns its target.
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

/-- The locals' bindings and freshness, and the globals' absence from `e`. -/
structure OEnv (e : env) (S : SLoc) (m₀ : mem) (L : OLocs) : Prop where
  enc : PTree.get dense.id.numcells e = some (L.bnc, tint)
  ek : PTree.get dense.id.refcode e = some (L.bk, tint)
  ez : PTree.get dense.id.tcellsize e = some (L.bz, tint)
  ec : PTree.get dense.id.tc e = some (L.bc, tint)
  eq : PTree.get dense.id.qinvar e = some (L.bq, tint)
  glob : ∀ x, x ∉ [dense.id.numcells, dense.id.refcode, dense.id.tcellsize, dense.id.tc,
    dense.id.qinvar] → PTree.get x e = none
  fresh : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z
  nodup : L.list.Pairwise (· ≠ ·)
  notS : ∀ z ∈ L.list, z ∉ S.blocks

/-- What `othernode0` carries through its child loop besides `SearchAt`, the
temporaries and the target cell's contents: the values of `numcells` and `tc`,
the target-cell list (entry `level - 1` is this node's), the locals' blocks,
the frame since entry `m₀`, and the callback's block. -/
structure Carry (m₀ m : mem) (S : SLoc) (chain₀ chain : List (block × block)) (level nc tc : Nat)
    (nd bt : block) (L : OLocs) : Prop where
  ncv : Mem.load .Mint32 m L.bnc (zOfInt 0) = some (.Vint (ir nc))
  tcv : Mem.load .Mint32 m L.bc (zOfInt 0) = some (.Vint (ir tc))
  tcc : TcChain m S.M Block.tcnode0 chain
  tco : TcOk m S chain
  own : chain[level - 1]? = some (nd, bt)
  take : chain.take (level - 1) = chain₀.take (level - 1)
  old : ∀ p ∈ chain, p ∈ chain₀ ∨ (¬ Mem.valid_block m₀ p.1 ∧ ¬ Mem.valid_block m₀ p.2)
  locs : ∀ z ∈ L.list, Mem.valid_access m .Mint32 z (zOfInt 0) .Freeable ∧ ¬ IsWork m z ∧
    ∀ p ∈ chain, p.1 ≠ z ∧ p.2 ≠ z
  frame : NodeFrame m₀ m S chain₀ level
  wm : WorkMono m₀ m
  uaV : Mem.valid_block m S.bUA
  uaP : Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty
  l1 : 1 ≤ level

/-- `othernode0` at the head of its child loop, the cursor holding `tvv`. -/
structure OAt (m₀ m : mem) (le : temp_env) (S : SLoc) (ctx : Ctx n) (st : Search n)
    (cell : VSet n) (chain₀ chain : List (block × block)) (level nc tc tv1 : Nat) (tvv : Int)
    (nd bt : block) (L : OLocs) : Prop where
  search : SearchAt m S ctx st false false
  lab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs)
  ptn : PTree.get dense.id.ptn le = some (.Vptr S.bp S.pofs)
  lev : PTree.get dense.id.level le = some (.Vint (ir level))
  this : PTree.get dense.id.tcnode_this le = some (.Vptr nd Ptrofs.zero)
  tcell : PTree.get dense.id.tcell le = some (.Vptr bt Ptrofs.zero)
  tv1 : PTree.get dense.id.tv1 le = some (.Vint (ir tv1))
  tv : PTree.get dense.id.tv le = some (.Vint (ir tvv))
  cellA : ∃ tw, ArrayAt m .Mint64 bt 0 (longs tw) S.M ∧ SetRep (fun w => bv64 (tw w)) S.M cell
  carry : Carry m₀ m S chain₀ chain level nc tc nd bt L

theorem TcChain.headValid {m : mem} {M : Nat} {prev : block} :
    ∀ {chain : List (block × block)}, TcChain m M prev chain → Mem.valid_block m prev
  | [], h => FieldAt.valid h
  | _ :: _, h => FieldAt.valid h.1

theorem SLoc.vars_blocks {S : SLoc} {z : block} (h : z ∈ S.vars) : z ∈ S.blocks := by
  rw [SLoc.blocks_split]; exact List.mem_append_left _ h

theorem workG_globs : ∀ z ∈ workG, z ∈ globs := by decide

theorem tcnode0_globs : Block.tcnode0 ∈ globs := by decide

theorem Carry.ntc {m₀ m : mem} {S : SLoc} {chain₀ chain : List (block × block)} {level nc tc : Nat}
    {nd bt : block} {L : OLocs} (c : Carry m₀ m S chain₀ chain level nc tc nd bt L) :
    bt ∉ S.blocks ∧ ¬ IsWork m bt ∧ Mem.valid_block m bt ∧ nd ∉ S.blocks ∧ Mem.valid_block m nd :=
  have hp := List.mem_of_getElem? c.own
  ⟨(c.tco.apart _ hp).2.1, (c.tco.apart _ hp).2.2.2, (c.tco.valid _ hp).2, (c.tco.apart _ hp).1,
    (c.tco.valid _ hp).1⟩

/-- `Carry` across a step that changes blocks of `S` other than the callback's,
`tcnode0` and the work arrays' globals, and the target cell. -/
theorem Carry.unch {m₀ m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    {chain₀ chain : List (block × block)} {level nc tc : Nat} {nd bt : block} {L : OLocs}
    (hLS : ∀ z ∈ L.list, z ∉ S.blocks) (h : SearchAt m S ctx st pre nsp)
    (c : Carry m₀ m S chain₀ chain level nc tc nd bt L)
    {W : block → Prop} (hu : Unch m m' W) (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hW : ∀ z, W z → (z ∈ S.blocks ∧ z ≠ S.bUA ∧ z ≠ Block.tcnode0 ∧ z ∉ workG) ∨ z = bt)
    (hbt : ∃ vals, ArrayAt m' .Mint64 bt 0 vals S.M) :
    Carry m₀ m' S chain₀ chain level nc tc nd bt L ∧ WorkMono m m' := by
  obtain ⟨btS, btW, btV, -, -⟩ := c.ntc
  have notW : ∀ z, z ∉ S.blocks → z ≠ bt → ¬ W z := fun z hz hb hw => by
    rcases hW z hw with ⟨h1, -⟩ | h1
    · exact hz h1
    · exact hb h1
  have hpw := c.tco.pairwise
  have locbt : ∀ z ∈ L.list, z ≠ bt := fun z hz e =>
    ((c.locs z hz).2.2 _ (List.mem_of_getElem? c.own)).2 e.symm
  have wm : WorkMono m m' := WorkMono.of_unch h.work hu
    (fun z hz hw => by
      rcases hW z hw with ⟨-, -, -, h1⟩ | h1
      · exact h1 hz
      · subst h1; exact btS (by rw [SLoc.blocks_split]; exact List.mem_append_right _ (workG_globs _ hz)))
    (fun z hz hw => by
      rcases hW z hw with ⟨h1, -⟩ | h1
      · exact h.work_not hz h1
      · exact btW (h1 ▸ hz))
  have hbn : ∀ z ∈ L.list, ¬ W z := fun z hz => notW z (hLS z hz) (locbt z hz)
  refine ⟨⟨?_, ?_, ?_, TcOk.mono c.tco hg wm, c.own, c.take, c.old, ?_, ?_,
    WorkMono.trans c.wm c.frame.grow wm, hg _ c.uaV, ?_, c.l1⟩, wm⟩
  · rw [hu.load _ _ _ (hbn _ (by simp))]; exact c.ncv
  · rw [hu.load _ _ _ (hbn _ (by simp))]; exact c.tcv
  · refine TcChain.setCell hu hbt c.tcc ?_ ?_ ?_
    · intro z hz hzb
      simp only [tcBlocks, List.mem_cons] at hz
      rcases hz with rfl | hz
      · intro hw
        rcases hW _ hw with ⟨-, -, h1, -⟩ | h1
        · exact h1 rfl
        · exact hzb h1
      · obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl
        · exact notW _ (c.tco.apart p hp).1 hzb
        · exact notW _ (c.tco.apart p hp).2.1 hzb
    · intro e; exact btS (e ▸ by rw [SLoc.blocks_split]; exact List.mem_append_right _ tcnode0_globs)
    · intro p hp; exact chain_cross hpw hp (List.mem_of_getElem? c.own)
  · intro z hz
    obtain ⟨ha, hw, hc⟩ := c.locs z hz
    refine ⟨hu.access _ _ _ _ (hbn z hz) ha, fun hw' => ?_, hc⟩
    rcases wm z hw' with h1 | h1
    · exact hw h1
    · exact h1 (Alloc.valid_of_access ha)
  · refine NodeFrame.mk' (c.frame.nset.trans (hu.mono fun z hz => ?_)) fun z hz => hg _ (c.frame.grow _ hz)
    rcases hW z hz with ⟨h1, h2, h3, -⟩ | rfl
    · exact nset_step (S := S) (chain₀ := chain₀) (level := level) c.frame.grow c.wm
        (.inl ⟨h1, h2, h3⟩)
    · exact nset_own hpw c.take c.old c.own
  · have hb : ¬ W S.bUA := fun hw => by
      rcases hW _ hw with ⟨-, h1, -⟩ | h1
      · exact h1 rfl
      · exact btS (h1 ▸ by simp [SLoc.blocks])
    exact (Keep.unch hu hb).perm _ _ c.uaP

/-- A local is none of the blocks a child may change. -/
theorem Carry.loc_out {m₀ m : mem} {S : SLoc} {chain₀ chain : List (block × block)} {level nc tc : Nat}
    {nd bt : block} {L : OLocs} (hLS : ∀ z ∈ L.list, z ∉ S.blocks)
    (c : Carry m₀ m S chain₀ chain level nc tc nd bt L) {z : block} (hz : z ∈ L.list) (k : Nat) :
    ¬ NSet m S chain k z := by
  obtain ⟨ha, hw, hc⟩ := c.locs z hz
  have hzS := hLS z hz
  rintro (h | h | h | h | ⟨i, p, hp, -, rfl⟩ | ⟨i, p, hp, -, rfl⟩)
  · exact hzS h.1
  · exact h (Alloc.valid_of_access ha)
  · exact hw h
  · exact hzS (h ▸ by simp [SLoc.blocks])
  · exact (hc p (List.mem_of_getElem? hp)).1 rfl
  · exact (hc p (List.mem_of_getElem? hp)).2 rfl

/-- The node's target cell is none of the blocks its child may change. -/
theorem Carry.own_out {m₀ m : mem} {S : SLoc} {chain₀ chain : List (block × block)} {level nc tc : Nat}
    {nd bt : block} {L : OLocs} (c : Carry m₀ m S chain₀ chain level nc tc nd bt L) :
    ¬ NSet m S chain (level + 1) bt := by
  obtain ⟨btS, btW, btV, -, -⟩ := c.ntc
  rintro (h | h | h | h | ⟨i, p, hp, -, e⟩ | ⟨i, p, hp, hi, e⟩)
  · exact btS h.1
  · exact h btV
  · exact btW h
  · exact btS (h ▸ by simp [SLoc.blocks])
  · exact chain_cross c.tco.pairwise (List.mem_of_getElem? hp) (List.mem_of_getElem? c.own) e.symm
  · have := chain_inj c.tco.pairwise hp c.own (.inr (by simpa using e.symm))
    have := c.l1; omega

/-- `Carry` across a child, which hands back the list `chain'`. -/
theorem Carry.child {m₀ m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    {chain₀ chain chain' : List (block × block)} {level nc tc : Nat} {nd bt : block} {L : OLocs}
    (hLS : ∀ z ∈ L.list, z ∉ S.blocks) (h : SearchAt m S ctx st pre nsp)
    (c : Carry m₀ m S chain₀ chain level nc tc nd bt L)
    (hF : NodeFrame m m' S chain (level + 1)) (hW : WorkMono m m')
    (hTc : TcChain m' S.M Block.tcnode0 chain') (hTo : TcOk m' S chain')
    (htk : chain'.take level = chain.take level)
    (hold : ∀ p ∈ chain', p ∈ chain ∨ (¬ Mem.valid_block m p.1 ∧ ¬ Mem.valid_block m p.2)) :
    Carry m₀ m' S chain₀ chain' level nc tc nd bt L := by
  have hpw := c.tco.pairwise
  have hlt : level - 1 < chain.length := by
    have := c.own; rw [List.getElem?_eq_some_iff] at this; exact this.1
  refine ⟨?_, ?_, hTc, hTo, ?_, ?_, ?_, ?_, ?_, WorkMono.trans c.wm c.frame.grow hW,
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
  · exact NodeFrame.mk' (c.frame.nset.trans (hF.nset.mono fun z hz =>
      nset_child c.frame.grow c.wm hpw c.take c.old hz)) fun z hz => hF.grow _ (c.frame.grow _ hz)
  · exact NodeFrame.perm_bUA h c.tco hF c.uaV c.uaP

/-- `Carry` across a search call (`SFrame`) whose work blocks are old or new. -/
theorem Carry.sframe {m₀ m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    {chain₀ chain : List (block × block)} {level nc tc : Nat} {nd bt : block} {L : OLocs}
    (hLS : ∀ z ∈ L.list, z ∉ S.blocks) (h : SearchAt m S ctx st pre nsp)
    (c : Carry m₀ m S chain₀ chain level nc tc nd bt L) (hF : SFrame m m' S) (hW : WorkMono m m') :
    Carry m₀ m' S chain₀ chain level nc tc nd bt L := by
  have hout : ∀ z, z ∉ S.blocks → Mem.valid_block m z → ¬ IsWork m z →
      ¬ (S.Chg z ∨ ¬ Mem.valid_block m z ∨ IsWork m z) := fun z h1 h2 h3 => by
    rintro (h | h | h)
    · exact h1 h.1
    · exact h h2
    · exact h3 h
  have hloc : ∀ z ∈ L.list, ¬ (S.Chg z ∨ ¬ Mem.valid_block m z ∨ IsWork m z) := fun z hz =>
    hout z (hLS z hz) (Alloc.valid_of_access (c.locs z hz).1) (c.locs z hz).2.1
  refine ⟨?_, ?_, ?_, TcOk.mono c.tco hF.2 hW, c.own, c.take, c.old, ?_, ?_,
    WorkMono.trans c.wm c.frame.grow hW, hF.2 _ c.uaV, ?_, c.l1⟩
  · rw [hF.1.load _ _ _ (hloc _ (by simp))]; exact c.ncv
  · rw [hF.1.load _ _ _ (hloc _ (by simp))]; exact c.tcv
  · refine TcChain.unch hF.1 c.tcc fun z hz => ?_
    simp only [tcBlocks, List.mem_cons] at hz
    rcases hz with rfl | hz
    · rintro (⟨-, -, h1⟩ | h1 | h1)
      · exact h1 rfl
      · exact h1 (TcChain.headValid c.tcc)
      · exact h.work_not h1 (by simp [SLoc.blocks])
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
  · exact NodeFrame.mk' (c.frame.nset.trans (hF.1.mono fun z hz =>
      nset_step c.frame.grow c.wm hz)) fun z hz => hF.2 _ (c.frame.grow _ hz)
  · exact SFrame.perm_bUA h hF c.uaV c.uaP

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

theorem OEnv.gl {e : env} {S : SLoc} {m₀ : mem} {L : OLocs} (hE : OEnv e S m₀ L) (l : List ident)
    (h : ∀ x ∈ l, x ∉ [dense.id.numcells, dense.id.refcode, dense.id.tcellsize, dense.id.tc,
      dense.id.qinvar] := by decide) : ∀ x ∈ l, PTree.get x e = none :=
  fun x hx => hE.glob x (h x hx)

theorem tcParent_succ {chain : List (block × block)} {level : Nat} {nd bt : block} (hl : 1 ≤ level)
    (h : chain[level - 1]? = some (nd, bt)) : tcParent chain (level + 1) = nd := by
  unfold tcParent
  rw [ite_cond_eq_false _ _ (eq_false (show ¬ level + 1 ≤ 1 by omega)), show level + 1 - 2 = level - 1 by omega, h]; rfl

/-- The temporaries `OAt` reads, when only others change. -/
theorem OAt.temps {m₀ m : mem} {le le' : temp_env} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {cell : VSet n} {chain₀ chain : List (block × block)} {level nc tc tv1 : Nat} {tvv : Int}
    {nd bt : block} {L : OLocs} (h : OAt m₀ m le S ctx st cell chain₀ chain level nc tc tv1 tvv nd bt L)
    (ht : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.tcnode_this, dense.id.tcell,
      dense.id.tv1, dense.id.tv], PTree.get x le' = PTree.get x le) :
    OAt m₀ m le' S ctx st cell chain₀ chain level nc tc tv1 tvv nd bt L := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ht
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := ht
  exact ⟨h.search, t1 ▸ h.lab, t2 ▸ h.ptn, t3 ▸ h.lev, t4 ▸ h.this, t5 ▸ h.tcell, t6 ▸ h.tv1,
    t7 ▸ h.tv, h.cellA, h.carry⟩

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

/-- The child step of `othernode0`'s sweep at `tv`. -/
abbrev oChild {k : Nat} (G : Colored n k) (level nc tc tv1 tv : Nat) (cell : VSet n) (st : Search n) :
    Exit × VSet n × Search n :=
  otherChild ⟨rowsOf G⟩ nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv cell st

set_option maxHeartbeats 8000000 in
theorem wp_otherIter {k : Nat} {G : Colored n k} {Em : Bool → Nat → Nat → Search n → List Int}
    {f : function} {Q : Post} {e : env} {le : temp_env} {m₀ m : mem} {S : SLoc} {st : Search n}
    {cell : VSet n} {chain₀ chain : List (block × block)} {level nc tc tv1 tv : Nat}
    {nd bt : block} {L : OLocs}
    (hE : OEnv e S m₀ L) (hfr : f.fn_return = tint)
    (hI : OAt m₀ m le S ⟨rowsOf G⟩ st cell chain₀ chain level nc tc tv1 tv nd bt L)
    (hsw : SweepOkOff G level nc tc cell (some tv) st) (hnc : nc < n) (htv1 : tv1 < n)
    (hcb : AutomCb xi S.bUA)
    (hRec : ∀ s ch, Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (othernodeSpecG xi G Em S s (level + 1) (nc + 1) ch))
    (hNext : ∀ t le' m' chain', (oChild G level nc tc tv1 tv cell st).1 = .done →
      Emits t (Em false (level + 1) (nc + 1) (child false level tc tv st)) →
      OAt m₀ m' le' S ⟨rowsOf G⟩ (oChild G level nc tc tv1 tv cell st).2.2
        (oChild G level nc tc tv1 tv cell st).2.1 chain₀ chain' level nc tc tv1 tv nd bt L →
      Q.normal t e le' m')
    (hRet : ∀ t m' tg s chain', (oChild G level nc tc tv1 tv cell st).1 = .unwind tg s → tg < level →
      SearchAt m' S ⟨rowsOf G⟩ (oChild G level nc tc tv1 tv cell st).2.2 false s →
      (s = true → 0 < (oChild G level nc tc tv1 tv cell st).2.2.autos.size) →
      Emits t (Em false (level + 1) (nc + 1) (child false level tc tv st)) →
      Carry m₀ m' S chain₀ chain' level nc tc nd bt L →
      match Mem.free_list m' (blocks_of_env ge e) with
      | some m'' => Q.ret t (.Vint (ir tg)) m''
      | none => False) :
    Wp xi ge f iterBody Q e le m := by
  have hS := hI.search
  have c := hI.carry
  have hLS := hE.notS
  have hd := hS.distinct
  have hn0 := hS.n0
  have hnl := hS.nlt
  have hl1 := c.l1
  have hnI : n + 2 < SearchInf.nautyInfinity := by show n + 2 < 2000000002; omega
  obtain ⟨htvn, htcn, hj⟩ := sweepOkOff_breakArgs hsw
  have hok := SearchInf.sweepOkOff_child hn0 hsw ⟨rowsOf G⟩ 100
  have hl2 : level + 1 ≤ n := by
    obtain ⟨⟨_, _, _, _, hso, _⟩, _⟩ := hok
    exact SearchInf.level_le_of_ok hso
  obtain ⟨tw, htw, hrep⟩ := hI.cellA
  obtain ⟨btS, btW, btV, -, -⟩ := c.ntc
  have vS : ∀ z, z = S.bl ∨ z = S.bp ∨ z = S.bA ∨ z = S.bF →
      (z ∈ S.blocks ∧ z ≠ S.bUA ∧ z ≠ Block.tcnode0 ∧ z ∉ workG) ∨ z = bt := by
    rintro z (rfl | rfl | rfl | rfl)
    all_goals exact .inl ⟨by simp [SLoc.blocks], by sep_ne hd, by sep_ne hd, by
      simp only [workG, List.mem_cons, List.mem_nil_iff, or_false, not_or]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sep_ne hd⟩
  -- breakout
  wp_step
  refine wp_nodeBreakout hS hE.ec c.tcv (hE.gl _) hI.lab hI.ptn hI.lev hI.tv (by omega) htcn hj
    (SInv.brokenSt hn0 hnI ⟨rowsOf G⟩ 100 hS.inv hsw.1) ?_
  intro m1 h1 hu1 hg1
  -- ADDELEMENT
  wp_step
  refine wp_fixAdd h1 (hE.glob _ (by decide)) (hE.glob _ (by decide)) hI.tv htvn ?_
  intro m2 h2 hu2 hg2
  have h2' : SearchAt m2 S ⟨rowsOf G⟩ (child false level tc tv st) false false := by
    rw [child_false_eq]; exact h2
  have hu12 : Unch m m2 (fun z => z = S.bl ∨ z = S.bp ∨ z = S.bA ∨ z = S.bF) :=
    (hu1.mono fun z hz => by rcases hz with h | h | h <;> simp [h]).trans
      (hu2.mono fun z hz => by simp [hz])
  have bt12 : ¬ (bt = S.bl ∨ bt = S.bp ∨ bt = S.bA ∨ bt = S.bF) := fun hz => by
    rcases hz with h | h | h | h <;> exact btS (h ▸ by simp [SLoc.blocks])
  have htw2 := htw.unch hu12 bt12
  obtain ⟨c2, -⟩ := c.unch hLS hS hu12 (fun z hz => hg2 _ (hg1 _ hz)) (fun z hz => vS z hz) ⟨_, htw2⟩
  have hlen : level ≤ chain.length := by
    have := c.own; rw [List.getElem?_eq_some_iff] at this; obtain ⟨hlt, -⟩ := this; omega
  -- the child
  wp_step
  refine wp_nodeChild (hRec _ chain) h2' c2.tcc c2.tco hlen hcb hl2 (by omega) hok c2.uaV c2.uaP
    hE.enc c2.ncv (hE.glob _ (by decide)) hI.lab hI.ptn hI.lev
    (by rw [tcParent_succ hl1 c.own]; exact hI.this) ?_
  intro t m3 h3 hEm hC3 hF3 hW3 _
  obtain ⟨c', hTc3, hTo3, -, htk3, hold3⟩ := hC3
  have c3 := c2.child hLS h2' hF3 hW3 hTc3 hTo3 htk3 hold3
  have htw3 := htw2.unch hF3.nset c2.own_out
  have hnf := SearchInf.nodeOk_noFuel hn0 hnI hok ⟨rowsOf G⟩ 100 hl2
  generalize hr : hexNode false ⟨rowsOf G⟩ (level + 1) (nc + 1) (child false level tc tv st) = r at h3 ⊢
  have hoc : oChild G level nc tc tv1 tv cell st = (match r.1 with
      | .fuel => (.fuel, cell, { r.2 with fixedpts := r.2.fixedpts.erase tv })
      | .unwind target short =>
        if target < level then (.unwind target short, cell, { r.2 with fixedpts := r.2.fixedpts.erase tv }) else
          let tcell := if short then shortprune cell { r.2 with fixedpts := r.2.fixedpts.erase tv } else cell
          let tcell := if tv == tv1 then longprune tcell (r.2.fixedpts.erase tv) r.2.autos else tcell
          (.done, tcell, Hex.GraphIso.Nauty.recover nautyInf level { r.2 with fixedpts := r.2.fixedpts.erase tv })
      | .done =>
        let tcell := if tv == tv1 then longprune cell (r.2.fixedpts.erase tv) r.2.autos else cell
        (.done, tcell, Hex.GraphIso.Nauty.recover nautyInf level { r.2 with fixedpts := r.2.fixedpts.erase tv })) := by
    rw [← hr]; rfl
  -- DELELEMENT
  have hle3 : ∀ x, x ≠ idOf 717 → x ≠ dense.id.rtnlevel →
      PTree.get x (PTree.set dense.id.rtnlevel (.Vint (ir (exitValue (level + 1) r.1).1))
        (PTree.set (idOf 717) (.Vint (ir (exitValue (level + 1) r.1).1)) le)) = PTree.get x le :=
    fun x h1 h2 => by rw [temps_gso _ _ h2, temps_gso _ _ h1]
  have hI3 := hI.temps (le' := PTree.set dense.id.rtnlevel (.Vint (ir (exitValue (level + 1) r.1).1))
        (PTree.set (idOf 717) (.Vint (ir (exitValue (level + 1) r.1).1)) le))
    (fun x hx => hle3 x (by revert x; decide) (by revert x; decide))
  wp_step
  refine wp_fixDel h3 (hE.glob _ (by decide)) (hE.glob _ (by decide)) hI3.tv htvn ?_
  intro m4 h4 hu4 hg4
  have bt4 : ¬ bt = S.bF := fun h => btS (h ▸ by simp [SLoc.blocks])
  have htw4 := htw3.unch hu4 bt4
  obtain ⟨c4, -⟩ := c3.unch hLS h3 hu4 hg4
    (fun z hz => vS z (.inr (.inr (.inr hz)))) ⟨_, htw4⟩
  have hcap : 0 < r.2.wsCap := by rw [h3.inv.wsCap]; decide
  have hshort : ∀ tg, r.1 = .unwind tg true → 0 < r.2.autos.size := fun tg he => by
    rw [← hr] at he hcap ⊢; exact node_short_autos _ _ _ _ _ _ _ _ hcap he
  -- the steps after `earlyRet`, for a child that does not unwind below `level`
  have tail : ∀ (rv : Int) (sh : Bool) (Q' : Post), (sh = true → 0 < r.2.autos.size) →
      SearchAt m4 S ⟨rowsOf G⟩ { r.2 with fixedpts := r.2.fixedpts.erase tv } false sh →
      (∀ m', OAt m₀ m' (PTree.set dense.id.rtnlevel (.Vint (ir rv))
          (PTree.set (idOf 717) (.Vint (ir rv)) le)) S ⟨rowsOf G⟩
          (Hex.GraphIso.Nauty.recover nautyInf level { r.2 with fixedpts := r.2.fixedpts.erase tv })
          (if tv == tv1 then longprune (if sh then shortprune cell
              { r.2 with fixedpts := r.2.fixedpts.erase tv } else cell) (r.2.fixedpts.erase tv) r.2.autos
            else (if sh then shortprune cell { r.2 with fixedpts := r.2.fixedpts.erase tv } else cell))
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
    refine wp_prune0 h4' (hE.glob _ (by decide)) (hE.glob _ (by decide)) (hE.glob _ (by decide))
      (hE.glob _ (by decide)) hI3.tcell htw4 hrep btS btW4 hsa ?_
    intro m5 tw5 h5 htw5 hrep5 hu5 hg5
    obtain ⟨c5, -⟩ := c4.unch hLS h4' hu5 hg5 (fun z hz => by
      rcases hz with rfl | rfl
      · exact .inl ⟨by simp [SLoc.blocks], by sep_ne hd, by decide, by decide⟩
      · exact .inr rfl) ⟨_, htw5⟩
    obtain ⟨-, btW5, -, -, -⟩ := c5.ntc
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine wp_nodeLong h5 (hE.gl _) hI3.tcell htw5 hrep5 btS btW5 hI3.tv hI3.tv1 htvn htv1 ?_
    intro m6 tw6 h6 htw6 hrep6 hu6 hg6
    obtain ⟨c6, -⟩ := c5.unch hLS h5 hu6 hg6 (fun z hz => .inr hz) ⟨_, htw6⟩
    obtain ⟨-, btW6, btV6, -, -⟩ := c6.ntc
    simp only [seqPost, Post.after, E0_append]
    refine wp_nodeRecover h6 (hE.glob _ (by decide)) hI3.ptn hI3.lev hl1 (by omega) ?_
    intro m7 h7 hF7 hW7
    have c7 := c6.sframe hLS h6 hF7 hW7
    have htw7 := htw6.unch hF7.1 (by
      rintro (h | h | h)
      · exact btS h.1
      · exact h btV6
      · exact btW6 h)
    exact hQ' m7 ⟨h7, hI3.lab, hI3.ptn, hI3.lev, hI3.this, hI3.tcell, hI3.tv1, hI3.tv,
      ⟨tw6, htw7, hrep6⟩, c7⟩
  have hrl : PTree.get dense.id.rtnlevel (PTree.set dense.id.rtnlevel
      (.Vint (ir (exitValue (level + 1) r.1).1)) (PTree.set (idOf 717)
        (.Vint (ir (exitValue (level + 1) r.1).1)) le)) = some (.Vint (ir (exitValue (level + 1) r.1).1)) :=
    temps_gss _ _ _
  have hlev3 := hI3.lev
  wp_step
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hrl, hlev3, Refine.tv, typeof, cop]
  rcases hx : r.1 with _ | ⟨tg, sh⟩ | _
  · -- the child returned normally
    simp only [exitValue]
    simp only [ir_lt (a := ((level + 1 : Nat) : Int)) (b := level) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩,
      show ¬ ((level + 1 : Nat) : Int) < level by omega, decide_false, Bool.false_eq_true, ite_false]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    rw [hx] at h4
    simp only [exitValue] at h4
    refine tail _ false _ (fun h => absurd h (by decide)) h4 fun m' hO => ?_
    simp only [hx, exitValue, Bool.false_eq_true, ite_false, append_E0] at hO ⊢
    have hd' : (oChild G level nc tc tv1 tv cell st).1 = .done := by rw [hoc, hx]
    refine hNext t _ m' c' hd' hEm ?_
    rw [hoc, hx]
    exact hO
  · -- an unwind
    have htgl : tg < level + 1 := by
      rw [← hr] at hx; exact SearchInf.nodeOk_unwind_lt hok _ _ _ _ tg sh hx
    simp only [exitValue]
    simp only [ir_lt (a := (tg : Int)) (b := level) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    rw [hx] at h4
    simp only [exitValue] at h4
    by_cases htg : tg < level
    · simp only [show (tg : Int) < level by omega, decide_true, ite_true]
      wp_step; wp_step
      apply wp_return_some_eval
      simp only [Exec.evalExpr, hrl, Refine.tv, typeof, hfr, cop, hx, exitValue]
      have hoc' : oChild G level nc tc tv1 tv cell st =
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
      have hoc' : oChild G level nc tc tv1 tv cell st =
          (.done, (if tv == tv1 then longprune (if sh then shortprune cell
              { r.2 with fixedpts := r.2.fixedpts.erase tv } else cell) (r.2.fixedpts.erase tv) r.2.autos
            else (if sh then shortprune cell { r.2 with fixedpts := r.2.fixedpts.erase tv } else cell)),
            Hex.GraphIso.Nauty.recover nautyInf level { r.2 with fixedpts := r.2.fixedpts.erase tv }) := by
        rw [hoc, hx]; simp [htg]
      refine hNext t _ m' c' (by rw [hoc']) hEm ?_
      rw [hoc']
      simp only [hx] at hO
      exact hO
  · rw [← hr] at hx; exact absurd hx hnf

end NautyVerified.Proofs.Search
