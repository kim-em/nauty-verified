import NautyVerified.Proofs.Search.Node.OtherIter

/-!
# `Carry` across a step of `othernode0`'s body

`Carry.step`: across a step that changes blocks a search call may change
(`S.Chg`, blocks new since the step began, work blocks), the locals (keeping
their permissions) and the target cell, whose work blocks are old or new.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified NautyVerified.Logic NautyVerified.Program
open NautyVerified.Proofs.Alloc (Keep)
open Hex.GraphIso.Nauty

variable {n : Nat}

theorem Keep.access' {m m' : mem} {b : block} (hk : Keep m m' b)
    {chunk : Common.AST.memory_chunk} {ofs : Z} {p : Common.Memtype.permission}
    (h : Mem.valid_access m chunk b ofs p) : Mem.valid_access m' chunk b ofs p :=
  ⟨fun o ho => hk.perm _ _ (h.1 o ho), h.2⟩

theorem Carry.step {m₀ m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    {chain₀ chain : List (block × block)} {level : Nat} {ncw tcw ncw' tcw' : val}
    {nd bt : block} {L : OLocs}
    (hLS : ∀ z ∈ L.list, z ∉ S.blocks) (hLF : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z)
    (h : SearchAt m S ctx st pre nsp) (c : Carry m₀ m S chain₀ chain level ncw tcw nd bt L)
    {W : block → Prop} (hu : Unch m m' W) (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hwm : WorkMono m m')
    (hW : ∀ z, W z → S.Chg z ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨ z ∈ L.list ∨ z = bt)
    (hK : ∀ z ∈ L.list, Keep m m' z) (hbt : ∃ vals, ArrayAt m' .Mint64 bt 0 vals S.M)
    (hkb : Keep m m' bt)
    (hnc : Mem.load .Mint32 m' L.bnc (zOfInt 0) = some ncw')
    (htc : Mem.load .Mint32 m' L.bc (zOfInt 0) = some tcw') :
    Carry m₀ m' S chain₀ chain level ncw' tcw' nd bt L := by
  obtain ⟨btS, btW, btV, -, -⟩ := c.ntc
  have hpw := c.tco.pairwise
  have h0S : Block.tcnode0 ∈ S.blocks := by simp [SLoc.blocks]
  -- a block outside `S`, valid, not in use as work, no local and not the cell, is unchanged
  have keep : ∀ z, (z ∉ S.blocks ∨ z = Block.tcnode0 ∨ z = S.bUA) → Mem.valid_block m z →
      ¬ IsWork m z → z ∉ L.list → z ≠ bt → ¬ W z := by
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
  have locS : ∀ z, z ∈ S.blocks → z ∉ L.list := fun z hz hl => hLS z hl hz
  refine ⟨hnc, htc, ?_, TcOk.mono c.tco hg hwm, c.own, c.take, c.old, ?_, ?_,
    WorkMono.trans c.wm c.frame.grow hwm, hg _ c.uaV, ?_, c.l1⟩
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
    refine ⟨Keep.access' (hK z hz) ha, fun hw' => ?_, hc⟩
    rcases hwm z hw' with h1 | h1
    · exact hw h1
    · exact h1 (Alloc.valid_of_access ha)
  · refine NodeFrame.mk' (c.frame.nset.trans (hu.mono fun z hz => ?_))
      fun z hz => hg _ (c.frame.grow _ hz)
    rcases hW z hz with h1 | h1 | h1 | h1 | rfl
    · exact nset_step c.frame.grow c.wm (.inl h1)
    · exact nset_step c.frame.grow c.wm (.inr (.inl h1))
    · exact nset_step c.frame.grow c.wm (.inr (.inr h1))
    · exact .inr (.inl (hLF z h1))
    · exact nset_own hpw c.take c.old c.own
  · have hbU : S.bUA ∈ S.blocks := by simp [SLoc.blocks]
    exact (Keep.unch hu (keep _ (.inr (.inr rfl)) c.uaV (fun hw => h.work_not hw hbU)
      (locS _ hbU) (fun e => btS (e ▸ hbU)))).perm _ _ c.uaP

end NautyVerified.Proofs.Search
