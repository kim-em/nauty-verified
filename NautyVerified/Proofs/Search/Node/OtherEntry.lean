import NautyVerified.Proofs.Search.Node.OtherCarry
import NautyVerified.Proofs.Search.Node.Env

/-!
# Entering and leaving `othernode0`

`oEnv L`: the local environment binding `numcells`, `refcode`, `tcellsize`,
`tc` and `qinvar` to the blocks of `L`, as `alloc_variables` builds it;
`blocks_oEnvG`: the blocks `return` frees. `CarryG.finish`: freeing the locals
succeeds and keeps `SearchAtG`, the target-cell list, the frame since entry
and `WorkMonoG`. `oAllocG` (and the dense `oAlloc`): the pre-state after the
locals are allocated; `CarryG.init`: `CarryG` after the prologue.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Source NautyVerified.Word
open NautyVerified.Proofs.Alloc (Keep)
open Hex.GraphIso.Nauty

variable {n : Nat}

/-- `othernode0`'s local environment. -/
abbrev oEnv (L : OLocs) : env :=
  PTree.set dense.id.qinvar (L.bq, tint) (PTree.set dense.id.tc (L.bc, tint)
    (PTree.set dense.id.tcellsize (L.bz, tint) (PTree.set dense.id.refcode (L.bk, tint)
      (PTree.set dense.id.numcells (L.bnc, tint) empty_env))))

/-- A freeable `int` local holds some value. -/
theorem arrayAt_of_access {m : mem} {b : block}
    (h : Mem.valid_access m .Mint32 b (zOfInt 0) .Freeable) :
    ∃ v, Mem.load .Mint32 m b (zOfInt 0) = some v ∧ ∃ vals, ArrayAt m .Mint32 b 0 vals 1 := by
  have hw : Mem.valid_access m .Mint32 b (zOfInt 0) .Writable :=
    Mem.valid_access_implies _ _ _ _ _ _ h (.perm_F_any _)
  obtain ⟨v, hv⟩ := Mem.valid_access_load _ _ _ _
    (Mem.valid_access_implies _ _ _ _ _ _ h (.perm_F_any _))
  refine ⟨v, hv, fun _ => v, ⟨Int.le_refl _, by decide, fun i hi => ?_, fun i hi => ?_⟩⟩
  · obtain rfl : i = 0 := by omega
    exact hv
  · obtain rfl : i = 0 := by omega
    exact hw

/-- The node's pre-state after its locals are allocated. -/
theorem oAlloc {m₀ m : mem} {S : SLoc} {ctx : Ctx n} {st : Search n} {pre : Bool}
    {chain : List (block × block)} {L : OLocs}
    (h : SearchAt m₀ S ctx st pre false) (hvU : Mem.valid_block m₀ S.bUA)
    (hTc : TcChain m₀ S.M Block.tcnode0 chain) (hTo : TcOk m₀ S chain)
    (hu : Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z)) (hg : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m z)
    (hLF : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z) :
    SearchAt m S ctx st pre false ∧ TcChain m S.M Block.tcnode0 chain ∧ TcOk m S chain ∧
      (∀ z, IsWork m z → IsWork m₀ z) ∧ WorkMono m₀ m ∧ (∀ z ∈ L.list, z ∉ S.blocks) ∧
      (∀ z ∈ L.list, ¬ IsWork m z) ∧ (∀ z ∈ L.list, ∀ p ∈ chain, p.1 ≠ z ∧ p.2 ≠ z) := by
  have hvT : Mem.valid_block m₀ Block.tcnode0 := TcChain.headValid hTc
  have hvA := h.valid_all hvU hvT
  have hwk : ∀ z, IsWork m₀ z → ¬ ¬ Mem.valid_block m₀ z := fun z hz hn => hn hz.valid
  have hback : ∀ z, IsWork m z → IsWork m₀ z := fun z hz =>
    IsWork.back h hu (fun z hz' hn => hn (hvA z (by revert z; simp [SLoc.blocks]))) hz
  have wm : WorkMono m₀ m := fun z hz => .inl (hback z hz)
  refine ⟨h.unch hu (fun z hz hn => hn (hvA z hz)) hwk, hTc.unch hu ?_, TcOk.mono hTo hg wm,
    hback, wm, fun z hz hS => hLF z hz (hvA z hS), fun z hz hw => hLF z hz (hback z hw).valid,
    fun z hz p hp => ⟨fun e => hLF z hz (e ▸ (hTo.valid p hp).1),
      fun e => hLF z hz (e ▸ (hTo.valid p hp).2)⟩⟩
  intro z hz hn
  simp only [tcBlocks, List.mem_cons] at hz
  rcases hz with rfl | hz
  · exact hn hvT
  · obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · exact hn (hTo.valid p hp).1
    · exact hn (hTo.valid p hp).2

/-- The parent a node at `level` writes is among the blocks the node may change. -/
theorem nset_parent {m : mem} {S : SLoc} {chain : List (block × block)} {level : Nat}
    (hlen : level - 1 ≤ chain.length) : NSet m S chain level (tcParent chain level) := by
  unfold tcParent
  split
  · exact .inr (.inr (.inr (.inl rfl)))
  · obtain ⟨p, hp⟩ : ∃ p, chain[level - 2]? = some p :=
      ⟨chain[level - 2]'(by omega), List.getElem?_eq_getElem _⟩
    rw [hp]
    exact .inr (.inr (.inr (.inr (.inl ⟨level - 2, p, hp, by omega, rfl⟩))))

/-- `tcParent` is in the list's blocks. -/
theorem tcParent_mem {chain : List (block × block)} {level : Nat} (hl1 : 1 ≤ level)
    (hlen : level - 1 ≤ chain.length) : tcParent chain level ∈ tcBlocks Block.tcnode0 chain :=
  (tcParent_eq hl1 hlen) ▸ prevAt_mem _ _ _

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

theorem blocks_oEnvG (L : OLocs) :
    blocks_of_env ge (oEnv L) = [L.bq, L.bnc, L.bc, L.bz, L.bk].map
      fun b => (b, zOfInt 0, sizeof ge.genv_cenv tint) := rfl

theorem CarryG.finish {m₀ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {chain₀ chain : List (block × block)} {level : Nat} {ncw tcw : val} {nd bt : block}
    {L : OLocs}
    (hLS : ∀ z ∈ L.list, z ∉ S.blocksG D gl cl) (hLF : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z)
    (hLd : L.list.Pairwise (· ≠ ·))
    (h : SearchAtG D m S gl cl G st pre nsp)
    (c : CarryG D m₀ m S gl cl chain₀ chain level ncw tcw nd bt L) :
    ∃ m', Mem.free_list m (blocks_of_env ge (oEnv L)) = some m' ∧
      SearchAtG D m' S gl cl G st pre nsp ∧
      TcChain m' S.M E.tcnode0 chain ∧ TcOkG D m' S gl cl chain ∧
      NodeFrameG D m₀ m' S gl cl chain₀ level ∧ WorkMonoG D m₀ m' := by
  have hmem : ∀ z, z ∈ [L.bq, L.bnc, L.bc, L.bz, L.bk] → z ∈ L.list := by
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢
    rcases hz with h | h | h | h | h <;> simp [h]
  have hnd : [L.bq, L.bnc, L.bc, L.bz, L.bk].Nodup := by
    simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true] at hLd
    obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b2, b3, b4⟩, ⟨c3, c4⟩, d4⟩ := hLd
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
      List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> intro e <;>
      first
        | exact a1 e | exact a1 e.symm | exact a2 e | exact a2 e.symm | exact a3 e | exact a3 e.symm
        | exact a4 e | exact a4 e.symm | exact b2 e | exact b2 e.symm | exact b3 e | exact b3 e.symm
        | exact b4 e | exact b4 e.symm | exact c3 e | exact c3 e.symm | exact c4 e | exact c4 e.symm
        | exact d4 e | exact d4 e.symm
  obtain ⟨m', hfree, hu⟩ := free_ints [L.bq, L.bnc, L.bc, L.bz, L.bk] m hnd
    (fun b hb => (c.locs b (hmem b hb)).1)
  have hu' : Unch m m' (· ∈ L.list) := hu.mono fun z hz => hmem z hz
  have hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z := free_list_valid hfree
  have hwk : ∀ z, IsWorkG D m z → z ∉ L.list := fun z hz hl => (c.locs z hl).2.1 hz
  have mB : ∀ z ∈ D.globs, z ∈ S.blocksG D gl cl := fun z hz =>
    SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inr hz)))))
  have wm : WorkMonoG D m m' := fun z hz => .inl ((h.work.unch hu'
    (fun z hz hl => hLS z hl (mB z (D.wglobs_sub z hz)))
    ⟨fun hl => hLS _ hl (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl (by simp))))))),
      fun hl => hLS _ hl (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl (by simp)))))))⟩
    hwk hv).2 z hz)
  refine ⟨m', by rw [blocks_oEnvG]; exact hfree, h.unch hu' (fun z hz hl => hLS z hl hz) hwk hv,
    ?_, TcOkG.mono c.tco hv wm,
    NodeFrameG.mk' (c.frame.nset.trans (hu'.mono fun z hz => .inr (.inl (hLF z hz))))
      (fun z hz => hv _ (c.frame.grow _ hz)), WorkMonoG.trans c.wm c.frame.grow wm⟩
  refine TcChain.unch hu' c.tcc fun z hz hl => ?_
  simp only [tcBlocks, List.mem_cons] at hz
  rcases hz with rfl | hz
  · exact hLS _ hl tcnode0_memG
  · obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · exact ((c.locs _ hl).2.2 p hp).1 rfl
    · exact ((c.locs _ hl).2.2 p hp).2 rfl

/-- The node's pre-state after its locals are allocated. -/
theorem oAllocG {m₀ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {pre : Bool}
    {chain : List (block × block)} {L : OLocs}
    (h : SearchAtG D m₀ S gl cl G st pre false) (hvU : Mem.valid_block m₀ S.bUA)
    (hTc : TcChain m₀ S.M E.tcnode0 chain) (hTo : TcOkG D m₀ S gl cl chain)
    (hu : Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z))
    (hg : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m z)
    (hLF : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z) :
    SearchAtG D m S gl cl G st pre false ∧ TcChain m S.M E.tcnode0 chain ∧
      TcOkG D m S gl cl chain ∧
      (∀ z, IsWorkG D m z → IsWorkG D m₀ z) ∧ WorkMonoG D m₀ m ∧
      (∀ z ∈ L.list, z ∉ S.blocksG D gl cl) ∧
      (∀ z ∈ L.list, ¬ IsWorkG D m z) ∧ (∀ z ∈ L.list, ∀ p ∈ chain, p.1 ≠ z ∧ p.2 ≠ z) := by
  have hvT : Mem.valid_block m₀ E.tcnode0 := TcChain.headValid hTc
  have hvA := h.valid_all hvU hvT
  have hwk : ∀ z, IsWorkG D m₀ z → ¬ ¬ Mem.valid_block m₀ z := fun z hz hn => hn hz.valid
  have mB : ∀ z ∈ D.globs, z ∈ S.blocksG D gl cl := fun z hz =>
    SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inr hz)))))
  have hback : ∀ z, IsWorkG D m z → IsWorkG D m₀ z := (h.work.unch hu
    (fun z hz hn => hn (hvA z (mB z (D.wglobs_sub z hz))))
    ⟨fun hn => hn (hvA _ (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl (by simp)))))))),
      fun hn => hn (hvA _ (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl (by simp))))))))⟩
    hwk hg).2
  have wm : WorkMonoG D m₀ m := fun z hz => .inl (hback z hz)
  refine ⟨h.unch hu (fun z hz hn => hn (hvA z hz)) hwk hg, hTc.unch hu ?_, TcOkG.mono hTo hg wm,
    hback, wm, fun z hz hS => hLF z hz (hvA z hS), fun z hz hw => hLF z hz (hback z hw).valid,
    fun z hz p hp => ⟨fun e => hLF z hz (e ▸ (hTo.valid p hp).1),
      fun e => hLF z hz (e ▸ (hTo.valid p hp).2)⟩⟩
  intro z hz hn
  simp only [tcBlocks, List.mem_cons] at hz
  rcases hz with rfl | hz
  · exact hn hvT
  · obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · exact hn (hTo.valid p hp).1
    · exact hn (hTo.valid p hp).2

/-- The parent a node at `level` writes is among the blocks the node may change. -/
theorem nset_parentG {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {chain : List (block × block)} {level : Nat}
    (hlen : level - 1 ≤ chain.length) : NSetG D m S gl cl chain level (tcParent chain level) := by
  unfold tcParent
  split
  · exact .inr (.inr (.inr (.inl rfl)))
  · obtain ⟨p, hp⟩ : ∃ p, chain[level - 2]? = some p :=
      ⟨chain[level - 2]'(by omega), List.getElem?_eq_getElem _⟩
    rw [hp]
    exact .inr (.inr (.inr (.inr (.inl ⟨level - 2, p, hp, by omega, rfl⟩))))

/-- `tcParent` is in the list's blocks. -/
theorem tcParent_tcBlocks {chain : List (block × block)} {level : Nat} (hl1 : 1 ≤ level)
    (hlen : level - 1 ≤ chain.length) :
    tcParent (E := E) chain level ∈ tcBlocks E.tcnode0 chain :=
  (tcParent_eq hl1 hlen) ▸ prevAt_mem _ _ _

/-- `CarryG` after the prologue. -/
theorem CarryG.init {m₀ mA m₁ : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {pre : Bool}
    {chain chain' : List (block × block)} {level nc : Nat} {nd bt : block} {L : OLocs}
    (h0 : SearchAtG D m₀ S gl cl G st pre false) (hTo0 : TcOkG D m₀ S gl cl chain)
    (hl1 : 1 ≤ level) (hlen : level - 1 ≤ chain.length)
    (huaV : Mem.valid_block m₀ S.bUA) (huaP : Mem.perm m₀ S.bUA (zOfInt 0) .Cur .Nonempty)
    (hLF : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z) (hLS : ∀ z ∈ L.list, z ∉ S.blocksG D gl cl)
    (hLd : L.list.Pairwise (· ≠ ·))
    (huA : Unch m₀ mA (fun z => ¬ Mem.valid_block m₀ z))
    (hgA : ∀ z, Mem.valid_block m₀ z → Mem.valid_block mA z) (hwmA : WorkMonoG D m₀ mA)
    (haccA : ∀ z ∈ L.list, Mem.valid_access mA .Mint32 z (zOfInt 0) .Freeable)
    (hwkA : ∀ z ∈ L.list, ¬ IsWorkG D mA z) (hcA : ∀ z ∈ L.list, ∀ p ∈ chain, p.1 ≠ z ∧ p.2 ≠ z)
    (hA1 : ArrayAt m₁ .Mint32 L.bnc 0 (fun _ => .Vint (ir nc)) 1)
    (hTc1 : TcChain m₁ S.M E.tcnode0 chain') (hTo1 : TcOkG D m₁ S gl cl chain')
    (hown : chain'[level - 1]? = some (nd, bt))
    (htake : chain'.take (level - 1) = chain.take (level - 1))
    (hold : ∀ p ∈ chain', p ∈ chain ∨ (¬ Mem.valid_block mA p.1 ∧ ¬ Mem.valid_block mA p.2))
    (hU1 : Unch mA m₁ (fun z => z = L.bnc ∨ z = tcParent chain level ∨ ¬ Mem.valid_block mA z))
    (hg1 : ∀ z, Mem.valid_block mA z → Mem.valid_block m₁ z) (hwm1 : WorkMonoG D mA m₁)
    (hK1 : Keep mA m₁ L.bnc) :
    ∃ tcw, CarryG D m₀ m₁ S gl cl chain chain' level (.Vint (ir nc)) tcw nd bt L := by
  have hl := h0.lit
  have hpT := tcParent_tcBlocks (E := E) hl1 hlen
  have hpar : ∀ z, z ∈ S.blocksG D gl cl → z ≠ E.tcnode0 → z ≠ tcParent chain level := by
    intro z hz h0' e
    rw [tcParent_eq hl1 hlen] at e
    rcases prevAt_mem_nodes E.tcnode0 chain (level - 1) with h' | ⟨p, hp, h'⟩
    · exact h0' (e.trans h')
    · exact (hTo0.apart p hp).1 (h' ▸ e ▸ hz)
  have hlocP : ∀ z ∈ L.list, z ≠ tcParent chain level := by
    intro z hz e
    have := hpT; rw [← e] at this
    simp only [tcBlocks, List.mem_cons] at this
    rcases this with e' | hz'
    · exact hLS z hz (e' ▸ tcnode0_memG)
    · obtain ⟨p, hp, hz'⟩ := List.mem_flatMap.1 hz'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz'
      rcases hz' with e' | e'
      · exact (hcA z hz p hp).1 e'.symm
      · exact (hcA z hz p hp).2 e'.symm
  simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true] at hLd
  have hout : ∀ z ∈ L.list, z ≠ L.bnc →
      ¬ (z = L.bnc ∨ z = tcParent chain level ∨ ¬ Mem.valid_block mA z) := by
    intro z hz hb
    rintro (e | e | e)
    · exact hb e
    · exact hlocP z hz e
    · exact e (Alloc.valid_of_access (haccA z hz))
  obtain ⟨tcw, htcw, -⟩ := arrayAt_of_access (haccA L.bc (by simp))
  refine ⟨tcw, ⟨?_, ?_, hTc1, hTo1, hown, htake, ?_, ?_, ?_, WorkMonoG.trans hwmA hgA hwm1,
    hg1 _ (hgA _ huaV), ?_, hl1⟩⟩
  · simpa [elemOfs] using hA1.load 0 (by decide)
  · rw [hU1.load _ _ _ (hout _ (by simp) (fun e => hLd.1.2.2.1 e.symm))]; exact htcw
  · intro p hp
    rcases hold p hp with hp' | ⟨h1, h2⟩
    · exact .inl hp'
    · exact .inr ⟨fun hv => h1 (hgA _ hv), fun hv => h2 (hgA _ hv)⟩
  · intro z hz
    have hzv := Alloc.valid_of_access (haccA z hz)
    refine ⟨?_, fun hw => ?_, fun p hp => ?_⟩
    · by_cases hb : z = L.bnc
      · subst hb; exact Keep.access' hK1 (haccA _ hz)
      · exact hU1.access _ _ _ _ (hout z hz hb) (haccA z hz)
    · rcases hwm1 z hw with h1 | h1
      · exact hwkA z hz h1
      · exact h1 hzv
    · rcases hold p hp with hp' | ⟨h1, h2⟩
      · exact hcA z hz p hp'
      · exact ⟨fun e => h1 (e ▸ hzv), fun e => h2 (e ▸ hzv)⟩
  · refine NodeFrameG.mk' ((huA.mono fun z hz => .inr (.inl hz)).trans (hU1.mono fun z hz => ?_))
      fun z hz => hg1 _ (hgA _ hz)
    rcases hz with rfl | rfl | hz
    · exact .inr (.inl (hLF _ (by simp)))
    · exact nset_parentG hlen
    · exact .inr (.inl fun hv => hz (hgA _ hv))
  · have hbU : S.bUA ∈ S.blocksG D gl cl := bUA_memG
    have k1 : Keep m₀ mA S.bUA := Keep.unch huA (fun hn => hn huaV)
    have k2 : Keep mA m₁ S.bUA := Keep.unch hU1 (by
      rintro (e | e | e)
      · exact hLS _ (by simp) (e ▸ hbU)
      · exact hpar _ hbU (by sep_ne hl) e
      · exact e (hgA _ huaV))
    exact k2.perm _ _ (k1.perm _ _ huaP)

end Generic

end NautyVerified.Proofs.Search
