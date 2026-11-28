import NautyVerified.Proofs.Search.Node.FirstLoopAt
import NautyVerified.Proofs.Search.Node.Env
import NautyVerified.Logic.Grow
import NautyVerified.Proofs.Search.Processnode.State

/-!
# The memory of `firstpathnode0` before and after its child loop

`HeadAt L m st pre nsp ch`: `LoopAt` without the target cell's contents and the
locals' values (the node's own steps before the loop are still filling them).
`HeadAt.step`: a step that changes only blocks of `S`, blocks new since the
last step, work blocks, the target cell and the locals keeps `HeadAt`.
`HeadAt.loop`: with the cell and the locals filled in, `HeadAt` is `LoopAt`.
`HeadAt.post`: on return, freeing the locals leaves the facts of the node
specification's postcondition about memory.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty

variable {n : Nat}

/-- The memory of `firstpathnode0` before its child loop. -/
structure HeadAt (L : LCtx n) (m : mem) (st : Search n) (pre nsp : Bool)
    (ch : List (block × block)) : Prop where
  search : SearchAt m L.S L.ctx st pre nsp
  cellv : ∃ v, ArrayAt m .Mint64 L.btc 0 v L.S.M
  locA : ∀ z ∈ L.locals, ∃ v, ArrayAt m .Mint32 z 0 v 1
  chain : ChainAt L m ch
  frame : NodeFrame L.m₀ m L.S L.chain₀ L.level
  work : ∀ z, IsWork m z → IsWork L.m₀ z ∨ ¬ Mem.valid_block L.m₀ z
  locals : ∀ z ∈ L.locals, Mem.valid_block m z ∧ z ∉ L.S.blocks ∧ ¬ IsWork m z
  fre : ∀ z ∈ L.locals, Mem.valid_access m .Mint32 z (zOfInt 0) .Freeable
  vU : Mem.valid_block m L.S.bUA
  pU : Mem.perm m L.S.bUA (zOfInt 0) .Cur .Nonempty

theorem LoopAt.head {L : LCtx n} {m : mem} {st : Search n} {pre nsp : Bool} {cell : VSet n}
    {ch : List (block × block)} (h : LoopAt L m st pre nsp cell ch) : HeadAt L m st pre nsp ch where
  search := h.search
  cellv := by obtain ⟨tw, ha, -⟩ := h.cell; exact ⟨_, ha⟩
  locA := by
    intro z hz
    simp only [LCtx.locals, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, h.nc⟩
    · exact h.q
    · exact h.k
    · exact ⟨_, h.tc⟩
    · exact ⟨_, h.tz⟩
  chain := h.chain
  frame := h.frame
  work := h.work
  locals := h.locals
  fre := h.fre
  vU := h.vU
  pU := h.pU

theorem HeadAt.loop {L : LCtx n} {m : mem} {st : Search n} {pre nsp : Bool}
    {ch : List (block × block)} (h : HeadAt L m st pre nsp ch) {cell : VSet n}
    (hc : ∃ tw, ArrayAt m .Mint64 L.btc 0 (longs tw) L.S.M ∧
      SetRep (fun w => bv64 (tw w)) L.S.M cell)
    (hnc : ArrayAt m .Mint32 L.bnc 0 (fun _ => .Vint (ir L.nc)) 1)
    (htc : ArrayAt m .Mint32 L.bc 0 (fun _ => .Vint (ir L.tc)) 1)
    (htz : ArrayAt m .Mint32 L.bz 0 (fun _ => .Vint (ir L.tcsize)) 1) :
    LoopAt L m st pre nsp cell ch where
  search := h.search
  cell := hc
  nc := hnc
  tc := htc
  tz := htz
  q := h.locA _ (by simp [LCtx.locals])
  k := h.locA _ (by simp [LCtx.locals])
  chain := h.chain
  frame := h.frame
  work := h.work
  locals := h.locals
  fre := h.fre
  vU := h.vU
  pU := h.pU

theorem Keep.access {m m' : mem} {b : block} (hk : Alloc.Keep m m' b) {c : memory_chunk}
    {o : Z} {p : Common.Memtype.permission} (h : Mem.valid_access m c b o p) : Mem.valid_access m' c b o p :=
  ⟨fun o' ho => hk.perm _ _ (h.1 o' ho), h.2⟩

/-- One of the node's own steps before the loop keeps `HeadAt`. -/
theorem HeadAt.step {L : LCtx n} {m : mem} {st : Search n} {pre nsp : Bool}
    {ch : List (block × block)} (h : HeadAt L m st pre nsp ch)
    (hfresh : ∀ z ∈ L.locals, ¬ Mem.valid_block L.m₀ z)
    {m' : mem} {st' : Search n} {pre' nsp' : Bool}
    (hS : SearchAt m' L.S L.ctx st' pre' nsp')
    (hu : Unch m m' (fun z => stepSet m L.S L.btc z ∨ z ∈ L.locals))
    (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hW : ∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z)
    (hc : ∃ v, ArrayAt m' .Mint64 L.btc 0 v L.S.M) (hkc : Alloc.Keep m m' L.btc)
    (hlA : ∀ z ∈ L.locals, ∃ v, ArrayAt m' .Mint32 z 0 v 1)
    (hkl : ∀ z ∈ L.locals, Alloc.Keep m m' z) :
    HeadAt L m' st' pre' nsp' ch := by
  have hc0 := h.chain
  have hok := hc0.ok
  have hT : ∀ z ∈ tcBlocks Block.tcnode0 ch, z ≠ L.btc →
      ¬ (stepSet m L.S L.btc z ∨ z ∈ L.locals) := by
    intro z hz hne
    simp only [tcBlocks, List.mem_cons] at hz
    rintro ((⟨hzS, -, h3⟩ | hz' | hz' | rfl) | hzl)
    · rcases hz with rfl | hz
      · exact h3 rfl
      · obtain ⟨p, hp, hzp⟩ := List.mem_flatMap.1 hz
        obtain ⟨a1, a2, -, -⟩ := hok.apart p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzp
        rcases hzp with rfl | rfl
        · exact a1 hzS
        · exact a2 hzS
    · rcases hz with rfl | hz
      · exact hz' hc0.chain.head_valid
      · obtain ⟨p, hp, hzp⟩ := List.mem_flatMap.1 hz
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzp
        rcases hzp with rfl | rfl
        · exact hz' (hok.valid p hp).1
        · exact hz' (hok.valid p hp).2
    · rcases hz with rfl | hz
      · exact h.search.work_not hz' (by simp [SLoc.blocks])
      · obtain ⟨p, hp, hzp⟩ := List.mem_flatMap.1 hz
        obtain ⟨-, -, a3, a4⟩ := hok.apart p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzp
        rcases hzp with rfl | rfl
        · exact a3 hz'
        · exact a4 hz'
    · exact hne rfl
    · rcases hz with rfl | hz
      · exact (h.locals _ hzl).2.1 (by simp [SLoc.blocks])
      · obtain ⟨p, hp, hzp⟩ := List.mem_flatMap.1 hz
        obtain ⟨a1, a2⟩ := hc0.apart p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzp
        rcases hzp with rfl | rfl
        · exact a1 hzl
        · exact a2 hzl
  have hmem := List.mem_of_getElem? hc0.own
  exact
    { search := hS
      cellv := hc
      locA := hlA
      chain :=
        { hc0 with
          chain := TcChain.setCell hu hc hkc hc0.chain hT
            (fun e => (hok.apart _ hmem).2.1 (e ▸ by simp [SLoc.blocks]))
            (fun p hp e => by
              have ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
              have := flat_idx hok.pairwise hi hc0.own (.inl e.symm) (.inr rfl)
              subst this; rw [hc0.own] at hi; cases hi
              exact flat_ne hok.pairwise hmem e)
          ok := hok.mono hg hW }
      frame := ⟨h.frame.unch.trans (hu.mono fun z hz => by
          rcases hz with hz | hz
          · have hg0 := h.frame.2
            rcases hz with hz | hz | hz | rfl
            · exact .inl hz
            · exact .inr (.inl fun hv => hz (hg0 _ hv))
            · rcases h.work z hz with hw | hw
              · exact .inr (.inr (.inl hw))
              · exact .inr (.inl hw)
            · exact hc0.entry_frame hc0.own (Nat.le_refl _) (.inr rfl)
          · exact .inr (.inl (hfresh z hz))), fun z hz => hg z (h.frame.2 z hz)⟩
      work := fun z hz => by
        rcases hW z hz with hw | hw
        · exact h.work z hw
        · exact .inr fun hv => hw (h.frame.2 _ hv)
      locals := fun z hz => by
        obtain ⟨a, b, c⟩ := h.locals z hz
        refine ⟨hg z a, b, fun hw => ?_⟩
        rcases hW z hw with hw | hw
        · exact c hw
        · exact hw a
      fre := fun z hz => Keep.access (hkl z hz) (h.fre z hz)
      vU := hg _ h.vU
      pU := perm_unch hu (by
          rintro ((⟨-, h2, -⟩ | hz | hz | hz) | hz)
          · exact h2 rfl
          · exact hz h.vU
          · exact h.search.work_not hz (by simp [SLoc.blocks])
          · exact (hok.apart _ hmem).2.1 (hz ▸ by simp [SLoc.blocks])
          · exact (h.locals _ hz).2.1 (by simp [SLoc.blocks])) h.pU }

/-- On return: freeing the locals leaves the memory facts of the node's postcondition. -/
theorem HeadAt.post {L : LCtx n} {m : mem} {st : Search n} {pre nsp : Bool}
    {ch : List (block × block)} (h : HeadAt L m st pre nsp ch)
    (hfresh : ∀ z ∈ L.locals, ¬ Mem.valid_block L.m₀ z) {e : env} {l : List block}
    (hbe : blocks_of_env ge e = l.map fun b => (b, zOfInt 0, Cfrontend.Ctypes.sizeof ge.genv_cenv tint))
    (hl : l.Nodup) (hlL : ∀ z ∈ l, z ∈ L.locals) :
    ∃ mf, Mem.free_list m (blocks_of_env ge e) = some mf ∧ SearchAt mf L.S L.ctx st pre nsp ∧
      (∃ chain', TcChain mf L.S.M Block.tcnode0 chain' ∧ TcOk mf L.S chain' ∧
        L.level ≤ chain'.length ∧ chain'.take (L.level - 1) = L.chain₀.take (L.level - 1) ∧
        ∀ p ∈ chain', p ∈ L.chain₀ ∨ (¬ Mem.valid_block L.m₀ p.1 ∧ ¬ Mem.valid_block L.m₀ p.2)) ∧
      NodeFrame L.m₀ mf L.S L.chain₀ L.level ∧
      (∀ z, IsWork mf z → IsWork L.m₀ z ∨ ¬ Mem.valid_block L.m₀ z) := by
  obtain ⟨mf, hfree, hu⟩ := free_ints l m hl fun b hb => h.fre b (hlL b hb)
  rw [hbe]
  have hg : ∀ z, Mem.valid_block m z → Mem.valid_block mf z := fun z hz => free_list_valid hfree z hz
  have hS : ∀ z ∈ L.S.blocks, ¬ z ∈ l := fun z hz hzl => (h.locals z (hlL z hzl)).2.1 hz
  have hwk : ∀ z, IsWork m z → ¬ z ∈ l := fun z hz hzl => (h.locals z (hlL z hzl)).2.2 hz
  have hwm : WorkMono m mf := WorkMono.of_unch h.search.work hu
    (fun z hz => hS z (Processnode.workG_blocks L.S hz)) hwk
  have hc0 := h.chain
  refine ⟨mf, hfree, h.search.unch hu hS hwk, ⟨ch, ?_, hc0.ok.mono hg hwm, hc0.len, hc0.take,
    hc0.fresh⟩, ⟨h.frame.unch.trans (hu.mono fun z hz => .inr (.inl (hfresh z (hlL z hz)))),
      fun z hz => hg z (h.frame.2 z hz)⟩, fun z hz => ?_⟩
  · refine TcChain.unch hu hc0.chain fun z hz hzl => ?_
    simp only [tcBlocks, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hS _ (by simp [SLoc.blocks]) hzl
    · obtain ⟨p, hp, hzp⟩ := List.mem_flatMap.1 hz
      obtain ⟨a1, a2⟩ := hc0.apart p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzp
      rcases hzp with rfl | rfl
      · exact a1 (hlL _ hzl)
      · exact a2 (hlL _ hzl)
  · rcases hwm z hz with h1 | h1
    · exact h.work z h1
    · exact .inr fun hv => h1 (h.frame.2 _ hv)

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

theorem SLoc.globs_mem {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {z : block} (hz : z ∈ D.globs) :
    z ∈ S.blocksG D gl cl :=
  SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inr hz)))))

/-- `HeadAt` for `D`. -/
structure HeadAtG (L : LCtxG D n) (m : mem) (st : SearchState n (O.Canon n)) (pre nsp : Bool)
    (ch : List (block × block)) : Prop where
  search : SearchAtG D m L.S L.gl L.cl L.G st pre nsp
  cellv : ∃ v, ArrayAt m .Mint64 L.btc 0 v L.S.M
  locA : ∀ z ∈ L.locals, ∃ v, ArrayAt m .Mint32 z 0 v 1
  chain : ChainAtG L m ch
  frame : NodeFrameG D L.m₀ m L.S L.gl L.cl L.chain₀ L.level
  work : ∀ z, IsWorkG D m z → IsWorkG D L.m₀ z ∨ ¬ Mem.valid_block L.m₀ z
  locals : ∀ z ∈ L.locals, Mem.valid_block m z ∧ z ∉ L.S.blocksG D L.gl L.cl ∧ ¬ IsWorkG D m z
  fre : ∀ z ∈ L.locals, Mem.valid_access m .Mint32 z (zOfInt 0) .Freeable
  vU : Mem.valid_block m L.S.bUA
  pU : Mem.perm m L.S.bUA (zOfInt 0) .Cur .Nonempty

theorem LoopAtG.head {L : LCtxG D n} {m : mem} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {cell : VSet n} {ch : List (block × block)} (h : LoopAtG L m st pre nsp cell ch) :
    HeadAtG L m st pre nsp ch where
  search := h.search
  cellv := by obtain ⟨tw, ha, -⟩ := h.cell; exact ⟨_, ha⟩
  locA := by
    intro z hz
    simp only [LCtxG.locals, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, h.nc⟩
    · exact h.q
    · exact h.k
    · exact ⟨_, h.tc⟩
    · exact ⟨_, h.tz⟩
  chain := h.chain
  frame := h.frame
  work := h.work
  locals := h.locals
  fre := h.fre
  vU := h.vU
  pU := h.pU

theorem HeadAtG.loop {L : LCtxG D n} {m : mem} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {ch : List (block × block)} (h : HeadAtG L m st pre nsp ch) {cell : VSet n}
    (hc : ∃ tw, ArrayAt m .Mint64 L.btc 0 (longs tw) L.S.M ∧
      SetRep (fun w => bv64 (tw w)) L.S.M cell)
    (hnc : ArrayAt m .Mint32 L.bnc 0 (fun _ => .Vint (ir L.nc)) 1)
    (htc : ArrayAt m .Mint32 L.bc 0 (fun _ => .Vint (ir L.tc)) 1)
    (htz : ArrayAt m .Mint32 L.bz 0 (fun _ => .Vint (ir L.tcsize)) 1) :
    LoopAtG L m st pre nsp cell ch where
  search := h.search
  cell := hc
  nc := hnc
  tc := htc
  tz := htz
  q := h.locA _ (by simp [LCtxG.locals])
  k := h.locA _ (by simp [LCtxG.locals])
  chain := h.chain
  frame := h.frame
  work := h.work
  locals := h.locals
  fre := h.fre
  vU := h.vU
  pU := h.pU

/-- One of the node's own steps before the loop keeps `HeadAtG`. -/
theorem HeadAtG.step {L : LCtxG D n} {m : mem} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {ch : List (block × block)} (h : HeadAtG L m st pre nsp ch)
    (hfresh : ∀ z ∈ L.locals, ¬ Mem.valid_block L.m₀ z)
    {m' : mem} {st' : SearchState n (O.Canon n)} {pre' nsp' : Bool}
    (hS : SearchAtG D m' L.S L.gl L.cl L.G st' pre' nsp')
    (hu : Unch m m' (fun z => stepSetG D m L.S L.gl L.cl L.btc z ∨ z ∈ L.locals))
    (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hW : ∀ z, IsWorkG D m' z → IsWorkG D m z ∨ ¬ Mem.valid_block m z)
    (hc : ∃ v, ArrayAt m' .Mint64 L.btc 0 v L.S.M) (hkc : Alloc.Keep m m' L.btc)
    (hlA : ∀ z ∈ L.locals, ∃ v, ArrayAt m' .Mint32 z 0 v 1)
    (hkl : ∀ z ∈ L.locals, Alloc.Keep m m' z) :
    HeadAtG L m' st' pre' nsp' ch := by
  have hc0 := h.chain
  have hok := hc0.ok
  have hT : ∀ z ∈ tcBlocks E.tcnode0 ch, z ≠ L.btc →
      ¬ (stepSetG D m L.S L.gl L.cl L.btc z ∨ z ∈ L.locals) := by
    intro z hz hne
    rintro (hs | hzl)
    · exact hc0.not_step h.search z hz hne hs
    · simp only [tcBlocks, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact (h.locals _ hzl).2.1 SLoc.tcnode0_mem
      · obtain ⟨p, hp, hzp⟩ := List.mem_flatMap.1 hz
        obtain ⟨a1, a2⟩ := hc0.apart p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzp
        rcases hzp with rfl | rfl
        · exact a1 hzl
        · exact a2 hzl
  have hmem := List.mem_of_getElem? hc0.own
  exact
    { search := hS
      cellv := hc
      locA := hlA
      chain :=
        { hc0 with
          chain := TcChain.setCell hu hc hkc hc0.chain hT
            (fun e => (hok.apart _ hmem).2.1 (e ▸ SLoc.tcnode0_mem))
            (fun p hp e => by
              have ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
              have := flat_idx hok.pairwise hi hc0.own (.inl e.symm) (.inr rfl)
              subst this; rw [hc0.own] at hi; cases hi
              exact flat_ne hok.pairwise hmem e)
          ok := hok.mono hg hW }
      frame := ⟨h.frame.nset.trans (hu.mono fun z hz => by
          rcases hz with hz | hz
          · have hg0 := h.frame.2
            rcases hz with hz | hz | hz | rfl
            · exact .inl hz
            · exact .inr (.inl fun hv => hz (hg0 _ hv))
            · rcases h.work z hz with hw | hw
              · exact .inr (.inr (.inl hw))
              · exact .inr (.inl hw)
            · exact hc0.entry_frame hc0.own (Nat.le_refl _) (.inr rfl)
          · exact .inr (.inl (hfresh z hz))), fun z hz => hg z (h.frame.2 z hz)⟩
      work := fun z hz => by
        rcases hW z hz with hw | hw
        · exact h.work z hw
        · exact .inr fun hv => hw (h.frame.2 _ hv)
      locals := fun z hz => by
        obtain ⟨a, b, c⟩ := h.locals z hz
        refine ⟨hg z a, b, fun hw => ?_⟩
        rcases hW z hw with hw | hw
        · exact c hw
        · exact hw a
      fre := fun z hz => Keep.access (hkl z hz) (h.fre z hz)
      vU := hg _ h.vU
      pU := perm_unch hu (by
          rintro ((⟨-, h2, -⟩ | hz | hz | hz) | hz)
          · exact h2 rfl
          · exact hz h.vU
          · exact h.search.work_not hz SLoc.bUA_mem
          · exact (hok.apart _ hmem).2.1 (hz ▸ SLoc.bUA_mem)
          · exact (h.locals _ hz).2.1 SLoc.bUA_mem) h.pU }

/-- On return: freeing the locals leaves the memory facts of the node's postcondition. -/
theorem HeadAtG.post {L : LCtxG D n} {m : mem} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {ch : List (block × block)} (h : HeadAtG L m st pre nsp ch)
    (hfresh : ∀ z ∈ L.locals, ¬ Mem.valid_block L.m₀ z) {e : env} {l : List block}
    (hbe : blocks_of_env ge e = l.map fun b => (b, zOfInt 0, Cfrontend.Ctypes.sizeof ge.genv_cenv tint))
    (hl : l.Nodup) (hlL : ∀ z ∈ l, z ∈ L.locals) :
    ∃ mf, Mem.free_list m (blocks_of_env ge e) = some mf ∧
      SearchAtG D mf L.S L.gl L.cl L.G st pre nsp ∧
      (∃ chain', TcChain mf L.S.M E.tcnode0 chain' ∧ TcOkG D mf L.S L.gl L.cl chain' ∧
        L.level ≤ chain'.length ∧ chain'.take (L.level - 1) = L.chain₀.take (L.level - 1) ∧
        ∀ p ∈ chain', p ∈ L.chain₀ ∨ (¬ Mem.valid_block L.m₀ p.1 ∧ ¬ Mem.valid_block L.m₀ p.2)) ∧
      NodeFrameG D L.m₀ mf L.S L.gl L.cl L.chain₀ L.level ∧
      (∀ z, IsWorkG D mf z → IsWorkG D L.m₀ z ∨ ¬ Mem.valid_block L.m₀ z) := by
  obtain ⟨mf, hfree, hu⟩ := free_ints l m hl fun b hb => h.fre b (hlL b hb)
  rw [hbe]
  have hg : ∀ z, Mem.valid_block m z → Mem.valid_block mf z := fun z hz => free_list_valid hfree z hz
  have hS : ∀ z ∈ L.S.blocksG D L.gl L.cl, ¬ z ∈ l := fun z hz hzl =>
    (h.locals z (hlL z hzl)).2.1 hz
  have hwk : ∀ z, IsWorkG D m z → ¬ z ∈ l := fun z hz hzl => (h.locals z (hlL z hzl)).2.2 hz
  have hwm : WorkMonoG D m mf := fun z hz => .inl ((h.search.work.unch hu
    (fun z hz => hS z (SLoc.globs_mem (D.wglobs_sub z hz)))
    ⟨hS _ (SLoc.mem_litG (by simp [SLoc.litG])), hS _ (SLoc.mem_litG (by simp [SLoc.litG]))⟩
    hwk hg).2 z hz)
  have hc0 := h.chain
  refine ⟨mf, hfree, h.search.unch hu hS hwk hg, ⟨ch, ?_, hc0.ok.mono hg hwm, hc0.len, hc0.take,
    hc0.fresh⟩, ⟨h.frame.nset.trans (hu.mono fun z hz => .inr (.inl (hfresh z (hlL z hz)))),
      fun z hz => hg z (h.frame.2 z hz)⟩, fun z hz => ?_⟩
  · refine TcChain.unch hu hc0.chain fun z hz hzl => ?_
    simp only [tcBlocks, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hS _ SLoc.tcnode0_mem hzl
    · obtain ⟨p, hp, hzp⟩ := List.mem_flatMap.1 hz
      obtain ⟨a1, a2⟩ := hc0.apart p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzp
      rcases hzp with rfl | rfl
      · exact a1 (hlL _ hzl)
      · exact a2 (hlL _ hzl)
  · rcases hwm z hz with h1 | h1
    · exact h.work z h1
    · exact .inr fun hv => h1 (h.frame.2 _ hv)

end Generic

end NautyVerified.Proofs.Search
