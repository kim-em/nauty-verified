import NautyVerified.Proofs.Dispatch.Spec
import NautyVerified.Proofs.Alloc.Slots
import NautyVerified.Proofs.Graph.Rows
import NautyVerified.Proofs.Init.Tables
import NautyVerified.Proofs.Refine.Fn

/-!
# naugraph.c's dispatch representation

`denseRep`: `dispatch_graph`'s procedures in the dense program, the graph as
its setword rows (`GraphAt`), the canonical store as `canong`'s setword rows
(`RowsAt`), both on one block (`GLoc = CLoc = Unit`), the scratch state as
naugraph.c's `workperm`, `workset` and `bucket` pairs (`denseSlots`), the
tables as naugraph.c's `bit` and `bytecount`, the workspace as naugraph.c's
`dnwork` pair, `init = NULL`.

`Dispatch/Dense.lean` adds the specifications (`dense : DispatchC`).
-/

namespace NautyVerified.Proofs.Dispatch

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep Slot InUse SlotsOk)
open NautyVerified.Proofs.Set (BitTable longs)
open NautyVerified.Proofs.Graph (GraphAt RowsAt)
open NautyVerified.Proofs.Init (BytecountTable)
open Hex.GraphIso.Nauty

local notation "WP" => Block.naugraphWorkperm
local notation "WPS" => Block.naugraphWorkpermSz
local notation "WS" => Block.naugraphWorkset
local notation "WSS" => Block.naugraphWorksetSz
local notation "BK" => Block.naugraphBucket
local notation "BKS" => Block.naugraphBucketSz

/-- naugraph.c's scratch pairs `workperm`, `workset`, `bucket`. -/
def denseSlots : List Slot := [(WP, WPS, 4), (WS, WSS, 8), (BK, BKS, 4)]

/-- The globals naugraph.c's procedures write. -/
def denseWGlobs : List block := [WP, WPS, WS, WSS, BK, BKS]

/-- naugraph.c's globals. -/
def denseGlobs : List block :=
  denseWGlobs ++ [Block.naugraphBit, Block.naugraphBytecount, Block.naugraphDnwork,
    Block.naugraphDnworkSz]

kernel_rfl denseGlobs_distinct_dec : decide (denseGlobs.Pairwise (· ≠ ·)) = true
kernel_rfl denseGlobs_env_dec :
  decide (∀ z ∈ denseGlobs, z ∉ (NautyEnv.dense.blocks)) = true

/-- What naugraph.c's scratch blocks avoid: its globals and the shared tables and
pair of `envAvoid`. -/
abbrev denseL : List block := denseGlobs ++ envAvoid

/-- The dense graph `G`'s rows at `bg`. -/
def denseGraphRep {n : Nat} (m : mem) (bg : block) (gofs : ptrofs) (G : Ctx n) (M : Nat) : Prop :=
  ∃ gw, GraphAt m bg gofs gw G.g M

/-- `canong`'s `M * n` words before `init`. -/
def denseCanonPre (m : mem) (bc : block) (cofs : ptrofs) (M n : Nat) : Prop :=
  ∃ cw, ArrayAt m .Mint64 bc (intOfZ (Ptrofs.unsigned cofs)) (longs cw) (M * n)

/-- `canong`'s first `sr` rows. -/
def denseCanonRep {n : Nat} (m : mem) (bc : block) (cofs : ptrofs) (M : Nat) (c : Array (VSet n))
    (sr : Nat) : Prop :=
  ∃ cw, RowsAt m bc cofs cw c sr M

theorem arrayAt_valid {m : mem} {chunk : memory_chunk} {b : block} {base : Int} {vals : Nat → val}
    {k : Nat} (h : ArrayAt m chunk b base vals k) (hk : 0 < k) : Mem.valid_block m b :=
  Alloc.valid_of_access (h.writable 0 hk)

/-- `dispatch_graph`'s representation. -/
def denseRep : DispatchRep Program.ge denseOps where
  isautom := Search.Block.isautomFn
  testcanlab := Search.Block.testcanlabFn
  updatecan := Search.Block.updatecanFn
  refine := Refine.Block.refine
  refine1 := Refine.Block.refine1
  cheapautom := Search.Block.cheapautomFn
  targetcell := Search.Block.targetcellFn
  freedyn := Search.Block.naugraphFreedyn
  check := Top.Block.naugraphCheck
  init := Vnullptr
  wsP := Block.naugraphDnwork
  wsS := Block.naugraphDnworkSz
  globs := denseGlobs
  wglobs := denseWGlobs
  Work m := SlotsOk m denseSlots denseL ∧ ∀ z ∈ denseL, Mem.valid_block m z
  IsWork m z := InUse m denseSlots z
  Tables m := BitTable m Block.naugraphBit ∧ BytecountTable m
  GLoc := Unit
  CLoc := Unit
  graphBlocks _ bg := [bg]
  canonBlocks _ bc := [bc]
  GraphRep m _ := denseGraphRep m
  CanonRep m _ := denseCanonRep m
  CanonPre := denseCanonPre
  globs_distinct := of_decide_eq_true denseGlobs_distinct_dec
  globs_env := of_decide_eq_true denseGlobs_env_dec
  wglobs_sub z hz := List.mem_append_left _ hz
  wsP_mem := by simp [denseGlobs]
  wsS_mem := by simp [denseGlobs]
  wsP_nw := by decide
  wsS_nw := by decide
  isWork_valid h := h.valid
  isWork_globs hw hz := by
    have := hw.1.notin _ hz
    simp only [List.mem_append, not_or] at this
    exact this
  work_unch hw hu hg hk hv :=
    let h := hw.1.unch hu (fun p hp => by
      simp only [denseSlots, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact ⟨hg _ (by simp [denseWGlobs]), hg _ (by simp [denseWGlobs])⟩) hk
    ⟨⟨h.1, fun z hz => hv z (hw.2 z hz)⟩, h.2⟩
  tables_unch ht hu hg := by
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [hu.load _ _ _ (hg _ (by simp [denseGlobs]) (by decide))]; exact ht.1 i hi
    · rw [hu.load _ _ _ (hg _ (by simp [denseGlobs]) (by decide))]; exact ht.2 i hi
  graphBlocks_head _ _ := List.mem_singleton_self _
  canonBlocks_head _ _ := List.mem_singleton_self _
  graph_unch h hu hb := let ⟨gw, hg⟩ := h
    ⟨gw, hg.arr.unch hu (hb _ (List.mem_singleton_self _)), hg.rep⟩
  canon_unch h hu hb := let ⟨cw, hc⟩ := h
    ⟨cw, hc.arr.unch hu (hb _ (List.mem_singleton_self _)), hc.rep⟩
  canon_le h hle := let ⟨cw, hc⟩ := h; ⟨cw, hc.arr, fun v hv => hc.rep v (Nat.lt_of_lt_of_le hv hle)⟩
  graph_valid h hn hM z hz := let ⟨_, hg⟩ := h
    (List.mem_singleton.1 hz) ▸ arrayAt_valid hg.arr (Nat.mul_pos hM hn)
  canon_valid h hn hM z hz := let ⟨_, hc⟩ := h
    (List.mem_singleton.1 hz) ▸ arrayAt_valid hc.arr (Nat.mul_pos hM hn)
  init_null _ _ _ _ _ _ h := let ⟨cw, ha⟩ := h; ⟨(), fun _ => ⟨cw, ha, fun _ hv => absurd hv (Nat.not_lt_zero _)⟩⟩


@[simp] theorem denseRep_graphBlocks (gl : denseRep.GLoc) (bg : block) : denseRep.graphBlocks gl bg = [bg] :=
  rfl
@[simp] theorem denseRep_canonBlocks (cl : denseRep.CLoc) (bc : block) : denseRep.canonBlocks cl bc = [bc] :=
  rfl

/-! ### naugraph.c's scratch pairs across a call -/

theorem dense_dyn {m : mem} (hw : denseRep.Work m) :
    (∃ c b, DynAt m WP WPS 4 c b) ∧ (∃ c b, DynAt m WS WSS 8 c b) ∧ (∃ c b, DynAt m BK BKS 4 c b) :=
  ⟨hw.1.dyn (WP, WPS, 4) (by simp [denseSlots]), hw.1.dyn (WS, WSS, 8) (by simp [denseSlots]),
    hw.1.dyn (BK, BKS, 4) (by simp [denseSlots])⟩

theorem dense_inUseW {m : mem} {c : Nat} {b : block} (d : DynAt m WP WPS 4 c b) (hc : 0 < c) :
    InUse m denseSlots b := ⟨(WP, WPS, 4), by simp [denseSlots], c, hc, d⟩
theorem dense_inUseS {m : mem} {c : Nat} {b : block} (d : DynAt m WS WSS 8 c b) (hc : 0 < c) :
    InUse m denseSlots b := ⟨(WS, WSS, 8), by simp [denseSlots], c, hc, d⟩
theorem dense_inUseB {m : mem} {c : Nat} {b : block} (d : DynAt m BK BKS 4 c b) (hc : 0 < c) :
    InUse m denseSlots b := ⟨(BK, BKS, 4), by simp [denseSlots], c, hc, d⟩

/-- naugraph.c's scratch state after a call that reallocated its pairs, each to
its old block or a new one, distinct new blocks. -/
theorem denseWork_next {m m' : mem} (hw : denseRep.Work m)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    {cW cS cB cW' cS' cB' : Nat} {bW bS bB bW' bS' bB' : block}
    (dW : DynAt m WP WPS 4 cW bW) (dS : DynAt m WS WSS 8 cS bS) (dB : DynAt m BK BKS 4 cB bB)
    (dW' : DynAt m' WP WPS 4 cW' bW') (dS' : DynAt m' WS WSS 8 cS' bS')
    (dB' : DynAt m' BK BKS 4 cB' bB')
    (rW : (cW' = cW ∧ bW' = bW) ∨ ¬ Mem.valid_block m bW')
    (rS : (cS' = cS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS')
    (rB : (cB' = cB ∧ bB' = bB) ∨ ¬ Mem.valid_block m bB')
    (fWS : ¬ Mem.valid_block m bW' → ¬ Mem.valid_block m bS' → 0 < cW' → 0 < cS' → bW' ≠ bS')
    (fWB : ¬ Mem.valid_block m bW' → ¬ Mem.valid_block m bB' → 0 < cW' → 0 < cB' → bW' ≠ bB')
    (fSB : ¬ Mem.valid_block m bS' → ¬ Mem.valid_block m bB' → 0 < cS' → 0 < cB' → bS' ≠ bB') :
    denseRep.Work m' ∧ ∀ z, denseRep.IsWork m' z → denseRep.IsWork m z ∨ ¬ Mem.valid_block m z := by
  have hn : ∀ p ∈ denseSlots, Alloc.Slot.Next m m' p := by
    intro p hp
    simp only [denseSlots, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact Alloc.Slot.next_of dW dW' rW
    · exact Alloc.Slot.next_of dS dS' rS
    · exact Alloc.Slot.next_of dB dB' rB
  have r := hw.1.next hw.2 hn (by
    intro p hp q hq c c' z hc hc' dp dq hnv
    simp only [denseSlots, List.mem_cons, List.mem_nil_iff, or_false] at hp hq
    have eW : ∀ {c z}, 0 < c → DynAt m' WP WPS 4 c z → z = bW' ∧ 0 < cW' := fun hc d =>
      ⟨dW'.same_block d (dW'.same_cap d ▸ hc), dW'.same_cap d ▸ hc⟩
    have eS : ∀ {c z}, 0 < c → DynAt m' WS WSS 8 c z → z = bS' ∧ 0 < cS' := fun hc d =>
      ⟨dS'.same_block d (dS'.same_cap d ▸ hc), dS'.same_cap d ▸ hc⟩
    have eB : ∀ {c z}, 0 < c → DynAt m' BK BKS 4 c z → z = bB' ∧ 0 < cB' := fun hc d =>
      ⟨dB'.same_block d (dB'.same_cap d ▸ hc), dB'.same_cap d ▸ hc⟩
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    · rfl
    · obtain ⟨e1, h1⟩ := eW hc dp; obtain ⟨e2, h2⟩ := eS hc' dq
      subst e1; exact absurd e2 (fWS hnv (e2 ▸ hnv) h1 h2)
    · obtain ⟨e1, h1⟩ := eW hc dp; obtain ⟨e2, h2⟩ := eB hc' dq
      subst e1; exact absurd e2 (fWB hnv (e2 ▸ hnv) h1 h2)
    · obtain ⟨e1, h1⟩ := eS hc dp; obtain ⟨e2, h2⟩ := eW hc' dq
      subst e1; exact absurd e2.symm (fWS (e2 ▸ hnv) hnv h2 h1)
    · rfl
    · obtain ⟨e1, h1⟩ := eS hc dp; obtain ⟨e2, h2⟩ := eB hc' dq
      subst e1; exact absurd e2 (fSB hnv (e2 ▸ hnv) h1 h2)
    · obtain ⟨e1, h1⟩ := eB hc dp; obtain ⟨e2, h2⟩ := eW hc' dq
      subst e1; exact absurd e2.symm (fWB (e2 ▸ hnv) hnv h2 h1)
    · obtain ⟨e1, h1⟩ := eB hc dp; obtain ⟨e2, h2⟩ := eS hc' dq
      subst e1; exact absurd e2.symm (fSB (e2 ▸ hnv) hnv h2 h1)
    · rfl)
  exact ⟨⟨r.1, fun z hz => hv z (hw.2 z hz)⟩, r.2⟩

/-- An unchanged pair's block is not new: the fresh-distinctness side condition. -/
theorem fresh_l {m : mem} {bp bs : block} {k c c' : Nat} {b b' : block} (d : DynAt m bp bs k c b) :
    ¬ Mem.valid_block m b → ¬ Mem.valid_block m b' → 0 < c → 0 < c' → b ≠ b' :=
  fun hnv _ hc _ => absurd (Alloc.Malloced.valid (d.mal hc)) hnv

theorem fresh_r {m : mem} {bp bs : block} {k c c' : Nat} {b b' : block} (d : DynAt m bp bs k c b) :
    ¬ Mem.valid_block m b' → ¬ Mem.valid_block m b → 0 < c' → 0 < c → b' ≠ b :=
  fun _ hnv _ hc => absurd (Alloc.Malloced.valid (d.mal hc)) hnv

end NautyVerified.Proofs.Dispatch
