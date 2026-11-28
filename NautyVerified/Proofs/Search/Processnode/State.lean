import NautyVerified.Proofs.Search.Processnode.Scatter

/-!
# What holds throughout `processnode`

`PAt`: memory holds the search state (`SearchAt`); the changes since entry
(`m₀`, before `sr` is allocated) are an `SFrame`; the work blocks in use are
those in use after the allocation (`m₁`) or new; `sr` is a fresh, freeable
`int`; the parameters are in their temporaries. `PAt.next` steps across the
search's own stores, `PAt.sr` across a store to `sr`, `PAt.call` across a call
that may reallocate the work arrays.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (Keep DynAt)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

/-- The fixed facts of one `processnode` call: entry memory `m₀`, memory after
allocating `sr` at `bsr` (`m₁`), the environment `e`. -/
structure PCtx (m₀ m₁ : mem) (S : SLoc) (e : env) (bsr : block) : Prop where
  valid0 : SValid m₀ S
  fresh : ¬ Mem.valid_block m₀ bsr
  valid1 : Mem.valid_block m₁ bsr
  grow01 : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m₁ z
  work10 : ∀ z, IsWork m₁ z → IsWork m₀ z
  esr : PTree.get dense.id.sr e = some (bsr, tint)
  eg : ∀ x, x ≠ dense.id.sr → PTree.get x e = none
  eEq : e = PTree.set dense.id.sr (bsr, tint) empty_env

/-- A point of `processnode`'s body. -/
structure PAt {n : Nat} (m₀ m₁ m : mem) (S : SLoc) (ctx : Ctx n) (bsr : block) (st : Search n)
    (nsp : Bool) : Prop where
  search : SearchAt m S ctx st false nsp
  frame : SFrame m₀ m S
  work : WorkMono m₁ m
  grow1 : ∀ z, Mem.valid_block m₁ z → Mem.valid_block m z
  srW : Mem.valid_access m .Mint32 bsr (zOfInt 0) .Freeable
  /-- `userautomproc`'s block has a permission at offset 0, so it compares
  unequal to `NULL`. -/
  ua : Mem.valid_access m .Mint8unsigned S.bUA (zOfInt 0) .Nonempty

/-- `∀ z ∈ [b₁, …], ¬ W z`, from `nw : ∀ z ∈ S.blocks, z ≠ x₁ → z ≠ x₂ → z ≠ x₃ → ¬ W z`
and the distinctness of `S.blocks`. -/
macro "all_notW " hd:term ", " nw:term : tactic =>
  `(tactic| ((simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
      and_true]; repeat' constructor) <;>
    exact $nw _ (by simp [SLoc.blocks]) (by sep_ne $hd) (by sep_ne $hd) (by sep_ne $hd)))

/-- As `all_notW`, with four exceptions. -/
macro "all_notW4 " hd:term ", " nw:term : tactic =>
  `(tactic| ((simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
      and_true]; repeat' constructor) <;>
    exact $nw _ (by simp [SLoc.blocks]) (by sep_ne $hd) (by sep_ne $hd) (by sep_ne $hd) (by sep_ne $hd)))

variable {n : Nat} {m₀ m₁ m m' : mem} {S : SLoc} {ctx : Ctx n} {e : env} {bsr : block}
  {st st' : Search n} {nsp nsp' : Bool}

theorem workG_blocks (S : SLoc) {z : block} (hz : z ∈ workG) : z ∈ S.blocks := by
  rw [SLoc.blocks_split]
  exact List.mem_append_right _ ((by decide : ∀ y ∈ workG, y ∈ globs) z hz)

theorem PCtx.ne_blocks (c : PCtx m₀ m₁ S e bsr) {z : block} (hz : z ∈ S.blocks) : z ≠ bsr :=
  fun h => c.fresh (h ▸ c.valid0 z hz)

/-- A work block in use is not `sr`. -/
theorem PAt.work_ne (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp) {z : block}
    (hz : IsWork m z) : z ≠ bsr := by
  rcases h.work z hz with h1 | h1
  · intro hzb; exact c.fresh (hzb ▸ (c.work10 z h1).valid)
  · intro hzb; exact h1 (hzb ▸ c.valid1)

/-- Across the search's own stores. -/
theorem PAt.next (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp) {L : List block}
    (hu : Unch m m' (· ∈ L)) (hL : ∀ z ∈ L, z ∈ S.wr)
    (hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC], Keep m m' z)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hsc : Scalars m' st' nsp') (hst : Stats m' S st' false) (har : Arrays m' S ctx st')
    (hinv : SInv st') : PAt m₀ m₁ m' S ctx bsr st' nsp' := by
  have hb : ∀ z ∈ L, z ∈ S.blocks := fun z hz => SLoc.wr_sub S z (hL z hz)
  have hwm : WorkMono m m' :=
    WorkMono.of_unch h.search.work hu
      (not_wr_all (SLoc.vars_ne h.search.distinct) hL (by decide) (by decide))
      fun z hz hzL => h.search.work_not hz (hb z hzL)
  refine ⟨h.search.rebuild hu hL hK hsc hst har hinv,
    ⟨h.frame.1.trans (hu.mono fun z hz => .inl (hb z hz)), fun z hz => hv _ (h.frame.2 z hz)⟩,
    fun z hz => ?_, fun z hz => hv _ (h.grow1 z hz),
    hu.access _ _ _ _ (fun hz => c.ne_blocks (hb _ hz) rfl) h.srW,
    hu.access _ _ _ _ (fun hz => by
      have := hL _ hz
      simp only [SLoc.wr, wrG, SLoc.wrV, List.mem_append, List.mem_cons, List.mem_nil_iff,
        or_false] at this
      have hd := h.search.distinct
      rcases this with (e | e | e | e | e | e | e | e | e | e | e | e | e) |
        (e | e | e | e | e | e | e | e | e | e | e | e | e | e) <;> exact absurd e (by sep_ne hd)) h.ua⟩
  rcases hwm z hz with h1 | h1
  · exact h.work z h1
  · exact .inr fun hv1 => h1 (h.grow1 _ hv1)

/-- Across a store to `sr`. -/
theorem PAt.sr (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (hu : Unch m m' (· = bsr)) (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hw : Mem.valid_access m' .Mint32 bsr (zOfInt 0) .Freeable) : PAt m₀ m₁ m' S ctx bsr st nsp := by
  have hwk : ∀ z, IsWork m z → ¬ z = bsr := fun z hz => h.work_ne c hz
  have hwm : WorkMono m m' :=
    WorkMono.of_unch h.search.work hu
      (fun z hz hzb => c.ne_blocks (workG_blocks S hz) hzb)
      hwk
  refine ⟨h.search.unch hu (fun z hz => c.ne_blocks hz) hwk,
    ⟨h.frame.1.trans (hu.mono fun z hz => .inr (.inl (hz ▸ c.fresh))),
      fun z hz => hv _ (h.frame.2 z hz)⟩,
    fun z hz => ?_, fun z hz => hv _ (h.grow1 z hz), hw,
    hu.access _ _ _ _ (fun e => c.ne_blocks (by simp [SLoc.blocks]) e) h.ua⟩
  rcases hwm z hz with h1 | h1
  · exact h.work z h1
  · exact .inr fun hv1 => h1 (h.grow1 _ hv1)

/-- Across a call confined to the search's blocks, the work arrays, `sr` and
blocks new since `m`. -/
theorem PAt.call (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp) {W : block → Prop}
    (hu : Unch m m' W)
    (hW : ∀ z, W z → z ∈ S.wr ∨ z ∈ workG ∨ IsWork m z ∨ ¬ Mem.valid_block m z ∨ z = bsr)
    (hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC], Keep m m' z)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) (hwm : WorkMono m m')
    (hwk : WorkAt n m' S S.blocks)
    (hsc : Scalars m' st' nsp') (hst : Stats m' S st' false) (har : Arrays m' S ctx st')
    (hinv : SInv st') (hsrw : Mem.valid_access m' .Mint32 bsr (zOfInt 0) .Freeable) :
    PAt m₀ m₁ m' S ctx bsr st' nsp' := by
  have hvm : ∀ z ∈ S.blocks, Mem.valid_block m z := fun z hz => h.frame.2 _ (c.valid0 z hz)
  have hS : ∀ z ∈ S.blocks, W z → z ∈ S.wr ∨ z ∈ workG := fun z hz hWz => by
    rcases hW z hWz with h1 | h1 | h1 | h1 | h1
    · exact .inl h1
    · exact .inr h1
    · exact absurd hz (h.search.work_not h1)
    · exact absurd (hvm z hz) h1
    · exact absurd h1 (c.ne_blocks hz)
  refine ⟨h.search.rebuildW hu hS hK hsc hst har hinv hwk,
    ⟨h.frame.1.trans (hu.mono fun z hz => ?_), fun z hz => hv _ (h.frame.2 z hz)⟩,
    fun z hz => ?_, fun z hz => hv _ (h.grow1 z hz), hsrw, hu.access _ _ _ _ (fun hW' => by
      rcases hW _ hW' with h1 | h1 | h1 | h1 | h1
      · simp only [SLoc.wr, wrG, SLoc.wrV, List.mem_append, List.mem_cons, List.mem_nil_iff,
          or_false] at h1
        have hd := h.search.distinct
        rcases h1 with (e | e | e | e | e | e | e | e | e | e | e | e | e) |
          (e | e | e | e | e | e | e | e | e | e | e | e | e | e) <;> exact absurd e (by sep_ne hd)
      · have hd := h.search.distinct
        simp only [workG, List.mem_cons, List.mem_nil_iff, or_false] at h1
        rcases h1 with e | e | e | e | e | e | e | e <;> exact absurd e (by sep_ne hd)
      · exact h.search.work_not h1 (by simp [SLoc.blocks])
      · exact h1 (hvm _ (by simp [SLoc.blocks]))
      · exact c.ne_blocks (by simp [SLoc.blocks]) h1) h.ua⟩
  · rcases hW z hz with h1 | h1 | h1 | h1 | h1
    · exact .inl (SLoc.wr_sub S _ h1)
    · exact .inl (workG_blocks S h1)
    · rcases h.work z h1 with h2 | h2
      · exact .inr (.inr (c.work10 z h2))
      · exact .inr (.inl fun hv0 => h2 (c.grow01 _ hv0))
    · exact .inr (.inl fun hv0 => h1 (h.frame.2 _ hv0))
    · exact .inr (.inl (h1 ▸ c.fresh))
  · rcases hwm z hz with h1 | h1
    · exact h.work z h1
    · exact .inr fun hv1 => h1 (h.grow1 _ hv1)

end NautyVerified.Proofs.Search.Processnode
