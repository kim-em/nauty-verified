import NautyVerified.Proofs.Search.Processnode.Scatter

/-!
# What holds throughout `processnode`

`PAt D`: memory holds the search state (`SearchAtG`); the changes since entry
(`m₀`, before `sr` is allocated) are an `SFrameG`; the work blocks in use are
those in use after the allocation (`m₁`) or new; `sr` is a fresh, freeable
`int`; the parameters are in their temporaries. `PAt.next` steps across the
search's own stores, `PAt.sr` across a store to `sr`, `PAt.call` across a call
of one of `D`'s procedures, `PAt.nautil` across a reallocation of nautil.c's
`workperm` pair. The dense helpers at the top (`all_notW`, `SLoc.wr_chg`) serve
the dense search proofs.
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

theorem workG_blocks (S : SLoc) {z : block} (hz : z ∈ workG) : z ∈ S.blocks := by
  rw [SLoc.blocks_split]
  exact List.mem_append_right _ ((by decide : ∀ y ∈ workG, y ∈ globs) z hz)

/-- The search's own writable blocks are not the callback's. -/
theorem SLoc.wr_ne_ua {S : SLoc} (hd : S.blocks.Pairwise (· ≠ ·)) {z : block} (hz : z ∈ S.wr) :
    z ≠ S.bUA := by
  simp only [SLoc.wr, wrG, SLoc.wrV, List.mem_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hz
  rcases hz with (e | e | e | e | e | e | e | e | e | e | e | e | e) |
    (e | e | e | e | e | e | e | e | e | e | e | e | e | e) <;> subst e <;> sep_ne hd

/-- The search's own writable blocks are not `tcnode0`. -/
theorem SLoc.wr_ne_tc {S : SLoc} (hd : S.blocks.Pairwise (· ≠ ·)) {z : block} (hz : z ∈ S.wr) :
    z ≠ Block.tcnode0 := by
  simp only [SLoc.wr, wrG, SLoc.wrV, List.mem_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hz
  rcases hz with (e | e | e | e | e | e | e | e | e | e | e | e | e) |
    (e | e | e | e | e | e | e | e | e | e | e | e | e | e) <;> subst e <;> sep_ne hd

/-- A block of `S` the search's own stores may change. -/
theorem SLoc.wr_chg {S : SLoc} (hd : S.blocks.Pairwise (· ≠ ·)) {z : block} (hz : z ∈ S.wr) :
    S.Chg z :=
  ⟨SLoc.wr_sub S _ hz, SLoc.wr_ne_ua hd hz, SLoc.wr_ne_tc hd hz⟩

/-! ### For any dispatch procedures

`PCtx D m₀ m₁ S gl cl e bsr` and `PAt D m₀ m₁ m S gl cl G bsr st nsp` over
`SearchAtG`. `PAt.next` steps across the search's own stores, `PAt.sr` across
a store to `sr`, `PAt.call` across a call of one of `D`'s procedures
(`DispatchRep.Step`) whose outputs are the canonical store's blocks or `sr`. -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC envAvoid)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}

/-- The fixed facts of one `processnode` call: entry memory `m₀`, memory after
allocating `sr` at `bsr` (`m₁`), the environment `e`. -/
structure PCtx (D : DispatchC ge O) (m₀ m₁ : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc)
    (e : env) (bsr : block) : Prop where
  valid0 : SValidG D.toDispatchRep m₀ S gl cl
  fresh : ¬ Mem.valid_block m₀ bsr
  valid1 : Mem.valid_block m₁ bsr
  grow01 : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m₁ z
  work10 : ∀ z, IsWorkG D.toDispatchRep m₁ z → IsWorkG D.toDispatchRep m₀ z
  esr : PTree.get dense.id.sr e = some (bsr, tint)
  eg : ∀ x, x ≠ dense.id.sr → PTree.get x e = none
  eEq : e = PTree.set dense.id.sr (bsr, tint) empty_env

/-- A point of `processnode`'s body. -/
structure PAt {n : Nat} (D : DispatchC ge O) (m₀ m₁ m : mem) (S : SLoc) (gl : D.GLoc)
    (cl : D.CLoc) (G : O.Gr n) (bsr : block) (st : SearchState n (O.Canon n)) (nsp : Bool) :
    Prop where
  search : SearchAtG D.toDispatchRep m S gl cl G st false nsp
  frame : SFrameG D.toDispatchRep m₀ m S gl cl
  work : WorkMonoG D.toDispatchRep m₁ m
  grow1 : ∀ z, Mem.valid_block m₁ z → Mem.valid_block m z
  srW : Mem.valid_access m .Mint32 bsr (zOfInt 0) .Freeable
  /-- `userautomproc`'s block has a permission at offset 0, so it compares
  unequal to `NULL`. -/
  ua : Mem.valid_access m .Mint8unsigned S.bUA (zOfInt 0) .Nonempty

variable {n : Nat} {D : DispatchC ge O} {m₀ m₁ m m' : mem} {S : SLoc} {gl : D.GLoc}
  {cl : D.CLoc} {G : O.Gr n} {e : env} {bsr : block} {st st' : SearchState n (O.Canon n)}
  {nsp nsp' : Bool}

theorem PCtx.ne_blocks (c : PCtx D m₀ m₁ S gl cl e bsr) {z : block}
    (hz : z ∈ S.blocksG D.toDispatchRep gl cl) : z ≠ bsr :=
  fun h => c.fresh (h ▸ c.valid0 z hz)

/-- The blocks of `S` are valid. -/
theorem PAt.valid (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp) :
    ∀ z ∈ S.blocksG D.toDispatchRep gl cl, Mem.valid_block m z :=
  fun z hz => h.frame.2 _ (c.valid0 z hz)

/-- A work block in use is not `sr`. -/
theorem PAt.work_ne (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {z : block} (hz : IsWorkG D.toDispatchRep m z) : z ≠ bsr := by
  rcases h.work z hz with h1 | h1
  · intro hzb; exact c.fresh (hzb ▸ (c.work10 z h1).valid)
  · intro hzb; exact h1 (hzb ▸ c.valid1)

/-- The list entries of `S.blocksG` by part. -/
theorem SLoc.litG_parts {D : DispatchRep ge O} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {y : block}
    (hy : y ∈ S.litG) :
    y ∈ D.graphBlocks gl S.bg ∨ y ∈ [S.bl, S.bp, S.bo, S.bst] ∨ y = S.bc ∨
      y ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ∨
      y ∈ envSearch := by
  simp only [SLoc.litG, List.mem_append] at hy
  rcases hy with hy | hy
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact .inl (D.graphBlocks_head gl _)
    iterate 4 exact .inr (.inl (by simp))
    · exact .inr (.inr (.inl rfl))
    iterate 10 exact .inr (.inr (.inr (.inl (by simp))))
  · exact .inr (.inr (.inr (.inr hy)))

theorem SLoc.mem_blocksG_lit {D : DispatchRep ge O} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {y : block} (hy : y ∈ S.litG) : y ∈ S.blocksG D gl cl :=
  (S.litG_sub D gl cl).subset hy

/-- A block the search's own statements write may change. -/
theorem _root_.NautyVerified.Proofs.Search.SearchAtG.chg_wr {D : DispatchRep ge O} {gl : D.GLoc} {cl : D.CLoc} {pre : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {z : block}
    (hz : z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc) : S.ChgG D gl cl z := by
  have hk := (h.not_wr (L := [z]) (by simpa using hz)).1
  refine ⟨SLoc.mem_blocksG_of D ?_, fun e => hk S.bUA (by simp) (by simp [e]),
    fun e => hk E.tcnode0 (by simp) (by simp [e])⟩
  rcases SLoc.wr_mem hz with h1 | h1 | h1 | h1
  · exact .inr (.inl h1)
  · exact .inr (.inr (.inl h1))
  · exact .inr (.inr (.inr (.inl h1)))
  · exact .inr (.inr (.inr (.inr (.inl h1))))

/-- A global of `D` may change. -/
theorem _root_.NautyVerified.Proofs.Search.SearchAtG.chg_globs {D : DispatchRep ge O} {gl : D.GLoc} {cl : D.CLoc} {pre : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {z : block} (hz : z ∈ D.globs) : S.ChgG D gl cl z :=
  ⟨SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inr hz))))),
    h.globs_ne hz (.inr (.inr (.inr (.inl (by simp))))),
    h.globs_ne hz (.inr (.inr (.inr (.inr (by simp)))))⟩

theorem _root_.NautyVerified.Proofs.Search.SearchAtG.graph_notin {D : DispatchRep ge O} {gl : D.GLoc} {cl : D.CLoc} {pre : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {L : List block}
    (hL : ∀ y ∈ L, y ∈ [S.bl, S.bp, S.bo, S.bst] ∨ y ∈ D.canonBlocks cl S.bc ∨
      y ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ∨ y ∈ envSearch ∨
      y ∈ D.globs) :
    ∀ z ∈ D.graphBlocks gl S.bg, ¬ z ∈ L :=
  fun z hz hzL => h.graph_ne hz (hL z hzL) rfl

theorem _root_.NautyVerified.Proofs.Search.SearchAtG.canon_notin {D : DispatchRep ge O} {gl : D.GLoc} {cl : D.CLoc} {pre : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {L : List block}
    (hL : ∀ y ∈ L, y ∈ D.graphBlocks gl S.bg ∨ y ∈ [S.bl, S.bp, S.bo, S.bst] ∨
      y ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ∨ y ∈ envSearch ∨
      y ∈ D.globs) :
    ∀ z ∈ D.canonBlocks cl S.bc, ¬ z ∈ L :=
  fun z hz hzL => h.canon_ne hz (hL z hzL) rfl

/-- `SFrameG` from `m₀` across a change since `m`, its blocks changeable, invalid
at `m₀` or in use as work blocks at `m`. -/
theorem PAt.frame_trans (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {W : block → Prop} (hu : Unch m m' W) (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hW : ∀ z, W z → S.ChgG D.toDispatchRep gl cl z ∨ ¬ Mem.valid_block m₀ z ∨
      IsWorkG D.toDispatchRep m z) :
    SFrameG D.toDispatchRep m₀ m' S gl cl := by
  refine ⟨h.frame.1.trans (hu.mono fun z hz => ?_), fun z hz => hv _ (h.frame.2 z hz)⟩
  rcases hW z hz with h1 | h1 | h1
  · exact .inl h1
  · exact .inr (.inl h1)
  · rcases h.work z h1 with h2 | h2
    · exact .inr (.inr (c.work10 z h2))
    · exact .inr (.inl fun hv0 => h2 (c.grow01 _ hv0))

/-- `PAt` at `m'` from the search state there, the frame and the work blocks. -/
theorem PAt.of_step (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    (hs : SearchAtG D.toDispatchRep m' S gl cl G st' false nsp')
    {W : block → Prop} (hu : Unch m m' W) (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hW : ∀ z, W z → S.ChgG D.toDispatchRep gl cl z ∨ ¬ Mem.valid_block m₀ z ∨
      IsWorkG D.toDispatchRep m z)
    (hwm : WorkMonoG D.toDispatchRep m m')
    (hsr : Mem.valid_access m' .Mint32 bsr (zOfInt 0) .Freeable) (hua : ¬ W S.bUA) :
    PAt D m₀ m₁ m' S gl cl G bsr st' nsp' :=
  ⟨hs, h.frame_trans c hu hv hW, h.work.trans h.grow1 hwm, fun z hz => hv _ (h.grow1 z hz), hsr,
    hu.access _ _ _ _ hua h.ua⟩

/-- Across the search's own stores. -/
theorem PAt.next (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {L : List block} (hu : Unch m m' (· ∈ L))
    (hL : ∀ z ∈ L, z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc)
    (hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws], Keep m m' z)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hsc : ScalarsG m' st' nsp') (hst : StatsG m' S st' false)
    (har : ArraysG D.toDispatchRep m' S gl cl G st') (hinv : SInvG O G st') :
    PAt D m₀ m₁ m' S gl cl G bsr st' nsp' := by
  have hs := h.search
  obtain ⟨nK, nG, -⟩ := hs.not_wr hL
  have hchg : ∀ z ∈ L, S.ChgG D.toDispatchRep gl cl z := fun z hz => hs.chg_wr (hL z hz)
  have hstep := SStepG.of_unch hs hu hv (fun z hz => .inl (hchg z hz))
    (fun z hz => nG z (D.wglobs_sub z hz)) ⟨nK _ (by simp), nK _ (by simp)⟩
  refine h.of_step c (hs.rebuild hu hL hK hv hsc hst har hinv) hu hv
    (fun z hz => .inl (hchg z hz)) hstep.2
    (hu.access _ _ _ _ (fun hz => c.ne_blocks (hchg _ hz).1 rfl) h.srW) (nK _ (by simp))

/-- Across the search's own stores together with a reallocation of nautil.c's
`workperm` pair (as `fmperm` may do). -/
theorem PAt.nautil (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {L : List block} (hL : ∀ z ∈ L, z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc)
    {cN cap' : Nat} {bN b' : block}
    (dN : DynAt m E.nautilWorkperm E.nautilWorkpermSz 4 cN bN)
    {W : block → Prop} (hu : Unch m m' W)
    (hW : ∀ z, W z → z ∈ L ∨ z = E.nautilWorkperm ∨ z = E.nautilWorkpermSz ∨ (0 < cN ∧ z = bN) ∨
      ¬ Mem.valid_block m z)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws], Keep m m' z)
    (dN' : DynAt m' E.nautilWorkperm E.nautilWorkpermSz 4 cap' b')
    (hrel : (cap' = cN ∧ b' = bN) ∨ ¬ Mem.valid_block m b')
    (hsc : ScalarsG m' st' nsp') (hst : StatsG m' S st' false)
    (har : ArraysG D.toDispatchRep m' S gl cl G st') (hinv : SInvG O G st') :
    PAt D m₀ m₁ m' S gl cl G bsr st' nsp' := by
  have hs := h.search
  have hval := h.valid c
  obtain ⟨nK, nG, nWk⟩ := hs.not_wr hL
  obtain ⟨cN0, bN0, dN0, nN0, uN0⟩ := hs.work.nautil
  have hcc : cN0 = cN := dN.same_cap dN0
  subst hcc
  have hbb : 0 < cN0 → bN0 = bN := fun hc => dN.same_block dN0 hc
  have hp := (S.keepG_perm.pairwise_iff (fun h => Ne.symm h)).2 hs.lit
  have hkd : S.keepG.Pairwise (· ≠ ·) := (List.pairwise_append.1 (List.pairwise_append.1 hp).1).1
  have hkN : ∀ y ∈ (fixedBlocks : List block) ++ dynPairs,
      y ≠ E.nautilWorkperm ∧ y ≠ E.nautilWorkpermSz := fun y hy =>
    ⟨(List.pairwise_append.1 hkd).2.2 y hy _ (by simp),
      (List.pairwise_append.1 hkd).2.2 y hy _ (by simp)⟩
  have hkL : ∀ y ∈ S.keepG, y ∈ S.blocksG D.toDispatchRep gl cl := fun y hy =>
    SLoc.mem_blocksG_lit (S.keepG_perm.subset (List.mem_append_left _ (List.mem_append_left _ hy)))
  have nB : ∀ y ∈ S.blocksG D.toDispatchRep gl cl, ¬ y ∈ L → y ≠ E.nautilWorkperm →
      y ≠ E.nautilWorkpermSz → ¬ W y := by
    intro y hy h1 h2 h3 hWy
    rcases hW y hWy with h4 | h4 | h4 | ⟨hc, h4⟩ | h4
    · exact h1 h4
    · exact h2 h4
    · exact h3 h4
    · exact nN0 hc (by rw [hbb hc, ← h4]; exact hy)
    · exact h4 (hval y hy)
  have nP : ∀ y ∈ (fixedBlocks : List block) ++ dynPairs, ¬ W y := fun y hy =>
    nB y (hkL y (List.mem_append_left _ hy)) (nK y (List.mem_append_left _ hy)) (hkN y hy).1
      (hkN y hy).2
  have nGl : ∀ y ∈ D.globs, ¬ W y := fun y hy =>
    nB y (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inr hy)))))) (nG y hy)
      (hs.globs_ne hy (.inr (.inr (.inr (.inr (by simp))))))
      (hs.globs_ne hy (.inr (.inr (.inr (.inr (by simp))))))
  have nT : ∀ y ∈ ([E.nautyBit, E.nautilBit, E.leftbit, E.tcnode0, S.bg, S.bUA] : List block),
      ¬ W y := by
    intro y hy
    have hy' : y ∈ S.keepG := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [SLoc.keepG]
    refine nB y (hkL y hy') (nK y hy') ?_ ?_
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> sep_ne hs.lit
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> sep_ne hs.lit
  have hwk0 : ∀ z, D.IsWork m z → ¬ W z := by
    intro z hz hWz
    have hzB : z ∉ S.blocksG D.toDispatchRep gl cl := hs.work.notin z hz
    rcases hW z hWz with h4 | h4 | h4 | ⟨hc, h4⟩ | h4
    · exact nWk z (.inl hz) h4
    · exact hzB (h4 ▸ SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp)))))))
    · exact hzB (h4 ▸ SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp)))))))
    · exact uN0 hc (by rw [hbb hc, ← h4]; exact hz)
    · exact h4 (D.isWork_valid hz)
  obtain ⟨hdw, back⟩ := D.work_unch hs.work.disp hu (fun z hz => nGl z (D.wglobs_sub z hz)) hwk0 hv
  have hnew : 0 < cap' → b' ∉ S.blocksG D.toDispatchRep gl cl ∧ ¬ D.IsWork m b' := by
    intro hc
    rcases hrel with ⟨rfl, rfl⟩ | hnv
    · rw [← hbb hc]; exact ⟨nN0 hc, uN0 hc⟩
    · exact ⟨fun hb => hnv (hval _ hb), fun hw => hnv (D.isWork_valid hw)⟩
  have hD := hs.dyns
  simp only [List.forall_mem_cons] at hK
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, -⟩ := hK
  have nD : ∀ y ∈ (dynPairs : List block), ¬ W y := fun y hy => nP y (List.mem_append_right _ hy)
  simp only [List.forall_mem_cons] at nD
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, -⟩ := nD
  have hs' : SearchAtG D.toDispatchRep m' S gl cl G st' false nsp' :=
    { hs with
      fixed := hs.fixed.unch hu fun z hz => nP z (List.mem_append_left _ hz)
      scalars := hsc
      stats := hst
      arrays := har
      dyns := { hD with
        workspace := hD.workspace.keep hu (nGl _ D.wsP_mem) (nGl _ D.wsS_mem) fun _ => k9
        active := hD.active.keep hu g1 g2 fun _ => k1
        fixedpts := hD.fixedpts.keep hu g3 g4 fun _ => k2
        workperm := hD.workperm.keep hu g5 g6 fun _ => k3
        firstlab := hD.firstlab.keep hu g7 g8 fun _ => k4
        canonlab := hD.canonlab.keep hu g9 g10 fun _ => k5
        firstcode := hD.firstcode.keep hu g11 g12 fun _ => k6
        canoncode := hD.canoncode.keep hu g13 g14 fun _ => k7
        firsttc := hD.firsttc.keep hu g15 g16 fun _ => k8 }
      work := ⟨hdw, ⟨cap', b', dN', fun hc => (hnew hc).1, fun hc hb => (hnew hc).2 (back b' hb)⟩,
        fun z hz => hs.work.notin z (back z hz)⟩
      tables := hs.tables.unch hu (nT _ (by simp)) (nT _ (by simp)) (nT _ (by simp))
        fun z hz _ => nGl z hz
      inv := hinv }
  have hwm : WorkMonoG D.toDispatchRep m m' := by
    rintro z (hz | ⟨c', hc, d⟩)
    · exact .inl (.inl (back z hz))
    · have e1 := d.same_block dN' hc
      have e2 := d.same_cap dN'
      subst e1; subst e2
      rcases hrel with ⟨rfl, rfl⟩ | hnv
      · exact .inl (.inr ⟨_, hc, dN⟩)
      · exact .inr hnv
  have hchg : ∀ z ∈ L, S.ChgG D.toDispatchRep gl cl z := fun z hz => hs.chg_wr (hL z hz)
  have hNchg : ∀ z, z = E.nautilWorkperm ∨ z = E.nautilWorkpermSz →
      S.ChgG D.toDispatchRep gl cl z := by
    rintro z (rfl | rfl)
    · exact ⟨SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp)))))), by sep_ne hs.lit,
        by sep_ne hs.lit⟩
    · exact ⟨SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp)))))), by sep_ne hs.lit,
        by sep_ne hs.lit⟩
  refine h.of_step c hs' hu hv (fun z hz => ?_) hwm (hu.access _ _ _ _ (fun hW' => ?_) h.srW)
    (nT _ (by simp))
  · rcases hW z hz with h4 | h4 | h4 | ⟨hc, h4⟩ | h4
    · exact .inl (hchg z h4)
    · exact .inl (hNchg z (.inl h4))
    · exact .inl (hNchg z (.inr h4))
    · exact .inr (.inr (.inr ⟨_, hc, h4 ▸ dN⟩))
    · exact .inr (.inl fun hv0 => h4 (h.frame.2 _ hv0))
  · rcases hW _ hW' with h4 | h4 | h4 | ⟨hc, h4⟩ | h4
    · exact c.ne_blocks (hchg _ h4).1 rfl
    · exact c.ne_blocks (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp))))))) h4.symm
    · exact c.ne_blocks (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp))))))) h4.symm
    · exact h.work_ne c (.inr ⟨_, hc, h4 ▸ dN⟩) rfl
    · exact h4 (h.grow1 _ c.valid1)

/-- Across a change confined to `sr`. -/
theorem PAt.sr (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    (hu : Unch m m' (· = bsr)) (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hw : Mem.valid_access m' .Mint32 bsr (zOfInt 0) .Freeable) :
    PAt D m₀ m₁ m' S gl cl G bsr st nsp := by
  have hs := h.search
  have hS : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, ¬ z = bsr := fun z hz => c.ne_blocks hz
  have hwk : ∀ z, IsWorkG D.toDispatchRep m z → ¬ z = bsr := fun z hz => h.work_ne c hz
  have hwm : WorkMonoG D.toDispatchRep m m' := fun z hz =>
    .inl ((hs.work.unch hu (fun z hz => hS z (SLoc.mem_blocksG_of _
      (.inr (.inr (.inr (.inr (.inr (D.wglobs_sub z hz))))))))
      ⟨hS _ (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp))))))),
        hS _ (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp)))))))⟩ hwk hv).2 z hz)
  exact h.of_step c (hs.unch hu hS hwk hv) hu hv (fun z hz => .inr (.inl (hz ▸ c.fresh))) hwm hw
    (hS _ (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inl (by simp)))))))

/-- What a call of one of `D`'s procedures leaves alone: the list entries of
`S.blocksG` and the graph's blocks outside the canonical store, and `D`'s globals
it does not write. -/
theorem PAt.stepNot (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {out : block → Prop} (hout : ∀ z, out z → z ∈ D.canonBlocks cl S.bc ∨ z = bsr) {y : block}
    (hy : y ∈ S.litG ∨ y ∈ D.graphBlocks gl S.bg ∨ (y ∈ D.globs ∧ y ∉ D.wglobs))
    (hyc : y ∉ D.canonBlocks cl S.bc) :
    ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) := by
  have hs := h.search
  have hB : y ∈ S.blocksG D.toDispatchRep gl cl := by
    rcases hy with hy | hy | hy
    · exact SLoc.mem_blocksG_lit hy
    · exact SLoc.mem_blocksG_of _ (.inl hy)
    · exact SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inr hy.1)))))
  rintro (h1 | h1 | h1 | h1)
  · rcases hout y h1 with h2 | h2
    · exact hyc h2
    · exact c.ne_blocks hB h2
  · rcases hy with hy | hy | hy
    · rcases SLoc.litG_parts (D := D.toDispatchRep) (gl := gl) (cl := cl) hy with h2 | h2 | h2 | h2 | h2
      · exact hs.globs_ne (D.wglobs_sub _ h1) (.inl h2) rfl
      · exact hs.globs_ne (D.wglobs_sub _ h1) (.inr (.inl h2)) rfl
      · exact hyc (h2 ▸ D.canonBlocks_head cl S.bc)
      · exact hs.globs_ne (D.wglobs_sub _ h1) (.inr (.inr (.inr (.inl h2)))) rfl
      · exact hs.globs_ne (D.wglobs_sub _ h1) (.inr (.inr (.inr (.inr h2)))) rfl
    · exact hs.globs_ne (D.wglobs_sub _ h1) (.inl hy) rfl
    · exact hy.2 h1
  · exact hs.work.notin y h1 hB
  · exact h1 (h.valid c y hB)

theorem PAt.stepNotE (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {out : block → Prop} (hout : ∀ z, out z → z ∈ D.canonBlocks cl S.bc ∨ z = bsr) {y : block}
    (hy : y ∈ envSearch) : ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) :=
  h.stepNot c hout (.inl (by unfold SLoc.litG; exact List.mem_append_right _ hy))
    (fun hc => h.search.canon_ne hc (.inr (.inr (.inr (.inl hy)))) rfl)

theorem PAt.stepNotV (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {out : block → Prop} (hout : ∀ z, out z → z ∈ D.canonBlocks cl S.bc ∨ z = bsr) {y : block}
    (hy : y ∈ [S.bl, S.bp, S.bo, S.bst] ∨
      y ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA]) :
    ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) :=
  h.stepNot c hout (.inl (by
      rcases hy with hy | hy <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy <;>
        rcases hy with h | h | h | h | h | h | h | h | h | h <;> simp [SLoc.litG, h]))
    (fun hc => h.search.canon_ne hc
      (hy.elim (fun h => .inr (.inl h)) (fun h => .inr (.inr (.inl h)))) rfl)

theorem PAt.stepNotG (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {out : block → Prop} (hout : ∀ z, out z → z ∈ D.canonBlocks cl S.bc ∨ z = bsr) {y : block}
    (hy : y ∈ D.graphBlocks gl S.bg) :
    ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) :=
  h.stepNot c hout (.inr (.inl hy)) (fun hc => h.search.canon_ne hc (.inl hy) rfl)

/-- Across a call of one of `D`'s procedures whose outputs are the canonical
store's blocks or `sr`. -/
theorem PAt.call (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {out : block → Prop} (hstep : D.Step m m' out)
    (hout : ∀ z, out z → z ∈ D.canonBlocks cl S.bc ∨ z = bsr)
    (hsc : ScalarsG m' st' nsp') (hst : StatsG m' S st' false)
    (har : ArraysG D.toDispatchRep m' S gl cl G st') (hinv : SInvG O G st')
    (hsrw : Mem.valid_access m' .Mint32 bsr (zOfInt 0) .Freeable) :
    PAt D m₀ m₁ m' S gl cl G bsr st' nsp' := by
  have hs := h.search
  have hval := h.valid c
  have nE : ∀ y ∈ envSearch, ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) :=
    fun y hy => h.stepNotE c hout hy
  have nV : ∀ y ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA],
      ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) :=
    fun y hy => h.stepNotV c hout (.inr hy)
  have nG : ∀ y ∈ D.globs, y ∉ D.wglobs →
      ¬ (out y ∨ y ∈ D.wglobs ∨ D.IsWork m y ∨ ¬ Mem.valid_block m y) :=
    fun y hy hyw => h.stepNot c hout (.inr (.inr ⟨hy, hyw⟩))
      (fun hc => hs.canon_ne hc (.inr (.inr (.inr (.inr hy)))) rfl)
  have hN : ∀ z, out z → z ≠ E.nautilWorkperm ∧ z ≠ E.nautilWorkpermSz ∧
      ∀ c' b, DynAt m E.nautilWorkperm E.nautilWorkpermSz 4 c' b → 0 < c' → z ≠ b := by
    intro z hz
    rcases hout z hz with h1 | h1
    · refine ⟨hs.canon_ne h1 (.inr (.inr (.inr (.inl (by simp))))),
        hs.canon_ne h1 (.inr (.inr (.inr (.inl (by simp))))), fun c' b d hc e => ?_⟩
      exact hs.work_not (.inr ⟨c', hc, e ▸ d⟩) (SLoc.mem_blocksG_of _ (.inr (.inr (.inl h1))))
    · subst h1
      refine ⟨fun e => c.ne_blocks (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl
          (by simp))))))) e.symm,
        fun e => c.ne_blocks (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl
          (by simp))))))) e.symm, fun c' b d hc e => h.work_ne c (.inr ⟨c', hc, e ▸ d⟩) rfl⟩
  obtain ⟨hwk, hwm⟩ := hs.work.step hstep hval
    (fun z hz => SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inr hz))))))
    hN ⟨SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp)))))),
      SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp))))))⟩
  have hs' : SearchAtG D.toDispatchRep m' S gl cl G st' false nsp' :=
    { hs with
      fixed := hs.fixed.unch hstep.unch fun z hz => nE z (by revert z; simp)
      scalars := hsc
      stats := hst
      arrays := har
      dyns := hs.dyns.unch hstep.unch fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        iterate 16 exact nE _ (by simp)
        iterate 8 exact nV _ (by simp)
        exact nG _ D.wsP_mem D.wsP_nw
        exact nG _ D.wsS_mem D.wsS_nw
        exact nV _ (by simp)
      work := hwk
      tables := hs.tables.unch hstep.unch (nE _ (by simp)) (nE _ (by simp)) (nE _ (by simp))
        fun z hz hzw => nG z hz hzw
      inv := hinv }
  refine h.of_step c hs' hstep.unch hstep.valid (fun z hz => ?_) hwm hsrw (nV _ (by simp))
  rcases hz with h1 | h1 | h1 | h1
  · rcases hout z h1 with h2 | h2
    · exact .inl (hs.chg_wr (.inr (.inr h2)))
    · exact .inr (.inl (h2 ▸ c.fresh))
  · exact .inl (hs.chg_globs (D.wglobs_sub _ h1))
  · exact .inr (.inr (.inl h1))
  · exact .inr (.inl fun hv0 => h1 (h.frame.2 _ hv0))

/-- `sr` is none of the blocks a call of one of `D`'s procedures may change, unless an output. -/
theorem PAt.bsrNot (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {out : block → Prop} (ho : ¬ out bsr) :
    ¬ (out bsr ∨ bsr ∈ D.wglobs ∨ D.IsWork m bsr ∨ ¬ Mem.valid_block m bsr) := by
  rintro (h1 | h1 | h1 | h1)
  · exact ho h1
  · exact c.ne_blocks
      (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inr (D.wglobs_sub _ h1))))))) rfl
  · exact h.work_ne c (.inl h1) rfl
  · exact h1 (h.grow1 _ c.valid1)

theorem PAt.arraysW (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {out : block → Prop} (hout : ∀ z, out z → z ∈ D.canonBlocks cl S.bc ∨ z = bsr) :
    ∀ z ∈ [S.bl, S.bp, S.bo, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws,
      E.fmptr], ¬ (out z ∨ z ∈ D.wglobs ∨ D.IsWork m z ∨ ¬ Mem.valid_block m z) := by
  intro z hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 3 exact h.stepNotV c hout (.inl (by simp))
  iterate 9 exact h.stepNotV c hout (.inr (by simp))
  exact h.stepNotE c hout (by simp)

/-- Across a call of one of `D`'s procedures writing at most `sr`. -/
theorem PAt.callSame (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {out : block → Prop} (hstep : D.Step m m' out) (hout : ∀ z, out z → z = bsr)
    (hsrw : Mem.valid_access m' .Mint32 bsr (zOfInt 0) .Freeable) :
    PAt D m₀ m₁ m' S gl cl G bsr st nsp := by
  have hs := h.search
  have ho : ∀ z, out z → z ∈ D.canonBlocks cl S.bc ∨ z = bsr := fun z hz => .inr (hout z hz)
  refine h.call c hstep ho (hs.scalars.unch hstep.unch fun z hz => h.stepNotE c ho (by revert z; simp))
    (hs.stats.unch hstep.unch (h.stepNotV c ho (.inl (by simp))))
    (hs.arrays.unch hstep.unch (h.arraysW c ho) (fun z hz => h.stepNotG c ho hz) ?_) hs.inv hsrw
  rintro z hz (h1 | h1 | h1 | h1)
  · exact c.ne_blocks (SLoc.mem_blocksG_of _ (.inr (.inr (.inl hz)))) (hout z h1)
  · exact hs.canon_ne hz (.inr (.inr (.inr (.inr (D.wglobs_sub _ h1))))) rfl
  · exact hs.work.notin z h1 (SLoc.mem_blocksG_of _ (.inr (.inr (.inl hz))))
  · exact h1 (h.valid c z (SLoc.mem_blocksG_of _ (.inr (.inr (.inl hz)))))

/-- The blocks of a call's arguments, from `S.blocksG` and `sr`. -/
theorem PAt.sep (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {bs : List block} (hd : bs.Pairwise (· ≠ ·))
    (hbs : ∀ z ∈ bs, (z ∈ S.blocksG D.toDispatchRep gl cl ∧ z ∉ D.globs ∧ z ≠ E.nautyBit ∧
      z ≠ E.nautilBit ∧ z ≠ E.leftbit) ∨ z = bsr) :
    D.Sep m bs := by
  have hs := h.search
  have hbG : ∀ z, z = bsr → z ∉ D.globs := fun z hz hg =>
    c.ne_blocks (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inr hg)))))) hz
  have hbE : ∀ y ∈ envSearch, y ≠ bsr := fun y hy =>
    c.ne_blocks (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl hy))))))
  refine ⟨hd, fun z hz => ?_, fun z hz hw => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · rcases hbs z hz with h1 | h1
    · exact h.valid c z h1.1
    · exact h1 ▸ h.grow1 _ c.valid1
  · rcases hbs z hz with h1 | h1
    · exact hs.work.notin z hw h1.1
    · exact h.work_ne c (.inl hw) h1
  · rcases hbs z hz with h1 | h1
    · exact h1.2.1
    · exact hbG z h1
  · rcases hbs z hz with h1 | h1
    · exact h1.2.2
    · subst h1
      exact ⟨(hbE _ (by simp)).symm, (hbE _ (by simp)).symm, (hbE _ (by simp)).symm⟩

/-- A call's argument block besides the graph's and the store's: one of `S`'s own
blocks or `sr`. -/
def ArgBlock (S : SLoc) (bsr y : block) : Prop :=
  (y ∈ [S.bl, S.bp, S.bo, S.bst] ∨
    y ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA]) ∨ y = bsr

theorem PAt.arg (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {y : block} (hy : ArgBlock S bsr y) :
    (∀ z ∈ D.graphBlocks gl S.bg, z ≠ y) ∧ (∀ z ∈ D.canonBlocks cl S.bc, z ≠ y) ∧
      ((y ∈ S.blocksG D.toDispatchRep gl cl ∧ y ∉ D.globs ∧ y ≠ E.nautyBit ∧
        y ≠ E.nautilBit ∧ y ≠ E.leftbit) ∨ y = bsr) := by
  have hs := h.search
  rcases hy with hy | rfl
  · have hl : y ∈ ([S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL,
        S.bFC, S.bCC, S.bTC, S.bUA] : List block) := by
      rcases hy with hy | hy <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy <;>
        rcases hy with h | h | h | h | h | h | h | h | h | h <;> simp [h]
    have hx := (List.pairwise_append.1 hs.lit).2.2 y hl
    refine ⟨fun z hz => hs.graph_ne hz (hy.elim .inl fun h => .inr (.inr (.inl h))),
      fun z hz => hs.canon_ne hz (by rcases hy with hy | hy; exact .inr (.inl hy); exact .inr (.inr (.inl hy))),
      .inl ⟨SLoc.mem_blocksG_of _ (by rcases hy with hy | hy; exact .inr (.inl hy); exact .inr (.inr (.inr (.inl hy)))),
        fun hg => hs.globs_ne hg (by rcases hy with hy | hy; exact .inr (.inl hy); exact .inr (.inr (.inr (.inl hy)))) rfl,
        hx _ (by simp), hx _ (by simp), hx _ (by simp)⟩⟩
  · have hB : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, z ≠ y := fun z hz => c.ne_blocks hz
    exact ⟨fun z hz => hB z (SLoc.mem_blocksG_of _ (.inl hz)),
      fun z hz => hB z (SLoc.mem_blocksG_of _ (.inr (.inr (.inl hz)))), .inr rfl⟩

/-- The graph's blocks and further argument blocks, as a call needs them. -/
theorem PAt.sepG (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {L : List block} (hL : L.Pairwise (· ≠ ·)) (ha : ∀ y ∈ L, ArgBlock S bsr y) :
    D.Sep m (D.graphBlocks gl S.bg ++ L) := by
  have hs := h.search
  have hg : (D.graphBlocks gl S.bg).Pairwise (· ≠ ·) :=
    hs.distinct.sublist (by simp only [SLoc.blocksG, List.append_assoc]; exact List.sublist_append_left _ _)
  refine h.sep c (List.pairwise_append.2 ⟨hg, hL, fun z hz y hy => (h.arg c (ha y hy)).1 z hz⟩)
    fun z hz => ?_
  rcases List.mem_append.1 hz with hz | hz
  · exact .inl ⟨SLoc.mem_blocksG_of _ (.inl hz),
      fun hg => hs.graph_ne hz (.inr (.inr (.inr (.inr hg)))) rfl,
      hs.graph_ne hz (.inr (.inr (.inr (.inl (by simp))))),
      hs.graph_ne hz (.inr (.inr (.inr (.inl (by simp))))),
      hs.graph_ne hz (.inr (.inr (.inr (.inl (by simp)))))⟩
  · exact (h.arg c (ha z hz)).2.2

/-- The graph's and the canonical store's blocks and further argument blocks. -/
theorem PAt.sepGC (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    {L : List block} (hL : L.Pairwise (· ≠ ·)) (ha : ∀ y ∈ L, ArgBlock S bsr y) :
    D.Sep m (D.graphBlocks gl S.bg ++ D.canonBlocks cl S.bc ++ L) := by
  have hs := h.search
  have hg : (D.graphBlocks gl S.bg).Pairwise (· ≠ ·) :=
    hs.distinct.sublist (by simp only [SLoc.blocksG, List.append_assoc]; exact List.sublist_append_left _ _)
  have hc : (D.canonBlocks cl S.bc).Pairwise (· ≠ ·) :=
    hs.distinct.sublist (by
      simp only [SLoc.blocksG, List.append_assoc]
      exact ((List.sublist_append_left _ _).trans (List.sublist_append_right _ _)).trans
        (List.sublist_append_right _ _))
  refine h.sep c (List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨hg, hc,
      fun z hz y hy => hs.graph_ne hz (.inr (.inl hy))⟩, hL, fun z hz y hy => ?_⟩) fun z hz => ?_
  · rcases List.mem_append.1 hz with hz | hz
    · exact (h.arg c (ha y hy)).1 z hz
    · exact (h.arg c (ha y hy)).2.1 z hz
  · rcases List.mem_append.1 hz with hz | hz
    · rcases List.mem_append.1 hz with hz | hz
      · exact .inl ⟨SLoc.mem_blocksG_of _ (.inl hz),
          fun hg => hs.graph_ne hz (.inr (.inr (.inr (.inr hg)))) rfl,
          hs.graph_ne hz (.inr (.inr (.inr (.inl (by simp))))),
          hs.graph_ne hz (.inr (.inr (.inr (.inl (by simp))))),
          hs.graph_ne hz (.inr (.inr (.inr (.inl (by simp)))))⟩
      · exact .inl ⟨SLoc.mem_blocksG_of _ (.inr (.inr (.inl hz))),
          fun hg => hs.canon_ne hz (.inr (.inr (.inr (.inr hg)))) rfl,
          hs.canon_ne hz (.inr (.inr (.inr (.inl (by simp))))),
          hs.canon_ne hz (.inr (.inr (.inr (.inl (by simp))))),
          hs.canon_ne hz (.inr (.inr (.inr (.inl (by simp)))))⟩
    · exact (h.arg c (ha z hz)).2.2

/-- What a call of one of `D`'s procedures needs of the state around it. -/
theorem _root_.NautyVerified.Proofs.Search.SearchAtG.ctx {D : DispatchRep ge O} {gl : D.GLoc} {cl : D.CLoc} {pre : Bool} (h : SearchAtG D m S gl cl G st pre nsp) :
    D.Ctx m n S.M :=
  ⟨h.work.disp, h.tables.disp, h.tables.env, h.n0, h.nlt, h.M1, h.Mlt, h.nM⟩

end Generic

end NautyVerified.Proofs.Search.Processnode
