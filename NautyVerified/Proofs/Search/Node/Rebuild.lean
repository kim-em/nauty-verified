import NautyVerified.Proofs.Search.Frame

/-!
# Rebuilding `SearchAt` after the search's own writes

`SLoc.wr S`: the blocks the search's statements write directly: nauty.c's
scalars and `fmptr`, the caller's arrays and `statsblk`, the workspace and
nauty.c's `DYNALLSTAT` arrays. `SearchAt.rebuild`: after changes confined to
some of these (keeping the `DYNALLSTAT` blocks' headers), new `Scalars`,
`Stats`, `Arrays` and `SInv` give `SearchAt` again; the rest moves across.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open NautyVerified NautyVerified.Logic NautyVerified.Program
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty

/-- The blocks the search's own statements write. -/
def wrG : List block :=
  [Block.gcaFirst, Block.gcaCanon, Block.noncheaplevel, Block.allsamelevel, Block.eqlevFirst,
   Block.eqlevCanon, Block.compCanon, Block.samerows, Block.canonlevel, Block.stabvertex,
   Block.cosetindex, Block.needshortprune, Block.fmptr]

def SLoc.wrV (S : SLoc) : List block :=
  [S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC]

def SLoc.wr (S : SLoc) : List block := wrG ++ S.wrV

theorem SLoc.wr_sub (S : SLoc) : ∀ z ∈ S.wr, z ∈ S.blocks := by
  intro z hz
  simp only [SLoc.wr, wrG, SLoc.wrV, List.mem_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hz
  rcases hz with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [SLoc.blocks]

/-- The blocks of `S` that are not globals. -/
def SLoc.vars (S : SLoc) : List block :=
  [S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA]

theorem SLoc.wrV_sub (S : SLoc) : ∀ y ∈ S.wrV, y ∈ S.vars := by
  intro y hy
  simp only [SLoc.wrV, List.mem_cons, List.mem_nil_iff, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> simp [SLoc.vars]

/-- The globals and tables among `S.blocks`. -/
def globs : List block :=
  [Block.getcanon, Block.digraph, Block.writeautoms, Block.domarkers, Block.doschreier,
   Block.tcLevel, Block.invarproc, Block.usernodeproc, Block.userlevelproc, Block.usercanonproc,
   Block.userautomproc, Block.dispatch, Block.orbits, Block.m, Block.n, Block.g, Block.canong,
   Block.stats, Block.gcaFirst, Block.gcaCanon, Block.noncheaplevel, Block.allsamelevel,
   Block.eqlevFirst, Block.eqlevCanon, Block.compCanon, Block.samerows, Block.canonlevel,
   Block.stabvertex, Block.cosetindex, Block.needshortprune, Block.tcnode0, Block.allocM,
   Block.workspace, Block.worktop, Block.fmptr, Block.killRequest, Program.Block.nautyActive,
   Program.Block.nautyActiveSz, Program.Block.nautyFixedpts, Program.Block.nautyFixedptsSz,
   Program.Block.nautyWorkperm, Program.Block.nautyWorkpermSz, Program.Block.nautyFirstlab,
   Program.Block.nautyFirstlabSz, Program.Block.nautyCanonlab, Program.Block.nautyCanonlabSz,
   Program.Block.nautyFirstcode, Program.Block.nautyFirstcodeSz, Program.Block.nautyCanoncode,
   Program.Block.nautyCanoncodeSz, Program.Block.nautyFirsttc, Program.Block.nautyFirsttcSz,
   Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
   Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz, Block.nautilWorkperm,
   Block.nautilWorkpermSz, Program.Block.nautyBit, Block.naugraphBit, Block.nautilBit,
   Block.naugraphBytecount, Block.leftbit, Block.mininvarlevel, Block.maxinvarlevel,
   Block.invararg, Block.naugraphDnwork, Block.naugraphDnworkSz]

theorem SLoc.blocks_split (S : SLoc) : S.blocks = S.vars ++ globs := rfl

/-- `S`'s own blocks differ from every global. -/
theorem SLoc.vars_ne {S : SLoc} (hd : S.blocks.Pairwise (· ≠ ·)) :
    ∀ a ∈ S.vars, ∀ b ∈ globs, a ≠ b := by
  rw [SLoc.blocks_split, List.pairwise_append] at hd
  exact hd.2.2

/-- Globals not written directly are outside any `L` within `S.wr`. -/
theorem not_wr_all {S : SLoc} {L : List block} (hv : ∀ a ∈ S.vars, ∀ b ∈ globs, a ≠ b)
    (hL : ∀ z ∈ L, z ∈ S.wr) {l : List block} (h1 : ∀ z ∈ l, z ∉ wrG) (h2 : ∀ z ∈ l, z ∈ globs) :
    ∀ z ∈ l, ¬ z ∈ L := by
  intro z hz hzL
  rcases List.mem_append.1 (hL z hzL) with h | h
  · exact h1 z hz h
  · exact hv _ (SLoc.wrV_sub _ _ h) _ (h2 z hz) rfl

theorem SearchAt.rebuild {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st st' : Search n}
    {pre nsp pre' nsp' : Bool} (h : SearchAt m S ctx st pre nsp) {L : List block}
    (hu : Unch m m' (· ∈ L)) (hL : ∀ z ∈ L, z ∈ S.wr)
    (hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws], Keep m m' z)
    (hsc : Scalars m' st' nsp') (hst : Stats m' S st' pre') (har : Arrays m' S ctx st')
    (hinv : SInv st') : SearchAt m' S ctx st' pre' nsp' := by
  have hd := h.distinct
  have hv := SLoc.vars_ne hd
  have nW : ∀ z ∈ S.blocks, z ∉ S.wr → ¬ z ∈ L := fun z _ hz hzL => hz (hL z hzL)
  have hdy : Dyns n m' S := by
    have hD := h.dyns
    have hg : ∀ z ∈ [Program.Block.nautyActive, Program.Block.nautyActiveSz,
        Program.Block.nautyFixedpts, Program.Block.nautyFixedptsSz, Program.Block.nautyWorkperm,
        Program.Block.nautyWorkpermSz, Program.Block.nautyFirstlab, Program.Block.nautyFirstlabSz,
        Program.Block.nautyCanonlab, Program.Block.nautyCanonlabSz, Program.Block.nautyFirstcode,
        Program.Block.nautyFirstcodeSz, Program.Block.nautyCanoncode,
        Program.Block.nautyCanoncodeSz, Program.Block.nautyFirsttc, Program.Block.nautyFirsttcSz,
        Block.naugraphDnwork, Block.naugraphDnworkSz],
        ¬ z ∈ L := not_wr_all hv hL (by decide) (by decide)
    simp only [List.forall_mem_cons] at hg hK
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, -⟩ := hg
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, -⟩ := hK
    exact { hD with
      workspace := hD.workspace.keep hu g17 g18 fun _ => k9
      active := hD.active.keep hu g1 g2 fun _ => k1
      fixedpts := hD.fixedpts.keep hu g3 g4 fun _ => k2
      workperm := hD.workperm.keep hu g5 g6 fun _ => k3
      firstlab := hD.firstlab.keep hu g7 g8 fun _ => k4
      canonlab := hD.canonlab.keep hu g9 g10 fun _ => k5
      firstcode := hD.firstcode.keep hu g11 g12 fun _ => k6
      canoncode := hD.canoncode.keep hu g13 g14 fun _ => k7
      firsttc := hD.firsttc.keep hu g15 g16 fun _ => k8 }
  exact
    { h with
      fixed := h.fixed.unch hu (not_wr_all hv hL (by decide) (by decide))
      scalars := hsc
      stats := hst
      arrays := har
      dyns := hdy
      work := h.work.unch hu (not_wr_all hv hL (by decide) (by decide))
        fun z hz hzL => h.work_not hz (SLoc.wr_sub S z (hL z hzL))
      tables := h.tables.unch hu (not_wr_all hv hL (by decide) (by decide))
      inv := hinv }

/-- nauty.c's static scalars. -/
def scalG : List block :=
  [Block.gcaFirst, Block.gcaCanon, Block.noncheaplevel, Block.allsamelevel, Block.eqlevFirst,
   Block.eqlevCanon, Block.compCanon, Block.samerows, Block.canonlevel, Block.stabvertex,
   Block.cosetindex, Block.needshortprune]

theorem scalG_globs : ∀ y ∈ scalG, y ∈ globs := by decide

theorem scalG_wr (S : SLoc) : ∀ y ∈ scalG, y ∈ S.wr := fun y hy =>
  List.mem_append.2 (.inl (by revert y; decide))

/-- After writes to scalars only: new `Scalars`, and the other parts for the new state. -/
theorem SearchAt.setScalars {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st st' : Search n}
    {pre nsp pre' nsp' : Bool} (h : SearchAt m S ctx st pre nsp) {L : List block}
    (hu : Unch m m' (· ∈ L)) (hL : ∀ z ∈ L, z ∈ scalG) (hsc : Scalars m' st' nsp')
    (har : Arrays m S ctx st') (hst : Stats m S st' pre') (hinv : SInv st') :
    SearchAt m' S ctx st' pre' nsp' := by
  have hv := SLoc.vars_ne h.distinct
  have nv : ∀ z ∈ S.vars, ¬ z ∈ L := fun z hz hzL =>
    hv z hz z (scalG_globs z (hL z hzL)) rfl
  have nf : ¬ Block.fmptr ∈ L := fun hzL => absurd (hL _ hzL) (by decide)
  refine h.rebuild hu (fun z hz => scalG_wr S z (hL z hz)) (fun z hz => Keep.unch hu
      (nv z (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
                rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [SLoc.vars])))
    hsc (hst.unch hu (nv _ (by simp [SLoc.vars]))) (har.unch hu ?_) hinv
  intro z hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals first | exact nf | exact nv _ (by simp [SLoc.vars])

/-! ### For any dispatch representation

`wrEnv` and `S.wrVG`: the shared globals and `S`'s blocks the search's own
statements write; besides them it may write the canonical store's blocks.
`SearchAtG.rebuild`: after changes confined to these (keeping the
`DYNALLSTAT` blocks' headers, and every valid block valid), new
`ScalarsG`, `StatsG`, `ArraysG` and `SInvG` give `SearchAtG` again. -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

/-- The shared globals the search's own statements write. -/
abbrev wrEnv : List block :=
  [E.gcaFirst, E.gcaCanon, E.noncheaplevel, E.allsamelevel, E.eqlevFirst, E.eqlevCanon,
   E.compCanon, E.samerows, E.canonlevel, E.stabvertex, E.cosetindex, E.needshortprune, E.fmptr]

/-- `S`'s blocks the search's own statements write, besides the store's. -/
abbrev SLoc.wrVG (S : SLoc) : List block :=
  [S.bl, S.bp, S.bo, S.bst, S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC]

/-- The `DYNALLSTAT` pairs of nauty.c. -/
abbrev dynPairs : List block :=
  [E.nautyActive, E.nautyActiveSz, E.nautyFixedpts, E.nautyFixedptsSz, E.nautyWorkperm,
   E.nautyWorkpermSz, E.nautyFirstlab, E.nautyFirstlabSz, E.nautyCanonlab, E.nautyCanonlabSz,
   E.nautyFirstcode, E.nautyFirstcodeSz, E.nautyCanoncode, E.nautyCanoncodeSz, E.nautyFirsttc,
   E.nautyFirsttcSz]

/-- The list entries of `S.blocksG` the search's own statements do not write. -/
abbrev SLoc.keepG (S : SLoc) : List block :=
  fixedBlocks ++ dynPairs ++
    [E.nautilWorkperm, E.nautilWorkpermSz, E.nautyBit, E.nautilBit, E.leftbit, E.tcnode0, S.bg,
     S.bUA]

theorem SLoc.keepG_perm (S : SLoc) :
    (S.keepG ++ (wrEnv ++ S.wrVG) ++ [S.bc]).Perm S.litG := by perm_lit

theorem SLoc.wr_mem {S : SLoc} {cl : D.CLoc} {z : block}
    (hz : z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc) :
    z ∈ [S.bl, S.bp, S.bo, S.bst] ∨ z ∈ D.canonBlocks cl S.bc ∨
      z ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ∨ z ∈ envSearch := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hz
  iterate 13 exact .inr (.inr (.inr (by simp)))
  iterate 4 exact .inl (by simp)
  iterate 9 exact .inr (.inr (.inl (by simp)))
  exact .inr (.inl hz)

/-- The blocks of `S.blocksG` the search's own statements do not write lie
outside a list of written blocks. -/
theorem SearchAtG.not_wr {n : Nat} {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {pre nsp : Bool} (h : SearchAtG D m S gl cl G st pre nsp)
    {L : List block} (hL : ∀ z ∈ L, z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc) :
    (∀ y ∈ S.keepG, ¬ y ∈ L) ∧ (∀ y ∈ D.globs, ¬ y ∈ L) ∧
      (∀ z, IsWorkG D m z → ¬ z ∈ L) := by
  have fE : ∀ y ∈ (fixedBlocks : List block), y ∈ envSearch := by simp
  have pE : ∀ y ∈ (dynPairs : List block), y ∈ envSearch := by simp
  have hp := (S.keepG_perm.pairwise_iff (fun h => Ne.symm h)).2 h.lit
  have hd := (List.pairwise_append.1 (List.pairwise_append.1 hp).1).2.2
  refine ⟨fun y hy hyL => ?_, fun y hy hyL => ?_, fun z hz hzL => ?_⟩
  · rcases hL _ hyL with hz | hz | hz
    · exact hd y hy y (List.mem_append_left _ hz) rfl
    · exact hd y hy y (List.mem_append_right _ hz) rfl
    · refine h.canon_ne hz (y := y) ?_ rfl
      rcases List.mem_append.1 hy with hy | hy
      · rcases List.mem_append.1 hy with hy | hy
        · exact .inr (.inr (.inr (.inl (fE y hy))))
        · exact .inr (.inr (.inr (.inl (pE y hy))))
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        iterate 6 exact .inr (.inr (.inr (.inl (by simp))))
        · exact .inl (D.graphBlocks_head gl S.bg)
        · exact .inr (.inr (.inl (by simp)))
  · rcases SLoc.wr_mem (hL _ hyL) with hz | hz | hz | hz
    · exact h.globs_ne hy (.inr (.inl hz)) rfl
    · exact h.globs_ne hy (.inr (.inr (.inl hz))) rfl
    · exact h.globs_ne hy (.inr (.inr (.inr (.inl hz)))) rfl
    · exact h.globs_ne hy (.inr (.inr (.inr (.inr hz)))) rfl
  · refine h.work_not hz (SLoc.mem_blocksG_of D ?_)
    rcases SLoc.wr_mem (hL _ hzL) with hz | hz | hz | hz
    · exact .inr (.inl hz)
    · exact .inr (.inr (.inl hz))
    · exact .inr (.inr (.inr (.inl hz)))
    · exact .inr (.inr (.inr (.inr (.inl hz))))

theorem SearchAtG.rebuild {n : Nat} {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st st' : SearchState n (O.Canon n)} {pre nsp pre' nsp' : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {L : List block} (hu : Unch m m' (· ∈ L))
    (hL : ∀ z ∈ L, z ∈ wrEnv ∨ z ∈ S.wrVG ∨ z ∈ D.canonBlocks cl S.bc)
    (hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws], Keep m m' z)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hsc : ScalarsG m' st' nsp') (hst : StatsG m' S st' pre') (har : ArraysG D m' S gl cl G st')
    (hinv : SInvG O G st') : SearchAtG D m' S gl cl G st' pre' nsp' := by
  obtain ⟨nK, nG, nW⟩ := h.not_wr hL
  have nF : ∀ z ∈ fixedBlocks, ¬ z ∈ L := fun z hz =>
    nK z (List.mem_append_left _ (List.mem_append_left _ hz))
  have nP : ∀ z ∈ dynPairs, ¬ z ∈ L := fun z hz =>
    nK z (List.mem_append_left _ (List.mem_append_right _ hz))
  have nR : ∀ z ∈ [E.nautilWorkperm, E.nautilWorkpermSz, E.nautyBit, E.nautilBit, E.leftbit,
      E.tcnode0, S.bg, S.bUA], ¬ z ∈ L := fun z hz => nK z (List.mem_append_right _ hz)
  simp only [List.forall_mem_cons] at nP nR hK
  have hD := h.dyns
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, -⟩ := nP
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, -⟩ := hK
  have hdy : DynsG D n m' S := { hD with
    workspace := hD.workspace.keep hu (nG _ D.wsP_mem) (nG _ D.wsS_mem) fun _ => k9
    active := hD.active.keep hu g1 g2 fun _ => k1
    fixedpts := hD.fixedpts.keep hu g3 g4 fun _ => k2
    workperm := hD.workperm.keep hu g5 g6 fun _ => k3
    firstlab := hD.firstlab.keep hu g7 g8 fun _ => k4
    canonlab := hD.canonlab.keep hu g9 g10 fun _ => k5
    firstcode := hD.firstcode.keep hu g11 g12 fun _ => k6
    canoncode := hD.canoncode.keep hu g13 g14 fun _ => k7
    firsttc := hD.firsttc.keep hu g15 g16 fun _ => k8 }
  exact
    { h with
      fixed := h.fixed.unch hu nF
      scalars := hsc
      stats := hst
      arrays := har
      dyns := hdy
      work := (h.work.unch hu (fun z hz => nG z (D.wglobs_sub z hz)) ⟨nR.1, nR.2.1⟩ nW hv).1
      tables := h.tables.unch hu nR.2.2.1 nR.2.2.2.1 nR.2.2.2.2.1 fun z hz _ => nG z hz
      inv := hinv }

end Generic

end NautyVerified.Proofs.Search
