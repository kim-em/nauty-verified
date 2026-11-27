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
  [S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC,
   S.bTC, S.bUA]

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
   Block.naugraphBytecount, Block.leftbit]

theorem SLoc.blocks_split (S : SLoc) : S.blocks = S.vars ++ globs := rfl

/-- `S`'s own blocks differ from every global. -/
theorem SLoc.vars_ne {S : SLoc} (hd : S.blocks.Pairwise (· ≠ ·)) :
    ∀ a ∈ S.vars, ∀ b ∈ globs, a ≠ b := by
  rw [SLoc.blocks_split, List.pairwise_append] at hd
  exact hd.2.2

/-- `¬ z ∈ L` for a global `z` and `L` within `S.wr`. -/
macro "not_wr " hL:ident hv:ident : tactic =>
  `(tactic| (
    intro hzL
    have hw := $hL _ hzL
    rcases List.mem_append.1 hw with h | h
    · exact absurd h (by decide)
    · exact $hv _ (SLoc.wrV_sub _ _ h) _ (by decide) rfl))

theorem SearchAt.rebuild {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st st' : Search n}
    {pre nsp pre' nsp' : Bool} (h : SearchAt m S ctx st pre nsp) {L : List block}
    (hu : Unch m m' (· ∈ L)) (hL : ∀ z ∈ L, z ∈ S.wr)
    (hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC], Keep m m' z)
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
        Program.Block.nautyCanoncodeSz, Program.Block.nautyFirsttc, Program.Block.nautyFirsttcSz],
        ¬ z ∈ L := by
      intro z hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> not_wr hL hv
    simp only [List.forall_mem_cons] at hg hK
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, -⟩ := hg
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, -⟩ := hK
    exact { hD with
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
      fixed := h.fixed.unch hu fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> not_wr hL hv
      scalars := hsc
      stats := hst
      arrays := har
      dyns := hdy
      work := h.work.unch hu (fun z hz => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> not_wr hL hv)
        fun z hz hzL => h.work_not hz (SLoc.wr_sub S z (hL z hzL))
      tables := h.tables.unch hu fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> not_wr hL hv
      inv := hinv }

end NautyVerified.Proofs.Search
