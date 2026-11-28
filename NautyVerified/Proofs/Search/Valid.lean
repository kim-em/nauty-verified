import NautyVerified.Proofs.Search.Step

/-!
# The blocks of `SearchAt` are valid

Every block of `S.blocks` but the `userautomproc` target `bUA` and the
target-cell list head `tcnode0` carries a load or an access in `SearchAt`, so
it is valid. (`tcnode0` is described by `TcAt`, outside `SearchAt`; nothing
reads memory at `bUA`.)
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Spec NautyVerified.Source
open Hex.GraphIso.Nauty
open NautyVerified.Proofs.Alloc (DynAt)

theorem FieldAt.valid {m : mem} {chunk : memory_chunk} {b : block} {off : Int} {v : val}
    (h : FieldAt m chunk b off v) : Mem.valid_block m b :=
  Alloc.valid_of_access h.writable

theorem dyn_valid_p {m : mem} {bp bs : block} {c cap : Nat} {b : block}
    (h : DynAt m bp bs c cap b) : Mem.valid_block m bp :=
  Alloc.valid_of_access h.bpW

theorem dyn_valid_s {m : mem} {bp bs : block} {c cap : Nat} {b : block}
    (h : DynAt m bp bs c cap b) : Mem.valid_block m bs :=
  Alloc.valid_of_access h.bsW

theorem valid_of_load {m : mem} {chunk : memory_chunk} {b : block} {ofs : Z} {v : val}
    (h : Mem.load chunk m b ofs = some v) : Mem.valid_block m b :=
  Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h)


/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : Cfrontend.Clight.genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

/-- Every block of `S.blocksG` but `bUA` and `tcnode0` is valid. -/
theorem SearchAtG.valid_blocks {n : Nat} {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) :
    ∀ z ∈ S.blocksG D gl cl, z ≠ S.bUA → z ≠ E.tcnode0 → Mem.valid_block m z := by
  have hn := h.n0
  have hM := h.M1
  have hF := h.fixed
  have hS := h.scalars
  have hT := h.stats
  have hA := h.arrays
  have hD := h.dyns
  have hB := h.tables
  obtain ⟨_, _, dN, -⟩ := h.work.nautil
  intro z hz hua htc
  simp only [SLoc.blocksG, List.mem_append] at hz
  rcases hz with ((((hz | hz) | hz) | hz) | hz) | hz
  · exact D.graph_valid hA.graph hn hM z hz
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ArrayAt.valid hA.lab hn
    · exact ArrayAt.valid hA.ptn hn
    · exact ArrayAt.valid hA.orbits hn
    · exact hT.numorbits.valid
  · exact D.canon_valid hA.canong hn hM z hz
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨_, hw, -⟩ := hA.autos.arr; exact ArrayAt.valid hw (Nat.mul_pos (by decide) hM)
    · obtain ⟨_, ha, -⟩ := hA.active; exact ArrayAt.valid ha hM
    · obtain ⟨_, hf, -⟩ := hA.fixedpts; exact ArrayAt.valid hf hM
    · obtain ⟨_, hw⟩ := hA.workperm; exact ArrayAt.valid hw hn
    · exact ArrayAt.valid hA.firstlab hn
    · exact ArrayAt.valid hA.canonlab hn
    · exact ArrayAt.valid hA.firstcode (by omega)
    · exact ArrayAt.valid hA.canoncode (by omega)
    · exact ArrayAt.valid hA.firsttc (by omega)
    · exact absurd rfl hua
  · simp only [envSearch, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact hF.getcanon.valid
    · exact hF.digraph.valid
    · exact hF.writeautoms.valid
    · exact hF.domarkers.valid
    · exact hF.doschreier.valid
    · exact hF.tcLevel.valid
    · exact hF.invarproc.valid
    · exact hF.usernodeproc.valid
    · exact hF.userlevelproc.valid
    · exact hF.usercanonproc.valid
    · exact hF.userautomproc.valid
    · exact hF.dIsautom.valid
    · exact hF.orbits.valid
    · exact hF.mm.valid
    · exact hF.nn.valid
    · exact hF.g.valid
    · exact hF.canong.valid
    · exact hF.stats.valid
    · exact hS.gcaFirst.valid
    · exact hS.gcaCanon.valid
    · exact hS.noncheaplevel.valid
    · exact hS.allsamelevel.valid
    · exact hS.eqlevFirst.valid
    · exact hS.eqlevCanon.valid
    · exact hS.compCanon.valid
    · exact hS.samerows.valid
    · exact hS.canonlevel.valid
    · exact hS.stabvertex.valid
    · exact hS.cosetindex.valid
    · exact hS.needshortprune.valid
    · exact absurd rfl htc
    · exact hF.allocM.valid
    · exact hF.workspace.valid
    · exact hF.worktop.valid
    · exact hA.autos.fmptr.valid
    · exact Alloc.valid_of_access hF.kill
    · exact dyn_valid_p hD.active
    · exact dyn_valid_s hD.active
    · exact dyn_valid_p hD.fixedpts
    · exact dyn_valid_s hD.fixedpts
    · exact dyn_valid_p hD.workperm
    · exact dyn_valid_s hD.workperm
    · exact dyn_valid_p hD.firstlab
    · exact dyn_valid_s hD.firstlab
    · exact dyn_valid_p hD.canonlab
    · exact dyn_valid_s hD.canonlab
    · exact dyn_valid_p hD.firstcode
    · exact dyn_valid_s hD.firstcode
    · exact dyn_valid_p hD.canoncode
    · exact dyn_valid_s hD.canoncode
    · exact dyn_valid_p hD.firsttc
    · exact dyn_valid_s hD.firsttc
    · exact dyn_valid_p dN
    · exact dyn_valid_s dN
    · exact valid_of_load (hB.env.nautyBit 0 (by decide))
    · exact valid_of_load (hB.env.nautilBit 0 (by decide))
    · exact valid_of_load (hB.env.left 0 (by decide))
    · obtain ⟨_, hv⟩ := hF.mininv; exact hv.valid
    · obtain ⟨_, hv⟩ := hF.maxinv; exact hv.valid
    · obtain ⟨_, hv⟩ := hF.invarg; exact hv.valid
  · exact D.globs_valid h.work.disp z hz

/-- Every block of `S.blocksG`, given `bUA` and `tcnode0`. -/
theorem SearchAtG.valid_all {n : Nat} {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) (hvU : Mem.valid_block m S.bUA)
    (hvT : Mem.valid_block m E.tcnode0) : ∀ z ∈ S.blocksG D gl cl, Mem.valid_block m z := by
  intro z hz
  by_cases hu : z = S.bUA
  · exact hu ▸ hvU
  by_cases ht : z = E.tcnode0
  · exact ht ▸ hvT
  exact h.valid_blocks z hz hu ht

/-- `SearchAtG` across a call of one of `D`'s procedures whose outputs `out`
are none of the blocks of `S` and no scratch block in use: the state is unchanged,
and the scratch blocks in use afterwards were in use or are new. -/
theorem SearchAtG.dstep {n : Nat} {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) (hvU : Mem.valid_block m S.bUA)
    (hvT : Mem.valid_block m E.tcnode0) {out : block → Prop} (hs : D.Step m m' out)
    (hout : ∀ z, out z → z ∉ S.blocksG D gl cl ∧ ¬ IsWorkG D m z) :
    SearchAtG D m' S gl cl G st pre nsp ∧ WorkMonoG D m m' := by
  have hv := h.valid_all hvU hvT
  have hu := hs.unch
  have key : ∀ z ∈ S.blocksG D gl cl, z ∉ D.globs →
      ¬ (out z ∨ z ∈ D.wglobs ∨ D.IsWork m z ∨ ¬ Mem.valid_block m z) := by
    rintro z hz hg (ho | hw | hi | hn)
    · exact (hout z ho).1 hz
    · exact hg (D.wglobs_sub z hw)
    · exact h.work_not (.inl hi) hz
    · exact hn (hv z hz)
  have kg : ∀ z ∈ D.globs, z ∉ D.wglobs →
      ¬ (out z ∨ z ∈ D.wglobs ∨ D.IsWork m z ∨ ¬ Mem.valid_block m z) := by
    rintro z hz hnw (ho | hw | hi | hn)
    · exact (hout z ho).1 (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inr hz))))))
    · exact hnw hw
    · exact (D.isWork_globs h.work.disp hi).1 hz
    · exact hn (D.globs_valid h.work.disp z hz)
  have hE : ∀ z ∈ envSearch, ¬ (out z ∨ z ∈ D.wglobs ∨ D.IsWork m z ∨ ¬ Mem.valid_block m z) :=
    fun z hz => key z (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl hz))))))
      fun hg => h.globs_ne hg (.inr (.inr (.inr (.inr hz)))) rfl
  have hV : ∀ z ∈ [S.bl, S.bp, S.bo, S.bst],
      ¬ (out z ∨ z ∈ D.wglobs ∨ D.IsWork m z ∨ ¬ Mem.valid_block m z) :=
    fun z hz => key z (SLoc.mem_blocksG_of D (.inr (.inl hz)))
      fun hg => h.globs_ne hg (.inr (.inl hz)) rfl
  have hV' : ∀ z ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA],
      ¬ (out z ∨ z ∈ D.wglobs ∨ D.IsWork m z ∨ ¬ Mem.valid_block m z) :=
    fun z hz => key z (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inl hz)))))
      fun hg => h.globs_ne hg (.inr (.inr (.inr (.inl hz)))) rfl
  have mN : E.nautilWorkperm ∈ S.blocksG D gl cl ∧ E.nautilWorkpermSz ∈ S.blocksG D gl cl :=
    ⟨SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl (by simp)))))),
      SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl (by simp))))))⟩
  obtain ⟨hw', hmono⟩ := h.work.step hs hv
    (fun z hz => SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inr hz))))))
    (fun z ho => ⟨fun e => (hout z ho).1 (e ▸ mN.1), fun e => (hout z ho).1 (e ▸ mN.2),
      fun c b d hc e => (hout z ho).2 (e ▸ .inr ⟨c, hc, d⟩)⟩) mN
  refine ⟨{ h with
    fixed := h.fixed.unch hu fun z hz => hE z (by revert z; simp)
    scalars := h.scalars.unch hu fun z hz => hE z (by revert z; simp)
    stats := h.stats.unch hu (hV _ (by simp))
    arrays := h.arrays.unch hu (fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        iterate 3 exact hV _ (by simp)
        iterate 9 exact hV' _ (by simp)
        exact hE _ (by simp))
      (fun z hz => key z (SLoc.mem_blocksG_of D (.inl hz)) fun hg => h.globs_ne hg (.inl hz) rfl)
      (fun z hz => key z (SLoc.mem_blocksG_of D (.inr (.inr (.inl hz))))
        fun hg => h.globs_ne hg (.inr (.inr (.inl hz))) rfl)
    dyns := h.dyns.unch hu fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      iterate 16 exact hE _ (by simp)
      iterate 8 exact hV' _ (by simp)
      exact kg _ D.wsP_mem D.wsP_nw
      exact kg _ D.wsS_mem D.wsS_nw
      exact hV' _ (by simp)
    work := hw'
    tables := h.tables.unch hu (hE _ (by simp)) (hE _ (by simp)) (hE _ (by simp)) kg }, hmono⟩

end Generic

theorem SearchAt.valid_blocks {n : Nat} {m : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) :
    ∀ z ∈ S.blocks, z ≠ S.bUA → z ≠ Block.tcnode0 → Mem.valid_block m z := fun z hz hua htc =>
  h.toG.valid_blocks z (SLoc.mem_blocksG.2 hz) hua htc

/-- Every block of `S.blocks`, given `bUA` and `tcnode0`. -/
theorem SearchAt.valid_all {n : Nat} {m : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) (hvU : Mem.valid_block m S.bUA)
    (hvT : Mem.valid_block m Block.tcnode0) : ∀ z ∈ S.blocks, Mem.valid_block m z := by
  intro z hz
  by_cases hu : z = S.bUA
  · exact hu ▸ hvU
  by_cases ht : z = Block.tcnode0
  · exact ht ▸ hvT
  exact h.valid_blocks z hz hu ht

end NautyVerified.Proofs.Search
