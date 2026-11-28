import NautyVerified.Proofs.Search.Processnode.State

/-!
# Updating one component of the search state

Each lemma rebuilds `Arrays`, `Scalars` or `Stats` after a change confined to
the blocks of the fields it replaces.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

variable {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n} {nsp : Bool}
  {pre : Bool}

/-- `Arrays` after a change, from each field and the graph's block unchanged. -/
theorem Arrays.set {st' : Search n} (h : Arrays m S ctx st) {W : block → Prop}
    (hu : Unch m m' W)
    (lab : ArrayAt m' .Mint32 S.bl S.lb (ints st'.lab) n)
    (ptn : ArrayAt m' .Mint32 S.bp S.pb (ints st'.ptn) n)
    (orbits : ArrayAt m' .Mint32 S.bo S.ob (ints st'.orbits) n)
    (active : ∃ aw, ArrayAt m' .Mint64 S.bA 0 (longs aw) S.M ∧
      SetRep (fun w => bv64 (aw w)) S.M st'.active)
    (fixedpts : ∃ fw, ArrayAt m' .Mint64 S.bF 0 (longs fw) S.M ∧
      SetRep (fun w => bv64 (fw w)) S.M st'.fixedpts)
    (workperm : ∃ v, ArrayAt m' .Mint32 S.bWP 0 v n)
    (firstlab : ArrayAt m' .Mint32 S.bFL 0 (ints st'.firstlab) n)
    (canonlab : ArrayAt m' .Mint32 S.bCL 0 (ints st'.canonlab) n)
    (firstcode : ArrayAt m' .Mint16signed S.bFC 0 (shorts st'.firstcode) (n + 2))
    (canoncode : ArrayAt m' .Mint16signed S.bCC 0 (shorts st'.canoncode) (n + 2))
    (firsttc : ArrayAt m' .Mint32 S.bTC 0 (intsZ st'.firsttc) (n + 2))
    (canong : CanongAt m' S st'.canong st'.samerows)
    (autos : AutosAt m' S st'.autos) (hg : ¬ W S.bg) : Arrays m' S ctx st' :=
  ⟨lab, ptn, orbits, active, fixedpts, workperm, firstlab, canonlab, firstcode, canoncode, firsttc,
    canong, autos, ⟨h.graph.arr.unch hu hg, h.graph.rep⟩⟩

theorem Arrays.active' (h : Arrays m S ctx st) {W : block → Prop} (hu : Unch m m' W) (hb : ¬ W S.bA) :
    ∃ aw, ArrayAt m' .Mint64 S.bA 0 (longs aw) S.M ∧ SetRep (fun w => bv64 (aw w)) S.M st.active :=
  let ⟨aw, ha, hr⟩ := h.active; ⟨aw, ha.unch hu hb, hr⟩

theorem Arrays.fixedpts' (h : Arrays m S ctx st) {W : block → Prop} (hu : Unch m m' W) (hb : ¬ W S.bF) :
    ∃ fw, ArrayAt m' .Mint64 S.bF 0 (longs fw) S.M ∧ SetRep (fun w => bv64 (fw w)) S.M st.fixedpts :=
  let ⟨fw, ha, hr⟩ := h.fixedpts; ⟨fw, ha.unch hu hb, hr⟩

theorem Arrays.workperm' (h : Arrays m S ctx st) {W : block → Prop} (hu : Unch m m' W) (hb : ¬ W S.bWP) :
    ∃ v, ArrayAt m' .Mint32 S.bWP 0 v n :=
  let ⟨v, ha⟩ := h.workperm; ⟨v, ha.unch hu hb⟩

/-- A store to one `statsblk` member leaves the others. -/
theorem stats_other {chunk c' : memory_chunk} {off off' : Int} {v w : val}
    (h : FieldAt m chunk S.bst (S.sb + off) v)
    (hst : Mem.store c' m S.bst (zOfInt (S.sb + off')) w = some m')
    (hd : off + csize chunk ≤ off' ∨ off' + csize c' ≤ off) : FieldAt m' chunk S.bst (S.sb + off) v :=
  h.store_other hst (by omega)

/-- The fields of the search state held in nauty.c's static `int`s. -/
def scalView {κ : Type} (st : SearchState n κ) : Nat × Nat × Nat × Nat × Nat × Int × Int × Nat × Nat × Nat × Nat :=
  (st.gcaFirst, st.gcaCanon, st.noncheaplevel, st.allsamelevel, st.eqlevFirst, st.eqlevCanon,
    st.compCanon, st.samerows, st.canonlevel, st.stabvertex, st.cosetindex)

/-- The counters held in the `statsblk`. -/
def statView {κ : Type} (st : SearchState n κ) : Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (st.numorbits, st.numgenerators, st.numnodes, st.numbadleaves, st.maxlevel, st.tctotal,
    st.canupdates)

theorem Scalars.cast {st' : Search n} (h : Scalars m st nsp) (e : scalView st' = scalView st) :
    Scalars m st' nsp := by
  simp only [scalView, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := e
  exact ⟨e1 ▸ h.gcaFirst, e2 ▸ h.gcaCanon, e3 ▸ h.noncheaplevel, e4 ▸ h.allsamelevel,
    e5 ▸ h.eqlevFirst, e6 ▸ h.eqlevCanon, e7 ▸ h.compCanon, e8 ▸ h.samerows, e9 ▸ h.canonlevel,
    e10 ▸ h.stabvertex, e11 ▸ h.cosetindex, h.needshortprune⟩

theorem Stats.cast {st' : Search n} (h : Stats m S st pre) (e : statView st' = statView st) :
    Stats m S st' pre := by
  simp only [statView, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := e
  exact ⟨e1 ▸ h.numorbits, e2 ▸ h.numgenerators, e3 ▸ h.numnodes, e4 ▸ h.numbadleaves,
    e5 ▸ h.maxlevel, h.maxlevelW, e6 ▸ h.tctotal, e7 ▸ h.canupdates, h.fits, h.perm, h.errstatus,
    h.grpsize1, h.grpsize2⟩

/-- `Arrays` after a change confined to `workperm`'s block. -/
theorem Arrays.wp {st' : Search n} (h : Arrays m S ctx st) (hd : S.blocks.Pairwise (· ≠ ·))
    (hu : Unch m m' (· = S.bWP)) (hw : ∃ v, ArrayAt m' .Mint32 S.bWP 0 v n)
    (e : st'.lab = st.lab ∧ st'.ptn = st.ptn ∧ st'.orbits = st.orbits ∧ st'.active = st.active ∧
      st'.fixedpts = st.fixedpts ∧ st'.firstlab = st.firstlab ∧ st'.canonlab = st.canonlab ∧
      st'.firstcode = st.firstcode ∧ st'.canoncode = st.canoncode ∧ st'.firsttc = st.firsttc ∧
      st'.canong = st.canong ∧ st'.samerows = st.samerows ∧ st'.autos = st.autos) :
    Arrays m' S ctx st' := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ := e
  obtain ⟨aw, ha, har⟩ := h.active
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  have c := h.canong.unch hu (by sep_ne hd)
  have au := h.autos.unch hu (by sep_ne hd) (by sep_ne hd)
  exact ⟨e1 ▸ h.lab.unch hu (by sep_ne hd), e2 ▸ h.ptn.unch hu (by sep_ne hd),
    e3 ▸ h.orbits.unch hu (by sep_ne hd), ⟨aw, ha.unch hu (by sep_ne hd), e4 ▸ har⟩,
    ⟨fw, hf.unch hu (by sep_ne hd), e5 ▸ hfr⟩, hw, e6 ▸ h.firstlab.unch hu (by sep_ne hd),
    e7 ▸ h.canonlab.unch hu (by sep_ne hd), e8 ▸ h.firstcode.unch hu (by sep_ne hd),
    e9 ▸ h.canoncode.unch hu (by sep_ne hd), e10 ▸ h.firsttc.unch hu (by sep_ne hd),
    e11 ▸ e12 ▸ c, e13 ▸ au, ⟨h.graph.arr.unch hu (by sep_ne hd), h.graph.rep⟩⟩

/-- The fields of the search state held in arrays. -/
def arrView {κ : Type} (st : SearchState n κ) :=
  (st.lab, st.ptn, st.orbits, st.active, st.fixedpts, st.firstlab, st.canonlab, st.firstcode,
    st.canoncode, st.firsttc, st.canong, st.samerows, st.autos)

theorem Arrays.cast {st' : Search n} (h : Arrays m S ctx st) (e : arrView st' = arrView st) :
    Arrays m S ctx st' := by
  simp only [arrView, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ := e
  exact ⟨e1 ▸ h.lab, e2 ▸ h.ptn, e3 ▸ h.orbits, e4 ▸ h.active, e5 ▸ h.fixedpts, h.workperm,
    e6 ▸ h.firstlab, e7 ▸ h.canonlab, e8 ▸ h.firstcode, e9 ▸ h.canoncode, e10 ▸ h.firsttc,
    e11 ▸ e12 ▸ h.canong, e13 ▸ h.autos, h.graph⟩

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O} {gl : D.GLoc}
  {cl : D.CLoc} {G : O.Gr n}

theorem ScalarsG.cast {κ : Type} {st st' : SearchState n κ} (h : ScalarsG m st nsp)
    (e : scalView st' = scalView st) : ScalarsG m st' nsp := by
  simp only [scalView, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := e
  exact ⟨e1 ▸ h.gcaFirst, e2 ▸ h.gcaCanon, e3 ▸ h.noncheaplevel, e4 ▸ h.allsamelevel,
    e5 ▸ h.eqlevFirst, e6 ▸ h.eqlevCanon, e7 ▸ h.compCanon, e8 ▸ h.samerows, e9 ▸ h.canonlevel,
    e10 ▸ h.stabvertex, e11 ▸ h.cosetindex, h.needshortprune⟩

theorem StatsG.cast {κ : Type} {st st' : SearchState n κ} (h : StatsG m S st pre)
    (e : statView st' = statView st) : StatsG m S st' pre := by
  simp only [statView, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := e
  exact ⟨e1 ▸ h.numorbits, e2 ▸ h.numgenerators, e3 ▸ h.numnodes, e4 ▸ h.numbadleaves,
    e5 ▸ h.maxlevel, h.maxlevelW, e6 ▸ h.tctotal, e7 ▸ h.canupdates, h.fits, h.perm, h.errstatus,
    h.grpsize1, h.grpsize2⟩

theorem ArraysG.cast {st st' : SearchState n (O.Canon n)} (h : ArraysG D m S gl cl G st)
    (e : arrView st' = arrView st) : ArraysG D m S gl cl G st' := by
  simp only [arrView, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ := e
  exact ⟨e1 ▸ h.lab, e2 ▸ h.ptn, e3 ▸ h.orbits, e4 ▸ h.active, e5 ▸ h.fixedpts, h.workperm,
    e6 ▸ h.firstlab, e7 ▸ h.canonlab, e8 ▸ h.firstcode, e9 ▸ h.canoncode, e10 ▸ h.firsttc,
    e11 ▸ e12 ▸ h.canong, e13 ▸ h.autos, h.graph⟩

/-- `ArraysG` after a change confined to `workperm`'s block. -/
theorem ArraysG.wp {m₀ : mem} {st st' st₀ : SearchState n (O.Canon n)} {nsp₀ : Bool}
    (h : ArraysG D m S gl cl G st) (h₀ : SearchAtG D m₀ S gl cl G st₀ pre nsp₀)
    (hu : Unch m m' (· = S.bWP)) (hw : ∃ v, ArrayAt m' .Mint32 S.bWP 0 v n)
    (e : arrView st' = arrView st) : ArraysG D m' S gl cl G st' := by
  have hd := h₀.lit
  simp only [arrView, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ := e
  obtain ⟨aw, ha, har⟩ := h.active
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  have c := D.canon_unch h.canong hu fun z hz e => h₀.canon_ne hz (.inr (.inr (.inl (by simp)))) e
  have au := h.autos.unch hu (by sep_ne hd) (by sep_ne hd)
  exact ⟨e1 ▸ h.lab.unch hu (by sep_ne hd), e2 ▸ h.ptn.unch hu (by sep_ne hd),
    e3 ▸ h.orbits.unch hu (by sep_ne hd), ⟨aw, ha.unch hu (by sep_ne hd), e4 ▸ har⟩,
    ⟨fw, hf.unch hu (by sep_ne hd), e5 ▸ hfr⟩, hw, e6 ▸ h.firstlab.unch hu (by sep_ne hd),
    e7 ▸ h.canonlab.unch hu (by sep_ne hd), e8 ▸ h.firstcode.unch hu (by sep_ne hd),
    e9 ▸ h.canoncode.unch hu (by sep_ne hd), e10 ▸ h.firsttc.unch hu (by sep_ne hd),
    e11 ▸ e12 ▸ c, e13 ▸ au,
    D.graph_unch h.graph hu fun z hz e => h₀.graph_ne hz (.inr (.inr (.inl (by simp)))) e⟩

/-- `ArraysG` with a new canonical store, after a change avoiding the other arrays
and the graph's blocks. -/
theorem ArraysG.setCanong {st : SearchState n (O.Canon n)} (h : ArraysG D m S gl cl G st)
    {W : block → Prop} (hu : Unch m m' W)
    (hW : ∀ z ∈ [S.bl, S.bp, S.bo, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws,
      E.fmptr], ¬ W z)
    (hg : ∀ z ∈ D.graphBlocks gl S.bg, ¬ W z) {c : O.Canon n}
    (hc : D.CanonRep m' cl S.bc S.cofs S.M (O.rows c) st.samerows) :
    ArraysG D m' S gl cl G { st with canong := c } := by
  simp only [List.forall_mem_cons] at hW
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h13, h14, -⟩ := hW
  obtain ⟨aw, ha, har⟩ := h.active
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  obtain ⟨wv, hwv⟩ := h.workperm
  exact ⟨h.lab.unch hu h1, h.ptn.unch hu h2, h.orbits.unch hu h3, ⟨aw, ha.unch hu h4, har⟩,
    ⟨fw, hf.unch hu h5, hfr⟩, ⟨wv, hwv.unch hu h6⟩, h.firstlab.unch hu h7,
    h.canonlab.unch hu h8, h.firstcode.unch hu h9, h.canoncode.unch hu h10,
    h.firsttc.unch hu h11, hc, h.autos.unch hu h13 h14, D.graph_unch h.graph hu hg⟩

/-- `ArraysG` with new automorphism pairs, after a change avoiding the other arrays,
the graph's and the canonical store's blocks. -/
theorem ArraysG.setAutos {st : SearchState n (O.Canon n)} (h : ArraysG D m S gl cl G st)
    {W : block → Prop} (hu : Unch m m' W)
    (hW : ∀ z ∈ [S.bl, S.bp, S.bo, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC], ¬ W z)
    (hg : ∀ z ∈ D.graphBlocks gl S.bg, ¬ W z) (hc : ∀ z ∈ D.canonBlocks cl S.bc, ¬ W z)
    {a : Array (VSet n × VSet n)} (ha : AutosAtG m' S a) :
    ArraysG D m' S gl cl G { st with autos := a } := by
  simp only [List.forall_mem_cons] at hW
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := hW
  obtain ⟨aw, haw, har⟩ := h.active
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  obtain ⟨wv, hwv⟩ := h.workperm
  exact ⟨h.lab.unch hu h1, h.ptn.unch hu h2, h.orbits.unch hu h3, ⟨aw, haw.unch hu h4, har⟩,
    ⟨fw, hf.unch hu h5, hfr⟩, ⟨wv, hwv.unch hu h6⟩, h.firstlab.unch hu h7,
    h.canonlab.unch hu h8, h.firstcode.unch hu h9, h.canoncode.unch hu h10,
    h.firsttc.unch hu h11, D.canon_unch h.canong hu hc, ha, D.graph_unch h.graph hu hg⟩

/-- `ArraysG` after a change, from each field and the graph's blocks unchanged. -/
theorem ArraysG.set {st st' : SearchState n (O.Canon n)} (h : ArraysG D m S gl cl G st)
    {W : block → Prop} (hu : Unch m m' W)
    (lab : ArrayAt m' .Mint32 S.bl S.lb (ints st'.lab) n)
    (ptn : ArrayAt m' .Mint32 S.bp S.pb (ints st'.ptn) n)
    (orbits : ArrayAt m' .Mint32 S.bo S.ob (ints st'.orbits) n)
    (active : ∃ aw, ArrayAt m' .Mint64 S.bA 0 (longs aw) S.M ∧
      SetRep (fun w => bv64 (aw w)) S.M st'.active)
    (fixedpts : ∃ fw, ArrayAt m' .Mint64 S.bF 0 (longs fw) S.M ∧
      SetRep (fun w => bv64 (fw w)) S.M st'.fixedpts)
    (workperm : ∃ v, ArrayAt m' .Mint32 S.bWP 0 v n)
    (firstlab : ArrayAt m' .Mint32 S.bFL 0 (ints st'.firstlab) n)
    (canonlab : ArrayAt m' .Mint32 S.bCL 0 (ints st'.canonlab) n)
    (firstcode : ArrayAt m' .Mint16signed S.bFC 0 (shorts st'.firstcode) (n + 2))
    (canoncode : ArrayAt m' .Mint16signed S.bCC 0 (shorts st'.canoncode) (n + 2))
    (firsttc : ArrayAt m' .Mint32 S.bTC 0 (intsZ st'.firsttc) (n + 2))
    (canong : D.CanonRep m' cl S.bc S.cofs S.M (O.rows st'.canong) st'.samerows)
    (autos : AutosAtG m' S st'.autos) (hg : ∀ z ∈ D.graphBlocks gl S.bg, ¬ W z) :
    ArraysG D m' S gl cl G st' :=
  ⟨lab, ptn, orbits, active, fixedpts, workperm, firstlab, canonlab, firstcode, canoncode, firsttc,
    canong, autos, D.graph_unch h.graph hu hg⟩

theorem ArraysG.active' {st : SearchState n (O.Canon n)} (h : ArraysG D m S gl cl G st)
    {W : block → Prop} (hu : Unch m m' W) (hb : ¬ W S.bA) :
    ∃ aw, ArrayAt m' .Mint64 S.bA 0 (longs aw) S.M ∧ SetRep (fun w => bv64 (aw w)) S.M st.active :=
  let ⟨aw, ha, hr⟩ := h.active; ⟨aw, ha.unch hu hb, hr⟩

theorem ArraysG.fixedpts' {st : SearchState n (O.Canon n)} (h : ArraysG D m S gl cl G st)
    {W : block → Prop} (hu : Unch m m' W) (hb : ¬ W S.bF) :
    ∃ fw, ArrayAt m' .Mint64 S.bF 0 (longs fw) S.M ∧
      SetRep (fun w => bv64 (fw w)) S.M st.fixedpts :=
  let ⟨fw, ha, hr⟩ := h.fixedpts; ⟨fw, ha.unch hu hb, hr⟩

theorem ArraysG.workperm' {st : SearchState n (O.Canon n)} (h : ArraysG D m S gl cl G st)
    {W : block → Prop} (hu : Unch m m' W) (hb : ¬ W S.bWP) : ∃ v, ArrayAt m' .Mint32 S.bWP 0 v n :=
  let ⟨v, ha⟩ := h.workperm; ⟨v, ha.unch hu hb⟩

end Generic

end NautyVerified.Proofs.Search
