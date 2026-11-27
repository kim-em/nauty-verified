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
def scalView (st : Search n) : Nat × Nat × Nat × Nat × Nat × Int × Int × Nat × Nat × Nat × Nat :=
  (st.gcaFirst, st.gcaCanon, st.noncheaplevel, st.allsamelevel, st.eqlevFirst, st.eqlevCanon,
    st.compCanon, st.samerows, st.canonlevel, st.stabvertex, st.cosetindex)

/-- The counters held in the `statsblk`. -/
def statView (st : Search n) : Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
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
    e5 ▸ h.maxlevel, h.maxlevelW, e6 ▸ h.tctotal, e7 ▸ h.canupdates, h.fits⟩

end NautyVerified.Proofs.Search
