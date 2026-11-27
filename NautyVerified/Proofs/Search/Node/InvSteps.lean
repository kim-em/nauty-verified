import NautyVerified.Proofs.Search.State
import NautyVerified.Spec.PartOk
import NautyVerified.Spec.Processnode
import NautyVerified.Spec.Firstterminal
import NautyVerified.Spec.Recover
import NautyVerified.Spec.Testcanlab
import NautyVerified.Spec.Bestcell
import NautyVerified.Proofs.Search.Node.Compare

/-!
# `SInv` across the search's steps

`SInv` (Proofs/Search/State.lean) splits into the partition facts
(`Spec.PartFacts`, closed across a node's steps by `Spec/PartOk.lean`) and the
rest, `SRest`: the code arrays, `firsttc`, `workperm`, the sizes, the
level-valued statics, the workspace capacity, `maxlevel`, `numorbits` and the
orbit forest. `SInv.of` reassembles `SInv`, and each `SRest.<step>` keeps
`SRest` across one of HexGraphIso's search steps, taking as hypotheses only
the facts about its inputs that the step needs (level bounds, `lab`'s size
and values, the vertex individualised). The results of the recursive calls
need no lemma: their specifications return `SearchAt`, which contains
`SInv`.
-/

namespace NautyVerified.Proofs.Search

open NautyVerified.Spec NautyVerified.Spec.SearchInf Hex.GraphIso.Nauty

variable {n : Nat}

/-- The part of `SInv` that is not about the partition. -/
structure SRest (st : Search n) : Prop where
  codesSmall : ∀ i < n + 2, st.firstcode[i]! < 32768 ∧ st.canoncode[i]! < 32768
  firsttcRange : ∀ i < n + 2, -1 ≤ st.firsttc[i]! ∧ st.firsttc[i]! < n
  workpermSmall : ∀ i < n, st.workperm[i]! < n
  samerows : st.samerows ≤ n
  workpermSize : st.workperm.size = n
  firstlabSize : st.firstlab.size = n
  canonlabSize : st.canonlab.size = n
  firstcodeSize : st.firstcode.size = n + 2
  canoncodeSize : st.canoncode.size = n + 2
  firsttcSize : st.firsttc.size = n + 2
  canongSize : st.canong.size = n
  scalars : st.gcaFirst < 2147483648 ∧ st.gcaCanon < 2147483648 ∧
    st.noncheaplevel < 2147483648 ∧ st.allsamelevel < 2147483648 ∧
    st.eqlevFirst < 2147483648 ∧ -1 ≤ st.eqlevCanon ∧ st.eqlevCanon < 2147483648 ∧
    -1 ≤ st.compCanon ∧ st.compCanon ≤ 1 ∧ st.canonlevel < 2147483648 ∧
    st.stabvertex < 2147483648 ∧ st.cosetindex < 2147483648
  wsCap : st.wsCap = wsPairs
  maxlevelLe : st.maxlevel ≤ n
  numorbitsLe : st.numorbits ≤ n
  orbitsDesc : Hex.GraphIso.Nauty.Orbit.Descending st.orbits n

theorem SInv.rest {st : Search n} (h : SInv st) : SRest st :=
  { codesSmall := h.codesSmall, firsttcRange := h.firsttcRange, workpermSmall := h.workpermSmall
    samerows := h.samerows, workpermSize := h.workpermSize, firstlabSize := h.firstlabSize
    canonlabSize := h.canonlabSize, firstcodeSize := h.firstcodeSize
    canoncodeSize := h.canoncodeSize, firsttcSize := h.firsttcSize, canongSize := h.canongSize
    scalars := h.scalars, wsCap := h.wsCap, maxlevelLe := h.maxlevelLe
    numorbitsLe := h.numorbitsLe, orbitsDesc := h.orbitsDesc }

/-- `SInv` from the partition facts at a level `≤ n` and the rest. -/
theorem SInv.of {level numcells : Nat} {st : Search n} (hp : PartFacts n level numcells st)
    (hr : SRest st) : SInv st where
  labSize := hp.labSize
  labSmall := hp.labSmall
  labSurj := hp.labSurj
  ptnSize := hp.ptnSize
  ptnVals := fun i hi => by
    rcases hp.ptnVals i hi with h | h
    · have := hp.levelLe; have := hp.numcellsLe; exact .inl (by omega)
    · exact .inr h
  ptnLast := hp.ptnLast
  orbitsSmall := fun i hi => Nat.lt_of_le_of_lt (hr.orbitsDesc.2 i hi) hi
  codesSmall := hr.codesSmall
  firsttcRange := hr.firsttcRange
  workpermSmall := hr.workpermSmall
  samerows := hr.samerows
  orbitsSize := hr.orbitsDesc.1
  workpermSize := hr.workpermSize
  firstlabSize := hr.firstlabSize
  canonlabSize := hr.canonlabSize
  firstcodeSize := hr.firstcodeSize
  canoncodeSize := hr.canoncodeSize
  firsttcSize := hr.firsttcSize
  canongSize := hr.canongSize
  scalars := hr.scalars
  wsCap := hr.wsCap
  maxlevelLe := hr.maxlevelLe
  numorbitsLe := hr.numorbitsLe
  orbitsDesc := hr.orbitsDesc

/-! ## Steps that change only the partition, the active set or counters -/

/-- `SRest` reads none of `lab`, `ptn`, `active`, `fixedpts`, `autos` and the counters
other than `maxlevel` and `numorbits`. -/
theorem SRest.congr {st st' : Search n} (h : SRest st) (h1 : st'.firstcode = st.firstcode)
    (h2 : st'.canoncode = st.canoncode) (h3 : st'.firsttc = st.firsttc)
    (h4 : st'.workperm = st.workperm) (h5 : st'.samerows = st.samerows)
    (h6 : st'.firstlab = st.firstlab) (h7 : st'.canonlab = st.canonlab)
    (h8 : st'.canong = st.canong) (h9 : st'.gcaFirst = st.gcaFirst)
    (h10 : st'.gcaCanon = st.gcaCanon) (h11 : st'.noncheaplevel = st.noncheaplevel)
    (h12 : st'.allsamelevel = st.allsamelevel) (h13 : st'.eqlevFirst = st.eqlevFirst)
    (h14 : st'.eqlevCanon = st.eqlevCanon) (h15 : st'.compCanon = st.compCanon)
    (h16 : st'.canonlevel = st.canonlevel) (h17 : st'.stabvertex = st.stabvertex)
    (h18 : st'.cosetindex = st.cosetindex) (h19 : st'.wsCap = st.wsCap)
    (h20 : st'.maxlevel = st.maxlevel) (h21 : st'.numorbits = st.numorbits)
    (h22 : st'.orbits = st.orbits) : SRest st' := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, mm, o, p, q, r⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, h21, h22] <;> assumption

theorem SRest.visit {ctx : Ctx n} {level numcells : Nat} {st : Search n} (h : SRest st) :
    SRest (Hex.GraphIso.Nauty.visit ctx level numcells st).2.2 :=
  h.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- The refinement code `visit` returns is below `2^15`. -/
theorem visit_code_lt (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (Hex.GraphIso.Nauty.visit ctx level numcells st).2.1 < 32767 := by
  show (refine ctx level st.lab st.ptn st.active numcells).longcode < 32767
  simp only [refine, cleanup]
  exact Nat.mod_lt _ (by decide)

theorem SRest.afterSweep {first : Bool} {level tcellsize index : Nat} {st : Search n}
    (h : SRest st) : SRest (Hex.GraphIso.Nauty.afterSweep first level tcellsize index st) := by
  unfold Hex.GraphIso.Nauty.afterSweep
  split
  · have := h.scalars
    exact { h with scalars := by simp only; omega }
  · exact h

theorem SRest.afterChildFirst {level tv1 : Nat} {st : Search n} (h : SRest st)
    (hl : level < 2147483648) (ht : tv1 < 2147483648) :
    SRest (Hex.GraphIso.Nauty.afterChildFirst level tv1 st) := by
  have := h.scalars
  exact { h with scalars := by simp only [Hex.GraphIso.Nauty.afterChildFirst]; omega }

theorem SRest.child {first : Bool} {level tc tv : Nat} {st : Search n} (h : SRest st)
    (ht : tv < 2147483648) : SRest (Hex.GraphIso.Nauty.child first level tc tv st) := by
  cases first
  · simp only [Hex.GraphIso.Nauty.child, Bool.false_eq_true, ite_false]
    exact h.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · simp only [Hex.GraphIso.Nauty.child, ite_true]
    have := h.scalars
    exact { h with scalars := by simp only; omega }

theorem SRest.cheapCheck {first : Bool} {level : Nat} {st : Search n} (h : SRest st)
    (hl : level + 1 < 2147483648) : SRest (Hex.GraphIso.Nauty.cheapCheck first level st) := by
  unfold Hex.GraphIso.Nauty.cheapCheck
  split
  · have := h.scalars
    exact { h with scalars := by simp only; omega }
  · exact h

theorem SRest.recover {inf level : Nat} {st : Search n} (h : SRest st)
    (hl : level + 1 < 2147483648) : SRest (Hex.GraphIso.Nauty.recover inf level st) := by
  rw [← recover_eq, recoverLevels_upd]
  have h' : SRest (recoverPtn inf level st) := by
    rw [recoverPtn_eq]
    exact h.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have := h'.scalars
  refine { h' with scalars := ?_ }
  simp only
  refine ⟨this.1, ?_, ?_, this.2.2.2.1, ?_, ?_, ?_, ?_, ?_, this.2.2.2.2.2.2.2.2.2.1,
    this.2.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.2⟩ <;> split <;>
    (try simp only [Int.ofNat_eq_natCast] at *) <;> omega

/-! ## Array updates -/

theorem getElem!_set!_or {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) (j : Nat) :
    (a.set! i v)[j]! = v ∨ (a.set! i v)[j]! = a[j]! := by
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · left; simp [hi]
    · right; simp [hi]
  · right
    by_cases hj : j < a.size
    · rw [getElem!_pos (a.set! i v) j (by simpa using hj), getElem!_pos a j hj]
      exact Array.getElem_setIfInBounds_ne hj hij
    · rw [getElem!_neg (a.set! i v) j (by simpa using hj), getElem!_neg a j hj]

theorem forall_set! {α : Type} [Inhabited α] {P : α → Prop} {a : Array α} {N : Nat}
    (h : ∀ j < N, P a[j]!) {v : α} (hv : P v) (i : Nat) : ∀ j < N, P (a.set! i v)[j]! :=
  fun j hj => (getElem!_set!_or a i v j).elim (fun e => by rw [e]; exact hv)
    (fun e => by rw [e]; exact h j hj)

theorem codes_set {st : Search n} (h : SRest st) {i v : Nat} (hv : v < 32768) :
    (∀ j < n + 2, (st.firstcode.set! i v)[j]! < 32768) ∧
      ∀ j < n + 2, (st.canoncode.set! i v)[j]! < 32768 :=
  ⟨forall_set! (P := (· < 32768)) (fun j hj => (h.codesSmall j hj).1) hv i,
   forall_set! (P := (· < 32768)) (fun j hj => (h.codesSmall j hj).2) hv i⟩

/-! ## The code comparisons -/

theorem SRest.recordFirst {level code : Nat} {st : Search n} (h : SRest st) (hc : code < 32768) :
    SRest (Hex.GraphIso.Nauty.recordFirst level code st) :=
  { h with
    codesSmall := fun j hj => ⟨(codes_set h hc).1 j hj, (h.codesSmall j hj).2⟩
    firstcodeSize := by simp only [Hex.GraphIso.Nauty.recordFirst, Array.size_set!]; exact h.firstcodeSize }

theorem SRest.compareCodes {level code : Nat} {st : Search n} (h : SRest st)
    (hl : level < 2147483648) (hc : code < 32768) :
    SRest (Hex.GraphIso.Nauty.compareCodes level code st) := by
  rw [compareCodes_eq]
  have h1 : SRest (cmpFirst level code st) := by
    unfold cmpFirst
    split
    · have := h.scalars
      exact { h with scalars := by simp only; omega }
    · exact h
  rw [cmpCanon_eq]
  have h2 : SRest (cmpCanonA level code (cmpFirst level code st)) := by
    have := h1.scalars
    unfold cmpCanonA
    split
    · split
      · exact { h1 with scalars := by simp only; omega }
      · split
        · exact { h1 with scalars := by simp only; omega }
        · exact { h1 with scalars := by simp only [Int.ofNat_eq_natCast]; omega }
    · exact h1
  unfold cmpCanonB
  split
  · exact { h2 with
      codesSmall := fun j hj => ⟨(h2.codesSmall j hj).1, (codes_set h2 hc).2 j hj⟩
      canoncodeSize := by simp only [Array.size_set!]; exact h2.canoncodeSize }
  · exact h2

/-! ## The first leaf -/

theorem SRest.firstterminal {level : Nat} {st : Search n} (h : SRest st) (hl : level ≤ n)
    (hn : n < 1073741824) (hlab : st.lab.size = n) :
    SRest (Hex.GraphIso.Nauty.firstterminal level st) := by
  rw [firstterminal_eq]
  have := h.scalars
  have hfc := h.firstcodeSize
  have hcc := h.canoncodeSize
  have hfs : ∀ j < n + 2, (st.firstcode.set! (level + 1) codeSentinel)[j]! < 32768 :=
    forall_set! (P := (· < 32768)) (fun j hj => (h.codesSmall j hj).1) (by decide) _
  refine
    { codesSmall := fun j hj => ⟨hfs j hj, ?_⟩
      firsttcRange := forall_set! (P := fun x : Int => -1 ≤ x ∧ x < (n : Int)) h.firsttcRange
        ⟨by decide, by omega⟩ _
      workpermSmall := h.workpermSmall
      samerows := Nat.zero_le _
      workpermSize := h.workpermSize
      firstlabSize := hlab
      canonlabSize := hlab
      firstcodeSize := by simp only [Array.size_set!]; exact hfc
      canoncodeSize := by simp only [Array.size_set!, ccCopy_size]; exact hcc
      firsttcSize := by simp only [Array.size_set!]; exact h.firsttcSize
      canongSize := h.canongSize
      scalars := by simp only [Int.ofNat_eq_natCast]; omega
      wsCap := h.wsCap
      maxlevelLe := hl
      numorbitsLe := h.numorbitsLe
      orbitsDesc := h.orbitsDesc }
  refine forall_set! (P := (· < 32768)) (fun j hj => ?_) (by decide) _ j hj
  rw [ccCopy_get _ _ _ (by omega)]
  split
  · exact hfs j hj
  · exact (h.codesSmall j hj).2

/-! ## Target cells -/

/-- Below `n` cells, some position is inside a nontrivial cell. -/
theorem exists_gt_of_bcount {ptn : Array Nat} {level : Nat} (h : bcount ptn level n < n) :
    ∃ x < n, level < ptn[x]! := by
  apply Classical.byContradiction
  intro hne
  have hall : ∀ q ∈ List.range n, decide (ptn[q]! ≤ level) = true := fun q hq => by
    have hq' : q < n := List.mem_range.1 hq
    simp only [decide_eq_true_eq]
    exact Nat.le_of_not_lt fun hlt => hne ⟨q, hq', hlt⟩
  rw [bcount, List.countP_eq_length.2 hall, List.length_range] at h
  exact Nat.lt_irrefl _ h

theorem SRest.chooseTarget {first : Bool} {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : Search n} (h : SRest st) (hl : level < 2147483648)
    (hpos : first = true → numcells ≠ n →
      (maketargetcell ctx st.lab st.ptn level tcLevel (-1)).1 < n) :
    SRest (Hex.GraphIso.Nauty.chooseTarget first ctx tcLevel level numcells st).2.2.2 := by
  unfold Hex.GraphIso.Nauty.chooseTarget
  have := h.scalars
  cases first <;> simp only [Id.run, pure, Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.true_and, Bool.false_eq_true, ite_false, ite_true] <;> repeat' split
  all_goals first
    | exact h
    | exact { h with scalars := by simp only; omega }
    | (refine { h with
         firsttcRange := forall_set! (P := fun x : Int => -1 ≤ x ∧ x < (n : Int)) h.firsttcRange
           ⟨?_, ?_⟩ _
         firsttcSize := by simp only [Array.size_set!]; exact h.firsttcSize } <;>
       (try simp only [Int.ofNat_eq_natCast]) <;>
       first | omega | (have hp := hpos rfl (by simp_all); omega))

/-- The target cell chosen below `n` cells starts inside the partition. -/
theorem PartFacts.target_lt {ctx : Ctx n} {level numcells tcLevel : Nat} {st : Search n}
    (hp : PartFacts n level numcells st) (h1 : 1 ≤ level) (hlt : numcells < n) (hint : Int)
    (hh : hint < n) : (maketargetcell ctx st.lab st.ptn level tcLevel hint).1 < n := by
  obtain ⟨x, hx, hgt⟩ := exists_gt_of_bcount (hp.count ▸ hlt)
  exact (Bestcell.targetcell_mem ctx st.lab st.ptn level tcLevel hint hp.ptnSize
    (Nat.le_trans hp.ptnLast h1) hh hx hgt).1

end NautyVerified.Proofs.Search
