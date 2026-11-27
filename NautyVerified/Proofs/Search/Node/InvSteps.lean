import NautyVerified.Proofs.Search.State
import NautyVerified.Spec.PartOk
import NautyVerified.Spec.NodeOk
import NautyVerified.Spec.Processnode
import NautyVerified.Spec.Firstterminal
import NautyVerified.Spec.Recover
import NautyVerified.Spec.Testcanlab
import NautyVerified.Spec.Updatecan
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

/-! ## Leaves -/

theorem SRest.scatter {st : Search n} (h : SRest st) (hlab : ∀ i < n, st.lab[i]! < n)
    (ref : Array Nat) : SRest (Hex.GraphIso.Nauty.scatter ref st) := by
  rw [Spec.scatter_eq]
  have hsz := h.workpermSize
  refine { h with
    workpermSmall := fun i hi => scatterW_small (ref := ref) hlab
      (fun x hx => h.workpermSmall x (hsz ▸ hx)) n (Nat.le_refl _) i (by omega)
    workpermSize := by simp only [scatterW_size]; exact hsz }

theorem updatecan_size (ctx : Ctx n) (c : Array (VSet n)) (lab : Array Nat) (sr : Nat) :
    (updatecan ctx c lab sr).size = c.size := by
  rw [Spec.updatecan_eq]
  generalize List.range' sr (n - sr) = l
  induction l generalizing c with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, canStep]; rw [ih, Array.size_set!]

theorem tclGo_range (ctx : Ctx n) (c : Array (VSet n)) (lab : Array Nat) :
    ∀ l : List Nat, (∀ i ∈ l, i < n) →
      (-1 ≤ (tclGo ctx c lab l).1 ∧ (tclGo ctx c lab l).1 ≤ 1) ∧ (tclGo ctx c lab l).2 ≤ n
  | [], _ => by simp [tclGo]
  | i :: l, hl => by
    have hi := hl i (by simp)
    simp only [tclGo]
    split
    · exact ⟨⟨by simp, by simp⟩, by simp only; omega⟩
    · exact ⟨⟨by simp, by simp⟩, by simp only; omega⟩
    · exact tclGo_range ctx c lab l fun j hj => hl j (by simp [hj])

theorem testcanlab_range (ctx : Ctx n) (c : Array (VSet n)) (lab : Array Nat) :
    (-1 ≤ (testcanlab ctx c lab).1 ∧ (testcanlab ctx c lab).1 ≤ 1) ∧ (testcanlab ctx c lab).2 ≤ n := by
  rw [testcanlab_eq]
  exact tclGo_range ctx c lab _ fun i hi => List.mem_range.1 hi

/-- The last step of `classifyCanon`, for any comparison outcome `p`. -/
theorem classifyCanon_tail (p : Search n × Nat) (h : SRest p.1) (hlab : ∀ i < n, p.1.lab[i]! < n)
    (hp : p.2 ≤ n) :
    SRest (if p.1.compCanon = 0 then ((.autoCanon : Leaf), Hex.GraphIso.Nauty.scatter p.1.canonlab p.1)
      else if p.1.compCanon > 0 then (.better p.2, p.1) else (.bad, p.1)).2 ∧
      ∀ sr, (if p.1.compCanon = 0 then ((.autoCanon : Leaf), Hex.GraphIso.Nauty.scatter p.1.canonlab p.1)
        else if p.1.compCanon > 0 then (.better p.2, p.1) else (.bad, p.1)).1 = .better sr → sr ≤ n := by
  split
  · exact ⟨h.scatter hlab _, fun _ e => by cases e⟩
  · split
    · exact ⟨h, fun sr e => by cases e; exact hp⟩
    · exact ⟨h, fun _ e => by cases e⟩

theorem SRest.classifyCanon {ctx : Ctx n} {level : Nat} {st : Search n} (h : SRest st)
    (hlab : ∀ i < n, st.lab[i]! < n) :
    SRest (classifyCanon ctx level st).2 ∧
      ∀ sr, (classifyCanon ctx level st).1 = .better sr → sr ≤ n := by
  have := h.scalars
  unfold Spec.classifyCanon
  apply classifyCanon_tail
  · split
    · split
      · exact { h with scalars := by simp only; omega }
      · obtain ⟨⟨r1, r2⟩, r3⟩ := testcanlab_range ctx
          (updatecan ctx st.canong st.canonlab st.samerows) st.lab
        exact { h with
          samerows := Nat.le_refl _
          canongSize := by simp only [updatecan_size]; exact h.canongSize
          scalars := by simp only; omega }
    · exact h
  · split
    · split <;> exact hlab
    · exact hlab
  · split
    · split
      · exact Nat.zero_le _
      · exact (testcanlab_range ctx _ _).2
    · exact Nat.zero_le _

theorem SRest.classify {ctx : Ctx n} {level numcells : Nat} {st : Search n} (h : SRest st)
    (hlab : ∀ i < n, st.lab[i]! < n) :
    SRest (Hex.GraphIso.Nauty.classify ctx level numcells st).2 ∧
      ∀ sr, (Hex.GraphIso.Nauty.classify ctx level numcells st).1 = .better sr → sr ≤ n := by
  rw [Spec.classify_eq]
  have hsc : ∀ i < n, (Hex.GraphIso.Nauty.scatter st.firstlab st).lab[i]! < n := by
    simpa [Spec.scatter_eq] using hlab
  split
  · exact ⟨h, fun _ h => by cases h⟩
  · split
    · exact ⟨h, fun _ h => by cases h⟩
    · split
      · split
        · exact ⟨h.scatter hlab _, fun _ h => by cases h⟩
        · exact (h.scatter hlab _).classifyCanon hsc
      · exact h.classifyCanon hlab

theorem SRest.pushAuto {st : Search n} (h : SRest st) (pair : VSet n × VSet n) :
    SRest (Hex.GraphIso.Nauty.pushAuto st pair) := by
  unfold Hex.GraphIso.Nauty.pushAuto
  split
  · exact h.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · exact h.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- `SRest.congr` with new orbits and orbit count. -/
theorem SRest.congrO {st st' : Search n} (h : SRest st) (h1 : st'.firstcode = st.firstcode)
    (h2 : st'.canoncode = st.canoncode) (h3 : st'.firsttc = st.firsttc)
    (h4 : st'.workperm = st.workperm) (h5 : st'.samerows = st.samerows)
    (h6 : st'.firstlab = st.firstlab) (h7 : st'.canonlab = st.canonlab)
    (h8 : st'.canong = st.canong) (h9 : st'.gcaFirst = st.gcaFirst)
    (h10 : st'.gcaCanon = st.gcaCanon) (h11 : st'.noncheaplevel = st.noncheaplevel)
    (h12 : st'.allsamelevel = st.allsamelevel) (h13 : st'.eqlevFirst = st.eqlevFirst)
    (h14 : st'.eqlevCanon = st.eqlevCanon) (h15 : st'.compCanon = st.compCanon)
    (h16 : st'.canonlevel = st.canonlevel) (h17 : st'.stabvertex = st.stabvertex)
    (h18 : st'.cosetindex = st.cosetindex) (h19 : st'.wsCap = st.wsCap)
    (h20 : st'.maxlevel = st.maxlevel) (hk : st'.numorbits ≤ n)
    (hd : Hex.GraphIso.Nauty.Orbit.Descending st'.orbits n) : SRest st' := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, mm, o, p, -, -⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hk, hd⟩ <;>
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20] <;> assumption

theorem pushAuto_fields {st : Search n} (pair : VSet n × VSet n) :
    (Hex.GraphIso.Nauty.pushAuto st pair).orbits = st.orbits ∧
      (Hex.GraphIso.Nauty.pushAuto st pair).workperm = st.workperm := by
  unfold Hex.GraphIso.Nauty.pushAuto; split <;> exact ⟨rfl, rfl⟩

theorem SRest.admit {st : Search n} (h : SRest st) : SRest (Hex.GraphIso.Nauty.admit st) := by
  have hpa : SRest (Hex.GraphIso.Nauty.pushAuto { st with genTrace := st.genTrace.push st.workperm }
      (fmperm st.workperm n)) :=
    (h.congr (st' := { st with genTrace := st.genTrace.push st.workperm }) rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).pushAuto _
  have hd := joins_desc h.orbitsDesc h.workpermSmall n (Nat.le_refl _)
  have hc := compresses_desc hd n (Nat.le_refl _)
  rw [← orbjoin_eq] at hc
  obtain ⟨ho, hw⟩ := pushAuto_fields (st := { st with genTrace := st.genTrace.push st.workperm })
    (fmperm st.workperm n)
  unfold Hex.GraphIso.Nauty.admit
  simp only [Id.run, pure]
  refine hpa.congrO rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    ?_ ?_
  · simp only [ho, hw]; exact hc.2
  · simp only [ho, hw]; exact hc.1

theorem SRest.install {level sr : Nat} {st : Search n} (h : SRest st) (hl : level < 2147483648)
    (hsr : sr ≤ n) (hlab : st.lab.size = n) : SRest (Hex.GraphIso.Nauty.install level sr st) := by
  have := h.scalars
  exact { h with
    codesSmall := fun j hj => ⟨(h.codesSmall j hj).1,
      forall_set! (P := (· < 32768)) (fun j hj => (h.codesSmall j hj).2) (by decide) _ j hj⟩
    canonlabSize := hlab
    canoncodeSize := by simp only [Hex.GraphIso.Nauty.install, Array.size_set!]; exact h.canoncodeSize
    samerows := hsr
    scalars := by simp only [Hex.GraphIso.Nauty.install, Int.ofNat_eq_natCast]; omega }

theorem SRest.pruneReturn {level : Nat} {st : Search n} (h : SRest st) :
    SRest (Hex.GraphIso.Nauty.pruneReturn level st).2 := by
  unfold Hex.GraphIso.Nauty.pruneReturn
  simp only [Id.run]
  split
  · exact h.pushAuto _
  · exact h

/-- `leafExit` after its `maxlevel` update. -/
def lxBody (leaf : Leaf) (level : Nat) (st : Search n) : Exit × Search n :=
  match leaf with
  | .internal => (.done, st)
  | .autoFirst =>
    let st := { Hex.GraphIso.Nauty.admit st with
      numgenerators := (Hex.GraphIso.Nauty.admit st).numgenerators + 1 }
    (.unwind st.gcaFirst false, st)
  | .autoCanon =>
    let save := st.numorbits
    let st := Hex.GraphIso.Nauty.admit st
    if st.numorbits == save then (.unwind st.gcaCanon (st.gcaCanon != st.gcaFirst), st)
    else
      let st := { st with numgenerators := st.numgenerators + 1 }
      if st.orbits[st.cosetindex]! < st.cosetindex then (.unwind st.gcaFirst false, st)
      else (.unwind st.gcaCanon (st.gcaCanon != st.gcaFirst), st)
  | .better sr => Hex.GraphIso.Nauty.pruneReturn level (Hex.GraphIso.Nauty.install level sr st)
  | .bad => Hex.GraphIso.Nauty.pruneReturn level { st with numbadleaves := st.numbadleaves + 1 }

theorem leafExit_eq (leaf : Leaf) (level : Nat) (st : Search n) :
    Hex.GraphIso.Nauty.leafExit leaf level st = lxBody leaf level
      (if leaf != .internal && level > st.maxlevel then { st with maxlevel := level } else st) := by
  cases leaf <;> simp only [Hex.GraphIso.Nauty.leafExit, lxBody, Id.run, pure] <;> split <;> rfl

theorem SRest.leafExit {leaf : Leaf} {level : Nat} {st : Search n} (h : SRest st)
    (hl : level ≤ n) (hn : n < 1073741824) (hlab : st.lab.size = n)
    (hsr : ∀ sr, leaf = .better sr → sr ≤ n) :
    SRest (Hex.GraphIso.Nauty.leafExit leaf level st).2 := by
  rw [leafExit_eq]
  have h0 : SRest (if leaf != .internal && level > st.maxlevel then { st with maxlevel := level }
      else st) := by
    split
    · exact { h with maxlevelLe := hl }
    · exact h
  have hlab0 : (if leaf != .internal && level > st.maxlevel then { st with maxlevel := level }
      else st).lab.size = n := by split <;> exact hlab
  generalize (if leaf != .internal && level > st.maxlevel then { st with maxlevel := level }
      else st) = st₀ at h0 hlab0
  cases leaf with
  | internal => exact h0
  | autoFirst =>
    exact h0.admit.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl
  | autoCanon =>
    simp only [lxBody]
    split
    · exact h0.admit
    · split
      · exact h0.admit.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl
      · exact h0.admit.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl
  | better sr => exact (h0.install (by omega) (hsr sr rfl) hlab0).pruneReturn
  | bad =>
    exact (h0.congr (st' := { st₀ with numbadleaves := st₀.numbadleaves + 1 }) rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).pruneReturn

/-! ## The root -/

theorem SRest.initialC (hn0 : 0 < n) (lab0 : Array Nat) (cellEnds : List Nat) :
    SRest (SearchInf.initialC n lab0 cellEnds) := by
  have hd : Hex.GraphIso.Nauty.Orbit.Descending (Array.ofFn (n := n) fun i => i.val) n :=
    ⟨by simp, fun v hv => by simp [hv]⟩
  refine
    { codesSmall := fun i hi => ⟨?_, ?_⟩
      firsttcRange := fun i hi => ⟨?_, ?_⟩
      workpermSmall := fun i hi => ?_
      samerows := Nat.zero_le _
      workpermSize := by simp [SearchInf.initialC, initial]
      firstlabSize := by simp [SearchInf.initialC, initial]
      canonlabSize := by simp [SearchInf.initialC, initial]
      firstcodeSize := by simp [SearchInf.initialC, initial]
      canoncodeSize := by simp [SearchInf.initialC, initial]
      firsttcSize := by simp [SearchInf.initialC, initial]
      canongSize := by simp [SearchInf.initialC, initial]
      scalars := by simp [SearchInf.initialC, initial]
      wsCap := rfl
      maxlevelLe := hn0
      numorbitsLe := Nat.le_refl _
      orbitsDesc := hd } <;>
    simp [SearchInf.initialC, initial, hi] <;> omega

/-- `SInv` at nauty's root state. -/
theorem SInv.root {k : Nat} (G : Hex.GraphIso.Colored n k) (hn0 : 0 < n) (hn : n < 1073741824) :
    SInv (SearchInf.initialC n (initialPartition G).1 (initialPartition G).2) :=
  have hi : n + 2 < nautyInfinity := by simp only [nautyInfinity]; omega
  SInv.of (PartOk.facts hn0 hi (PartOk.of_nodeOk hi (SearchInf.nodeOk_root G hn0)))
    (SRest.initialC hn0 _ _)

end NautyVerified.Proofs.Search
