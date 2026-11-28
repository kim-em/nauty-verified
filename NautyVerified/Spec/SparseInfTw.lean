import NautyVerified.Spec.SearchInf

/-!
# The infinity map on search states with any canonical store

`twG f t st` is `SearchInf.tw` for `SearchState n κ` with any carried store
`κ`: `ptn` mapped by `f`, `firsttc` replaced by `t`. The transitions the
dense and sparse searches share are generic in the store, and so are their
commutation lemmas, proved as the dense ones are. `tw_eq_twG`: at the dense
store the two maps agree.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {n : Nat} {κ : Type}

/-! ## The shared search operations commute with the map, for any store -/

/-- `twG` for any store: `st` with its `ptn` mapped by `f` and `firsttc` replaced by `t`. -/
def twG (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : SearchState n κ :=
  { st with ptn := st.ptn.map f, firsttc := t }

@[simp] theorem twG_lab (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).lab = st.lab := rfl
@[simp] theorem twG_active (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).active = st.active := rfl
@[simp] theorem twG_orbits (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).orbits = st.orbits := rfl
@[simp] theorem twG_fixedpts (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).fixedpts = st.fixedpts := rfl
@[simp] theorem twG_autos (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).autos = st.autos := rfl
@[simp] theorem twG_wsCap (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).wsCap = st.wsCap := rfl
@[simp] theorem twG_firstcode (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).firstcode = st.firstcode := rfl
@[simp] theorem twG_canoncode (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).canoncode = st.canoncode := rfl
@[simp] theorem twG_firstlab (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).firstlab = st.firstlab := rfl
@[simp] theorem twG_canonlab (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).canonlab = st.canonlab := rfl
@[simp] theorem twG_canong (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).canong = st.canong := rfl
@[simp] theorem twG_samerows (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).samerows = st.samerows := rfl
@[simp] theorem twG_compCanon (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).compCanon = st.compCanon := rfl
@[simp] theorem twG_eqlevFirst (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).eqlevFirst = st.eqlevFirst := rfl
@[simp] theorem twG_eqlevCanon (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).eqlevCanon = st.eqlevCanon := rfl
@[simp] theorem twG_gcaFirst (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).gcaFirst = st.gcaFirst := rfl
@[simp] theorem twG_gcaCanon (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).gcaCanon = st.gcaCanon := rfl
@[simp] theorem twG_canonlevel (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).canonlevel = st.canonlevel := rfl
@[simp] theorem twG_noncheaplevel (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).noncheaplevel = st.noncheaplevel := rfl
@[simp] theorem twG_allsamelevel (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).allsamelevel = st.allsamelevel := rfl
@[simp] theorem twG_cosetindex (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).cosetindex = st.cosetindex := rfl
@[simp] theorem twG_stabvertex (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).stabvertex = st.stabvertex := rfl
@[simp] theorem twG_numnodes (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).numnodes = st.numnodes := rfl
@[simp] theorem twG_tctotal (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).tctotal = st.tctotal := rfl
@[simp] theorem twG_canupdates (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).canupdates = st.canupdates := rfl
@[simp] theorem twG_numorbits (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).numorbits = st.numorbits := rfl
@[simp] theorem twG_numgenerators (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).numgenerators = st.numgenerators := rfl
@[simp] theorem twG_numbadleaves (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).numbadleaves = st.numbadleaves := rfl
@[simp] theorem twG_maxlevel (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).maxlevel = st.maxlevel := rfl
@[simp] theorem twG_order (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).order = st.order := rfl
@[simp] theorem twG_genTrace (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).genTrace = st.genTrace := rfl
@[simp] theorem twG_workperm (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).workperm = st.workperm := rfl
@[simp] theorem twG_ptn (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).ptn = st.ptn.map f := rfl
@[simp] theorem twG_firsttc (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) : (twG f t st).firsttc = t := rfl

theorem recordFirst_twG (f : Nat → Nat) (t : Array Int) (level code : Nat) (st : SearchState n κ) :
    recordFirst level code (twG f t st) = twG f t (recordFirst level code st) := rfl

theorem compareCodes_twG (f : Nat → Nat) (t : Array Int) (level code : Nat) (st : SearchState n κ) :
    compareCodes level code (twG f t st) = twG f t (compareCodes level code st) := by
  unfold compareCodes
  dsimp only [twG]
  split <;> split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all

theorem afterChildFirst_twG (f : Nat → Nat) (t : Array Int) (level tv : Nat) (st : SearchState n κ) :
    afterChildFirst level tv (twG f t st) = twG f t (afterChildFirst level tv st) := rfl

theorem afterSweep_twG (f : Nat → Nat) (t : Array Int) (first : Bool) (level size index : Nat)
    (st : SearchState n κ) :
    afterSweep first level size index (twG f t st) = twG f t (afterSweep first level size index st) := by
  unfold afterSweep
  dsimp only [twG]
  split <;> (try split) <;> simp_all

theorem leave_twG (f : Nat → Nat) (t : Array Int) (tv : Nat) (st : SearchState n κ) :
    ({ twG f t st with fixedpts := (twG f t st).fixedpts.erase tv } : SearchState n κ) =
      twG f t { st with fixedpts := st.fixedpts.erase tv } := rfl

theorem firstterminal_twG (f : Nat → Nat) (t : Array Int) (level : Nat) (st : SearchState n κ) :
    firstterminal level (twG f t st) = twG f (t.set! (level + 1) (-1)) (firstterminal level st) := by
  unfold firstterminal
  rfl

theorem scatter_twG (f : Nat → Nat) (t : Array Int) (refLab : Array Nat) (st : SearchState n κ) :
    scatter refLab (twG f t st) = twG f t (scatter refLab st) := by
  unfold scatter
  rfl

theorem pushAuto_twG (f : Nat → Nat) (t : Array Int) (pair : VSet n × VSet n) (st : SearchState n κ) :
    pushAuto (twG f t st) pair = twG f t (pushAuto st pair) := by
  unfold pushAuto
  by_cases h : (st.autos.size == st.wsCap) = true
  · have h' : ((twG f t st).autos.size == (twG f t st).wsCap) = true := h
    simp only [h, h', ite_true]; rfl
  · have h' : ¬ ((twG f t st).autos.size == (twG f t st).wsCap) = true := h
    simp only [h, h', ite_false, Bool.false_eq_true]; rfl

theorem admit_twG (f : Nat → Nat) (t : Array Int) (st : SearchState n κ) :
    admit (twG f t st) = twG f t (admit st) := by
  unfold admit
  simp only [Id.run]
  have : ({ twG f t st with genTrace := (twG f t st).genTrace.push (twG f t st).workperm } : SearchState n κ) =
      twG f t { st with genTrace := st.genTrace.push st.workperm } := rfl
  rw [this, pushAuto_twG]
  rfl

theorem install_twG (f : Nat → Nat) (t : Array Int) (level sr : Nat) (st : SearchState n κ) :
    install level sr (twG f t st) = twG f t (install level sr st) := rfl

theorem pruneReturn_twG {a b : Nat} (t : Array Int) (level : Nat) (st : SearchState n κ)
    (ha : st.noncheaplevel < a) (hb : st.noncheaplevel < b) :
    pruneReturn level (twG (phi a b) t st) =
      ((pruneReturn level st).1, twG (phi a b) t (pruneReturn level st).2) := by
  have hf : fmptn (twG (phi a b) t st).lab (twG (phi a b) t st).ptn (twG (phi a b) t st).noncheaplevel n =
      fmptn st.lab st.ptn st.noncheaplevel n :=
    (fmptn_congr (sameAt_map ha hb st.ptn) st.lab).symm
  unfold pruneReturn
  by_cases h : (level != st.noncheaplevel) = true
  · have h' : (level != (twG (phi a b) t st).noncheaplevel) = true := h
    simp only [Id.run, h, h', ite_true, hf]
    rw [pushAuto_twG]
    rfl
  · have h' : ¬ (level != (twG (phi a b) t st).noncheaplevel) = true := h
    simp only [Id.run, h, h', ite_false, Bool.false_eq_true]
    rfl

theorem leafExit_twG {a b : Nat} (t : Array Int) (leaf : Leaf) (level : Nat) (st : SearchState n κ)
    (ha : st.noncheaplevel < a) (hb : st.noncheaplevel < b) :
    leafExit leaf level (twG (phi a b) t st) =
      ((leafExit leaf level st).1, twG (phi a b) t (leafExit leaf level st).2) := by
  -- the `maxlevel` update commutes, and keeps `noncheaplevel`
  have hmax : ∀ (S : SearchState n κ), S.noncheaplevel = st.noncheaplevel →
      (match leaf with
        | .internal => ((Generic.Exit.done, twG (phi a b) t S) : Exit × SearchState n κ)
        | .autoFirst =>
          let s1 := admit (twG (phi a b) t S)
          let s2 := { s1 with numgenerators := s1.numgenerators + 1 }
          (Generic.Exit.unwind s2.gcaFirst false, s2)
        | .autoCanon =>
          let s1 := admit (twG (phi a b) t S)
          if s1.numorbits == (twG (phi a b) t S).numorbits then
            (Generic.Exit.unwind s1.gcaCanon (s1.gcaCanon != s1.gcaFirst), s1)
          else
            let s2 := { s1 with numgenerators := s1.numgenerators + 1 }
            if s2.orbits[s2.cosetindex]! < s2.cosetindex then (Generic.Exit.unwind s2.gcaFirst false, s2)
            else (Generic.Exit.unwind s2.gcaCanon (s2.gcaCanon != s2.gcaFirst), s2)
        | .better sr => pruneReturn level (install level sr (twG (phi a b) t S))
        | .bad => pruneReturn level { twG (phi a b) t S with numbadleaves := (twG (phi a b) t S).numbadleaves + 1 }) =
      (((match leaf with
        | .internal => ((Generic.Exit.done, S) : Exit × SearchState n κ)
        | .autoFirst =>
          let s1 := admit S
          let s2 := { s1 with numgenerators := s1.numgenerators + 1 }
          (Generic.Exit.unwind s2.gcaFirst false, s2)
        | .autoCanon =>
          let s1 := admit S
          if s1.numorbits == S.numorbits then
            (Generic.Exit.unwind s1.gcaCanon (s1.gcaCanon != s1.gcaFirst), s1)
          else
            let s2 := { s1 with numgenerators := s1.numgenerators + 1 }
            if s2.orbits[s2.cosetindex]! < s2.cosetindex then (Generic.Exit.unwind s2.gcaFirst false, s2)
            else (Generic.Exit.unwind s2.gcaCanon (s2.gcaCanon != s2.gcaFirst), s2)
        | .better sr => pruneReturn level (install level sr S)
        | .bad => pruneReturn level { S with numbadleaves := S.numbadleaves + 1 }).1),
        twG (phi a b) t (match leaf with
        | .internal => ((Generic.Exit.done, S) : Exit × SearchState n κ)
        | .autoFirst =>
          let s1 := admit S
          let s2 := { s1 with numgenerators := s1.numgenerators + 1 }
          (Generic.Exit.unwind s2.gcaFirst false, s2)
        | .autoCanon =>
          let s1 := admit S
          if s1.numorbits == S.numorbits then
            (Generic.Exit.unwind s1.gcaCanon (s1.gcaCanon != s1.gcaFirst), s1)
          else
            let s2 := { s1 with numgenerators := s1.numgenerators + 1 }
            if s2.orbits[s2.cosetindex]! < s2.cosetindex then (Generic.Exit.unwind s2.gcaFirst false, s2)
            else (Generic.Exit.unwind s2.gcaCanon (s2.gcaCanon != s2.gcaFirst), s2)
        | .better sr => pruneReturn level (install level sr S)
        | .bad => pruneReturn level { S with numbadleaves := S.numbadleaves + 1 }).2) := by
    intro S hS
    cases leaf with
    | internal => rfl
    | autoFirst => simp only [admit_twG]; rfl
    | autoCanon =>
      simp only [admit_twG]
      by_cases h1 : ((admit S).numorbits == S.numorbits) = true
      · have h1' : ((twG (phi a b) t (admit S)).numorbits == (twG (phi a b) t S).numorbits) = true := h1
        simp only [h1, h1', ite_true]; rfl
      · have h1' : ¬ ((twG (phi a b) t (admit S)).numorbits == (twG (phi a b) t S).numorbits) = true := h1
        simp only [h1, h1', ite_false, Bool.false_eq_true]
        by_cases h2 : (admit S).orbits[(admit S).cosetindex]! < (admit S).cosetindex
        · have h2' : ({ twG (phi a b) t (admit S) with
              numgenerators := (twG (phi a b) t (admit S)).numgenerators + 1 } : SearchState n κ).orbits[
              ({ twG (phi a b) t (admit S) with
                numgenerators := (twG (phi a b) t (admit S)).numgenerators + 1 } : SearchState n κ).cosetindex]! <
              ({ twG (phi a b) t (admit S) with
                numgenerators := (twG (phi a b) t (admit S)).numgenerators + 1 } : SearchState n κ).cosetindex := h2
          simp only [h2, h2', ite_true]; rfl
        · have h2' : ¬ ({ twG (phi a b) t (admit S) with
              numgenerators := (twG (phi a b) t (admit S)).numgenerators + 1 } : SearchState n κ).orbits[
              ({ twG (phi a b) t (admit S) with
                numgenerators := (twG (phi a b) t (admit S)).numgenerators + 1 } : SearchState n κ).cosetindex]! <
              ({ twG (phi a b) t (admit S) with
                numgenerators := (twG (phi a b) t (admit S)).numgenerators + 1 } : SearchState n κ).cosetindex := h2
          simp only [h2, h2', ite_false]; rfl
    | better sr =>
      simp only [install_twG]
      exact pruneReturn_twG t level _ (by show S.noncheaplevel < a; omega) (by show S.noncheaplevel < b; omega)
    | bad =>
      exact pruneReturn_twG t level { S with numbadleaves := S.numbadleaves + 1 }
        (by show S.noncheaplevel < a; omega) (by show S.noncheaplevel < b; omega)
  unfold leafExit
  simp only [Id.run]
  by_cases c0 : (leaf != .internal && decide (level > st.maxlevel)) = true
  · have c0' : (leaf != .internal && decide (level > (twG (phi a b) t st).maxlevel)) = true := c0
    simp only [c0, c0', ite_true]
    exact hmax { st with maxlevel := level } rfl
  · have c0' : ¬ (leaf != .internal && decide (level > (twG (phi a b) t st).maxlevel)) = true := c0
    simp only [c0, c0', ite_false, Bool.false_eq_true]
    exact hmax st rfl

theorem cheapCheck_twG {a b : Nat} (t : Array Int) (first : Bool) (level : Nat) (st : SearchState n κ)
    (ha : level < a) (hb : level < b) :
    cheapCheck first level (twG (phi a b) t st) = twG (phi a b) t (cheapCheck first level st) := by
  have hc : cheapautom (twG (phi a b) t st).ptn level n = cheapautom st.ptn level n :=
    (cheapautom_congr (sameAt_map ha hb st.ptn)).symm
  unfold cheapCheck
  rw [hc]
  by_cases h : ((!first || decide (st.noncheaplevel ≥ level)) && !cheapautom st.ptn level n) = true
  · have h' : ((!first || decide ((twG (phi a b) t st).noncheaplevel ≥ level)) &&
        !cheapautom st.ptn level n) = true := h
    simp only [h, h', ite_true]; rfl
  · have h' : ¬ ((!first || decide ((twG (phi a b) t st).noncheaplevel ≥ level)) &&
        !cheapautom st.ptn level n) = true := h
    simp only [h, h', ite_false, Bool.false_eq_true]

theorem child_twG {a b : Nat} (t : Array Int) (first : Bool) (level tc tv : Nat) (st : SearchState n κ)
    (ha : level + 1 ≠ a) :
    child first level tc tv (twG (phi a b) t st) = twG (phi a b) t (child first level tc tv st) := by
  unfold child breakout
  cases first <;> simp only [twG, set_phi ha, Bool.false_eq_true, ite_false, ite_true]

theorem recoverLevels_twG (f : Nat → Nat) (t : Array Int) (level : Nat) (st : SearchState n κ) :
    recoverLevels level (twG f t st) = twG f t (recoverLevels level st) := by
  unfold recoverLevels
  dsimp only [twG]
  split <;> split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> (try split) <;> simp_all

theorem recoverPtn_twG {a b : Nat} (t : Array Int) (level : Nat) (st : SearchState n κ)
    (ha : level < a) (hb : level < b) :
    recoverPtn b level (twG (phi a b) t st) = twG (phi a b) t (recoverPtn a level st) := by
  unfold recoverPtn
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [show (twG (phi a b) t st).ptn = st.ptn.map (phi a b) from rfl, recoverLoop_map ha hb]
  rfl

theorem recover_twG {a b : Nat} (t : Array Int) (level : Nat) (st : SearchState n κ)
    (ha : level < a) (hb : level < b) :
    recover b level (twG (phi a b) t st) = twG (phi a b) t (recover a level st) := by
  unfold recover
  rw [recoverPtn_twG t level st ha hb, recoverLevels_twG]


theorem tw_eq_twG (f : Nat → Nat) (t : Array Int) (st : Search n) : tw f t st = twG f t st := rfl

end NautyVerified.Spec.SearchInf
