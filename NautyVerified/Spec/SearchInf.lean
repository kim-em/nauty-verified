import HexGraphIso.Nauty.Policy.Partition
import HexGraphIso.Nauty.Policy.Classify

/-!
# The search does not depend on the value written for "infinity"

nauty marks the positions of `ptn` that do not end a cell at any level with
`NAUTY_INFINITY = 2000000002`; HexGraphIso's search writes `n + 2` instead.
Every reader compares `ptn[i]! > level` for levels at most `n + 1`, so only
whether an entry exceeds the level matters.

`phi a b` sends `a` to `b` and fixes everything else. Reading
`ptn.map (phi a b)` instead of `ptn` changes no comparison with a level below
both `a` and `b` (`SameAt`), so the read-only partition functions agree on
the two arrays, and the functions writing levels into `ptn` commute with the
map.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {n : Nat}

/-- Send `a` to `b`, fixing every other value. -/
def phi (a b v : Nat) : Nat := if v = a then b else v

theorem phi_ne {a b v : Nat} (h : v ≠ a) : phi a b v = v := by simp [phi, h]

/-- Two `ptn` arrays of the same size agree on every comparison with `level`. -/
def SameAt (level : Nat) (p q : Array Nat) : Prop :=
  p.size = q.size ∧ ∀ i : Nat, (level < p[i]!) ↔ (level < q[i]!)

theorem getElem!_map_phi {a b : Nat} (ha : a ≠ 0) (p : Array Nat) (i : Nat) :
    (p.map (phi a b))[i]! = phi a b p[i]! := by
  rcases Nat.lt_or_ge i p.size with hi | hi
  · rw [getElem!_pos (p.map (phi a b)) i (by simpa using hi), getElem!_pos p i hi]
    simp
  · rw [getElem!_neg (p.map (phi a b)) i (by simpa using Nat.not_lt.2 hi),
      getElem!_neg p i (Nat.not_lt.2 hi)]
    exact (phi_ne (Ne.symm ha)).symm

theorem sameAt_map {a b level : Nat} (ha : level < a) (hb : level < b) (p : Array Nat) :
    SameAt level p (p.map (phi a b)) := by
  refine ⟨(Array.size_map ..).symm, fun i => ?_⟩
  rw [getElem!_map_phi (by omega)]
  unfold phi
  split
  · rename_i h; rw [h]; omega
  · exact Iff.rfl

theorem SameAt.le {level : Nat} {p q : Array Nat} (h : SameAt level p q) (i : Nat) :
    (p[i]! ≤ level) ↔ (q[i]! ≤ level) := by
  rw [← Nat.not_lt, ← Nat.not_lt]; exact not_congr (h.2 i)

theorem cellEnd_go_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q) :
    ∀ fuel j, cellEnd.go p level fuel j = cellEnd.go q level fuel j
  | 0, _ => rfl
  | fuel + 1, j => by
    simp only [cellEnd.go, GT.gt]
    by_cases hc : level < p[j]!
    · rw [ite_eq_left hc, ite_eq_left ((h.2 j).1 hc), cellEnd_go_congr h fuel]
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((h.2 j).2 h'))]

theorem cellEnd_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q) (i : Nat) :
    cellEnd p level i = cellEnd q level i := by
  unfold cellEnd; rw [cellEnd_go_congr h, h.1]

theorem cells_go_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q) :
    ∀ fuel c1, cells.go p level n fuel c1 = cells.go q level n fuel c1
  | 0, _ => rfl
  | fuel + 1, c1 => by
    simp only [cells.go, cellEnd_congr h, cells_go_congr h fuel]

theorem cells_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q) :
    cells p level n = cells q level n := by
  unfold cells; exact cells_go_congr h _ _

theorem bestcellRows_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q) (ctx : Ctx n)
    (lab startArr : Array Nat) :
    ∀ (l : List Nat) (bucket : Array Nat),
      bestcellRows ctx lab p level startArr l bucket = bestcellRows ctx lab q level startArr l bucket
  | [], _ => rfl
  | v2 :: rest, bucket => by
    simp only [bestcellRows, cellEnd_congr h]
    exact bestcellRows_congr h ctx lab startArr rest _

theorem bestcell_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q) (ctx : Ctx n)
    (lab : Array Nat) : bestcell ctx lab p level = bestcell ctx lab q level := by
  unfold bestcell
  rw [cells_congr h]
  simp only [bestcellRows_congr h]

theorem targetcell_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q) (ctx : Ctx n)
    (lab : Array Nat) (tcLevel : Nat) (hint : Int) :
    targetcell ctx lab p level tcLevel hint = targetcell ctx lab q level tcLevel hint := by
  unfold targetcell
  rw [bestcell_congr h, cells_congr h]
  have e : (hint ≥ 0 ∧ p[hint.toNat]! > level ∧ (hint == 0 ∨ p[hint.toNat - 1]! ≤ level)) ↔
      (hint ≥ 0 ∧ q[hint.toNat]! > level ∧ (hint == 0 ∨ q[hint.toNat - 1]! ≤ level)) := by
    rw [GT.gt, GT.gt, h.2, h.le]
  by_cases hc : hint ≥ 0 ∧ p[hint.toNat]! > level ∧ (hint == 0 ∨ p[hint.toNat - 1]! ≤ level)
  · rw [ite_eq_left hc, ite_eq_left (e.1 hc)]
  · rw [ite_eq_right hc, ite_eq_right (fun h' => hc (e.2 h'))]

theorem maketargetcell_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q) (ctx : Ctx n)
    (lab : Array Nat) (tcLevel : Nat) (hint : Int) :
    maketargetcell ctx lab p level tcLevel hint = maketargetcell ctx lab q level tcLevel hint := by
  unfold maketargetcell
  simp only [targetcell_congr h, cellEnd_congr h]

theorem cheapautom_go_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q) :
    ∀ fuel i k nnt, cheapautom.go p level fuel i k nnt = cheapautom.go q level fuel i k nnt
  | 0, _, _, _ => rfl
  | fuel + 1, i, k, nnt => by
    simp only [cheapautom.go, h.1, GT.gt, cellEnd_congr h]
    by_cases hi : i < q.size
    · rw [ite_eq_left hi, ite_eq_left hi]
      by_cases hc : level < p[i]!
      · rw [ite_eq_left hc, ite_eq_left ((h.2 i).1 hc), cheapautom_go_congr h]
      · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((h.2 i).2 h')), cheapautom_go_congr h]
    · rw [ite_eq_right hi, ite_eq_right hi]

theorem cheapautom_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q) :
    cheapautom p level n = cheapautom q level n := by
  unfold cheapautom; rw [cheapautom_go_congr h]

theorem fmptn_congr {level : Nat} {p q : Array Nat} (h : SameAt level p q) (lab : Array Nat) :
    fmptn lab p level n = fmptn lab q level n := by
  unfold fmptn; rw [cells_congr h]

/-! ## Refinement commutes with the map -/

/-- `rs` with its `ptn` mapped. -/
def mapR (f : Nat → Nat) (rs : RefineSt n) : RefineSt n := { rs with ptn := rs.ptn.map f }

theorem set_phi {a b L : Nat} (hL : L ≠ a) (p : Array Nat) (i : Nat) :
    (p.set! i L).map (phi a b) = (p.map (phi a b)).set! i L := by
  simp only [Array.set!, Array.map_setIfInBounds, phi_ne hL]

section
variable {a b level : Nat} (ha : level < a) (hb : level < b)
include ha hb

theorem trivialSplit_map (cell1 cell2 : Nat) (c1 c2 : Int) (st : RefineSt n) :
    trivialSplit level cell1 cell2 c1 c2 (mapR (phi a b) st) =
      mapR (phi a b) (trivialSplit level cell1 cell2 c1 c2 st) := by
  have hL : level ≠ a := by omega
  unfold trivialSplit
  simp only [mapR]
  by_cases h1 : c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2
  · by_cases h2 : st.active.mem cell1 = true ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat
    · by_cases h3 : (c1.toNat == cell2) = true
      · simp only [ite_eq_left h1, ite_eq_left h2, ite_eq_left h3, set_phi hL]
      · simp only [ite_eq_left h1, ite_eq_left h2, ite_eq_right h3, set_phi hL]
    · by_cases h3 : (c2.toNat == cell1) = true
      · simp only [ite_eq_left h1, ite_eq_right h2, ite_eq_left h3, set_phi hL]
      · simp only [ite_eq_left h1, ite_eq_right h2, ite_eq_right h3, set_phi hL]
  · simp only [ite_eq_right h1]

theorem trivialCell_map (gRow : VSet n) (cell1 cell2 : Nat) (st : RefineSt n) :
    trivialCell level gRow cell1 cell2 (mapR (phi a b) st) =
      mapR (phi a b) (trivialCell level gRow cell1 cell2 st) := by
  unfold trivialCell
  split
  · rfl
  · exact trivialSplit_map ha hb cell1 cell2 _ _ { st with lab := _ }

theorem refineTrivial_go_map (gRow : VSet n) :
    ∀ (l : List (Nat × Nat)) (st : RefineSt n),
      refineTrivial.go level gRow l (mapR (phi a b) st) =
        mapR (phi a b) (refineTrivial.go level gRow l st)
  | [], _ => rfl
  | (c1, c2) :: rest, st => by
    simp only [refineTrivial.go, trivialCell_map ha hb, refineTrivial_go_map gRow rest]

theorem refineTrivial_map (ctx : Ctx n) (split1 : Nat) (st : RefineSt n) :
    refineTrivial ctx level split1 (mapR (phi a b) st) =
      mapR (phi a b) (refineTrivial ctx level split1 st) := by
  unfold refineTrivial
  have hc : cells (mapR (phi a b) st).ptn level n = cells st.ptn level n :=
    (cells_congr (sameAt_map ha hb st.ptn)).symm
  rw [hc]
  exact refineTrivial_go_map ha hb _ _ _

theorem windowStep_map (cell1 cell2 v c1 c2 : Nat) (maxcell : Int) (st : RefineSt n) :
    windowStep level cell1 cell2 v c1 c2 maxcell (mapR (phi a b) st) =
      mapR (phi a b) (windowStep level cell1 cell2 v c1 c2 maxcell st) := by
  have hL : level ≠ a := by omega
  by_cases h1 : Int.ofNat (c2 - c1) > maxcell <;> by_cases h2 : (c1 != cell1) = true <;>
    by_cases h3 : (c2 - c1 == 1) = true <;> by_cases h4 : c2 ≤ cell2 <;>
    simp only [windowStep, mapR, h1, h2, h3, h4, ite_true, ite_false, Bool.false_eq_true,
      set_phi hL]

theorem windowScan_map (cell1 cell2 : Nat) (counts : List Nat) :
    ∀ (vs : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt n),
      windowScan level cell1 cell2 counts vs c1 maxcell (mapR (phi a b) st) =
        mapR (phi a b) (windowScan level cell1 cell2 counts vs c1 maxcell st)
  | [], _, _, _ => rfl
  | v :: vs, c1, maxcell, st => by
    simp only [windowScan]
    split
    · rw [windowStep_map ha hb, windowScan_map cell1 cell2 counts vs]
    · exact windowScan_map cell1 cell2 counts vs _ _ _

omit ha hb in
theorem nontrivialFix_map (f : Nat → Nat) (cell1 : Nat) (st : RefineSt n) :
    nontrivialFix cell1 (mapR f st) = mapR f (nontrivialFix cell1 st) := by
  unfold nontrivialFix
  by_cases h : st.active.mem cell1 = true
  · simp only [mapR, h, not_true_eq_false, ite_false]
  · simp only [mapR, h, Bool.false_eq_true, not_false_eq_true, ite_true]

theorem nontrivialCell_map (ctx : Ctx n) (workset : VSet n) (cell1 cell2 : Nat) (st : RefineSt n) :
    nontrivialCell ctx level workset cell1 cell2 (mapR (phi a b) st) =
      mapR (phi a b) (nontrivialCell ctx level workset cell1 cell2 st) := by
  have hl : (mapR (phi a b) st).lab = st.lab := rfl
  have hc : (mapR (phi a b) st).longcode = st.longcode := rfl
  unfold nontrivialCell
  rw [hl, hc]
  by_cases h1 : (cell1 == cell2) = true
  · simp only [h1, ite_true]
  · simp only [h1, Bool.false_eq_true, ite_false]
    by_cases h2 : (List.foldl Nat.min ((countsOf ctx st.lab workset cell1 cell2).headD 0)
        (countsOf ctx st.lab workset cell1 cell2) ==
        List.foldl Nat.max ((countsOf ctx st.lab workset cell1 cell2).headD 0)
          (countsOf ctx st.lab workset cell1 cell2)) = true
    · simp only [h2, ite_true]; rfl
    · simp only [h2, Bool.false_eq_true, ite_false]
      rw [windowScan_map ha hb, ← nontrivialFix_map]
      rfl

theorem refineNontrivial_go_map (ctx : Ctx n) (workset : VSet n) :
    ∀ (l : List (Nat × Nat)) (st : RefineSt n),
      refineNontrivial.go ctx level workset l (mapR (phi a b) st) =
        mapR (phi a b) (refineNontrivial.go ctx level workset l st)
  | [], _ => rfl
  | (c1, c2) :: rest, st => by
    simp only [refineNontrivial.go, nontrivialCell_map ha hb, refineNontrivial_go_map ctx workset rest]

theorem refineNontrivial_map (ctx : Ctx n) (split1 split2 : Nat) (st : RefineSt n) :
    refineNontrivial ctx level split1 split2 (mapR (phi a b) st) =
      mapR (phi a b) (refineNontrivial ctx level split1 split2 st) := by
  have hc : cells (mapR (phi a b) st).ptn level n = cells st.ptn level n :=
    (cells_congr (sameAt_map ha hb st.ptn)).symm
  unfold refineNontrivial
  dsimp only
  rw [hc]
  exact refineNontrivial_go_map ha hb ctx _ _ { st with longcode := mash st.longcode (split2 - split1 + 1) }

theorem refineStep_map (ctx : Ctx n) (split1 : Nat) (st : RefineSt n) :
    refineStep ctx level split1 (mapR (phi a b) st) =
      mapR (phi a b) (refineStep ctx level split1 st) := by
  have hce : cellEnd (mapR (phi a b) st).ptn level split1 = cellEnd st.ptn level split1 :=
    (cellEnd_congr (sameAt_map ha hb st.ptn) split1).symm
  unfold refineStep
  dsimp only
  rw [hce]
  by_cases hs : (split1 == cellEnd st.ptn level split1) = true
  · simp only [hs, ite_true]
    exact refineTrivial_map ha hb ctx split1
      { st with
        active := st.active.erase split1
        longcode := mash st.longcode (split1 + cellEnd st.ptn level split1) }
  · simp only [hs, Bool.false_eq_true, ite_false]
    exact refineNontrivial_map ha hb ctx split1 _
      { st with
        active := st.active.erase split1
        longcode := mash st.longcode (split1 + cellEnd st.ptn level split1) }

theorem refineLoop_map (ctx : Ctx n) :
    ∀ (fuel : Nat) (st : RefineSt n),
      refineLoop ctx level fuel (mapR (phi a b) st) = mapR (phi a b) (refineLoop ctx level fuel st)
  | 0, _ => rfl
  | fuel + 1, st => by
    have hn : (mapR (phi a b) st).numcells = st.numcells := rfl
    have ha' : (mapR (phi a b) st).active = st.active := rfl
    have hh : (mapR (phi a b) st).hint = st.hint := rfl
    rw [refineLoop, refineLoop, hn, ha', hh]
    by_cases hc : st.numcells < n
    · simp only [hc, ite_true]
      cases pickSplit st.active st.hint with
      | none => rfl
      | some s => simp only [refineStep_map ha hb, refineLoop_map ctx fuel]
    · simp only [hc, ite_false]

theorem refine_map (ctx : Ctx n) (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) :
    refine ctx level lab (ptn.map (phi a b)) active numcells =
      mapR (phi a b) (refine ctx level lab ptn active numcells) := by
  unfold refine
  have := refineLoop_map ha hb ctx (4 * n + 8)
    { lab, ptn, active, numcells, hint := 0, maxpos := 0, longcode := numcells }
  simp only [mapR] at this ⊢
  rw [this]

end

/-! ## Search operations commute with the map -/

/-- `st` with its `ptn` mapped by `f` and `firsttc` replaced by `t`. -/
def tw (f : Nat → Nat) (t : Array Int) (st : Search n) : Search n :=
  { st with ptn := st.ptn.map f, firsttc := t }

@[simp] theorem tw_lab (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).lab = st.lab := rfl
@[simp] theorem tw_active (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).active = st.active := rfl
@[simp] theorem tw_orbits (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).orbits = st.orbits := rfl
@[simp] theorem tw_fixedpts (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).fixedpts = st.fixedpts := rfl
@[simp] theorem tw_autos (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).autos = st.autos := rfl
@[simp] theorem tw_wsCap (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).wsCap = st.wsCap := rfl
@[simp] theorem tw_firstcode (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).firstcode = st.firstcode := rfl
@[simp] theorem tw_canoncode (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).canoncode = st.canoncode := rfl
@[simp] theorem tw_firstlab (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).firstlab = st.firstlab := rfl
@[simp] theorem tw_canonlab (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).canonlab = st.canonlab := rfl
@[simp] theorem tw_canong (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).canong = st.canong := rfl
@[simp] theorem tw_samerows (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).samerows = st.samerows := rfl
@[simp] theorem tw_compCanon (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).compCanon = st.compCanon := rfl
@[simp] theorem tw_eqlevFirst (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).eqlevFirst = st.eqlevFirst := rfl
@[simp] theorem tw_eqlevCanon (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).eqlevCanon = st.eqlevCanon := rfl
@[simp] theorem tw_gcaFirst (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).gcaFirst = st.gcaFirst := rfl
@[simp] theorem tw_gcaCanon (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).gcaCanon = st.gcaCanon := rfl
@[simp] theorem tw_canonlevel (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).canonlevel = st.canonlevel := rfl
@[simp] theorem tw_noncheaplevel (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).noncheaplevel = st.noncheaplevel := rfl
@[simp] theorem tw_allsamelevel (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).allsamelevel = st.allsamelevel := rfl
@[simp] theorem tw_cosetindex (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).cosetindex = st.cosetindex := rfl
@[simp] theorem tw_stabvertex (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).stabvertex = st.stabvertex := rfl
@[simp] theorem tw_numnodes (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).numnodes = st.numnodes := rfl
@[simp] theorem tw_tctotal (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).tctotal = st.tctotal := rfl
@[simp] theorem tw_canupdates (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).canupdates = st.canupdates := rfl
@[simp] theorem tw_numorbits (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).numorbits = st.numorbits := rfl
@[simp] theorem tw_numgenerators (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).numgenerators = st.numgenerators := rfl
@[simp] theorem tw_numbadleaves (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).numbadleaves = st.numbadleaves := rfl
@[simp] theorem tw_maxlevel (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).maxlevel = st.maxlevel := rfl
@[simp] theorem tw_order (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).order = st.order := rfl
@[simp] theorem tw_genTrace (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).genTrace = st.genTrace := rfl
@[simp] theorem tw_workperm (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).workperm = st.workperm := rfl
@[simp] theorem tw_ptn (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).ptn = st.ptn.map f := rfl
@[simp] theorem tw_firsttc (f : Nat → Nat) (t : Array Int) (st : Search n) : (tw f t st).firsttc = t := rfl

theorem recordFirst_tw (f : Nat → Nat) (t : Array Int) (level code : Nat) (st : Search n) :
    recordFirst level code (tw f t st) = tw f t (recordFirst level code st) := rfl

theorem compareCodes_tw (f : Nat → Nat) (t : Array Int) (level code : Nat) (st : Search n) :
    compareCodes level code (tw f t st) = tw f t (compareCodes level code st) := by
  unfold compareCodes
  dsimp only [tw]
  split <;> split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all

theorem afterChildFirst_tw (f : Nat → Nat) (t : Array Int) (level tv : Nat) (st : Search n) :
    afterChildFirst level tv (tw f t st) = tw f t (afterChildFirst level tv st) := rfl

theorem afterSweep_tw (f : Nat → Nat) (t : Array Int) (first : Bool) (level size index : Nat)
    (st : Search n) :
    afterSweep first level size index (tw f t st) = tw f t (afterSweep first level size index st) := by
  unfold afterSweep
  dsimp only [tw]
  split <;> (try split) <;> simp_all

theorem leave_tw (f : Nat → Nat) (t : Array Int) (tv : Nat) (st : Search n) :
    ({ tw f t st with fixedpts := (tw f t st).fixedpts.erase tv } : Search n) =
      tw f t { st with fixedpts := st.fixedpts.erase tv } := rfl

theorem firstterminal_tw (f : Nat → Nat) (t : Array Int) (level : Nat) (st : Search n) :
    firstterminal level (tw f t st) = tw f (t.set! (level + 1) (-1)) (firstterminal level st) := by
  unfold firstterminal
  rfl

theorem scatter_tw (f : Nat → Nat) (t : Array Int) (refLab : Array Nat) (st : Search n) :
    scatter refLab (tw f t st) = tw f t (scatter refLab st) := by
  unfold scatter
  rfl

theorem canonVerdict_tw (f : Nat → Nat) (t : Array Int) (ctx : Ctx n) (level : Nat) (st : Search n) :
    canonVerdict ctx level (tw f t st) =
      ((canonVerdict ctx level st).1, tw f t (canonVerdict ctx level st).2) := by
  by_cases hcomp : st.compCanon = 0
  · by_cases hlevel : level < st.canonlevel
    · simp only [canonVerdict, tw_compCanon, tw_canonlevel, hcomp, beq_self_eq_true, ite_true, hlevel,
        Id.run_pure, apply_ite Id.run]
      rfl
    · simp only [canonVerdict, tw_compCanon, tw_canonlevel, hcomp, beq_self_eq_true, ite_true, hlevel,
        ite_false, Id.run_pure, apply_ite Id.run]
      by_cases h1 : ((testcanlab ctx (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 == 0) = true
      · simp only [tw_canong, tw_canonlab, tw_samerows, tw_lab, h1, ite_true]
        rfl
      · simp only [tw_canong, tw_canonlab, tw_samerows, tw_lab, h1, Bool.false_eq_true, ite_false]
        by_cases h2 : (testcanlab ctx (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 > 0
        · simp only [h2, ite_true]; rfl
        · simp only [h2, ite_false]; rfl
  · simp only [canonVerdict, tw_compCanon, beq_eq_false_iff_ne.mpr hcomp, Bool.false_eq_true, ite_false,
      Id.run_pure, apply_ite Id.run]
    by_cases h2 : st.compCanon > 0
    · simp only [h2, ite_true]; rfl
    · simp only [h2, ite_false]; rfl

theorem classify_tw (f : Nat → Nat) (t : Array Int) (ctx : Ctx n) (level numcells : Nat)
    (st : Search n) :
    classify ctx level numcells (tw f t st) =
      ((classify ctx level numcells st).1, tw f t (classify ctx level numcells st).2) := by
  rw [classify_eq, classify_eq]
  by_cases c1 : (st.eqlevFirst != level && decide (st.compCanon < 0)) = true
  · have c1' : ((tw f t st).eqlevFirst != level && decide ((tw f t st).compCanon < 0)) = true := c1
    simp only [c1, c1', ite_true, Bool.false_eq_true, ite_false]
  · have c1' : ¬ ((tw f t st).eqlevFirst != level && decide ((tw f t st).compCanon < 0)) = true := c1
    simp only [c1, c1', ite_false, Bool.false_eq_true]
    by_cases c2 : (numcells != n) = true
    · simp only [c2, ite_true, Bool.false_eq_true, ite_false]
    · simp only [c2, ite_false, Bool.false_eq_true]
      by_cases c3 : (st.eqlevFirst == level) = true
      · have c3' : ((tw f t st).eqlevFirst == level) = true := c3
        simp only [c3, c3', ite_true, Bool.false_eq_true, ite_false]
        have hs : scatter (tw f t st).firstlab (tw f t st) = tw f t (scatter st.firstlab st) :=
          scatter_tw f t st.firstlab st
        rw [hs]
        by_cases c4 : (decide ((scatter st.firstlab st).gcaFirst ≥ (scatter st.firstlab st).noncheaplevel) ||
            isautom ctx (scatter st.firstlab st).workperm) = true
        · have c4' : (decide ((tw f t (scatter st.firstlab st)).gcaFirst ≥
              (tw f t (scatter st.firstlab st)).noncheaplevel) ||
              isautom ctx (tw f t (scatter st.firstlab st)).workperm) = true := c4
          simp only [c4, c4', ite_true, Bool.false_eq_true, ite_false]
        · have c4' : ¬ (decide ((tw f t (scatter st.firstlab st)).gcaFirst ≥
              (tw f t (scatter st.firstlab st)).noncheaplevel) ||
              isautom ctx (tw f t (scatter st.firstlab st)).workperm) = true := c4
          simp only [c4, c4', ite_false, Bool.false_eq_true]
          exact canonVerdict_tw f t ctx level _
      · have c3' : ¬ ((tw f t st).eqlevFirst == level) = true := c3
        simp only [c3, c3', ite_false, Bool.false_eq_true]
        exact canonVerdict_tw f t ctx level st

theorem pushAuto_tw (f : Nat → Nat) (t : Array Int) (pair : VSet n × VSet n) (st : Search n) :
    pushAuto (tw f t st) pair = tw f t (pushAuto st pair) := by
  unfold pushAuto
  by_cases h : (st.autos.size == st.wsCap) = true
  · have h' : ((tw f t st).autos.size == (tw f t st).wsCap) = true := h
    simp only [h, h', ite_true]; rfl
  · have h' : ¬ ((tw f t st).autos.size == (tw f t st).wsCap) = true := h
    simp only [h, h', ite_false, Bool.false_eq_true]; rfl

theorem admit_tw (f : Nat → Nat) (t : Array Int) (st : Search n) :
    admit (tw f t st) = tw f t (admit st) := by
  unfold admit
  simp only [Id.run]
  have : ({ tw f t st with genTrace := (tw f t st).genTrace.push (tw f t st).workperm } : Search n) =
      tw f t { st with genTrace := st.genTrace.push st.workperm } := rfl
  rw [this, pushAuto_tw]
  rfl

theorem install_tw (f : Nat → Nat) (t : Array Int) (level sr : Nat) (st : Search n) :
    install level sr (tw f t st) = tw f t (install level sr st) := rfl

theorem pruneReturn_tw {a b : Nat} (t : Array Int) (level : Nat) (st : Search n)
    (ha : st.noncheaplevel < a) (hb : st.noncheaplevel < b) :
    pruneReturn level (tw (phi a b) t st) =
      ((pruneReturn level st).1, tw (phi a b) t (pruneReturn level st).2) := by
  have hf : fmptn (tw (phi a b) t st).lab (tw (phi a b) t st).ptn (tw (phi a b) t st).noncheaplevel n =
      fmptn st.lab st.ptn st.noncheaplevel n :=
    (fmptn_congr (sameAt_map ha hb st.ptn) st.lab).symm
  unfold pruneReturn
  by_cases h : (level != st.noncheaplevel) = true
  · have h' : (level != (tw (phi a b) t st).noncheaplevel) = true := h
    simp only [Id.run, h, h', ite_true, hf]
    rw [pushAuto_tw]
    rfl
  · have h' : ¬ (level != (tw (phi a b) t st).noncheaplevel) = true := h
    simp only [Id.run, h, h', ite_false, Bool.false_eq_true]
    rfl

theorem leafExit_tw {a b : Nat} (t : Array Int) (leaf : Leaf) (level : Nat) (st : Search n)
    (ha : st.noncheaplevel < a) (hb : st.noncheaplevel < b) :
    leafExit leaf level (tw (phi a b) t st) =
      ((leafExit leaf level st).1, tw (phi a b) t (leafExit leaf level st).2) := by
  -- the `maxlevel` update commutes, and keeps `noncheaplevel`
  have hmax : ∀ (S : Search n), S.noncheaplevel = st.noncheaplevel →
      (match leaf with
        | .internal => ((Generic.Exit.done, tw (phi a b) t S) : Exit × Search n)
        | .autoFirst =>
          let s1 := admit (tw (phi a b) t S)
          let s2 := { s1 with numgenerators := s1.numgenerators + 1 }
          (Generic.Exit.unwind s2.gcaFirst false, s2)
        | .autoCanon =>
          let s1 := admit (tw (phi a b) t S)
          if s1.numorbits == (tw (phi a b) t S).numorbits then
            (Generic.Exit.unwind s1.gcaCanon (s1.gcaCanon != s1.gcaFirst), s1)
          else
            let s2 := { s1 with numgenerators := s1.numgenerators + 1 }
            if s2.orbits[s2.cosetindex]! < s2.cosetindex then (Generic.Exit.unwind s2.gcaFirst false, s2)
            else (Generic.Exit.unwind s2.gcaCanon (s2.gcaCanon != s2.gcaFirst), s2)
        | .better sr => pruneReturn level (install level sr (tw (phi a b) t S))
        | .bad => pruneReturn level { tw (phi a b) t S with numbadleaves := (tw (phi a b) t S).numbadleaves + 1 }) =
      (((match leaf with
        | .internal => ((Generic.Exit.done, S) : Exit × Search n)
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
        tw (phi a b) t (match leaf with
        | .internal => ((Generic.Exit.done, S) : Exit × Search n)
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
    | autoFirst => simp only [admit_tw]; rfl
    | autoCanon =>
      simp only [admit_tw]
      by_cases h1 : ((admit S).numorbits == S.numorbits) = true
      · have h1' : ((tw (phi a b) t (admit S)).numorbits == (tw (phi a b) t S).numorbits) = true := h1
        simp only [h1, h1', ite_true]; rfl
      · have h1' : ¬ ((tw (phi a b) t (admit S)).numorbits == (tw (phi a b) t S).numorbits) = true := h1
        simp only [h1, h1', ite_false, Bool.false_eq_true]
        by_cases h2 : (admit S).orbits[(admit S).cosetindex]! < (admit S).cosetindex
        · have h2' : ({ tw (phi a b) t (admit S) with
              numgenerators := (tw (phi a b) t (admit S)).numgenerators + 1 } : Search n).orbits[
              ({ tw (phi a b) t (admit S) with
                numgenerators := (tw (phi a b) t (admit S)).numgenerators + 1 } : Search n).cosetindex]! <
              ({ tw (phi a b) t (admit S) with
                numgenerators := (tw (phi a b) t (admit S)).numgenerators + 1 } : Search n).cosetindex := h2
          simp only [h2, h2', ite_true]; rfl
        · have h2' : ¬ ({ tw (phi a b) t (admit S) with
              numgenerators := (tw (phi a b) t (admit S)).numgenerators + 1 } : Search n).orbits[
              ({ tw (phi a b) t (admit S) with
                numgenerators := (tw (phi a b) t (admit S)).numgenerators + 1 } : Search n).cosetindex]! <
              ({ tw (phi a b) t (admit S) with
                numgenerators := (tw (phi a b) t (admit S)).numgenerators + 1 } : Search n).cosetindex := h2
          simp only [h2, h2', ite_false]; rfl
    | better sr =>
      simp only [install_tw]
      exact pruneReturn_tw t level _ (by show S.noncheaplevel < a; omega) (by show S.noncheaplevel < b; omega)
    | bad =>
      exact pruneReturn_tw t level { S with numbadleaves := S.numbadleaves + 1 }
        (by show S.noncheaplevel < a; omega) (by show S.noncheaplevel < b; omega)
  unfold leafExit
  simp only [Id.run]
  by_cases c0 : (leaf != .internal && decide (level > st.maxlevel)) = true
  · have c0' : (leaf != .internal && decide (level > (tw (phi a b) t st).maxlevel)) = true := c0
    simp only [c0, c0', ite_true]
    exact hmax { st with maxlevel := level } rfl
  · have c0' : ¬ (leaf != .internal && decide (level > (tw (phi a b) t st).maxlevel)) = true := c0
    simp only [c0, c0', ite_false, Bool.false_eq_true]
    exact hmax st rfl

theorem cheapCheck_tw {a b : Nat} (t : Array Int) (first : Bool) (level : Nat) (st : Search n)
    (ha : level < a) (hb : level < b) :
    cheapCheck first level (tw (phi a b) t st) = tw (phi a b) t (cheapCheck first level st) := by
  have hc : cheapautom (tw (phi a b) t st).ptn level n = cheapautom st.ptn level n :=
    (cheapautom_congr (sameAt_map ha hb st.ptn)).symm
  unfold cheapCheck
  rw [hc]
  by_cases h : ((!first || decide (st.noncheaplevel ≥ level)) && !cheapautom st.ptn level n) = true
  · have h' : ((!first || decide ((tw (phi a b) t st).noncheaplevel ≥ level)) &&
        !cheapautom st.ptn level n) = true := h
    simp only [h, h', ite_true]; rfl
  · have h' : ¬ ((!first || decide ((tw (phi a b) t st).noncheaplevel ≥ level)) &&
        !cheapautom st.ptn level n) = true := h
    simp only [h, h', ite_false, Bool.false_eq_true]

theorem child_tw {a b : Nat} (t : Array Int) (first : Bool) (level tc tv : Nat) (st : Search n)
    (ha : level + 1 ≠ a) :
    child first level tc tv (tw (phi a b) t st) = tw (phi a b) t (child first level tc tv st) := by
  unfold child breakout
  cases first <;> simp only [tw, set_phi ha, Bool.false_eq_true, ite_false, ite_true]

theorem recoverLevels_tw (f : Nat → Nat) (t : Array Int) (level : Nat) (st : Search n) :
    recoverLevels level (tw f t st) = tw f t (recoverLevels level st) := by
  unfold recoverLevels
  dsimp only [tw]
  split <;> split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> (try split) <;> simp_all

/-- The loop of `recoverPtn`, over any list of positions. -/
theorem recoverLoop_map {a b level : Nat} (ha : level < a) (hb : level < b) :
    ∀ (l : List Nat) (p : Array Nat),
      (forIn l (p.map (phi a b)) (fun i (r : Array Nat) =>
          if r[i]! > level then (pure (ForInStep.yield (r.set! i b)) : Id (ForInStep (Array Nat)))
          else pure (ForInStep.yield r)) : Id (Array Nat)) =
        (forIn l p (fun i (r : Array Nat) =>
          if r[i]! > level then (pure (ForInStep.yield (r.set! i a)) : Id (ForInStep (Array Nat)))
          else pure (ForInStep.yield r)) : Id (Array Nat)).map (phi a b)
  | [], _ => rfl
  | i :: l, p => by
    rw [List.forIn_cons, List.forIn_cons]
    have hg : (level < (p.map (phi a b))[i]!) ↔ (level < p[i]!) := ((sameAt_map ha hb p).2 i).symm
    by_cases h : level < p[i]!
    · have h' : (p.map (phi a b))[i]! > level := hg.2 h
      simp only [GT.gt] at h'
      simp only [GT.gt, h, h', ite_true]
      have e : (p.set! i a).map (phi a b) = (p.map (phi a b)).set! i b := by
        simp only [Array.set!, Array.map_setIfInBounds, phi, ite_true]
      rw [← e]
      exact recoverLoop_map ha hb l _
    · have h' : ¬ (p.map (phi a b))[i]! > level := fun h'' => h (hg.1 h'')
      simp only [GT.gt] at h'
      simp only [GT.gt, h, h', ite_false]
      exact recoverLoop_map ha hb l _

theorem recoverPtn_tw {a b : Nat} (t : Array Int) (level : Nat) (st : Search n)
    (ha : level < a) (hb : level < b) :
    recoverPtn b level (tw (phi a b) t st) = tw (phi a b) t (recoverPtn a level st) := by
  unfold recoverPtn
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [show (tw (phi a b) t st).ptn = st.ptn.map (phi a b) from rfl, recoverLoop_map ha hb]
  rfl

theorem recover_tw {a b : Nat} (t : Array Int) (level : Nat) (st : Search n)
    (ha : level < a) (hb : level < b) :
    recover b level (tw (phi a b) t st) = tw (phi a b) t (recover a level st) := by
  unfold recover
  rw [recoverPtn_tw t level st ha hb, recoverLevels_tw]

theorem visit_tw {a b : Nat} (t : Array Int) (ctx : Ctx n) (level numcells : Nat) (st : Search n)
    (ha : level < a) (hb : level < b) :
    visit ctx level numcells (tw (phi a b) t st) =
      ((visit ctx level numcells st).1, (visit ctx level numcells st).2.1,
        tw (phi a b) t (visit ctx level numcells st).2.2) := by
  unfold visit
  simp only [Id.run, tw]
  rw [refine_map ha hb]
  rfl

theorem chooseTarget_tw {a b : Nat} (t : Array Int) (first : Bool) (ctx : Ctx n)
    (tcLevel level numcells : Nat) (st : Search n) (ha : level < a) (hb : level < b)
    (ht : first = false → st.eqlevFirst = level → t[level]! = st.firsttc[level]!) :
    chooseTarget first ctx tcLevel level numcells (tw (phi a b) t st) =
      ((chooseTarget first ctx tcLevel level numcells st).1,
        (chooseTarget first ctx tcLevel level numcells st).2.1,
        (chooseTarget first ctx tcLevel level numcells st).2.2.1,
        tw (phi a b) (if first then t.set! level (chooseTarget first ctx tcLevel level numcells st).1
          else t) (chooseTarget first ctx tcLevel level numcells st).2.2.2) := by
  have hm : ∀ hint, maketargetcell ctx (tw (phi a b) t st).lab (tw (phi a b) t st).ptn level tcLevel hint =
      maketargetcell ctx st.lab st.ptn level tcLevel hint := fun hint =>
    (maketargetcell_congr (sameAt_map ha hb st.ptn) ctx st.lab tcLevel hint).symm
  unfold chooseTarget
  simp only [Id.run]
  cases first with
  | true =>
    by_cases hc : (numcells != n) = true
    · simp only [hc, ite_true, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, hm]
      rfl
    · simp only [hc, ite_true, ite_false, Bool.false_eq_true]
      rfl
  | false =>
    by_cases hc : (numcells < n && (st.eqlevFirst == level || decide (st.compCanon ≥ 0))) = true
    · have hc' : (numcells < n && ((tw (phi a b) t st).eqlevFirst == level ||
          decide ((tw (phi a b) t st).compCanon ≥ 0))) = true := hc
      simp only [hc, hc', ite_true, ite_false, Bool.false_eq_true, Bool.not_false, Bool.true_and]
      by_cases hh : st.compCanon < 0
      · have hh' : (tw (phi a b) t st).compCanon < 0 := hh
        have hl : st.eqlevFirst = level := by
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hc
          omega
        have htl : (tw (phi a b) t st).firsttc[level]! = st.firsttc[level]! := ht rfl hl
        simp only [hh, hh', decide_true, ite_true, htl, hm, Bool.true_and]
        by_cases hd : (Int.ofNat (maketargetcell ctx st.lab st.ptn level tcLevel st.firsttc[level]!).fst !=
            st.firsttc[level]!) = true
        · simp only [hd, ite_true]; rfl
        · simp only [hd, ite_false, Bool.false_eq_true]; rfl
      · have hh' : ¬ (tw (phi a b) t st).compCanon < 0 := hh
        simp only [hh, hh', decide_false, ite_false, Bool.false_and, Bool.false_eq_true, hm]
        rfl
    · have hc' : ¬ (numcells < n && ((tw (phi a b) t st).eqlevFirst == level ||
          decide ((tw (phi a b) t st).compCanon ≥ 0))) = true := hc
      simp only [hc, hc', ite_false, Bool.false_eq_true]
      rfl

end NautyVerified.Spec.SearchInf