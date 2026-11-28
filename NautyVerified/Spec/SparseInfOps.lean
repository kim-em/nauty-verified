import NautyVerified.Spec.SparseInfRefine
import NautyVerified.Spec.SparseInfTw
import Std.Tactic.Do

/-!
# HexGraphIso's sparse search steps commute with the infinity map

The policy-specific steps of `Sparse.policy` (`visit`, `chooseTarget`,
`classify`, and the `child`, `recover` and `afterSweep` wrappers that
invalidate the refinement scratch) commute with `twG (phi a b) t` as the
dense ones commute with `tw`: `visit` through `refineWith_map`,
`chooseTarget` through `maketargetCached_congr`, and `classify` reads
neither `ptn` nor `firsttc`.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso.Nauty
open Std.Do
set_option mvcgen.warning false

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {n : Nat}

theorem sparse_visit_twG {a b : Nat} (t : Array Int) (g : Sparse.Graph n) (level numcells : Nat)
    (st : Sparse.State n) (ha : level < a) (hb : level < b) :
    Sparse.visit g level numcells (twG (phi a b) t st) =
      ((Sparse.visit g level numcells st).1, (Sparse.visit g level numcells st).2.1,
        twG (phi a b) t (Sparse.visit g level numcells st).2.2) := by
  unfold Sparse.visit
  simp only [twG_lab, twG_ptn, twG_active, twG_canong]
  rw [refineWith_map ha hb]
  rfl

theorem sparse_classify_twG (f : Nat → Nat) (t : Array Int) (g : Sparse.Graph n) (level numcells : Nat)
    (st : Sparse.State n) :
    Sparse.classify g level numcells (twG f t st) =
      ((Sparse.classify g level numcells st).1, twG f t (Sparse.classify g level numcells st).2) := by
  show _ = Prod.map id (twG f t) (Sparse.classify g level numcells st)
  unfold Sparse.classify
  simp only [Id.run_pure, Id.run_bind, apply_ite Id.run, apply_ite (Prod.map id (twG f t)),
    twG_eqlevFirst, twG_compCanon, scatter_twG, twG_gcaFirst, twG_noncheaplevel, twG_workperm,
    twG_canonlevel, twG_canong, twG_canonlab, twG_samerows, twG_lab]
  repeat' (first | rfl | (refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)))

theorem sparse_chooseTarget_twG {a b : Nat} (t : Array Int) (first : Bool) (g : Sparse.Graph n)
    (tcLevel level numcells : Nat) (st : Sparse.State n) (ha : level < a) (hb : level < b)
    (ht : first = false → st.eqlevFirst = level → t[level]! = st.firsttc[level]!) :
    Sparse.chooseTarget first g tcLevel level numcells (twG (phi a b) t st) =
      ((Sparse.chooseTarget first g tcLevel level numcells st).1,
        (Sparse.chooseTarget first g tcLevel level numcells st).2.1,
        (Sparse.chooseTarget first g tcLevel level numcells st).2.2.1,
        twG (phi a b) (if first then t.set! level (Sparse.chooseTarget first g tcLevel level numcells st).1
          else t) (Sparse.chooseTarget first g tcLevel level numcells st).2.2.2) := by
  have hm : ∀ hint sc, Sparse.maketargetCached g st.lab (st.ptn.map (phi a b)) level tcLevel hint sc =
      Sparse.maketargetCached g st.lab st.ptn level tcLevel hint sc := fun hint sc =>
    (maketargetCached_congr (sameAt_map ha hb st.ptn) g st.lab tcLevel hint sc).symm
  unfold Sparse.chooseTarget
  simp only [Id.run]
  cases first with
  | true =>
    by_cases hc : (numcells != n) = true
    · simp only [hc, ite_true, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, twG_lab,
        twG_ptn, twG_canong, hm]
      rfl
    · simp only [hc, ite_true, ite_false, Bool.false_eq_true]
      rfl
  | false =>
    by_cases hc : (numcells < n && (st.eqlevFirst == level || decide (st.compCanon ≥ 0))) = true
    · have hc' : (numcells < n && ((twG (phi a b) t st).eqlevFirst == level ||
          decide ((twG (phi a b) t st).compCanon ≥ 0))) = true := hc
      simp only [hc, hc', ite_true, ite_false, Bool.false_eq_true, Bool.not_false, Bool.true_and]
      by_cases hh : st.compCanon < 0
      · have hh' : (twG (phi a b) t st).compCanon < 0 := hh
        have hl : st.eqlevFirst = level := by
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hc
          omega
        have htl : (twG (phi a b) t st).firsttc[level]! = st.firsttc[level]! := ht rfl hl
        simp only [hh, hh', decide_true, ite_true, htl, twG_lab, twG_ptn, twG_canong, hm, Bool.true_and]
        by_cases hd : (Int.ofNat (Sparse.maketargetCached g st.lab st.ptn level tcLevel st.firsttc[level]!
            st.canong.scratch).fst != st.firsttc[level]!) = true
        · simp only [hd, ite_true]; rfl
        · simp only [hd, ite_false, Bool.false_eq_true]; rfl
      · have hh' : ¬ (twG (phi a b) t st).compCanon < 0 := hh
        simp only [hh, hh', decide_false, ite_false, Bool.false_and, Bool.false_eq_true, twG_lab, twG_ptn,
          twG_canong, hm]
        rfl
    · have hc' : ¬ (numcells < n && ((twG (phi a b) t st).eqlevFirst == level ||
          decide ((twG (phi a b) t st).compCanon ≥ 0))) = true := hc
      simp only [hc, hc', ite_false, Bool.false_eq_true]
      rfl

theorem sparse_child_twG {a b : Nat} (t : Array Int) (first : Bool) (level tc tv : Nat) (st : Sparse.State n)
    (ha : level + 1 ≠ a) :
    (Sparse.policy (n := n)).child first level tc tv (twG (phi a b) t st) =
      twG (phi a b) t ((Sparse.policy (n := n)).child first level tc tv st) := by
  show { child first level tc tv (twG (phi a b) t st) with
      canong := (child first level tc tv (twG (phi a b) t st)).canong.invalidate } = _
  rw [child_twG t first level tc tv st ha]
  rfl

theorem sparse_recover_twG {a b : Nat} (t : Array Int) (level : Nat) (st : Sparse.State n)
    (ha : level < a) (hb : level < b) :
    (Sparse.policy (n := n)).recover b level (twG (phi a b) t st) =
      twG (phi a b) t ((Sparse.policy (n := n)).recover a level st) := by
  show { recoverLevels level (recoverPtn b level (twG (phi a b) t st)) with
      canong := (recoverLevels level (recoverPtn b level (twG (phi a b) t st))).canong.invalidate } = _
  rw [recoverPtn_twG t level st ha hb, recoverLevels_twG]
  rfl

theorem sparse_afterSweep_twG (f : Nat → Nat) (t : Array Int) (first : Bool) (level size index : Nat)
    (st : Sparse.State n) :
    (Sparse.policy (n := n)).afterSweep first level size index (twG f t st) =
      twG f t ((Sparse.policy (n := n)).afterSweep first level size index st) := by
  show (if first then { afterSweep first level size index (twG f t st) with
      order := (afterSweep first level size index (twG f t st)).order * index }
    else afterSweep first level size index (twG f t st)) = _
  rw [afterSweep_twG]
  cases first <;> rfl

/-! ## Fields the sparse steps keep -/

theorem sparse_chooseTarget_keeps (first : Bool) (g : Sparse.Graph n) (tcLevel level numcells : Nat)
    (st : Sparse.State n) :
    let r := Sparse.chooseTarget first g tcLevel level numcells st
    r.2.2.2.noncheaplevel = st.noncheaplevel ∧ r.2.2.2.firstcode = st.firstcode ∧
      r.2.2.2.orbits = st.orbits ∧
      r.2.2.2.firsttc = (if first then st.firsttc.set! level r.1 else st.firsttc) := by
  unfold Sparse.chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × Sparse.State n =>
    out.2.2.2.noncheaplevel = st.noncheaplevel ∧ out.2.2.2.firstcode = st.firstcode ∧
      out.2.2.2.orbits = st.orbits ∧
      out.2.2.2.firsttc = (if first then st.firsttc.set! level out.1 else st.firsttc))
  mvcgen
  all_goals simp_all +zetaDelta

theorem sparse_classify_noncheap (g : Sparse.Graph n) (level numcells : Nat) (st : Sparse.State n) :
    (Sparse.classify g level numcells st).2.noncheaplevel = st.noncheaplevel := by
  unfold Sparse.classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.noncheaplevel, ite_self]

end NautyVerified.Spec.SearchInf
