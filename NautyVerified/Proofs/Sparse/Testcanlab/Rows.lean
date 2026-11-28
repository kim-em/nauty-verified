import HexGraphIso.Nauty.Sparse.GraphProps
import HexGraphIso.Nauty.Sparse.Inverse
import Std.Tactic.Do

/-!
# HexGraphIso's `Sparse.testcanlab`, row by row

`rowCode g R lab i` is the outcome of row `i` of `Sparse.testcanlab g R lab`:
`none` when the stored row `i` of `R` (`stored R i`) and the candidate row
(`candidate g lab i`, the neighbours of `lab[i]` relabelled by
`inverse n lab`) compare equal, otherwise the sign returned. The candidate
pass (`unmark`) unmarks each marked entry and keeps the least unmarked
one. `testcanlab_rows`: the result is the first row with an outcome, or
`(0, n)`. This is the form `testcanlab_sg`'s loops establish.
-/

namespace NautyVerified.Proofs.Sparse

open Std.Do
open Hex.GraphIso.Nauty.Sparse
set_option mvcgen.warning false
set_option linter.deprecated.syntax false
set_option maxHeartbeats 1600000

/-- The entries of stored row `i`. -/
def stored {n : Nat} (R : Rows n) (i : Nat) : List Nat :=
  (List.range' R.offsets[i]! (R.offsets[i + 1]! - R.offsets[i]!)).map (R.neighbors[·]!)

/-- The entries of the candidate row `i`. -/
def candidate {n : Nat} (g : Graph n) (lab : Array Nat) (i : Nat) : List Nat :=
  (List.range' g.offsets[lab[i]!]! (g.offsets[lab[i]! + 1]! - g.offsets[lab[i]!]!)).map
    (fun j => (inverse n lab)[g.neighbor j]!)

/-- One step of the candidate pass: unmark a marked entry, otherwise keep
the least unmarked entry. -/
def unmarkStep (s : (Nat → Bool) × Nat) (k : Nat) : (Nat → Bool) × Nat :=
  if s.1 k then (fun x => if x = k then false else s.1 x, s.2) else (s.1, if k < s.2 then k else s.2)

/-- The candidate pass over `B`, from the marks `mk` and least entry `mina`. -/
def unmark (B : List Nat) (mk : Nat → Bool) (mina : Nat) : (Nat → Bool) × Nat :=
  B.foldl unmarkStep (mk, mina)

/-- The outcome of row `i`. -/
def rowCode {n : Nat} (g : Graph n) (R : Rows n) (lab : Array Nat) (i : Nat) : Option Int :=
  if R.degree i ≠ g.degree lab[i]! then some (if R.degree i < g.degree lab[i]! then -1 else 1) else
    let s := unmark (candidate g lab i) (fun k => decide (k ∈ stored R i)) n
    if s.2 = n then none else
      some (if (stored R i).any (fun k => s.1 k && decide (k < s.2)) then -1 else 1)

/-- The result of a comparison whose rows have the outcomes `f`. -/
def Scan (n : Nat) (f : Nat → Option Int) (r : Int × Nat) : Prop :=
  (r = (0, n) ∧ ∀ i < n, f i = none) ∨
    (r.2 < n ∧ (∀ i < r.2, f i = none) ∧ f r.2 = some r.1)

private theorem range_cursor {s t i : Nat} {pref suff : List Nat}
    (h : List.range' s (t - s) = pref ++ i :: suff) :
    s ≤ i ∧ i < t ∧ i = s + pref.length := by
  have hi := List.mem_of_range'_eq_append_cons h
  have he := List.eq_of_range'_eq_append_cons h
  simp only [List.mem_range'_1] at *
  omega

theorem prefix_lt {n cur : Nat} {pref suff : List Nat}
    (h : List.range' 0 n = pref ++ cur :: suff) :
    (∀ i, i ∈ pref ↔ i < cur) ∧ cur < n ∧ pref.length = cur := by
  have hc := range_cursor (s := 0) (t := n) (by simpa using h)
  obtain ⟨k, -, hk, -⟩ := List.range'_eq_append_iff.1 h
  have hk' : pref.length = k := by rw [hk]; simp
  refine ⟨fun i => ?_, hc.2.1, by omega⟩
  rw [hk, List.mem_range'_1]; omega

theorem get_set (a : Array Nat) (k x v : Nat) (hv : v < a.size) (h' : v < (a.setIfInBounds k x).size) :
    (a.setIfInBounds k x)[v]'h' = if k = v then x else a[v]! := by
  rw [Array.getElem_setIfInBounds hv, getElem!_pos a v hv]

theorem unmark_concat (l : List Nat) (k : Nat) (mk : Nat → Bool) (mina : Nat) :
    unmark (l ++ [k]) mk mina = unmarkStep (unmark l mk mina) k := by
  simp [unmark, List.foldl_append]

theorem unmark_nil (mk : Nat → Bool) (mina : Nat) : unmark [] mk mina = (mk, mina) := rfl

theorem mem_stored {n : Nat} (R : Rows n) (i v : Nat) :
    v ∈ stored R i ↔ ∃ a, (R.offsets[i]! ≤ a ∧ a < R.offsets[i]! + (R.offsets[i + 1]! - R.offsets[i]!)) ∧
      R.neighbors[a]! = v := by
  simp [stored, List.mem_range'_1]

theorem any_stored {n : Nat} (R : Rows n) (i : Nat) (f : Nat → Bool) :
    (stored R i).any f = true ↔ ∃ a, (R.offsets[i]! ≤ a ∧ a < R.offsets[i]! + (R.offsets[i + 1]! - R.offsets[i]!)) ∧
      f R.neighbors[a]! = true := by
  simp [stored, List.any_eq_true, List.mem_range'_1]

theorem stored_lt {n : Nat} {R : Rows n} (hR : ∀ i < n, ∀ k ∈ stored R i, k < n) {i a : Nat} (hi : i < n)
    (ha : R.offsets[i]! ≤ a ∧ a < R.offsets[i]! + (R.offsets[i + 1]! - R.offsets[i]!)) :
    R.neighbors[a]! < n :=
  hR i hi _ ((mem_stored R i _).2 ⟨a, ha, rfl⟩)

/-- The candidate pass of row `i`. -/
abbrev pass {n : Nat} (g : Graph n) (R : Rows n) (lab : Array Nat) (i : Nat) : (Nat → Bool) × Nat :=
  unmark (candidate g lab i) (fun k => decide (k ∈ stored R i)) n

theorem rowCode_lt {n : Nat} {g : Graph n} {R : Rows n} {lab : Array Nat} {i : Nat}
    (hdeg : R.degree i = g.degree lab[i]!) (hne : ¬ (pass g R lab i).2 = n) {e : Nat}
    (he : R.offsets[i]! ≤ e ∧ e < R.offsets[i]! + (R.offsets[i + 1]! - R.offsets[i]!))
    (hm : (pass g R lab i).1 R.neighbors[e]! = true) (hlt : R.neighbors[e]! < (pass g R lab i).2) :
    rowCode g R lab i = some (-1) := by
  have hany := (any_stored R i (fun k => (pass g R lab i).1 k && decide (k < (pass g R lab i).2))).2
    ⟨e, he, by simp [hm, hlt]⟩
  simp only [rowCode, hdeg, ne_eq, not_true_eq_false, ↓reduceIte]
  simp only [pass] at hne hany
  simp only [hne, ↓reduceIte, hany]

theorem rowCode_gt {n : Nat} {g : Graph n} {R : Rows n} {lab : Array Nat} {i : Nat}
    (hdeg : R.degree i = g.degree lab[i]!) (hne : ¬ (pass g R lab i).2 = n)
    (hnone : ∀ e, R.offsets[i]! ≤ e → e < R.offsets[i]! + (R.offsets[i + 1]! - R.offsets[i]!) →
      (pass g R lab i).1 R.neighbors[e]! = true → (pass g R lab i).2 ≤ R.neighbors[e]!) :
    rowCode g R lab i = some 1 := by
  have hany := Bool.eq_false_iff.2 (fun h => by
    obtain ⟨e, he, hf⟩ := (any_stored R i (fun k => (pass g R lab i).1 k &&
      decide (k < (pass g R lab i).2))).1 h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    have := hnone e he.1 he.2 hf.1
    omega)
  simp only [rowCode, hdeg, ne_eq, not_true_eq_false, ↓reduceIte]
  simp only [pass] at hne hany
  simp only [hne, ↓reduceIte, hany]
  rfl

theorem rowCode_none {n : Nat} {g : Graph n} {R : Rows n} {lab : Array Nat} {i : Nat}
    (hdeg : R.degree i = g.degree lab[i]!) (heq : (pass g R lab i).2 = n) :
    rowCode g R lab i = none := by
  simp only [rowCode, hdeg, ne_eq, not_true_eq_false, ↓reduceIte]
  simp only [pass] at heq
  simp only [heq, ↓reduceIte]

theorem testcanlab_rows {n : Nat} (g : Graph n) (R : Rows n) (lab : Array Nat)
    (hR : ∀ i < n, ∀ k ∈ stored R i, k < n) (hlab : lab.size = n) (hn : 0 < n) :
    Scan n (rowCode g R lab) (testcanlab g R lab) := by
  unfold testcanlab
  apply Id.of_wp_run_eq rfl (Scan n (rowCode g R lab))
  mvcgen invariants
  | inv1 => ⇓⟨cursor, s⟩ => ⌜
      (s.1 = none ∨ cursor.suffix = []) ∧
      (s.1 = none → s.2.size = n ∧ (∀ v, v < n → s.2[v]! ≤ cursor.prefix.length) ∧
        ∀ i ∈ cursor.prefix, rowCode g R lab i = none) ∧
      (∀ r, s.1 = some r → Scan n (rowCode g R lab) r)⌝
  | inv2 pref i suff he s marks v di dli hdegree stamp hs => ⇓⟨cursor, marks⟩ => ⌜
      marks.size = n ∧ (∀ v, v < n → marks[v]! ≤ i + 1) ∧
      (∀ v, v < n → (marks[v]! = i + 1 ↔ v ∈ cursor.prefix.map (R.neighbors[·]!)))⌝
  | inv3 pref i suff he s marks v di dli hdegree stamp hs rowmarks hm => ⇓⟨cursor, s⟩ => ⌜
      s.1.size = n ∧ (∀ v, v < n → s.1[v]! ≤ i + 1) ∧
      (∀ v, v < n → (s.1[v]! = i + 1 ↔
        (unmark (cursor.prefix.map (fun j => (inverse n lab)[g.neighbor j]!))
          (fun k => decide (k ∈ stored R i)) n).1 v)) ∧
      s.2 = (unmark (cursor.prefix.map (fun j => (inverse n lab)[g.neighbor j]!))
          (fun k => decide (k ∈ stored R i)) n).2⌝
  | inv4 pref i suff he s marks v di dli hdegree stamp hs rowmarks hm st marks' mina hd hne =>
      ⇓⟨cursor, r⟩ => ⌜
        (r.1 = none ∨ cursor.suffix = []) ∧
        (r.1 = none → ∀ e ∈ cursor.prefix, ¬ (marks'[R.neighbors[e]!]! = i + 1 ∧ R.neighbors[e]! < mina)) ∧
        (∀ result, r.1 = some result → result = (-1, i) ∧
          ∃ e ∈ cursor.prefix, marks'[R.neighbors[e]!]! = i + 1 ∧ R.neighbors[e]! < mina)⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, bne_iff_ne] at *
  all_goals simp_all
  case vc1.step.isTrue =>
    rename_i pref cur suff b _ _ _ _ hinv hr hd
    obtain ⟨hpre, hc, -⟩ := prefix_lt hr
    exact .inr ⟨hc, fun i hi => (hinv.2.1 hinv.1).2.2 i ((hpre i).2 hi), by simp [rowCode, hd]⟩
  case vc2.step =>
    rename_i pref cur suff b _ hm5 hold hm hr hdeg he
    have hs := hm.1
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [get_set _ _ _ _ (by omega)]
      have := hm.2.1 v hv
      split <;> omega
    · rw [get_set _ _ _ _ (by omega)]
      have := hm.2.2 v hv
      by_cases hk : R.neighbors[cur]! = v
      · simp [hk]
      · simp only [hk, ↓reduceIte]; rw [this]; constructor
        · intro h; exact .inl h
        · rintro (h | h)
          · exact h
          · exact absurd h.symm hk
  case vc3.step.isFalse.pre =>
    rename_i pref cur suff b _ _ _ _ _ hinv hinv' hr hdeg
    have hs := hinv'.2.1 hinv'.1
    have hc := (prefix_lt hr).2.2
    constructor <;> intro v hv
    all_goals
      have h := hs.2.1 v hv
      rw [getElem!_pos b.2 v (by omega)] at h
      omega
  case vc4.step.isTrue =>
    rename_i pref cur suff b _ _ _ _ hI _ hmk _ hr _ _ _
    have hK : (inverse n lab)[g.neighbor cur]! < n := inverse_lt hlab hn _
    have hs := hI.1
    have hm := (hI.2.2.1 _ hK).1 hmk
    rw [unmark_concat]
    simp only [unmarkStep, hm, ↓reduceIte]
    refine ⟨fun v hv => ?_, fun v hv => ?_, by first | trivial | exact hI.2.2.2⟩
    · rw [get_set _ _ _ _ (by omega)]
      have := hI.2.1 v hv
      split <;> omega
    · rw [get_set _ _ _ _ (by omega)]
      by_cases hk : (inverse n lab)[g.neighbor cur]! = v
      · subst hk; simp
      · simp only [hk, ↓reduceIte, Ne.symm hk]; exact hI.2.2.1 v hv
  case vc5.step.isFalse.isTrue =>
    rename_i pref cur suff b _ _ _ hI _ hmk hlt _ hr _ _ _
    have hK := inverse_lt hlab hn (g.neighbor cur)
    have hs := hI.1
    have hm := Bool.eq_false_iff.2 (fun h => hmk ((hI.2.2.1 _ hK).2 h))
    rw [unmark_concat]
    simp only [unmarkStep, hm, hlt, ↓reduceIte, Bool.false_eq_true]
    refine ⟨fun v hv => ?_, fun v hv => ?_, by first | trivial | rfl⟩
    · have := hI.2.1 v hv; rwa [getElem!_pos _ v (by omega)] at this
    · rw [← getElem!_pos _ v (by omega)]; exact hI.2.2.1 v hv
  case vc6.step.isFalse.isFalse =>
    rename_i pref cur suff b _ _ _ hI _ hmk hlt _ hr _ _ _
    have hK := inverse_lt hlab hn (g.neighbor cur)
    have hs := hI.1
    have hm := Bool.eq_false_iff.2 (fun h => hmk ((hI.2.2.1 _ hK).2 h))
    rw [unmark_concat]
    simp only [unmarkStep, hm, ↓reduceIte, Bool.false_eq_true]
    refine ⟨fun v hv => ?_, fun v hv => ?_, by split <;> omega⟩
    · have := hI.2.1 v hv; rwa [getElem!_pos _ v (by omega)] at this
    · rw [← getElem!_pos _ v (by omega)]; exact hI.2.2.1 v hv
  case vc7.step.isFalse.post.success.pre =>
    rename_i pref cur suff b _ _ _ _ _ r _ _ hr _ hM
    have hs := hM.1
    simp only [unmark_nil, decide_eq_true_eq]
    refine ⟨fun v hv => ?_, fun v hv => ?_, by first | trivial | rfl⟩
    · have := hM.2.1 v hv; rwa [getElem!_pos r v (by omega)] at this
    · rw [← getElem!_pos r v (by omega), hM.2.2 v hv, mem_stored]
  case vc8.step.isTrue =>
    rename_i hit _ _ _ _ _ _ _
    exact ⟨_, .inr (.inl rfl), hit⟩
  case vc9.step.isFalse =>
    rename_i hn7 hI _ _ _ _ _ _
    rintro e (he | rfl) hm
    · exact (hI.2.1 hI.1) e he hm
    · first | exact Nat.le_of_not_lt (fun hlt => hn7 ⟨hm, hlt⟩) | exact hn7 hm
  case vc11.step.isFalse.post.success.post.success.isTrue.post.success.h_1 =>
    rename_i hinv _ hr hdeg _ hne hU hfound
    obtain ⟨hpre, hc, -⟩ := prefix_lt hr
    refine .inr ⟨hc, fun i hi => (hinv.2.1 hinv.1).2.2 i ((hpre i).2 hi), ?_⟩
    obtain ⟨-, e, he, hm, hlt⟩ := hfound
    exact rowCode_lt hdeg hne he ((hU.2.2.1 _ (stored_lt hR hc he)).1 hm) (hU.2.2.2 ▸ hlt)
  case vc12.step.isFalse.post.success.post.success.isTrue.post.success.h_2 =>
    rename_i hinv _ hr hdeg hM hne hU hnone
    obtain ⟨hpre, hc, -⟩ := prefix_lt hr
    refine .inr ⟨hc, fun i hi => (hinv.2.1 hinv.1).2.2 i ((hpre i).2 hi), ?_⟩
    exact rowCode_gt hdeg hne fun e h1 h2 hm =>
      hnone e h1 h2 ((hU.2.2.1 _ (stored_lt hR hc ⟨h1, h2⟩)).2 hm)
  case vc13.step.isFalse.post.success.post.success.isFalse =>
    rename_i _ _ hinv hr hdeg _ heq hU
    obtain ⟨hpre, hc, hlen⟩ := prefix_lt hr
    refine ⟨fun v hv => ?_, ?_⟩
    · have := hU.2.1 v hv; rw [getElem!_pos _ v (by have := hU.1; omega)] at this; omega
    · rintro i (hi | rfl)
      · exact (hinv.2.1 hinv.1).2.2 i hi
      · exact rowCode_none hdeg heq
  case vc16.post.success.h_2 =>
    rename_i h
    exact .inl ⟨rfl, h.2.2⟩

end NautyVerified.Proofs.Sparse
