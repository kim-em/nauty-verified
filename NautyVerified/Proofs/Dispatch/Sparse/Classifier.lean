import NautyVerified.Proofs.Dispatch.Sparse.Rep
import NautyVerified.Proofs.Search.Processnode.Classifier
import NautyVerified.Proofs.Sparse.Testcanlab.Rows
import HexGraphIso.Nauty.Sparse.Classify

/-!
# Sparse nauty's leaf classification

`sparseClassifier : Classifier sparseOps`: HexGraphIso's sparse `classify`
is `classifyBy` with the store update `Storage.update`
(`Sparse.classify_eq`), and `Sparse.testcanlab` returns `-1`, `0` or `1` with
a row index at most `n` (`testcanlab_range`).
-/

namespace NautyVerified.Proofs.Dispatch

open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty
open Std.Do

set_option mvcgen.warning false
set_option linter.deprecated.syntax false

theorem cur_lt {n cur : Nat} {pref suff : List Nat} (h : [:n].toList = pref ++ cur :: suff) :
    cur < n :=
  (Sparse.prefix_lt (by simpa [Std.Legacy.Range.toList] using h)).2.1

set_option maxHeartbeats 1600000 in
theorem sparse_testcanlab_range {n : Nat} (g : Sparse.Graph n) (R : Sparse.Rows n) (lab : Array Nat) :
    -1 ≤ (Sparse.testcanlab g R lab).1 ∧ (Sparse.testcanlab g R lab).1 ≤ 1 ∧
      (Sparse.testcanlab g R lab).2 ≤ n := by
  unfold Sparse.testcanlab
  apply Id.of_wp_run_eq rfl (fun r : Int × Nat => -1 ≤ r.1 ∧ r.1 ≤ 1 ∧ r.2 ≤ n)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, s⟩ => ⌜∀ r, s.1 = some r → -1 ≤ r.1 ∧ r.1 ≤ 1 ∧ r.2 ≤ n⌝
  | inv2 pref i suff he s marks v di dli hdegree stamp hs => ⇓⟨cursor, marks⟩ => ⌜True⌝
  | inv3 pref i suff he s marks v di dli hdegree stamp hs rowmarks hm => ⇓⟨cursor, s⟩ => ⌜True⌝
  | inv4 pref i suff he s marks v di dli hdegree stamp hs rowmarks hm st marks' mina hd hne =>
      ⇓⟨cursor, r⟩ => ⌜∀ result, r.1 = some result → result = (-1, i)⌝
  all_goals (try simp_all)
  all_goals first
    | omega
    | (have := cur_lt ‹[:n].toList = _ ++ _ :: _›; split <;> omega)
    | (have := cur_lt ‹[:n].toList = _ ++ _ :: _›; omega)
    | (rename_i x h; exact h _ _ x)

theorem canonVerdict_eq {n : Nat} (G : Sparse.Graph n) (level : Nat) (s : Sparse.State n) :
    Sparse.canonVerdict G level s =
      classifyCanonG sparseOps (fun c lab sr => c.update G lab sr) G level s := by
  unfold Sparse.canonVerdict classifyCanonG canonTestG pickCanon
  by_cases h0 : s.compCanon = 0
  · by_cases hl : level < s.canonlevel
    · simp [h0, hl, Id.run_pure, apply_ite Id.run]
    · rcases ht : Sparse.testcanlab G (s.canong.update G s.canonlab s.samerows).toRows s.lab with ⟨c, sr⟩
      have : (Sparse.testcanlab G (sparseOps.rows (s.canong.update G s.canonlab s.samerows)) s.lab) =
        (c, sr) := ht
      by_cases hc : c = 0
      · simp [h0, hl, ht, this, hc, Id.run_pure, apply_ite Id.run]
      · by_cases hp : 0 < c
        · simp [h0, hl, ht, this, hc, hp, Id.run_pure, apply_ite Id.run]
        · simp [h0, hl, ht, this, hc, hp, Id.run_pure, apply_ite Id.run]
  · by_cases hp : 0 < s.compCanon
    · simp [h0, hp, Id.run_pure, apply_ite Id.run]
    · simp [h0, hp, Id.run_pure, apply_ite Id.run]

/-- Sparse nauty's classification. -/
def sparseClassifier : Classifier sparseOps where
  update G c lab sr := c.update G lab sr
  rows_update _ _ _ _ := rfl
  testcanlab_range G c lab := sparse_testcanlab_range G c lab
  classify_eq {n} G level numcells st := by
    show Sparse.classify G level numcells st = _
    rw [Sparse.classify_eq]
    unfold classifyBy
    simp only [canonVerdict_eq]
    have es : (scatter st.firstlab st).gcaFirst = st.gcaFirst ∧
        (scatter st.firstlab st).noncheaplevel = st.noncheaplevel := by simp [Spec.scatter_eq]
    by_cases h1 : st.eqlevFirst = level
    · by_cases h3 : numcells = n
      · simp [h1, h3, es]
      · simp [h1, h3]
    · by_cases h2 : st.compCanon < 0
      · simp [h1, h2]
      · by_cases h3 : numcells = n
        · simp [h1, h2, h3]
        · simp [h1, h2, h3]

end NautyVerified.Proofs.Dispatch
