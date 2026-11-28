import HexGraphIso.Nauty.Sparse.Update
import NautyVerified.Proofs.Sparse.Canon
import Std.Tactic.Do

/-!
# HexGraphIso's `Sparse.updatecan`, row by row

`updatecan_rows`: from row `s = samerows` on, `Sparse.updatecan g R lab s`
starts row `s + k` at `start g lab s (base R s) k` (the running sum of the
degrees of `lab[s]`, …, `lab[s + k - 1]` from `base R s`) and stores there
the relabelled neighbours of `lab[s + k]`, provided the offsets have `n + 1`
entries and the neighbours fit. This is the form `updatecan_sg`'s loops
establish.
-/

namespace NautyVerified.Proofs.Sparse

open Std.Do
open Hex.GraphIso.Nauty.Sparse
set_option mvcgen.warning false
set_option linter.deprecated.syntax false
set_option maxHeartbeats 1600000

/-- Where row `s + k` starts. -/
def start {n : Nat} (g : Graph n) (lab : Array Nat) (s b0 : Nat) : Nat → Nat
  | 0 => b0
  | k + 1 => start g lab s b0 k + g.degree lab[s + k]!

theorem start_mono {n : Nat} (g : Graph n) (lab : Array Nat) (s b0 : Nat) {k k' : Nat} (h : k ≤ k') :
    start g lab s b0 k ≤ start g lab s b0 k' := by
  induction k' with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with h' | h'
    · exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · rw [show k = k' + 1 by omega]; exact Nat.le_refl _

private theorem range_cursor {s t i : Nat} {pref suff : List Nat}
    (h : List.range' s (t - s) = pref ++ i :: suff) :
    s ≤ i ∧ i < t ∧ i = s + pref.length := by
  have hi := List.mem_of_range'_eq_append_cons h
  have he := List.eq_of_range'_eq_append_cons h
  simp only [List.mem_range'_1] at *
  omega

theorem get_setb (a : Array Nat) (i v j : Nat) (hj : j < a.size) :
    (a.setIfInBounds i v)[j]! = if i = j then v else a[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_setIfInBounds hj, getElem!_pos a j hj]

theorem updatecan_rows {n : Nat} (g : Graph n) (R : Rows n) (lab : Array Nat) (s : Nat) (hs : s ≤ n)
    (hsz : R.offsets.size = n + 1)
    (hfit : start g lab s (base R s) (n - s) ≤ R.neighbors.size) :
    (∀ k ≤ n - s, (updatecan g R lab s).offsets[s + k]! = start g lab s (base R s) k) ∧
    (∀ k < n - s, ∀ j < g.degree lab[s + k]!,
      (updatecan g R lab s).neighbors[start g lab s (base R s) k + j]! =
        (inverse n lab)[g.neighbor (g.offsets[lab[s + k]!]! + j)]!) := by
  unfold updatecan
  apply Id.of_wp_run_eq rfl (fun r : Rows n =>
    (∀ k ≤ n - s, r.offsets[s + k]! = start g lab s (base R s) k) ∧
    (∀ k < n - s, ∀ j < g.degree lab[s + k]!,
      r.neighbors[start g lab s (base R s) k + j]! =
        (inverse n lab)[g.neighbor (g.offsets[lab[s + k]!]! + j)]!))
  mvcgen invariants
  | inv1 => ⇓⟨cur, st⟩ => ⌜st.1.size = n + 1 ∧ st.2.1.size = R.neighbors.size ∧
      st.2.2 = start g lab s (base R s) cur.prefix.length ∧
      (∀ k < cur.prefix.length, st.1[s + k]! = start g lab s (base R s) k) ∧
      (∀ k < cur.prefix.length, ∀ j < g.degree lab[s + k]!,
        st.2.1[start g lab s (base R s) k + j]! =
          (inverse n lab)[g.neighbor (g.offsets[lab[s + k]!]! + j)]!)⌝
  | inv2 _ _ _ nb0 k0 _ v _ => ⇓⟨cur, st'⟩ => ⌜st'.1.size = R.neighbors.size ∧
      st'.2 = k0 + cur.prefix.length ∧ (∀ e < k0, st'.1[e]! = nb0[e]!) ∧
      (∀ j < cur.prefix.length, st'.1[k0 + j]! = (inverse n lab)[g.neighbor (g.offsets[v]! + j)]!)⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.add_sub_cancel,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil] at *
  all_goals simp_all
  case vc4.pre => simp [base]; rfl
  case vc1.step =>
    rename_i pref1 cur1 suff1 b1 _ _ _ _ _ _ hI pref cur suff b _ _ _ _ hJ hr1 hr
    have c1 := range_cursor (s := s) (t := n) hr1
    have c2 := range_cursor hr
    have hS1 : start g lab s (base R s) (pref1.length + 1) =
        start g lab s (base R s) pref1.length + g.degree lab[s + pref1.length]! := rfl
    have hle := start_mono g lab s (base R s) (show pref1.length + 1 ≤ n - s by omega)
    have hdeg : g.degree lab[s + pref1.length]! =
        g.offsets[lab[cur1]! + 1]! - g.offsets[lab[cur1]!]! := by rw [← c1.2.2]; rfl
    have hK : start g lab s (base R s) pref1.length + pref.length < b.fst.size := by
      rw [hJ.1]; omega
    refine ⟨by omega, fun e he => ?_, fun j hj => ?_⟩
    · rw [get_setb _ _ _ _ (by omega), ite_eq_right (by omega), hJ.2.2.1 e he]
    · rw [get_setb _ _ _ _ (by omega)]
      by_cases hjp : j = pref.length
      · subst hjp; rw [ite_eq_left rfl, c2.2.2]
      · rw [ite_eq_right (by omega)]; exact hJ.2.2.2 j (by omega)
  case vc3.step.post.success =>
    rename_i pref cur suff b _ _ _ _ _ _ hI r _ _ hr hJ
    have c1 := range_cursor (s := s) (t := n) hr
    have hlab : lab[cur]! = lab[s + pref.length]! := by rw [c1.2.2]
    refine ⟨by simp only [start]; rw [← hlab]; rfl, fun k hk => ?_, fun k hk j hj => ?_⟩
    · rw [get_setb _ _ _ _ (by rw [hI.1]; omega)]
      by_cases hkp : k = pref.length
      · subst hkp; rw [ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega)]; exact hI.2.2.2.1 k (by omega)
    · by_cases hkp : k = pref.length
      · subst hkp
        rw [hJ.2.2.2 j (by rw [← hlab] at hj; exact hj), hlab]
      · have hk' : k < pref.length := by omega
        have h1 : start g lab s (base R s) (k + 1) ≤ start g lab s (base R s) pref.length :=
          start_mono g lab s (base R s) hk'
        have h2 : start g lab s (base R s) (k + 1) = start g lab s (base R s) k + g.degree lab[s + k]! := rfl
        rw [hJ.2.2.1 _ (by omega)]
        exact hI.2.2.2.2 k hk' j hj
  case vc5.post.success =>
    rename_i r hI
    intro k hk
    rw [get_setb _ _ _ _ (by rw [hI.1]; omega)]
    by_cases hkn : k = n - s
    · subst hkn; rw [ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega)]; exact hI.2.2.2.1 k (by omega)

end NautyVerified.Proofs.Sparse
