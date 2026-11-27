import NautyVerified.Spec.Orbjoin

/-!
# HexGraphIso's `firstterminal`, unrolled

`firstterminal_eq`: the `canoncode` loop as a fold, so the C loop can be
matched against it iteration by iteration.
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty

/-- The `canoncode` copy loop of `firstterminal`. -/
def ccCopy (fc : Array Nat) (k : Nat) (cc : Array Nat) : Array Nat :=
  (List.range k).foldl (fun a i => a.set! i fc[i]!) cc

theorem firstterminal_eq {n : Nat} {κ : Type} (level : Nat) (st : SearchState n κ) :
    firstterminal level st =
      { st with
        maxlevel := level
        gcaFirst := level, allsamelevel := level, eqlevFirst := level
        firstcode := st.firstcode.set! (level + 1) codeSentinel
        firsttc := st.firsttc.set! (level + 1) (-1)
        firstlab := st.lab
        canonlevel := level, eqlevCanon := Int.ofNat level, gcaCanon := level
        compCanon := 0
        samerows := 0
        canonlab := st.lab
        canupdates := 1
        canoncode := (ccCopy (st.firstcode.set! (level + 1) codeSentinel) (level + 1)
          st.canoncode).set! (level + 1) codeSentinel } := by
  simp only [firstterminal, ccCopy]
  rw [forIn_range_eq, forIn_fold]
  rfl

theorem ccCopy_size (fc : Array Nat) : ∀ (k : Nat) (cc : Array Nat), (ccCopy fc k cc).size = cc.size
  | 0, _ => rfl
  | k + 1, cc => by
    rw [ccCopy, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.size_set!]
    exact ccCopy_size fc k cc

theorem ccCopy_get (fc : Array Nat) : ∀ (k : Nat) (cc : Array Nat), k ≤ cc.size → ∀ j,
    (ccCopy fc k cc)[j]! = if j < k then fc[j]! else cc[j]!
  | 0, _, _, j => by simp [ccCopy]
  | k + 1, cc, hk, j => by
    have ih := ccCopy_get fc k cc (by omega)
    have hs := ccCopy_size fc k cc
    have e : ccCopy fc (k + 1) cc = (ccCopy fc k cc).set! k fc[k]! := by
      simp only [ccCopy, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e]
    by_cases hj : j = k
    · subst hj
      rw [Array.getElem!_set!_self _ _ _ (by omega), ite_eq_left (by omega)]
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hj), ih j]
      by_cases hjk : j < k
      · rw [ite_eq_left hjk, ite_eq_left (by omega)]
      · rw [ite_eq_right hjk, ite_eq_right (by omega)]

end NautyVerified.Spec
