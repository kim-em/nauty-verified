import NautyVerified.Spec.Orbjoin

/-!
# HexGraphIso's `recover`, unrolled

`recoverPtn_eq`: the rescan of `ptn` as a fold, for the C loop to follow.
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty

/-- One step of the rescan: reopen position `i` if it lies above `level`. -/
def reopen (inf level : Nat) (p : Array Nat) (i : Nat) : Array Nat :=
  if p[i]! > level then p.set! i inf else p

theorem recoverPtn_eq {n : Nat} {κ : Type} (inf level : Nat) (st : SearchState n κ) :
    recoverPtn inf level st = { st with ptn := (List.range n).foldl (reopen inf level) st.ptn } := by
  simp only [recoverPtn]
  rw [forIn_range_eq]
  have e : ∀ p : Array Nat, (forIn (List.range n) p fun i s =>
      if s[i]! > level then pure (ForInStep.yield (s.set! i inf))
      else pure (ForInStep.yield s) : Id (Array Nat)) =
      (List.range n).foldl (reopen inf level) p := by
    intro p
    rw [← forIn_fold]
    congr 1
    funext i s
    simp only [reopen]
    split <;> rfl
  rw [e]
  rfl

/-- `recoverLevels` as nauty's four clamps, one record update each. -/
theorem recoverLevels_eq {n : Nat} {κ : Type} (level : Nat) (st : SearchState n κ) :
    recoverLevels level st =
      let st := if level < st.noncheaplevel then { st with noncheaplevel := level + 1 } else st
      let st := if level < st.eqlevFirst then { st with eqlevFirst := level } else st
      let st := if level < st.gcaCanon then { st with gcaCanon := level } else st
      if Int.ofNat level ≤ st.eqlevCanon then
        { st with eqlevCanon := Int.ofNat level, compCanon := 0 } else st := by
  simp only [recoverLevels]
  split <;> split <;> split <;> split <;> rfl

/-- `recoverLevels` as one record update. -/
theorem recoverLevels_upd {n : Nat} {κ : Type} (level : Nat) (st : SearchState n κ) :
    recoverLevels level st =
      { st with
        noncheaplevel := if level < st.noncheaplevel then level + 1 else st.noncheaplevel
        eqlevFirst := if level < st.eqlevFirst then level else st.eqlevFirst
        gcaCanon := if level < st.gcaCanon then level else st.gcaCanon
        eqlevCanon := if Int.ofNat level ≤ st.eqlevCanon then Int.ofNat level else st.eqlevCanon
        compCanon := if Int.ofNat level ≤ st.eqlevCanon then 0 else st.compCanon } := by
  simp only [recoverLevels]
  split <;> split <;> split <;> split <;> simp_all

/-- The rescan keeps `ptn`'s size and its values: each is `≤ n + 1` or `inf`. -/
theorem reopen_fold {inf level n : Nat} {p : Array Nat} (hs : p.size = n)
    (hv : ∀ j < n, p[j]! ≤ n + 1 ∨ p[j]! = inf) :
    ∀ k, ((List.range k).foldl (reopen inf level) p).size = n ∧
      ∀ j < n, ((List.range k).foldl (reopen inf level) p)[j]! ≤ n + 1 ∨
        ((List.range k).foldl (reopen inf level) p)[j]! = inf
  | 0 => ⟨hs, hv⟩
  | k + 1 => by
    obtain ⟨ihs, ihv⟩ := reopen_fold hs hv k
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [reopen]
    split
    · refine ⟨by rw [Array.size_set!]; exact ihs, fun j hj => ?_⟩
      by_cases hjk : j = k
      · subst hjk; rw [Array.getElem!_set!_self _ _ _ (by omega)]; exact .inr rfl
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hjk)]; exact ihv j hj
    · exact ⟨ihs, ihv⟩

/-- Positions at or below `level` are not reopened. -/
theorem reopen_fold_le {inf level : Nat} {p : Array Nat} {j : Nat} (hj : p[j]! ≤ level) :
    ∀ k, ((List.range k).foldl (reopen inf level) p)[j]! = p[j]!
  | 0 => rfl
  | k + 1 => by
    have ih := reopen_fold_le (inf := inf) hj k
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [reopen]
    split
    · rename_i hgt
      by_cases hjk : j = k
      · subst hjk; omega
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hjk), ih]
    · exact ih

end NautyVerified.Spec
