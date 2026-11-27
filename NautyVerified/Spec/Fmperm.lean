import HexGraphIso.Nauty.Search.Refine
import NautyVerified.Spec.Fmptn

/-!
# HexGraphIso's `fmperm`, unrolled

`fmperm_eq` rewrites HexGraphIso's `fmperm` as a fold of `permStep` over
`0 .. n-1`, with the inner cycle walk as `mark` (fuel: the list it walks).
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty

/-- Mark the cycle of `perm` through `l`, back to `i`, with fuel `fuel`. -/
def mark (perm : Array Nat) (i : Nat) : List Nat → Array Bool → Nat → Array Bool
  | [], seen, _ => seen
  | _ :: rest, seen, l =>
    if perm[l]! == i then seen.set! l true else mark perm i rest (seen.set! l true) perm[l]!

/-- One vertex of `fmperm`. -/
def permStep {n : Nat} (perm : Array Nat) (s : VSet n × VSet n × Array Bool) (i : Nat) :
    VSet n × VSet n × Array Bool :=
  if perm[i]! == i then (s.1.insert i, s.2.1.insert i, s.2.2)
  else if ¬ s.2.2[i]! then (s.1, s.2.1.insert i, mark perm i (List.range n) s.2.2 i)
  else s

theorem forIn_mark (perm : Array Nat) (i : Nat) :
    ∀ (l : List Nat) (seen : Array Bool) (cur : Nat),
      ((forIn l (seen, cur) fun _ (s : Array Bool × Nat) =>
        if (perm[s.2]! == i) = true then pure (ForInStep.done (s.1.set! s.2 true, perm[s.2]!))
        else pure (ForInStep.yield (s.1.set! s.2 true, perm[s.2]!))) : Id (Array Bool × Nat)).1 =
      mark perm i l seen cur
  | [], _, _ => rfl
  | _ :: l, seen, cur => by
    rw [List.forIn_cons, mark]
    by_cases h : (perm[cur]! == i) = true
    · rw [ite_eq_left h, ite_eq_left h]; rfl
    · rw [ite_eq_right h, ite_eq_right h]
      exact forIn_mark perm i l _ _

theorem fmperm_eq (perm : Array Nat) (n : Nat) :
    fmperm perm n =
      (((List.range n).foldl (permStep perm) (VSet.empty, VSet.empty, Array.replicate n false)).1,
       ((List.range n).foldl (permStep perm) (VSet.empty, VSet.empty, Array.replicate n false)).2.1) := by
  rw [fmperm]
  simp only [forIn_range_eq]
  rw [← forIn_foldl]
  show ((forIn (List.range n) _ _ : Id (VSet n × VSet n × Array Bool)).1,
    (forIn (List.range n) _ _ : Id (VSet n × VSet n × Array Bool)).2.1) = _
  have : ∀ s : VSet n × VSet n × Array Bool, ∀ i : Nat,
      (if (perm[i]! == i) = true then
          pure (ForInStep.yield (s.fst.insert i, s.snd.fst.insert i, s.snd.snd))
        else if ¬s.snd.snd[i]! = true then do
          let s1 ← forIn (List.range n) (s.snd.snd, i) fun _ (s' : Array Bool × Nat) =>
            if (perm[s'.snd]! == i) = true then
              pure (ForInStep.done (s'.fst.set! s'.snd true, perm[s'.snd]!))
            else pure (ForInStep.yield (s'.fst.set! s'.snd true, perm[s'.snd]!))
          pure (ForInStep.yield (s.fst, s.snd.fst.insert i, s1.fst))
        else pure (ForInStep.yield (s.fst, s.snd.fst, s.snd.snd)) : Id _) =
      pure (ForInStep.yield (permStep perm s i)) := by
    intro s i
    simp only [permStep]
    split
    · rfl
    · split
      · show pure (ForInStep.yield (s.fst, s.snd.fst.insert i, _)) = _
        rw [forIn_mark]
      · rfl
  simp only [this]

end NautyVerified.Spec
