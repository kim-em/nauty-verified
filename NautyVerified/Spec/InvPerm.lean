import HexGraphIso.Nauty.Search.Refine

/-!
# HexGraphIso's `invPerm`

`invPerm.go` writes `inv[lab[i]] = i` for each `i` of a list in order, as
nauty's `for (i = 0; i < n; ++i) workperm[lab[i]] = i;` does.
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty

theorem invPerm_go_append (lab : Array Nat) :
    ∀ (l1 l2 : List Nat) (inv : Array Nat),
      invPerm.go lab (l1 ++ l2) inv = invPerm.go lab l2 (invPerm.go lab l1 inv)
  | [], _, _ => rfl
  | _ :: l1, l2, inv => by
    rw [List.cons_append, invPerm.go, invPerm.go, invPerm_go_append lab l1 l2]

theorem invPerm_go_succ (lab : Array Nat) (k : Nat) (inv : Array Nat) :
    invPerm.go lab (List.range (k + 1)) inv = (invPerm.go lab (List.range k) inv).set! lab[k]! k := by
  rw [List.range_succ, invPerm_go_append]
  rfl

theorem invPerm_go_size (lab : Array Nat) :
    ∀ (l : List Nat) (inv : Array Nat), (invPerm.go lab l inv).size = inv.size
  | [], _ => rfl
  | _ :: l, inv => by rw [invPerm.go, invPerm_go_size lab l, Array.size_set!]

/-- Every entry of `invPerm.go` over `range k` is an initial entry or some
`i < k`. -/
theorem invPerm_go_lt (lab : Array Nat) (inv : Array Nat) (B : Nat) (hinv : ∀ p : Nat, inv[p]! < B) :
    ∀ k, k ≤ B → ∀ p : Nat, (invPerm.go lab (List.range k) inv)[p]! < B
  | 0, _, p => hinv p
  | k + 1, hk, p => by
    rw [invPerm_go_succ]
    by_cases hp : p = lab[k]! ∧ lab[k]! < (invPerm.go lab (List.range k) inv).size
    · rw [hp.1, Array.getElem!_set!_self _ _ _ hp.2]; omega
    · by_cases hpl : p = lab[k]!
      · subst hpl
        rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le (by omega)]
        exact invPerm_go_lt lab inv B hinv k (by omega) _
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hpl)]
        exact invPerm_go_lt lab inv B hinv k (by omega) p

end NautyVerified.Spec
