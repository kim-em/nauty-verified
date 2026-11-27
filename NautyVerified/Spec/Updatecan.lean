import NautyVerified.Spec.Fmptn

/-!
# HexGraphIso's `updatecan`, unrolled

`updatecan_eq`: HexGraphIso's `updatecan` sets rows `samerows .. n-1` in
order, as a fold.
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty

/-- One row of `updatecan`. -/
def canStep {n : Nat} (ctx : Ctx n) (lab : Array Nat) (c : Array (VSet n)) (i : Nat) :
    Array (VSet n) :=
  c.set! i (ctx.g[lab[i]!]!.permset (invPerm lab))

theorem updatecan_eq {n : Nat} (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat)
    (samerows : Nat) :
    updatecan ctx canong lab samerows =
      (List.range' samerows (n - samerows)).foldl (canStep ctx lab) canong := by
  rw [updatecan]
  simp only [forIn_range'_eq]
  rw [← forIn_foldl]
  rfl

end NautyVerified.Spec
