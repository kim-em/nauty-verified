import NautyVerified.Spec.Fmptn

/-!
# HexGraphIso's `testcanlab`, unrolled

`testcanlab_eq`: HexGraphIso's `testcanlab` compares rows `0, 1, …` of
`g^lab` with `canong` and stops at the first difference (`tclGo`).
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty

/-- Compare rows `l` of `g^lab` with `canong`, stopping at the first difference. -/
def tclGo {n : Nat} (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat) : List Nat → Int × Nat
  | [] => (0, n)
  | i :: l =>
    match (ctx.g[lab[i]!]!.permset (invPerm lab)).rowCmp canong[i]! with
    | .lt => (-1, i)
    | .gt => (1, i)
    | .eq => tclGo ctx canong lab l

theorem testcanlab_eq {n : Nat} (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat) :
    testcanlab ctx canong lab = tclGo ctx canong lab (List.range n) := by
  rw [testcanlab]
  simp only [forIn_range_eq]
  generalize List.range n = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.forIn_cons, tclGo]
    cases h : (ctx.g[lab[i]!]!.permset (invPerm lab)).rowCmp canong[i]! with
    | lt => simp
    | gt => simp
    | eq => simpa [h] using ih

end NautyVerified.Spec
