import NautyVerified.Proofs.Sparse.Refine.Trivial.Rev
import NautyVerified.Proofs.Sparse.Refine.Trivial.Push

namespace NautyVerified.Proofs.Sparse.Refine.Trivial

open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

variable {n : Nat}

/-- The bookkeeping after a touched cell's partition and write-back, from
the state `u` holding the new labels and cell starts. -/
def fixRes (level first v2 v3 : Nat) (u : RefineSt n) : RefineSt n :=
  if (v2 != v3 && v2 != first) = true then
    let st1 := if (v2 == first + 1) = true then u.cellstart.set! u.lab[first]! n else u.cellstart
    let st2 := if (v3 == v2 + 1) = true then st1.set! u.lab[v2]! n else st1
    let u5 := ({ u with
      numcells := u.numcells + 1, ptn := u.ptn.set! (v2 - 1) level
      cellend := (u.cellend.set! first (v2 - 1)).set! v2 (v3 - 1), cellstart := st2 } : RefineSt n).hash v2
    if (decide (v2 - first ≤ v3 - v2) && !u.active.mem first) = true then u5.push first else u5.push v2
  else u

/-- The state after a touched cell's partition and write-back. -/
abbrev midSt (stamp first : Nat) (s : RefineSt n) : RefineSt n :=
  let p := partAt s.vmarks stamp first s.lab (s.cellend[first]! + 1 - first)
  let r := revAt p.2.1 p.2.2 p.1 s.cellstart p.2.2.size
  { s with
    lab := r.1, cellstart := r.2.1
    longcode := Hex.GraphIso.Nauty.mash (Hex.GraphIso.Nauty.mash s.longcode first) p.2.2.size }

theorem ite_pure_eq {β : Type} {b : Bool} {A B A' B' : β} (h1 : A = A') (h2 : B = B') :
    (if b = true then (pure A : Id β) else pure B) = (if b = true then A' else B') := by
  subst h1 h2; split <;> rfl

theorem cellT_fix (level stamp first : Nat) (s : RefineSt n) :
    cellT level stamp first s =
      fixRes level first (partAt s.vmarks stamp first s.lab (s.cellend[first]! + 1 - first)).2.1
        (revAt (partAt s.vmarks stamp first s.lab (s.cellend[first]! + 1 - first)).2.1
          (partAt s.vmarks stamp first s.lab (s.cellend[first]! + 1 - first)).2.2
          (partAt s.vmarks stamp first s.lab (s.cellend[first]! + 1 - first)).1 s.cellstart
          (partAt s.vmarks stamp first s.lab (s.cellend[first]! + 1 - first)).2.2.size).2.2
        (midSt stamp first s) := by
  unfold cellT fixRes
  simp only [Id.run, RefineSt.hash, RefineSt.push, partAt, revAt]
  split
  · rename_i h1
    simp only [h1, ite_true]
    split
    · rename_i h2
      simp only [h2, ite_true]
      split
      · rename_i h3
        simp only [h3, ite_true]
        exact ite_pure_eq rfl rfl
      · rename_i h3
        simp only [h3, Bool.false_eq_true, ite_false]
        exact ite_pure_eq rfl rfl
    · rename_i h2
      simp only [h2, Bool.false_eq_true, ite_false]
      split
      · rename_i h3
        simp only [h3, ite_true]
        exact ite_pure_eq rfl rfl
      · rename_i h3
        simp only [h3, Bool.false_eq_true, ite_false]
        exact ite_pure_eq rfl rfl
  · rename_i h1
    simp only [h1, Bool.false_eq_true, ite_false]
    rfl

end NautyVerified.Proofs.Sparse.Refine.Trivial
