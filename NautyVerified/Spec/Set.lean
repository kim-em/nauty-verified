/-!
# nauty's sets, mathematically

nauty represents a set of vertices as `m` words of 64 bits ("setwords"),
most significant bit first: vertex `v` is bit `63 - v % 64` of word `v / 64`.
`SetwordsMem words v` is that membership; `IsNext S pos r` says `r` is the
least member of `S` greater than `pos` (any member when `pos < 0`), which is
what nauty's `nextelement` computes, and `NoNext S pos bound` says there is
none below `bound`.

These are stated over `Nat → Bool` membership functions so that they apply
equally to the C representation and to HexGraphIso's `VSet` (63-bit limbs,
least significant first), which share the membership function but not the
bit layout.
-/

namespace NautyVerified.Spec

/-- Membership in `m` setwords, most significant bit first. -/
def SetwordsMem (words : Nat → BitVec 64) (v : Nat) : Bool :=
  (words (v / 64)).getMsbD (v % 64)

/-- `r` is the least member of `S` above `pos` (from `0` when `pos < 0`). -/
def IsNext (S : Nat → Bool) (pos : Int) (r : Nat) : Prop :=
  pos < r ∧ S r = true ∧ ∀ v : Nat, pos < v → v < r → S v = false

/-- No member of `S` lies strictly between `pos` and `bound`. -/
def NoNext (S : Nat → Bool) (pos : Int) (bound : Nat) : Prop :=
  ∀ v : Nat, pos < v → v < bound → S v = false

theorem IsNext.unique {S : Nat → Bool} {pos : Int} {r r' : Nat} (h : IsNext S pos r)
    (h' : IsNext S pos r') : r = r' := by
  rcases Nat.lt_trichotomy r r' with hlt | heq | hgt
  · have := h'.2.2 r h.1 hlt
    rw [h.2.1] at this; cases this
  · exact heq
  · have := h.2.2 r' h'.1 hgt
    rw [h'.2.1] at this; cases this

theorem IsNext.not_noNext {S : Nat → Bool} {pos : Int} {r bound : Nat} (h : IsNext S pos r)
    (hr : r < bound) : ¬ NoNext S pos bound := fun hn => by
  have := hn r h.1 hr
  rw [h.2.1] at this; cases this

end NautyVerified.Spec
