import HexGraphIso.Nauty.Search.VSet.Basic
import NautyVerified.Spec.Set

/-!
# nauty's `nextelement` against HexGraphIso's `VSet.nextElem`

A C set and a `VSet` represent the same set when their membership functions
agree. Then nauty's `nextelement` result (`IsNext` or `NoNext` of the C
membership) determines `VSet.nextElem`: this is how the C function's
specification transfers to HexGraphIso, whatever the two bit layouts.
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty

/-- `nextelement`'s `pos` argument for HexGraphIso's optional position. -/
def posOf : Option Nat → Int
  | none => -1
  | some p => p

theorem scanStart_eq (pos : Option Nat) (v : Nat) :
    VSet.scanStart pos ≤ v ↔ posOf pos < v := by
  cases pos <;> simp [VSet.scanStart, posOf] <;> omega

theorem nextElem_eq_some {n : Nat} {s : VSet n} {S : Nat → Bool} (hrep : ∀ v, s.mem v = S v)
    {pos : Option Nat} {r : Nat} (h : IsNext S (posOf pos) r) : s.nextElem pos = some r := by
  cases hn : s.nextElem pos with
  | none =>
    have := VSet.nextElem_none hn r ((scanStart_eq pos r).2 h.1)
    rw [hrep, h.2.1] at this; cases this
  | some r' =>
    have h' := VSet.nextElem_some hn
    have : IsNext S (posOf pos) r' :=
      ⟨(scanStart_eq pos r').1 h'.2.1, by rw [← hrep]; exact h'.1,
        fun v hv hvr => by rw [← hrep]; exact h'.2.2 v ((scanStart_eq pos v).2 hv) hvr⟩
    rw [this.unique h]

theorem nextElem_eq_none {n : Nat} {s : VSet n} {S : Nat → Bool} (hrep : ∀ v, s.mem v = S v)
    {pos : Option Nat} {bound : Nat} (hb : n ≤ bound) (h : NoNext S (posOf pos) bound) :
    s.nextElem pos = none := by
  cases hn : s.nextElem pos with
  | none => rfl
  | some r =>
    have h' := VSet.nextElem_some hn
    have hr : r < n := VSet.mem_lt h'.1
    have := h r ((scanStart_eq pos r).1 h'.2.1) (by omega)
    rw [← hrep, h'.1] at this; cases this

end NautyVerified.Spec
