import HexGraphIso.Nauty.Search.VSet.Basic
import NautyVerified.Spec.Set

/-!
# nauty's setwords representing HexGraphIso's `VSet`

`SetRep ws M s`: the `M` setwords `ws` (64 bits each, most significant bit
first) hold the same members as the `VSet` `s` (63-bit limbs, least
significant first). The relation is membership-level, so it is independent
of either bit layout. `bitAt j` is nauty's `bit[j]`, the word with only
position `j` set; `setRep_empty` and `setRep_insert` are nauty's `EMPTYSET`
and `ADDELEMENT`.
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty

/-- `M` setwords represent `s`. -/
def SetRep {n : Nat} (ws : Nat → BitVec 64) (M : Nat) (s : VSet n) : Prop :=
  n ≤ 64 * M ∧ ∀ v, v < 64 * M → SetwordsMem ws v = s.mem v

/-- nauty's `bit[j]`: only position `j` (from the most significant end) set. -/
def bitAt (j : Nat) : BitVec 64 := BitVec.ofNat 64 (2 ^ (63 - j))

theorem getMsbD_bitAt {j i : Nat} (hj : j < 64) (hi : i < 64) :
    (bitAt j).getMsbD i = decide (i = j) := by
  unfold bitAt
  rw [BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_ofNat]
  simp only [hi, decide_true, Bool.true_and, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h; simp; omega
  · simp [h]; omega

theorem setRep_empty {n M : Nat} (hn : n ≤ 64 * M) :
    SetRep (fun _ => 0) M (VSet.empty : VSet n) :=
  ⟨hn, fun v _ => by simp [SetwordsMem]⟩

theorem setRep_insert {n M : Nat} {ws : Nat → BitVec 64} {s : VSet n} (h : SetRep ws M s)
    {v : Nat} (hv : v < n) :
    SetRep (fun w => if w = v / 64 then ws w ||| bitAt (v % 64) else ws w) M (s.insert v) := by
  refine ⟨h.1, fun u hu => ?_⟩
  rw [VSet.mem_insert_of_lt s hv, ← h.2 u hu]
  simp only [SetwordsMem]
  by_cases hw : u / 64 = v / 64
  · rw [ite_eq_left hw, BitVec.getMsbD_or, getMsbD_bitAt (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
    congr 1
    by_cases huv : u = v
    · subst huv; simp
    · have : u % 64 ≠ v % 64 := fun h' => huv (by omega)
      simp [this, Ne.symm huv]
  · rw [ite_eq_right hw]
    have : u ≠ v := fun h' => hw (by rw [h'])
    simp [Ne.symm this]

end NautyVerified.Spec
