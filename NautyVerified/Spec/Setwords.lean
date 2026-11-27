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

theorem setRep_inter {n M : Nat} {ws wt : Nat → BitVec 64} {s t : VSet n} (hs : SetRep ws M s)
    (ht : SetRep wt M t) : SetRep (fun w => ws w &&& wt w) M (s.inter t) :=
  ⟨hs.1, fun v hv => by
    rw [VSet.mem_inter, ← hs.2 v hv, ← ht.2 v hv]
    simp only [SetwordsMem, BitVec.getMsbD_and]⟩

/-- nauty's word-wise `NOTSUBSET` test over `M` words decides HexGraphIso's `subset`. -/
theorem setRep_subset {n M : Nat} {ws wt : Nat → BitVec 64} {s t : VSet n} (hs : SetRep ws M s)
    (ht : SetRep wt M t) : (∀ i < M, ws i &&& ~~~ wt i = 0) ↔ s.subset t = true := by
  rw [VSet.subset_iff]
  constructor
  · intro h v hv
    have hvn := VSet.mem_lt hv
    have hvM : v < 64 * M := Nat.lt_of_lt_of_le hvn hs.1
    have hw := h (v / 64) (by omega)
    have hb := congrArg (fun x => x.getMsbD (v % 64)) hw
    simp only [BitVec.getMsbD_and, BitVec.getMsbD_not] at hb
    rw [← ht.2 v hvM]
    rw [← hs.2 v hvM] at hv
    simp only [SetwordsMem] at hv ⊢
    rw [hv] at hb
    simpa [Nat.mod_lt v (by decide : 64 > 0)] using hb
  · intro h i hi
    apply BitVec.eq_of_getMsbD_eq
    intro j hj
    simp only [BitVec.getMsbD_and, BitVec.getMsbD_not, hj, decide_true,
      Bool.true_and]
    have hv : 64 * i + j < 64 * M := by omega
    have e1 : (64 * i + j) / 64 = i := by omega
    have e2 : (64 * i + j) % 64 = j := by omega
    have h1 := hs.2 _ hv
    have h2 := ht.2 _ hv
    simp only [SetwordsMem, e1, e2] at h1 h2
    rw [h1, h2]
    cases hm : s.mem (64 * i + j)
    · simp
    · simp [h _ hm]

end NautyVerified.Spec
