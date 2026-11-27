import NautyVerified.Proofs.Nextelement.Bits

/-!
# What `nextelement` computes, and the scan invariant

`NextSpec ws n pos r`: `r` is the least member above `pos` of the set held in
the `n` words `ws` (most significant bit first), or `-1` if there is none.
`Good ws n pos w s` is the loop invariant of the word scan: `s` holds exactly
the bits of word `w` above `pos`, and nothing in `(pos, 64 w)` is a member.
Ported from the CLean-based experiment.
-/

namespace NautyVerified.Proofs.Nextelement

/-- `BITMASK(b)` keeps exactly the bits after position `b` (most significant first). -/
theorem bitmask_getMsbD (x : BitVec 64) (b i : Nat) (hb : b < 64) (hi : i < 64) :
    (x &&& (BitVec.ofInt 64 9223372036854775807 >>> b)).getMsbD i = (x.getMsbD i && decide (b < i)) := by
  have hc : ∀ j < 64, (BitVec.ofInt 64 9223372036854775807).getMsbD j = decide (0 < j) := by
    decide
  simp only [BitVec.getMsbD_and, BitVec.getMsbD_ushiftRight]
  by_cases hib : i < b
  · simp [hib, show ¬ b < i by omega]
  · rw [hc (i - b) (by omega)]
    by_cases h : b < i
    · simp [hi, hib, h, show 0 < i - b by omega]
    · simp [hi, hib, h, show i - b = 0 by omega]


/-- `v` belongs to the set held in the `n` words `ws`. -/
def InSet (ws : Nat → BitVec 64) (n v : Nat) : Prop :=
  v < 64 * n ∧ (ws (v / 64)).getMsbD (v % 64) = true

/-- `r` is what `nextelement(set1, n, pos)` must return: the least element
    `> pos`, or `-1` if there is none. -/
def NextSpec (ws : Nat → BitVec 64) (n : Nat) (pos : _root_.Int) (r : _root_.Int) : Prop :=
  (r = -1 ∧ ∀ v : Nat, pos < v → ¬ InSet ws n v)
  ∨ (∃ v : Nat, r = v ∧ pos < v ∧ InSet ws n v ∧ ∀ u : Nat, pos < u → u < v → ¬ InSet ws n u)

/-- Scan state at word `w` holding the (masked) word `s`: `s` has exactly the
    bits of word `w` above `pos`, and nothing in `(pos, 64 w)` is in the set. -/
def Good (ws : Nat → BitVec 64) (n : Nat) (pos : _root_.Int) (w : Nat)
    (s : BitVec 64) : Prop :=
  pos < 64 * ((w : _root_.Int) + 1)
  ∧ (∀ i < 64, s.getMsbD i = ((ws w).getMsbD i && decide (pos < ((64 * w + i : Nat) : _root_.Int))))
  ∧ ∀ v : Nat, pos < v → v < 64 * w → ¬ InSet ws n v

theorem spec_found {ws : Nat → BitVec 64} {n : Nat} {pos : _root_.Int} {w : Nat}
    {s : BitVec 64} {r : Nat} (hg : Good ws n pos w s) (hw : w < n) (hl : LeadBit s r) :
    NextSpec ws n pos ((64 * w + r : Nat) : _root_.Int) := by
  obtain ⟨_, hbits, habs⟩ := hg
  obtain ⟨hr, hsr, hmin⟩ := hl
  have hdiv : (64 * w + r) / 64 = w := by omega
  have hmod : (64 * w + r) % 64 = r := by omega
  have hb := hbits r hr
  rw [hsr] at hb
  have hb' := hb.symm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb'
  refine Or.inr ⟨64 * w + r, rfl, hb'.2, ⟨by omega, by rw [hdiv, hmod]; exact hb'.1⟩, ?_⟩
  intro u hu1 hu2 hin
  by_cases hu : u < 64 * w
  · exact habs u hu1 hu hin
  · have hi : u - 64 * w < r := by omega
    have hdu : u / 64 = w := by omega
    have hmu : u % 64 = u - 64 * w := by omega
    have := hbits (u - 64 * w) (by omega)
    rw [hmin _ hi] at this
    obtain ⟨_, hin2⟩ := hin
    rw [hdu, hmu] at hin2
    rw [hin2, show 64 * w + (u - 64 * w) = u by omega] at this
    simp [hu1] at this

theorem good_zero {ws : Nat → BitVec 64} {n : Nat} {pos : _root_.Int} {w : Nat} (hg : Good ws n pos w 0) :
    ∀ v : Nat, pos < v → v < 64 * (w + 1) → ¬ InSet ws n v := by
  obtain ⟨_, hbits, habs⟩ := hg
  intro v hv1 hv2 hin
  by_cases hv : v < 64 * w
  · exact habs v hv1 hv hin
  · have := hbits (v - 64 * w) (by omega)
    obtain ⟨_, hin2⟩ := hin
    rw [show v / 64 = w by omega, show v % 64 = v - 64 * w by omega] at hin2
    rw [hin2, show 64 * w + (v - 64 * w) = v by omega] at this
    simp [hv1] at this

theorem spec_none {ws : Nat → BitVec 64} {n : Nat} {pos : _root_.Int} (h : ∀ v : Nat, pos < v → v < 64 * n → ¬ InSet ws n v) :
    NextSpec ws n pos (-1) :=
  Or.inl ⟨rfl, fun v hv hin => h v hv hin.1 hin⟩

theorem good_next {ws : Nat → BitVec 64} {n : Nat} {pos : _root_.Int} {w : Nat} (hp : pos < 64 * ((w : _root_.Int) + 1))
    (h : ∀ v : Nat, pos < v → v < 64 * (w + 1) → ¬ InSet ws n v) :
    Good ws n pos (w + 1) (ws (w + 1)) := by
  refine ⟨by push_cast; omega, fun i hi => ?_, h⟩
  have : decide (pos < ((64 * (w + 1) + i : Nat) : _root_.Int)) = true :=
    decide_eq_true (by push_cast; omega)
  rw [this, Bool.and_true]

theorem good_start_neg {ws : Nat → BitVec 64} {n : Nat} : Good ws n (-1) 0 (ws 0) := by
  refine ⟨by decide, fun i _ => ?_, fun v hv1 hv2 => by omega⟩
  have : decide ((-1 : _root_.Int) < ((64 * 0 + i : Nat) : _root_.Int)) = true :=
    decide_eq_true (by omega)
  rw [this, Bool.and_true]

theorem good_start {ws : Nat → BitVec 64} {n : Nat} (q : Nat) :
    Good ws n (q : _root_.Int) (q / 64)
      (ws (q / 64) &&& (BitVec.ofInt 64 9223372036854775807 >>> (q % 64))) := by
  refine ⟨by omega, fun i hi => ?_, fun v hv1 hv2 => by omega⟩
  rw [bitmask_getMsbD _ _ _ (by omega) hi]
  congr 1
  apply decide_eq_decide.2
  omega


end NautyVerified.Proofs.Nextelement
