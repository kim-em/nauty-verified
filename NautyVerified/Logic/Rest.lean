import NautyVerified.Logic.Array

/-!
# Two word ranges of one block

`fmperm` and `fmptn` write two `M`-word sets, `fix` at `flo` in block `bf` and
`mcr` at `mlo` in block `bm`; nauty passes them adjacent in one block, the
automorphism workspace. `Apart`: the two are in different blocks or their
ranges do not overlap. `Rest`: when they share a block, nothing else in it
changed. `ArrayAt.acrossF`/`acrossM`: one set survives a write to the other.
-/

namespace NautyVerified.Logic

open CompCert4Lean CompCert4Lean.Common.Memory CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Word

/-- The two sets are in different blocks or do not overlap. -/
def Apart (bf : block) (flo : Int) (bm : block) (mlo : Int) (M : Nat) : Prop :=
  bf ≠ bm ∨ flo + 8 * M ≤ mlo ∨ mlo + 8 * M ≤ flo

/-- When the two sets share a block, the rest of it is unchanged. -/
def Rest (m m' : mem) (bf : block) (flo : Int) (bm : block) (mlo : Int) (M : Nat) : Prop :=
  bf = bm → ∀ chunk (ofs : Int), (ofs + csize chunk ≤ flo ∨ flo + 8 * M ≤ ofs) →
    (ofs + csize chunk ≤ mlo ∨ mlo + 8 * M ≤ ofs) →
    Mem.load chunk m' bf (zOfInt ofs) = Mem.load chunk m bf (zOfInt ofs)

variable {m m₁ m₂ m₃ m' : mem} {bf bm : block} {flo mlo : Int} {M : Nat}

theorem Rest.refl (m : mem) (bf : block) (flo : Int) (bm : block) (mlo : Int) (M : Nat) :
    Rest m m bf flo bm mlo M := fun _ _ _ _ _ => rfl

theorem Rest.trans (h₁ : Rest m₁ m₂ bf flo bm mlo M) (h₂ : Rest m₂ m₃ bf flo bm mlo M) :
    Rest m₁ m₃ bf flo bm mlo M :=
  fun he c o h1 h2 => (h₂ he c o h1 h2).trans (h₁ he c o h1 h2)

/-- A write confined to `fix`'s range. -/
theorem Rest.fix (hu : Unch m m' (· = bf)) (hO : Outside m m' bf flo (flo + 8 * M)) :
    Rest m m' bf flo bm mlo M :=
  fun _ c o h1 _ => hO.load c o h1

/-- A write confined to `mcr`'s range. -/
theorem Rest.mcr (hu : Unch m m' (· = bm)) (hO : Outside m m' bm mlo (mlo + 8 * M)) :
    Rest m m' bf flo bm mlo M :=
  fun he c o _ h2 => by subst he; exact hO.load c o h2

/-- A change avoiding the block. -/
theorem Rest.unch {W : block → Prop} (hu : Unch m m' W) (hb : ¬ W bf) :
    Rest m m' bf flo bm mlo M :=
  fun _ c o _ _ => hu.load c bf _ hb

theorem ArrayAt.across {vals : Nat → val} {b b' : block} {lo lo' : Int}
    (h : ArrayAt m .Mint64 b lo vals M) (hu : Unch m m' (· = b'))
    (hO : Outside m m' b' lo' (lo' + 8 * M)) (ha : b' ≠ b ∨ lo' + 8 * M ≤ lo ∨ lo + 8 * M ≤ lo') :
    ArrayAt m' .Mint64 b lo vals M := by
  by_cases hb : b' = b
  · subst hb
    have h8 : csize .Mint64 = 8 := rfl
    have hbn := h.base_nonneg
    refine ⟨h.base_nonneg, h.fits, fun i hi => ?_, fun i hi => hO.access _ _ _ (h.writable i hi)⟩
    rw [elemOfs, hO.load _ _ ?_]
    · exact h.load i hi
    · rw [h8]
      rcases ha with ha | ha | ha
      · exact absurd rfl ha
      · right; omega
      · left
        have : 8 * ((i : Int) + 1) ≤ 8 * M := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
        omega
  · exact h.unch hu (Ne.symm hb ∘ Eq.symm ∘ Eq.symm)

/-- `mcr` across a write to `fix`. -/
theorem ArrayAt.acrossF {vals : Nat → val} (h : ArrayAt m .Mint64 bm mlo vals M)
    (hu : Unch m m' (· = bf)) (hO : Outside m m' bf flo (flo + 8 * M)) (ha : Apart bf flo bm mlo M) :
    ArrayAt m' .Mint64 bm mlo vals M := h.across hu hO ha

/-- `fix` across a write to `mcr`. -/
theorem ArrayAt.acrossM {vals : Nat → val} (h : ArrayAt m .Mint64 bf flo vals M)
    (hu : Unch m m' (· = bm)) (hO : Outside m m' bm mlo (mlo + 8 * M)) (ha : Apart bf flo bm mlo M) :
    ArrayAt m' .Mint64 bf flo vals M :=
  h.across hu hO (by
    rcases ha with ha | ha | ha
    · exact .inl (Ne.symm ha)
    · exact .inr (.inr ha)
    · exact .inr (.inl ha))

end NautyVerified.Logic
