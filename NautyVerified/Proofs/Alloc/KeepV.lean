import NautyVerified.Proofs.Alloc.Keep
import NautyVerified.Proofs.Alloc.Malloc

/-!
# Keeping every block allocated

`KeepV m m'`: every block valid in `m` is still valid in `m'` and keeps its
`malloc` header and permissions (`Keep`). Code that only stores at offsets
`≥ 0` and allocates keeps it; it composes, so a function that never frees a
block passed to it can report it once for the caller (`KeepV.keep`).
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word

def KeepV (m m' : mem) : Prop :=
  ∀ b, Mem.valid_block m b → Keep m m' b ∧ Mem.valid_block m' b

theorem KeepV.refl (m : mem) : KeepV m m := fun b hb => ⟨Keep.refl m b, hb⟩

theorem KeepV.trans {m₁ m₂ m₃ : mem} (h₁ : KeepV m₁ m₂) (h₂ : KeepV m₂ m₃) : KeepV m₁ m₃ :=
  fun b hb => ⟨(h₁ b hb).1.trans (h₂ b (h₁ b hb).2).1, (h₂ b (h₁ b hb).2).2⟩

theorem KeepV.keep {m m' : mem} (h : KeepV m m') {b : block} (hb : Mem.valid_block m b) :
    Keep m m' b := (h b hb).1

theorem KeepV.valid {m m' : mem} (h : KeepV m m') {b : block} (hb : Mem.valid_block m b) :
    Mem.valid_block m' b := (h b hb).2

/-- A store at an offset `≥ 0`. -/
theorem KeepV.store {m m' : mem} {chunk : memory_chunk} {b : block} {ofs : Z} {v : val}
    (h : Mem.store chunk m b ofs v = some m') (hofs : 0 ≤ intOfZ ofs) : KeepV m m' := by
  intro b' hb'
  refine ⟨?_, Mem.store_valid_block_1 _ _ _ _ _ _ h _ hb'⟩
  by_cases he : b' = b
  · subst he; exact Keep.store h hofs
  · exact Keep.unch (Unch.store h (S := (· = b)) rfl) he

/-- A store into element `i` of an array. -/
theorem KeepV.storeArr {m m' : mem} {chunk : memory_chunk} {b : block} {base : Int}
    {vals : Nat → val} {n : Nat} (ha : ArrayAt m chunk b base vals n) {i : Nat} {v : val}
    (h : Mem.store chunk m b (elemOfs chunk base i) v = some m') : KeepV m m' := by
  refine KeepV.store h ?_
  unfold elemOfs
  rw [intOfZ_zOfInt]
  have := ha.base_nonneg
  have := csize_pos chunk
  have : 0 ≤ csize chunk * (i : Int) := Int.mul_nonneg (by omega) (by omega)
  omega

/-- An allocation. -/
theorem KeepV.alloc {m m' : mem} {lo hi : Z} {b : block} (h : Mem.alloc m lo hi = (m', b)) :
    KeepV m m' := by
  intro b' hb'
  refine ⟨Keep.unch (Unch.alloc h) ?_, Mem.valid_block_alloc _ _ _ _ _ h _ hb'⟩
  rintro rfl
  exact Mem.fresh_block_alloc _ _ _ _ _ h hb'

/-! ## `KeepA`: code that neither allocates nor frees -/

/-- Every block keeps its `malloc` header and permissions. Code that only
stores at offsets `≥ 0` (no allocation, no `free`) keeps it. -/
def KeepA (m m' : mem) : Prop := ∀ b, Keep m m' b

theorem KeepA.refl (m : mem) : KeepA m m := fun b => Keep.refl m b

theorem KeepA.trans {m₁ m₂ m₃ : mem} (h₁ : KeepA m₁ m₂) (h₂ : KeepA m₂ m₃) : KeepA m₁ m₃ :=
  fun b => (h₁ b).trans (h₂ b)

/-- A store at an offset `≥ 0`. -/
theorem KeepA.store {m m' : mem} {chunk : memory_chunk} {b : block} {ofs : Z} {v : val}
    (h : Mem.store chunk m b ofs v = some m') (hofs : 0 ≤ intOfZ ofs) : KeepA m m' := by
  intro b'
  by_cases he : b' = b
  · subst he; exact Keep.store h hofs
  · exact Keep.unch (Unch.store h (S := (· = b)) rfl) he

/-- A store into element `i` of an array. -/
theorem KeepA.storeArr {m m' : mem} {chunk : memory_chunk} {b : block} {base : Int}
    {vals : Nat → val} {n : Nat} (ha : ArrayAt m chunk b base vals n) {i : Nat} {v : val}
    (h : Mem.store chunk m b (elemOfs chunk base i) v = some m') : KeepA m m' := by
  refine KeepA.store h ?_
  unfold elemOfs
  rw [intOfZ_zOfInt]
  have := ha.base_nonneg
  have := csize_pos chunk
  have : 0 ≤ csize chunk * (i : Int) := Int.mul_nonneg (by omega) (by omega)
  omega

/-- Only `b` changed, and keeps its header and permissions. -/
theorem KeepA.of_keep {m m' : mem} {b : block} (hu : Unch m m' (· = b)) (hk : Keep m m' b) :
    KeepA m m' := by
  intro b'
  by_cases he : b' = b
  · subst he; exact hk
  · exact Keep.unch hu he

/-- A change confined to offsets `≥ lo ≥ 0` of `b`. -/
theorem Keep.of_outside' {m m' : mem} {b : block} {lo hi : Int} (ho : Outside m m' b lo hi)
    (hlo : 0 ≤ lo) : Keep m m' b :=
  Keep.of_outside (hi := hi) ⟨fun c o h => ho.load c o (by
    rcases h with h | h
    · exact .inl (by omega)
    · exact .inr h), ho.access⟩

/-- Only `b` changed, and only at offsets `≥ lo ≥ 0`. -/
theorem KeepA.of_outside {m m' : mem} {b : block} {lo hi : Int} (hu : Unch m m' (· = b))
    (ho : Outside m m' b lo hi) (hlo : 0 ≤ lo) : KeepA m m' :=
  KeepA.of_keep hu (Keep.of_outside' ho hlo)

/-- `KeepA` gives `Keep` for the block a caller cares about. -/
theorem KeepA.keep {m m' : mem} (h : KeepA m m') (b : block) : Keep m m' b := h b

end NautyVerified.Proofs.Alloc
