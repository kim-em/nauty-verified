import NautyVerified.Word.Repr
import CompCert4Lean.Common.Memory

/-!
# Arrays in memory

`ArrayAt m chunk b base vals n`: block `b` holds, from byte offset `base`, `n`
elements of memory chunk `chunk`, element `i` being `vals i` and writable.
`load_array` and `store_array` read and write one element; `store_array`
returns the array with that element updated, and `load_store_away` frames
every location outside the element written.

Offsets are integers (`base + size * i`), with the array inside the address
space, so no wrap-around arises; `addr_elem` relates them to the pointer
arithmetic of C's `p + i`.
-/

namespace NautyVerified.Logic

open CompCert4Lean CompCert4Lean.Common.Memory CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values CompCert4Lean.Common.AST CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified.Word

/-- `f` with the value at `i` replaced by `v`. -/
def upd {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α := fun j => if j = i then v else f j

@[simp] theorem upd_same {α : Type} (f : Nat → α) (i : Nat) (v : α) : upd f i v i = v := by
  simp [upd]

theorem upd_ne {α : Type} (f : Nat → α) {i j : Nat} (v : α) (h : j ≠ i) : upd f i v j = f j := by
  simp [upd, h]

/-- The byte size of a chunk, as an integer. -/
abbrev csize (chunk : memory_chunk) : Int := intOfZ (size_chunk chunk)

/-- The byte offset of element `i`. -/
abbrev elemOfs (chunk : memory_chunk) (base : Int) (i : Nat) : Z :=
  zOfInt (base + csize chunk * i)

/-- An array of `n` elements of `chunk` at `base` in block `b`. -/
structure ArrayAt (m : mem) (chunk : memory_chunk) (b : block) (base : Int)
    (vals : Nat → val) (n : Nat) : Prop where
  base_nonneg : 0 ≤ base
  fits : base + csize chunk * n < 2 ^ 64
  load : ∀ i < n, Mem.load chunk m b (elemOfs chunk base i) = some (vals i)
  writable : ∀ i < n, Mem.valid_access m chunk b (elemOfs chunk base i) .Writable

theorem csize_pos (chunk : memory_chunk) : 0 < csize chunk := by
  cases chunk <;> decide

/-- Storing element `i` updates the array. -/
theorem store_array {m : mem} {chunk : memory_chunk} {b : block} {base : Int}
    {vals : Nat → val} {n : Nat} (h : ArrayAt m chunk b base vals n) {i : Nat} (hi : i < n)
    (v : val) (hv : Val.load_result chunk v = v) :
    ∃ m', Mem.store chunk m b (elemOfs chunk base i) v = some m' ∧
      ArrayAt m' chunk b base (upd vals i v) n ∧
      ∀ chunk' b' ofs', (b' ≠ b ∨
          intOfZ ofs' + csize chunk' ≤ base + csize chunk * i ∨
          base + csize chunk * (i + 1) ≤ intOfZ ofs') →
        Mem.load chunk' m' b' ofs' = Mem.load chunk' m b' ofs' := by
  obtain ⟨m', hm'⟩ := Mem.valid_access_store m chunk b _ v (h.writable i hi)
  refine ⟨m', hm', ⟨h.base_nonneg, h.fits, fun j hj => ?_, fun j hj => ?_⟩, ?_⟩
  · by_cases hij : j = i
    · subst hij
      rw [upd_same, Mem.load_store_same _ _ _ _ _ _ hm', hv]
    · rw [upd_ne _ _ hij]
      rw [Mem.load_store_other _ _ _ _ _ _ hm' _ _ _ (.inr ?_)]
      · exact h.load j hj
      have hs := csize_pos chunk
      rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
      · left
        change ZArith.BinInt.Z.le (ZArith.BinInt.Z.add _ _) _
        simp only [Z_le_iff, intOfZ_add, elemOfs, intOfZ_zOfInt]
        have : (j : Int) + 1 ≤ i := by omega
        have := Int.mul_le_mul_of_nonneg_left this (Int.le_of_lt hs)
        simp only [csize] at this ⊢
        rw [Int.mul_add, Int.mul_one] at this
        omega
      · right
        change ZArith.BinInt.Z.le (ZArith.BinInt.Z.add _ _) _
        simp only [Z_le_iff, intOfZ_add, elemOfs, intOfZ_zOfInt]
        have : (i : Int) + 1 ≤ j := by omega
        have := Int.mul_le_mul_of_nonneg_left this (Int.le_of_lt hs)
        simp only [csize] at this ⊢
        rw [Int.mul_add, Int.mul_one] at this
        omega
  · exact Mem.store_valid_access_1 _ _ _ _ _ _ hm' _ _ _ _ (h.writable j hj)
  · intro chunk' b' ofs' hfar
    apply Mem.load_store_other _ _ _ _ _ _ hm'
    rcases hfar with hb | hlo | hhi
    · exact .inl hb
    · right; left
      change ZArith.BinInt.Z.le (ZArith.BinInt.Z.add _ _) _
      simp only [Z_le_iff, intOfZ_add, elemOfs, intOfZ_zOfInt]; exact hlo
    · right; right
      change ZArith.BinInt.Z.le (ZArith.BinInt.Z.add _ _) _
      simp only [Z_le_iff, intOfZ_add, elemOfs, intOfZ_zOfInt]
      simp only [csize] at hhi ⊢
      push_cast at hhi
      rw [Int.mul_add, Int.mul_one] at hhi
      omega

/-- A store outside an array's region preserves it. -/
theorem ArrayAt.store_away {m m' : mem} {chunk : memory_chunk} {b : block} {base : Int}
    {vals : Nat → val} {n : Nat} (h : ArrayAt m chunk b base vals n)
    {chunk' : memory_chunk} {b' : block} {ofs' : Z} {v : val}
    (hst : Mem.store chunk' m b' ofs' v = some m')
    (hfar : b ≠ b' ∨ intOfZ ofs' + csize chunk' ≤ base ∨ base + csize chunk * n ≤ intOfZ ofs') :
    ArrayAt m' chunk b base vals n := by
  refine ⟨h.base_nonneg, h.fits, fun i hi => ?_, fun i hi =>
    Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ (h.writable i hi)⟩
  rw [Mem.load_store_other _ _ _ _ _ _ hst _ _ _ ?_]
  · exact h.load i hi
  have hs := csize_pos chunk
  rcases hfar with hb | hlo | hhi
  · exact .inl hb
  · right; right
    change ZArith.BinInt.Z.le (ZArith.BinInt.Z.add _ _) _
    simp only [Z_le_iff, intOfZ_add, elemOfs, intOfZ_zOfInt]
    have := Int.mul_nonneg (Int.le_of_lt hs) (Int.natCast_nonneg i)
    simp only [csize] at this hlo hs ⊢
    omega
  · right; left
    change ZArith.BinInt.Z.le (ZArith.BinInt.Z.add _ _) _
    simp only [Z_le_iff, intOfZ_add, elemOfs, intOfZ_zOfInt]
    have : (i : Int) + 1 ≤ n := by omega
    have := Int.mul_le_mul_of_nonneg_left this (Int.le_of_lt hs)
    simp only [csize] at this hhi ⊢
    rw [Int.mul_add, Int.mul_one] at this
    omega

/-- `m'` is `m` changed only inside the blocks `S` allows: every load from
another block is unchanged, and every valid access stays valid. -/
structure Unch (m m' : mem) (S : block → Prop) : Prop where
  load : ∀ chunk b' ofs, ¬ S b' → Mem.load chunk m' b' ofs = Mem.load chunk m b' ofs
  access : ∀ chunk b' ofs p, Mem.valid_access m chunk b' ofs p → Mem.valid_access m' chunk b' ofs p

theorem Unch.refl (m : mem) (S : block → Prop) : Unch m m S :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ h => h⟩

theorem Unch.trans {m₁ m₂ m₃ : mem} {S : block → Prop} (h₁ : Unch m₁ m₂ S) (h₂ : Unch m₂ m₃ S) :
    Unch m₁ m₃ S :=
  ⟨fun c b' o hb => (h₂.load c b' o hb).trans (h₁.load c b' o hb),
   fun c b' o p h => h₂.access c b' o p (h₁.access c b' o p h)⟩

theorem Unch.mono {m m' : mem} {S S' : block → Prop} (h : Unch m m' S) (hS : ∀ b, S b → S' b) :
    Unch m m' S' :=
  ⟨fun c b' o hb => h.load c b' o (fun h' => hb (hS _ h')), h.access⟩

theorem Unch.store {m m' : mem} {chunk : memory_chunk} {b : block} {ofs : Z} {v : val}
    (h : Mem.store chunk m b ofs v = some m') {S : block → Prop} (hb : S b) : Unch m m' S :=
  ⟨fun _ b' _ hb' => Mem.load_store_other _ _ _ _ _ _ h _ _ _ (.inl fun he => hb' (he ▸ hb)),
   fun _ _ _ _ hv => Mem.store_valid_access_1 _ _ _ _ _ _ h _ _ _ _ hv⟩

/-- An array in a block that does not change survives. -/
theorem ArrayAt.unch {m m' : mem} {S : block → Prop} (hu : Unch m m' S) {chunk : memory_chunk}
    {b : block} {base : Int} {vals : Nat → val} {n : Nat} (h : ArrayAt m chunk b base vals n)
    (hb : ¬ S b) : ArrayAt m' chunk b base vals n :=
  ⟨h.base_nonneg, h.fits, fun i hi => by rw [hu.load _ _ _ hb]; exact h.load i hi,
   fun i hi => hu.access _ _ _ _ (h.writable i hi)⟩

/-- C's `p + i`, for `p` pointing at offset `base` and an `int` index `i`
inside the array, is the address of element `i`. -/
theorem addr_elem (ofs : Lib.Integers.ptrofs) (sz : Z) (chunk : memory_chunk)
    (hsz : intOfZ sz = csize chunk) {base : Int} (hbase : intOfZ (Ptrofs.unsigned ofs) = base)
    {i : Nat} (hi : (i : Int) < 2147483648) (hfit : base + csize chunk * i < 2 ^ 64) :
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_ints (ir i)))) =
      elemOfs chunk base i := by
  apply intOfZ_injective
  rw [intOfZ_Ptrofs_unsigned, elemOfs, intOfZ_zOfInt]
  simp only [bvp_add, bvp_mul, bvp_repr, bvp_of_ints, toInt_ir (a := i) ⟨by omega, hi⟩, hsz,
    BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofInt]
  have hc := csize_pos chunk
  have hbase' : ((bvp ofs).toNat : Int) = base := by rw [← hbase, intOfZ_Ptrofs_unsigned]
  have hcs : csize chunk ≤ 8 := by cases chunk <;> decide
  have e1 : (csize chunk % ((2 ^ 64 : Nat) : Int)).toNat = (csize chunk).toNat := by
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
  have e2 : ((i : Int) % ((2 ^ 64 : Nat) : Int)).toNat = i := by omega
  rw [e1, e2]
  have hprod : (((csize chunk).toNat * i : Nat) : Int) = csize chunk * i := by
    push_cast; rw [Int.toNat_of_nonneg (by omega)]
  have hlt : (csize chunk).toNat * i < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  have hlt2 : (bvp ofs).toNat + (csize chunk).toNat * i < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt2]
  push_cast
  omega

/-- Loading element `i` through a pointer to it. -/
theorem load_array {m : mem} {chunk : memory_chunk} {b : block} {base : Int}
    {vals : Nat → val} {n : Nat} (h : ArrayAt m chunk b base vals n) {i : Nat} (hi : i < n)
    {ofs : Lib.Integers.ptrofs} (hofs : Ptrofs.unsigned ofs = elemOfs chunk base i) :
    Mem.loadv chunk m (.Vptr b ofs) = some (vals i) := by
  show Mem.load _ _ _ _ = _
  rw [hofs]; exact h.load i hi

end NautyVerified.Logic
