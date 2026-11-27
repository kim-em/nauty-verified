import NautyVerified.Logic.Array

/-!
# Pointer comparisons

C compares pointers into the same block by offset, provided both are (weakly)
valid: inside the block's permissions or one past its end. `cmplu_same`
states this; `ArrayAt.valid_pointer` and `ArrayAt.weak_valid` give the
validity of every address in an array and of the address one past its end.
-/

namespace NautyVerified.Logic

open CompCert4Lean CompCert4Lean.Common.Memory CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Values CompCert4Lean.Common.AST CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified.Word

theorem cmplu_same (vp : block → Z → Bool) (c : Lib.Integers.comparison) (b : block) (o1 o2 : ptrofs)
    (h1 : (vp b (Ptrofs.unsigned o1) || vp b (ZArith.BinInt.Z.sub (Ptrofs.unsigned o1) (.Zpos .xH))) = true)
    (h2 : (vp b (Ptrofs.unsigned o2) || vp b (ZArith.BinInt.Z.sub (Ptrofs.unsigned o2) (.Zpos .xH))) = true) :
    Val.cmplu_bool vp c (.Vptr b o1) (.Vptr b o2) = some (Ptrofs.cmpu c o1 o2) := by
  unfold Val.cmplu_bool
  rcases hb : Common.Values.eq_block b b with h | h
  · show (if _ then _ else _) = _
    simp only [show X86_64.Archi.ptr64 = true from rfl, ite_true]
    rw [hb]
    show (if true = true then _ else _) = _
    rw [ite_eq_left rfl]
    exact ite_eq_left (by rw [Bool.and_eq_true]; exact ⟨h1, h2⟩)
  · exact absurd rfl h

theorem ArrayAt.valid_pointer {m : mem} {chunk : memory_chunk} {b : block} {base : Int}
    {vals : Nat → val} {n : Nat} (h : ArrayAt m chunk b base vals n) {o : Int}
    (h1 : base ≤ o) (h2 : o < base + csize chunk * n) :
    Mem.valid_pointer m b (zOfInt o) = true := by
  have hs := csize_pos chunk
  -- the element containing byte `o`, computed in `Nat`
  obtain ⟨c, hc⟩ : ∃ c : Nat, csize chunk = c := ⟨(csize chunk).toNat, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d : Nat, o - base = d := ⟨(o - base).toNat, by omega⟩
  have hc0 : 0 < c := by omega
  have hdm := Nat.div_add_mod d c
  have hmod := Nat.mod_lt d hc0
  have hi : d / c < n := by
    apply Nat.lt_of_not_le
    intro hle
    have := Nat.mul_le_mul_left c hle
    have h2' : (d : Int) < c * n := by rw [hc] at h2; omega
    have : (c * n : Nat) ≤ c * (d / c) := this
    omega
  have hc' : intOfZ (size_chunk chunk) = c := hc
  have hcast : ((c * (d / c) : Nat) : Int) = (c : Int) * ((d / c : Nat) : Int) := by push_cast; rfl
  have hw := (h.writable (d / c) hi).1 (zOfInt o) ⟨by
      change intOfZ (zOfInt _) ≤ intOfZ (zOfInt o)
      simp only [intOfZ_zOfInt, hc]
      omega, by
      change intOfZ (zOfInt o) < intOfZ (ZArith.BinInt.Z.add _ _)
      simp only [elemOfs, intOfZ_zOfInt, intOfZ_add, hc, hc']
      omega⟩
  exact (Mem.valid_pointer_nonempty_perm m b _).2 (Mem.perm_implies _ _ _ _ _ _ hw (.perm_any_N _))

theorem ArrayAt.weak_valid {m : mem} {chunk : memory_chunk} {b : block} {base : Int}
    {vals : Nat → val} {n : Nat} (h : ArrayAt m chunk b base vals n) (hn : 0 < n) {o : Int}
    (h1 : base ≤ o) (h2 : o ≤ base + csize chunk * n) :
    (Mem.valid_pointer m b (zOfInt o) ||
      Mem.valid_pointer m b (ZArith.BinInt.Z.sub (zOfInt o) (.Zpos .xH))) = true := by
  have hs := csize_pos chunk
  rcases Int.lt_or_eq_of_le h2 with hlt | heq
  · rw [h.valid_pointer h1 hlt, Bool.true_or]
  · have : ZArith.BinInt.Z.sub (zOfInt o) (.Zpos .xH) = zOfInt (o - 1) := by
      apply intOfZ_injective; simp [intOfZ_zOfInt]; rfl
    rw [this, h.valid_pointer (o := o - 1) (by
      have : csize chunk * 1 ≤ csize chunk * n :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega) (by omega), Bool.or_true]

end NautyVerified.Logic
