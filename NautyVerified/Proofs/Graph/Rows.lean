import NautyVerified.Proofs.Prune.LongPair
import NautyVerified.Proofs.Nextelement.Satisfies
import NautyVerified.Proofs.Alloc.Dyn

/-!
# Graphs in memory

nauty stores a graph on `n` vertices as `n` rows of `M` setwords, row `v`
from word `M * v`. `GraphAt m bg gofs gw rows M`: the words `gw` are there,
and row `v` represents HexGraphIso's `rows[v]`. `row_words` gives a row in
the form `nextelement`'s specification reads.
-/

namespace NautyVerified.Proofs.Graph

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty (VSet)

/-- A graph on `n` vertices, `M` words per row, at `bg + gofs`. -/
structure GraphAt {n : Nat} (m : mem) (bg : block) (gofs : ptrofs) (gw : Nat → Lib.Integers.int64)
    (rows : Array (VSet n)) (M : Nat) : Prop where
  arr : ArrayAt m .Mint64 bg (intOfZ (Ptrofs.unsigned gofs)) (longs gw) (M * n)
  rep : ∀ v < n, SetRep (fun w => bv64 (gw (M * v + w))) M rows[v]!

/-- An array of words at a pointer, as `nextelement`'s specification reads it. -/
theorem wordsAt_of {m : mem} {b : block} {ofs : ptrofs} {ws : Nat → Lib.Integers.int64} {M : Nat}
    (h : ArrayAt m .Mint64 b (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M) :
    Nextelement.WordsAt m b ofs ws M := by
  intro i hi
  have hf := h.fits
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf
  have hu : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (zOfInt (8 * (i : Int))))) =
      elemOfs .Mint64 (intOfZ (Ptrofs.unsigned ofs)) i := by
    apply intOfZ_injective
    rw [intOfZ_Ptrofs_unsigned, elemOfs, intOfZ_zOfInt, h8, bvp_add, bvp_repr, intOfZ_zOfInt,
      BitVec.toNat_add, BitVec.toNat_ofInt]
    have hb : ((bvp ofs).toNat : Int) = intOfZ (Ptrofs.unsigned ofs) := by
      rw [intOfZ_Ptrofs_unsigned]
    have hb0 := h.base_nonneg
    omega
  rw [hu]
  exact h.load i hi

theorem ptrTo_zero (ofs : ptrofs) : ptrTo (intOfZ (Ptrofs.unsigned ofs)) 8 0 = ofs := by
  apply bvp_inj.1
  rw [bvp_repr, intOfZ_zOfInt, bvp_eq_ofInt ofs]
  simp

/-- `p + k` for an `unsigned long` offset `k`. -/
theorem add_ptrTo_long (ce : Cfrontend.Ctypes.composite_env) (ofs : ptrofs) (k : Nat) :
    Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr (Cfrontend.Ctypes.sizeof ce tulong))
      (Ptrofs.of_int64 (lr k))) = ptrTo (intOfZ (Ptrofs.unsigned ofs)) 8 k := by
  apply bvp_inj.1
  have h8 : intOfZ (Cfrontend.Ctypes.sizeof ce tulong) = 8 := rfl
  rw [bvp_add, bvp_mul, bvp_repr, bvp_of_int64, bv64_repr, intOfZ_zOfInt, bvp_repr, intOfZ_zOfInt,
    h8, bvp_eq_ofInt ofs, ← BitVec.ofInt_mul, ← BitVec.ofInt_add]

theorem mul_lr {a b : Nat} (ha : a < 2147483648) :
    Lib.Integers.Int64.mul (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir a))) (lr b) =
      lr (a * b) := by
  have := cast_int_long_ir (a := a) ⟨by omega, by omega⟩
  rw [show Cfrontend.Cop.cast_int_long .Signed (ir a) =
    Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir a)) from rfl] at this
  rw [this, Alloc.lr_mul]

/-- Row `v` of a graph, through a pointer to it. -/
theorem GraphAt.row {n : Nat} {m : mem} {bg : block} {gofs : ptrofs} {gw : Nat → Lib.Integers.int64}
    {rows : Array (VSet n)} {M : Nat} (h : GraphAt m bg gofs gw rows M) {v : Nat} (hv : v < n) :
    ArrayAt m .Mint64 bg (intOfZ (Ptrofs.unsigned (ptrTo (intOfZ (Ptrofs.unsigned gofs)) 8 (M * v))))
      (longs fun i => gw (M * v + i)) M :=
  Prune.Long.slice_at h.arr (M * v) M (by
    have := Nat.mul_le_mul_left M (show v + 1 ≤ n by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; exact this)

theorem setRep_congr {n M : Nat} {ws ws' : Nat → BitVec 64} {s : VSet n} (h : SetRep ws M s)
    (he : ∀ w < M, ws w = ws' w) : SetRep ws' M s :=
  ⟨h.1, fun v hv => by
    rw [← h.2 v hv]; simp only [SetwordsMem]; rw [he _ (by omega)]⟩

/-- The words of a graph with row `i` replaced by `w'`. -/
def rowSet (cw : Nat → Lib.Integers.int64) (M i : Nat) (w' : Nat → Lib.Integers.int64) (u : Nat) :
    Lib.Integers.int64 :=
  if M * i ≤ u ∧ u < M * i + M then w' (u - M * i) else cw u

/-- Replacing row `i` of a graph, after a change confined to that row. -/
theorem GraphAt.setRow {n : Nat} {m m' : mem} {bc : block} {cofs : ptrofs}
    {cw : Nat → Lib.Integers.int64} {rows : Array (VSet n)} {M i : Nat}
    (h : GraphAt m bc cofs cw rows M) (hi : i < n) (hsz : rows.size = n)
    {w' : Nat → Lib.Integers.int64} {r : VSet n}
    (h' : ArrayAt m' .Mint64 bc (intOfZ (Ptrofs.unsigned (ptrTo (intOfZ (Ptrofs.unsigned cofs)) 8 (M * i))))
      (longs w') M)
    (hrep : SetRep (fun w => bv64 (w' w)) M r)
    (ho : Outside m m' bc (intOfZ (Ptrofs.unsigned (ptrTo (intOfZ (Ptrofs.unsigned cofs)) 8 (M * i))))
      (intOfZ (Ptrofs.unsigned (ptrTo (intOfZ (Ptrofs.unsigned cofs)) 8 (M * i))) + 8 * M)) :
    GraphAt m' bc cofs (rowSet cw M i w') (rows.set! i r) M := by
  have hf := h.arr.fits
  have hb := h.arr.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf
  have hle : M * i + M ≤ M * n := by
    have := Nat.mul_le_mul_left M (show i + 1 ≤ n by omega); rw [Nat.mul_add, Nat.mul_one] at this
    exact this
  have hMn : ((M * n : Nat) : Int) = (M : Int) * n := by push_cast; rfl
  have hu : intOfZ (Ptrofs.unsigned (ptrTo (intOfZ (Ptrofs.unsigned cofs)) 8 (M * i))) =
      intOfZ (Ptrofs.unsigned cofs) + 8 * ((M * i : Nat) : Int) := by
    apply unsigned_ptrTo <;> push_cast at hf ⊢ <;> omega
  rw [hu] at h' ho
  refine ⟨?_, fun v hv => ?_⟩
  · have := ArrayAt.outside h.arr (M * i) M (by rw [h8]; exact h')
      (by rw [h8, Int.mul_add, ← Int.add_assoc]; exact ho)
    refine this.congr fun u _ => ?_
    simp only [rowSet, longs]
    split <;> rfl
  · by_cases hvi : v = i
    · subst hvi
      rw [Array.getElem!_set!_self _ _ _ (by omega)]
      refine setRep_congr hrep fun w hw => ?_
      simp only [rowSet]
      rw [ite_eq_left ⟨by omega, by omega⟩, show M * v + w - M * v = w by omega]
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hvi)]
      refine setRep_congr (h.rep v hv) fun w hw => ?_
      simp only [rowSet]
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      rcases Nat.lt_or_gt_of_ne hvi with hlt | hgt
      · have := Nat.mul_le_mul_left M (show v + 1 ≤ i by omega)
        rw [Nat.mul_add, Nat.mul_one] at this; omega
      · have := Nat.mul_le_mul_left M (show i + 1 ≤ v by omega)
        rw [Nat.mul_add, Nat.mul_one] at this; omega

end NautyVerified.Proofs.Graph
