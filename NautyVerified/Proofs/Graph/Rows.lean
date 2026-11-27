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

end NautyVerified.Proofs.Graph
