import NautyVerified.Proofs.Sparse.Refine.Ops
import NautyVerified.Proofs.Refine.Finish

/-!
# `refine_sg`'s code

`*code = CLEANUP(longcode)`, with `CLEANUP(l)` the `int` cast of `l % 077777`:
`wp_code` writes HexGraphIso's `cleanup l` into `*code`, both at the early
return (`l` the cell count) and at the end, after
`longcode = MASH(longcode, *numcells)` (`wp_finish`).
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- `l % 32767` for `0 ≤ l < 2^62`. -/
theorem mods_32767' {l : Nat} (hl : l < 2 ^ 62) :
    Lib.Integers.Int64.mods (lr l) (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir 32767))) =
      lr ((l % 32767 : Nat) : Int) := by
  apply bv64_inj.1
  have e : ∀ x y : Lib.Integers.int64, Lib.Integers.Int64.mods x y = Lib.Integers.Int64.repr
      (ZArith.BinInt.Z.sub (Lib.Integers.Int64.signed x) (ZArith.BinInt.Z.mul
        (ZArith.BinInt.Z.quot (Lib.Integers.Int64.signed x) (Lib.Integers.Int64.signed y))
        (Lib.Integers.Int64.signed y))) := fun _ _ => rfl
  rw [e, bv64_repr, bv64_repr]
  simp only [intOfZ_sub, intOfZ_mul, ZArith.BinInt.Z.quot, intOfZ_zOfInt, intOfZ_Int64_signed,
    bv64_repr]
  rw [show intOfZ (Lib.Integers.Int.signed (ir 32767)) = ((32767 : Nat) : Int) from
    Refine.signed_ir (by decide)]
  have h1 : (BitVec.ofInt 64 (l : Int)).toInt = l := by
    rw [BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> omega
  have h2 : (BitVec.ofInt 64 ((32767 : Nat) : Int)).toInt = 32767 := by
    rw [BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> decide
  rw [h1, h2]
  congr 1
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

/-- The machine `MASH` is HexGraphIso's `mash`, whatever the code. -/
theorem mash_eq' {l i : Nat} (hi : i < 2147483648) :
    Lib.Integers.Int64.and (Lib.Integers.Int64.add (Lib.Integers.Int64.xor (lr l) (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir 27421))))
      (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir (i : Int)))))
      (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir 32767))) =
      lr (Hex.GraphIso.Nauty.mash l i : Nat) := by
  apply bv64_inj.1
  have h1 : intOfZ (Lib.Integers.Int.signed (ir 27421)) = ((27421 : Nat) : Int) := Refine.signed_ir (by decide)
  have h2 : intOfZ (Lib.Integers.Int.signed (ir 32767)) = ((32767 : Nat) : Int) := Refine.signed_ir (by decide)
  simp only [bv64_and, bv64_add, bv64_xor, bv64_repr, intOfZ_zOfInt, h1, h2, Refine.signed_ir hi,
    BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_ofNat,
    Hex.GraphIso.Nauty.mash]
  have hb : ((l ^^^ 27421) + i) &&& 32767 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (show 27421 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (32767 : Nat) < 2 ^ 64 by decide)]
  rw [show (32767 : Nat) = 2 ^ 15 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 15 ∣ 2 ^ 64), Nat.add_mod, Nat.xor_mod_two_pow,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 15 ∣ 2 ^ 64), ← Nat.xor_mod_two_pow, ← Nat.add_mod]

/-- `longcode = MASH(longcode, a)`, whatever the code. -/
theorem wp_mashAny {f : function} {Q : Post} {le : temp_env} {m : mem} {a : expr}
    {l i : Nat} (hl : PTree.get id.longcode le = some (.Vlong (lr l)))
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir i))) (hty : typeof a = tint)
    (hi : i < 2147483648)
    (hQ : Q.normal E0 empty_env (PTree.set id.longcode
      (.Vlong (lr (Hex.GraphIso.Nauty.mash l i : Nat))) le) m) :
    Wp xi sge f (mash a) Q empty_env le m := by
  apply wp_set_eval
  simp only [Exec.evalExpr, ha, hty]
  simp only [hl, typeof, cop]
  rw [mash_eq' hi]
  exact hQ

/-- `*code = CLEANUP(longcode)`. -/
theorem wp_code {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (hcode : PTree.get id.«code» le = some (.Vptr L.bk L.kofs)) {l : Nat}
    (hl : PTree.get id.longcode le = some (.Vlong (lr l))) (hl2 : l < 2 ^ 62)
    (hQ : ∀ m', Mem m' L G t S →
      ArrayAt m' .Mint32 L.bk L.kb (fun _ => .Vint (ir (Hex.GraphIso.Nauty.cleanup l : Nat))) 1 →
      Unch m m' (· = L.bk) → Alloc.KeepA m m' →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (.Ederef (pi id.«code») tint)
      (.Ecast (.Ebinop .Omod (.Etempvar id.«longcode» tlong) (ci 32767 tint) tlong) tint))
      Q empty_env le m := by
  obtain ⟨kv, hk⟩ := hm.code
  have hcl : Hex.GraphIso.Nauty.cleanup l = l % 32767 := rfl
  obtain ⟨m', hst, harr', -⟩ := store_array hk (show 0 < 1 by decide)
    (.Vint (ir (Hex.GraphIso.Nauty.cleanup l : Nat))) rfl
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hcode, hl, typeof, cop, Exec.assignLoc,
    Cfrontend.Ctypes.access_mode, Mem.storev]
  rw [mods_32767' hl2, Refine.repr_unsigned_lr (by omega), ← hcl]
  rw [show Ptrofs.unsigned L.kofs = elemOfs .Mint32 L.kb 0 by
    unfold elemOfs
    rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, Loc.kb, zOfInt_intOfZ],
    hst]
  have harr : ArrayAt m' .Mint32 L.bk L.kb (fun _ => .Vint (ir (Hex.GraphIso.Nauty.cleanup l : Nat))) 1 :=
    harr'.congr fun i hi => by simp [upd, show i = 0 by omega]
  exact hQ m' (hm.setCode hok (Unch.store hst rfl) _ harr) harr (Unch.store hst rfl)
    (Alloc.KeepA.storeArr hk hst) (fun z h => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ h)

/-- `longcode = MASH(longcode, *numcells); *code = CLEANUP(longcode);` -/
theorem wp_finish {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    (ht : Tmp le L t) (hnc : t.numcells < 2147483648)
    (hQ : ∀ m', Mem m' L G t S →
      ArrayAt m' .Mint32 L.bk L.kb (fun _ => .Vint (ir (Hex.GraphIso.Nauty.cleanup
        (Hex.GraphIso.Nauty.mash t.longcode t.numcells) : Nat))) 1 →
      Unch m m' (· = L.bk) → Alloc.KeepA m m' → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 empty_env (PTree.set id.longcode
        (.Vlong (lr (Hex.GraphIso.Nauty.mash t.longcode t.numcells : Nat))) le) m') :
    Wp xi sge F finish Q empty_env le m := by
  have hml := Refine.mash_lt t.longcode t.numcells
  wp_step; wp_step; wp_step
  refine wp_mashAny ht.longcode (eval_nc hm ht) rfl hnc ?_
  simp only [E0_append]
  wp_step; wp_step
  exact wp_code hok hm (by rw [temps_gso _ _ (by decide)]; exact ht.code) (temps_gss _ _ _)
    (by omega) hQ

end NautyVerified.Proofs.Sparse.Refine
