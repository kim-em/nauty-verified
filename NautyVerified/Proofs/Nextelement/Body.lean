import NautyVerified.Proofs.Nextelement.Tree
import NautyVerified.Proofs.Nextelement.Spec
import NautyVerified.Word.Repr

/-!
# The body of `nextelement`
-/

namespace NautyVerified.Proofs.Nextelement

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word

variable {xi : ExternalCalls}

/-- The words of the set at `b + ofs`. -/
def WordsAt (m : mem) (b : block) (ofs : ptrofs) (ws : Nat → Lib.Integers.int64) (n : Nat) : Prop :=
  ∀ i : Nat, i < n → Mem.load .Mint64 m b
    (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (zOfInt (8 * (i : Int)))))) = some (.Vlong (ws i))

theorem eval_word {e : env} {le : temp_env} {m} {b : block} {ofs : ptrofs}
    {ws : Nat → Lib.Integers.int64} {n : Nat} (hset1 : PTree.get id.set1 le = some (.Vptr b ofs))
    (hw : WordsAt m b ofs ws n) (i : Nat) (hi : i < n) (hn : n < 2147483648) (idx : expr)
    (hidx : Exec.evalExpr ge e le m idx = some (.Vint (ir i))) (hty : typeof idx = tint) :
    Exec.evalExpr ge e le m (word idx) = some (.Vlong (ws i)) := by
  simp only [word, Exec.evalExpr, hset1, hidx, hty]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  rw [ofs_word8 ofs _ rfl ⟨by omega, by omega⟩]
  exact hw i hi

theorem eval_bitmask {e : env} {le : temp_env} {m} (a : expr) (p : Nat) (hp : p < 64)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir p))) (hty : typeof a = tint) :
    ∃ x, Exec.evalExpr ge e le m (bitmask a) = some (.Vlong x) ∧
      bv64 x = BitVec.ofInt 64 9223372036854775807 >>> p := by
  simp only [bitmask, Exec.evalExpr, ha, hty]
  simp only [typeof, cop]
  have hw' : (bv32 Lib.Integers.Int64.iwordsize').toNat = 64 := by decide
  rw [if_pos (by simp only [bv32_ltu, hw', decide_eq_true_eq, toNat_ir (a := p) (by omega) (by omega)]; omega)]
  refine ⟨_, rfl, ?_⟩
  rw [bv64_shru, bv64_repr, intOfZ_zOfInt]
  congr 1
  simp only [bv64_repr, intOfZ_Int_unsigned, toNat_ir (a := p) (by omega) (by omega)]
  simp only [BitVec.toNat_ofInt]
  omega

theorem free_empty (m : mem) : Mem.free_list m (blocks_of_env ge empty_env) = some m := rfl

theorem leftbit_empty : PTree.get id.leftbit empty_env = none := by
  simp [empty_env]

/-- `return -1`. -/
theorem wp_retNeg1 {Q : Post} {le : temp_env} {m} (h : Q.ret E0 (.Vint (ir (-1))) m) :
    Wp xi ge Source.dense.fn.nextelement retNeg1 Q empty_env le m := by
  simp only [retNeg1]
  wp_step; wp_step
  apply wp_return_some_eval
  simp only [Exec.evalExpr, typeof, cop, ir_neg, Source.dense.fn.nextelement.fn_return_eq, free_empty]
  exact h

/-- The tail of the `m == 1` case: with `setwd` holding the bits of the word
above `pos`, return the first of them, or `-1`. -/
theorem wp_oneTail {Q : Post} {le : temp_env} {m} {ws : Nat → BitVec 64} {pos : Int}
    (x : Lib.Integers.int64) (hsw : PTree.get id.setwd le = some (.Vlong x))
    (hg : Good ws 1 pos 0 (bv64 x)) (hlb : LeftbitTable m)
    (hQ : ∀ r : Int, NextSpec ws 1 pos r → Q.ret E0 (.Vint (ir r)) m) :
    Wp xi ge Source.dense.fn.nextelement
      (sif (.Ebinop .Oeq sw (ci 0 tint) tint) retNeg1
        (.Ssequence (fbTree (idOf 703)) (.Sreturn (some (.Etempvar (idOf 703) tint)))))
      Q empty_env le m := by
  simp only [sif]
  wp_step; wp_step; wp_step
  simp only [Exec.evalExpr, hsw, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩,
    bv64_eq]
  by_cases hx : bv64 x = 0
  · rw [ite_eq_left (by simp [intOfZ_zOfInt, hx])]
    apply wp_retNeg1
    apply hQ
    rw [hx] at hg
    exact spec_none (fun v hv1 hv2 => good_zero hg v hv1 (by omega))
  · rw [ite_eq_right (by simp [intOfZ_zOfInt]; exact hx)]
    wp_step
    refine wp_fbTree (idOf 703) x hsw hx leftbit_empty hlb ?_
    intro k hk
    apply wp_return_some_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop, Source.dense.fn.nextelement.fn_return_eq,
      free_empty]
    have := hQ _ (spec_found hg (by omega) hk)
    simpa using this

end NautyVerified.Proofs.Nextelement
