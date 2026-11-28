import NautyVerified.Program.Env
import NautyVerified.Logic.Wp
import NautyVerified.Logic.Simp
import NautyVerified.Exec.Cop
import NautyVerified.Proofs.Nextelement.Syntax
import NautyVerified.Proofs.Nextelement.Leftbit

/-!
# The `FIRSTBITNZ` decision tree

`wp_leaf`: a leaf `r = c + leftbit[idx]` sets `r` (three times, as SimplExpr's
casts do) to `c + lbv idx`.
-/

namespace NautyVerified.Proofs.Nextelement

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word

variable {xi : ExternalCalls}

theorem wp_leaf {f : function} {Q : Post} {e : env} {le : temp_env} {m} (r : Common.AST.ident) (c : Int)
    (idx : expr) (y : Lib.Integers.int64)
    (hidx : Exec.evalExpr ge e le m idx = some (.Vlong y)) (hty : typeof idx = tulong)
    (hy : (bv64 y).toNat < 256) (he : PTree.get id.leftbit e = none) (hlb : LeftbitTable m)
    (hQ : let v := Vint (Lib.Integers.Int.add (Lib.Integers.Int.repr (zOfInt c))
        (Lib.Integers.Int.repr (zOfInt (lbv (bv64 y).toNat))))
      Q.normal E0 e (PTree.set r v (PTree.set r v (PTree.set r v le))) m) :
    Wp xi ge f (leaf r c idx) Q e le m := by
  simp only [leaf]
  repeat wp_step
  simp only [hidx, hty]
  simp (config := {decide := true}) [he, typeof, Exec.lvalOfVar, Exec.derefLoc,
    E.find_leftbit, Cfrontend.Ctypes.access_mode, load_leftbit hlb _ y hy]
  repeat wp_step
  simp (config := {decide := true}) [typeof]
  repeat wp_step
  simp (config := {decide := true}) [typeof]
  exact hQ

/-- The leaf's value is the leading-bit index. -/
theorem leaf_value (x : BitVec 64) (s c : Nat) (hc : c + s = 56) (h1 : 2 ^ s ≤ x.toNat)
    (h2 : x.toNat < 2 ^ (s + 8)) (y : Lib.Integers.int64) (hy : (bv64 y).toNat = x.toNat / 2 ^ s) :
    LeadBit x (c + lbv (bv64 y).toNat) ∧
      Lib.Integers.Int.add (Lib.Integers.Int.repr (zOfInt c))
        (Lib.Integers.Int.repr (zOfInt (lbv (bv64 y).toNat))) =
      Lib.Integers.Int.repr (zOfInt ((c + lbv (bv64 y).toNat : Nat) : Int)) := by
  refine ⟨hy ▸ leaf_lead x s c hc h1 h2, ?_⟩
  rw [Int_add_repr]
  congr 1
  apply intOfZ_injective
  simp [intOfZ_zOfInt]

/-- The shift amount `(long)(unsigned)s` of `setwd >> s`. -/
theorem shift_amount (s : Int) (h0 : 0 ≤ s) (hs : s < 64) :
    (bv64 (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned
      (Lib.Integers.Int.repr (zOfInt s))))).toNat = s.toNat := by
  simp only [bv64_repr, intOfZ_Int_unsigned, bv32_repr, intOfZ_zOfInt, BitVec.toNat_ofInt]
  omega

/-- `setwd >> s` as a number. -/
theorem shr_toNat (x : Lib.Integers.int64) (s : Int) (h0 : 0 ≤ s) (hs : s < 64) :
    (bv64 (Lib.Integers.Int64.shru x (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned
      (Lib.Integers.Int.repr (zOfInt s)))))).toNat = (bv64 x).toNat / 2 ^ s.toNat := by
  rw [bv64_shru, BitVec.toNat_ushiftRight, shift_amount s h0 hs, Nat.shiftRight_eq_div_pow]

/-- `(setwd >> 56) & 0xFF` as a number. -/
theorem shr56_toNat (x : Lib.Integers.int64) :
    (bv64 (Lib.Integers.Int64.and (Lib.Integers.Int64.shru x (Lib.Integers.Int64.repr
      (Lib.Integers.Int.unsigned (Lib.Integers.Int.repr (zOfInt 56)))))
      (Lib.Integers.Int64.repr (zOfInt 255)))).toNat = (bv64 x).toNat / 2 ^ 56 := by
  rw [bv64_and, BitVec.toNat_and, shr_toNat x 56 (by decide) (by decide)]
  simp only [bv64_repr, intOfZ_zOfInt, BitVec.toNat_ofInt]
  have hx := (bv64 x).isLt
  have h : (bv64 x).toNat / 2 ^ 56 < 2 ^ 8 := by omega
  rw [show (((255 : Int) % ((2 ^ 64 : Nat) : Int)).toNat) = 2 ^ 8 - 1 by decide,
    show (56 : Int).toNat = 56 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

/-- `FIRSTBITNZ(w)` sets `r` to the index of the first (most significant)
set bit of a nonzero word `w`. -/
theorem wp_fbTree {f : function} {w : Common.AST.ident} {Q : Post} {e : env} {le : temp_env} {m}
    (r : Common.AST.ident)
    (x : Lib.Integers.int64) (hsw : PTree.get w le = some (.Vlong x)) (hx : bv64 x ≠ 0)
    (he : PTree.get id.leftbit e = none) (hlb : LeftbitTable m)
    (hQ : ∀ k : Nat, LeadBit (bv64 x) k →
      let v := Vint (Lib.Integers.Int.repr (zOfInt (k : Int)))
      Q.normal E0 e (PTree.set r v (PTree.set r v (PTree.set r v le))) m) :
    Wp xi ge f (fbTree r w) Q e le m := by
  have hxn : (bv64 x).toNat < 2 ^ 64 := (bv64 x).isLt
  have hx0 : 1 ≤ (bv64 x).toNat := by
    rcases Nat.eq_zero_or_pos (bv64 x).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hx
    · exact h
  -- one leaf: `c + leftbit[x >> s]` with `2^s ≤ x < 2^(s+8)`
  have leafOk : ∀ (c s : Nat) (idx : expr) (y : Lib.Integers.int64), c + s = 56 →
      Exec.evalExpr ge e le m idx = some (.Vlong y) → typeof idx = tulong →
      (bv64 y).toNat = (bv64 x).toNat / 2 ^ s →
      2 ^ s ≤ (bv64 x).toNat → (bv64 x).toNat < 2 ^ (s + 8) →
      Wp xi ge f (leaf r (c : Int) idx) Q e le m := by
    intro c s idx y hc hidx hty hy h1 h2
    have hy256 : (bv64 y).toNat < 256 := by
      rw [hy]
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
        (by rw [show 256 * 2 ^ s = 2 ^ (s + 8) by rw [Nat.pow_add]; omega]; exact h2)
    refine wp_leaf r c idx y hidx hty hy256 he hlb ?_
    obtain ⟨hlead, hval⟩ := leaf_value (bv64 x) s c hc h1 h2 y hy
    simp only
    rw [show ((c : Int)) = ((c : Nat) : Int) from rfl, hval]
    exact hQ _ hlead
  simp only [fbTree, sif]
  wp_step; wp_step; wp_step
  simp [hsw, typeof, intOfZ_zOfInt]
  by_cases h32 : bv64 x &&& BitVec.ofInt 64 18446744069414584320 = 0
  · have b32 := (tst_iff _ _ 32 64 k32 hxn).1 h32
    rw [ite_eq_left (by simpa using h32)]
    wp_step; wp_step; wp_step
    simp [hsw, typeof, intOfZ_zOfInt]
    by_cases h16 : bv64 x &&& BitVec.ofInt 64 4294901760 = 0
    · have b16 := (tst_iff _ _ 16 32 k16 b32).1 h16
      rw [ite_eq_left (by simpa using h16)]
      wp_step; wp_step; wp_step
      simp [hsw, typeof, intOfZ_zOfInt]
      by_cases h8 : bv64 x &&& BitVec.ofInt 64 65280 = 0
      · have b8 := (tst_iff _ _ 8 16 k8 b16).1 h8
        rw [ite_eq_left (by simpa using h8)]
        refine leafOk 56 0 (sw w) x rfl ?_ rfl (by simp) (by simp; omega) (by simp; omega)
        simp [Exec.evalExpr, hsw, typeof]
      · have b8 : ¬ (bv64 x).toNat < 2 ^ 8 := fun h => h8 ((tst_iff _ _ 8 16 k8 b16).2 h)
        rw [ite_eq_right (by simpa using h8)]
        refine leafOk 48 8 (shr 8 w) (Lib.Integers.Int64.shru x (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned (Lib.Integers.Int.repr (zOfInt 8))))) rfl ?_ rfl (shr_toNat x 8 (by decide) (by decide)) (by simp; omega) (by simp; omega)
        simp (config := {decide := true}) [Exec.evalExpr, hsw, typeof]
    · have b16 : ¬ (bv64 x).toNat < 2 ^ 16 := fun h => h16 ((tst_iff _ _ 16 32 k16 b32).2 h)
      rw [ite_eq_right (by simpa using h16)]
      wp_step; wp_step; wp_step
      simp [hsw, typeof, intOfZ_zOfInt]
      by_cases h24 : bv64 x &&& BitVec.ofInt 64 4278190080 = 0
      · have b24 := (tst_iff _ _ 24 32 k24 b32).1 h24
        rw [ite_eq_left (by simpa using h24)]
        refine leafOk 40 16 (shr 16 w) (Lib.Integers.Int64.shru x (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned (Lib.Integers.Int.repr (zOfInt 16))))) rfl ?_ rfl (shr_toNat x 16 (by decide) (by decide)) (by simp; omega) (by simp; omega)
        simp (config := {decide := true}) [Exec.evalExpr, hsw, typeof]
      · have b24 : ¬ (bv64 x).toNat < 2 ^ 24 := fun h => h24 ((tst_iff _ _ 24 32 k24 b32).2 h)
        rw [ite_eq_right (by simpa using h24)]
        refine leafOk 32 24 (shr 24 w) (Lib.Integers.Int64.shru x (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned (Lib.Integers.Int.repr (zOfInt 24))))) rfl ?_ rfl (shr_toNat x 24 (by decide) (by decide)) (by simp; omega) (by simp; omega)
        simp (config := {decide := true}) [Exec.evalExpr, hsw, typeof]
  · have b32 : ¬ (bv64 x).toNat < 2 ^ 32 := fun h => h32 ((tst_iff _ _ 32 64 k32 hxn).2 h)
    rw [ite_eq_right (by simpa using h32)]
    wp_step; wp_step; wp_step
    simp [hsw, typeof, intOfZ_zOfInt]
    by_cases h48 : bv64 x &&& BitVec.ofInt 64 18446462598732840960 = 0
    · have b48 := (tst_iff _ _ 48 64 k48 hxn).1 h48
      rw [ite_eq_left (by simpa using h48)]
      wp_step; wp_step; wp_step
      simp [hsw, typeof, intOfZ_zOfInt]
      by_cases h40 : bv64 x &&& BitVec.ofInt 64 280375465082880 = 0
      · have b40 := (tst_iff _ _ 40 48 k40 b48).1 h40
        rw [ite_eq_left (by simpa using h40)]
        refine leafOk 24 32 (shr 32 w) (Lib.Integers.Int64.shru x (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned (Lib.Integers.Int.repr (zOfInt 32))))) rfl ?_ rfl (shr_toNat x 32 (by decide) (by decide)) (by simp; omega) (by simp; omega)
        simp (config := {decide := true}) [Exec.evalExpr, hsw, typeof]
      · have b40 : ¬ (bv64 x).toNat < 2 ^ 40 := fun h => h40 ((tst_iff _ _ 40 48 k40 b48).2 h)
        rw [ite_eq_right (by simpa using h40)]
        refine leafOk 16 40 (shr 40 w) (Lib.Integers.Int64.shru x (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned (Lib.Integers.Int.repr (zOfInt 40))))) rfl ?_ rfl (shr_toNat x 40 (by decide) (by decide)) (by simp; omega) (by simp; omega)
        simp (config := {decide := true}) [Exec.evalExpr, hsw, typeof]
    · have b48 : ¬ (bv64 x).toNat < 2 ^ 48 := fun h => h48 ((tst_iff _ _ 48 64 k48 hxn).2 h)
      rw [ite_eq_right (by simpa using h48)]
      wp_step; wp_step; wp_step
      simp [hsw, typeof, intOfZ_zOfInt]
      by_cases h56 : bv64 x &&& BitVec.ofInt 64 18374686479671623680 = 0
      · have b56 := (tst_iff _ _ 56 64 k56 hxn).1 h56
        rw [ite_eq_left (by simpa using h56)]
        refine leafOk 8 48 (shr 48 w) (Lib.Integers.Int64.shru x (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned (Lib.Integers.Int.repr (zOfInt 48))))) rfl ?_ rfl (shr_toNat x 48 (by decide) (by decide)) (by simp; omega) (by simp; omega)
        simp (config := {decide := true}) [Exec.evalExpr, hsw, typeof]
      · have b56 : ¬ (bv64 x).toNat < 2 ^ 56 := fun h => h56 ((tst_iff _ _ 56 64 k56 hxn).2 h)
        rw [ite_eq_right (by simpa using h56)]
        refine leafOk 0 56 (.Ebinop .Oand (shr 56 w) (cl 255 tulong) tulong)
          (Lib.Integers.Int64.and (Lib.Integers.Int64.shru x (Lib.Integers.Int64.repr (Lib.Integers.Int.unsigned (Lib.Integers.Int.repr (zOfInt 56))))) (Lib.Integers.Int64.repr (zOfInt 255)))
          rfl ?_ rfl (shr56_toNat x) (by simp; omega) (by simp; omega)
        simp (config := {decide := true}) [Exec.evalExpr, hsw, typeof]

end NautyVerified.Proofs.Nextelement
