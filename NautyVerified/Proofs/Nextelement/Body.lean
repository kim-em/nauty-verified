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

/-- The `m == 1` case of `nextelement`. -/
theorem wp_oneWord {Q : Post} {le : temp_env} {m} {b : block} {ofs : ptrofs} {pos : Int}
    {ws : Nat → Lib.Integers.int64}
    (hset1 : PTree.get id.set1 le = some (.Vptr b ofs))
    (hpos : PTree.get id.pos le = some (.Vint (ir pos))) (hp1 : -1 ≤ pos) (hp2 : pos < 64)
    (hw : WordsAt m b ofs ws 1) (hlb : LeftbitTable m)
    (hQ : ∀ r : Int, NextSpec (fun i => bv64 (ws i)) 1 pos r → Q.ret E0 (.Vint (ir r)) m) :
    Wp xi ge Source.dense.fn.nextelement oneWord Q empty_env le m := by
  simp only [oneWord, sif]
  wp_step; wp_step; wp_step; wp_step
  simp only [hpos, typeof, cop, ir_lt (a := pos) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
  have hw0 : Exec.evalExpr ge empty_env le m (word (ci 0 tint)) = some (.Vlong (ws 0)) :=
    eval_word hset1 hw 0 (by omega) (by decide) _ rfl rfl
  by_cases hneg : pos < 0
  · rw [ite_eq_left (by simpa using hneg)]
    wp_step; wp_step
    apply wp_set_eval
    rw [hw0]
    simp only [seqPost, Post.after, E0_append]
    have hp : pos = -1 := by omega
    subst hp
    exact wp_oneTail (ws 0) (temps_gss _ _ _) good_start_neg hlb (fun r hr => by simpa using hQ r hr)
  · rw [ite_eq_right (by simpa using hneg)]
    obtain ⟨xm, hxm, hbv⟩ := eval_bitmask (Etempvar id.pos tint) pos.toNat (by omega)
      (by rw [show ((pos.toNat : Nat) : Int) = pos by omega]; exact hpos) rfl
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, hw0, hxm]
    simp only [typeof, cop, seqPost, Post.after, E0_append]
    refine wp_oneTail _ (temps_gss _ _ _) ?_ hlb (fun r hr => by simpa using hQ r hr)
    have hg := good_start (ws := fun i => bv64 (ws i)) (n := 1) pos.toNat
    rw [show pos.toNat / 64 = 0 by omega, show pos.toNat % 64 = pos.toNat by omega,
      show ((pos.toNat : Nat) : Int) = pos by omega] at hg
    simpa [bv64_and, hbv] using hg

/-- The invariant of the word scan, with variant `k`. -/
def LoopInv (b : block) (ofs : ptrofs) (n : Nat) (pos : Int) (ws : Nat → Lib.Integers.int64)
    (m₀ : mem) (k : Nat) (t : trace) (e : env) (le : temp_env) (m : mem) : Prop :=
  t = E0 ∧ e = empty_env ∧ m = m₀ ∧
  PTree.get id.set1 le = some (.Vptr b ofs) ∧ PTree.get id.m le = some (.Vint (ir n)) ∧
  ∃ (w : Nat) (x : Lib.Integers.int64), PTree.get id.w le = some (.Vint (ir w)) ∧
    PTree.get id.setwd le = some (.Vlong x) ∧ w < n ∧
    Good (fun i => bv64 (ws i)) n pos w (bv64 x) ∧ k = n - w

/-- One iteration of the scan: return the first member in the current word, or
move to the next word (returning `-1` past the last). -/
theorem wp_loopBody {Q : Post} {b : block} {ofs : ptrofs} {n : Nat} {pos : Int}
    {ws : Nat → Lib.Integers.int64} {m₀ : mem} (hn : 64 * n < 2147483648)
    (hw : WordsAt m₀ b ofs ws n) (hlb : LeftbitTable m₀)
    (hQ : ∀ r : Int, NextSpec (fun i => bv64 (ws i)) n pos r → Q.ret E0 (.Vint (ir r)) m₀)
    (k : Nat) (t : trace) (e : env) (le : temp_env) (m : mem)
    (hI : LoopInv b ofs n pos ws m₀ k t e le m) :
    Wp xi ge Source.dense.fn.nextelement loopBody
      { normal := fun t' e le m => ∃ k' < k, LoopInv b ofs n pos ws m₀ k' (t ++ t') e le m,
        cont := fun t' e le m => ∃ k' < k, LoopInv b ofs n pos ws m₀ k' (t ++ t') e le m,
        brk := fun t' => Q.normal (t ++ t'), ret := fun t' => Q.ret (t ++ t') } e le m := by
  obtain ⟨rfl, rfl, rfl, hset1, hm, w, x, hwv, hsw, hwn, hg, rfl⟩ := hI
  simp only [loopBody, sif]
  repeat wp_step
  simp only [Exec.evalExpr, hsw, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩,
    bv64_eq]
  have hw32 : InInt (w : Int) := ⟨by omega, by omega⟩
  by_cases hx : bv64 x = 0
  · rw [ite_eq_right (by simp [intOfZ_zOfInt, hx])]
    apply wp_skip
    simp only [advance]
    repeat (first | wp_step | (simp (config := {decide := true}) only [Exec.evalExpr, temps_gss,
      temps_gso, hwv, hm, typeof, cop, ir_add, seqPost, Post.after, E0_append,
      ir_eq (a := (w : Int) + 1) (b := n) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]))
    rw [hx] at hg
    by_cases hlast : (w : Int) + 1 = n
    · rw [ite_eq_left (by simpa using hlast)]
      apply wp_retNeg1
      apply hQ
      exact spec_none (fun v hv1 hv2 => good_zero hg v hv1 (by omega))
    · rw [ite_eq_right (by simpa using hlast)]
      apply wp_skip
      simp only [Post.after, E0_append]
      wp_step; wp_step
      apply wp_set_eval
      have hwn' : w + 1 < n := by omega
      rw [eval_word (by simp (config := {decide := true}) only [temps_gso, hset1]) hw (w + 1) hwn'
        (by omega) _ (by simp (config := {decide := true}) only [Exec.evalExpr, temps_gss]; push_cast; rfl) rfl]
      simp only [seqPost, Post.after, E0_append, append_E0]
      refine ⟨n - (w + 1), by omega, rfl, rfl, rfl, ?_, ?_, w + 1, ws (w + 1), ?_, temps_gss _ _ _,
        hwn', good_next hg.1 (good_zero hg), rfl⟩
      · simp (config := {decide := true}) only [temps_gso, hset1]
      · simp (config := {decide := true}) only [temps_gso, hm]
      · simp (config := {decide := true}) only [temps_gso, temps_gss]; push_cast; rfl
  · rw [ite_eq_left (by simp [intOfZ_zOfInt]; exact hx)]
    wp_step
    refine wp_fbTree (idOf 704) x hsw hx leftbit_empty hlb ?_
    intro r hr
    apply wp_return_some_eval
    have h6 : Lib.Integers.Int.ltu (ir 6) Lib.Integers.Int.iwordsize = true := by decide
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, temps_gso, hwv, typeof, cop,
      h6, ite_true,
      ir_shl6 (a := w) (by omega) (by omega), ir_add, Source.dense.fn.nextelement.fn_return_eq,
      free_empty, E0_append]
    have := hQ _ (spec_found hg hwn hr)
    rw [show ((64 * w + r : Nat) : Int) = (w : Int) * 64 + (r : Int) by push_cast; omega] at this
    exact this

end NautyVerified.Proofs.Nextelement
