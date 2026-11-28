import NautyVerified.Proofs.Sparse.Refine.Trivial.Model
import NautyVerified.Proofs.Sparse.Refine.Ops

/-!
# The marks in `refine_sg`'s singleton splitter

Reads of `vmark1[a]`, `vmark2[a]` and their stamps, the stores `MARK1(a)`
and `MARK2(a)` (`wp_mark1`, `wp_mark2`), with the memory afterwards as
`Mem` with the marks updated.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Trivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem mc1_pos (hok : Ok n L) : 0 < L.mc1 := by have := hok.mc1; have := hok.n0; omega
theorem mc2_pos (hok : Ok n L) : 0 < L.mc2 := by have := hok.mc2; have := hok.n0; omega

/-- `vmark1[a]`. -/
theorem eval_mk1 {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    {a : expr} {c : Nat} (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c)))
    (hty : typeof a = tint) (hc : c < L.mc1) :
    Exec.evalExpr sge empty_env le m (mk id.«nausparse:vmark1» a) = some (.Vint (ir (S.mk1 c))) :=
  eval_idx hm.k1.arr hm.k1.dyn.capLt (eval_vmark1 (hm.k1.dyn.ptr (mc1_pos hok))) rfl rfl rfl a c hc
    ha hty

/-- `vmark2[a]`. -/
theorem eval_mk2 {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    {a : expr} {c : Nat} (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c)))
    (hty : typeof a = tint) (hc : c < L.mc2) :
    Exec.evalExpr sge empty_env le m (mk id.«nausparse:vmark2» a) = some (.Vint (ir (S.mk2 c))) :=
  eval_idx hm.k2.arr hm.k2.dyn.capLt (Marks2.eval_vmark2 (hm.k2.dyn.ptr (mc2_pos hok))) rfl rfl rfl a c
    hc ha hty

theorem eval_val1 {le : temp_env} {m : mem} (hm : Mem m L G t S) :
    Exec.evalExpr sge empty_env le m (.Evar id.«nausparse:vmark1_val» tshort) =
      some (.Vint (ir S.st1)) := eval_val hm.k1.valLd

theorem eval_val2 {le : temp_env} {m : mem} (hm : Mem m L G t S) :
    Exec.evalExpr sge empty_env le m (.Evar id.«nausparse:vmark2_val» tshort) =
      some (.Vint (ir S.st2)) := Marks2.eval_val hm.k2.valLd

/-- `Int.eq` on two marks. -/
theorem eq_marks {a b : Int} (ha : 0 ≤ a) (ha' : a ≤ 32000) (hb : 0 ≤ b) (hb' : b ≤ 32000) :
    Lib.Integers.Int.eq (ir a) (ir b) = decide (a = b) :=
  ir_eq ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

/-- The values a mark array holds after `MARK(c)`. -/
def setMark (mk : Nat → Int) (c : Nat) (st : Nat) : Nat → Int := fun i => if i = c then st else mk i

/-- `MARK1(a)`. -/
theorem wp_mark1 {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < L.mc1)
    (hQ : ∀ m', Mem m' L G t { S with mk1 := setMark S.mk1 c S.st1 } → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (mk id.«nausparse:vmark1» a) (.Evar id.«nausparse:vmark1_val» tshort))
      Q empty_env le m := by
  have hM := hm.k1
  have hse := Search.sign_ext16_ir (a := (S.st1 : Int)) (by omega) (by have := hM.val32; omega)
  refine wp_idx_store (chunk := .Mint16signed) (bo := L.mb1) (ofs := Ptrofs.zero) hM.arr hM.dyn.capLt
    (eval_vmark1 (hM.dyn.ptr (mc1_pos hok))) rfl rfl rfl a c hc ha hty _ tshort rfl
    (.Vint (ir S.st1)) (.Vint (ir S.st1)) (eval_val hM.valLd) (by rw [Search.cast_ss, hse])
    (by exact congrArg val.Vint hse) ?_
  intro m' harr hu hk hg
  refine hQ m' (hm.setMk1 hok hu hk _ (harr.congr fun i _ => ?_) (fun q hq => ?_) (mc1_pos hok))
    (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))
  · simp only [upd, markVals, setMark]; split <;> rfl
  · simp only [setMark]
    split
    · have := hM.val1; exact ⟨by omega, Int.le_refl _⟩
    · exact hM.bounds q hq

/-- `MARK2(a)`. -/
theorem wp_mark2 {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < L.mc2)
    (hQ : ∀ m', Mem m' L G t { S with mk2 := setMark S.mk2 c S.st2 } → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (mk id.«nausparse:vmark2» a) (.Evar id.«nausparse:vmark2_val» tshort))
      Q empty_env le m := by
  have hM := hm.k2
  have hse := Search.sign_ext16_ir (a := (S.st2 : Int)) (by omega) (by have := hM.val32; omega)
  refine wp_idx_store (chunk := .Mint16signed) (bo := L.mb2) (ofs := Ptrofs.zero) hM.arr hM.dyn.capLt
    (Marks2.eval_vmark2 (hM.dyn.ptr (mc2_pos hok))) rfl rfl rfl a c hc ha hty _ tshort rfl
    (.Vint (ir S.st2)) (.Vint (ir S.st2)) (Marks2.eval_val hM.valLd) (by rw [Search.cast_ss, hse])
    (by exact congrArg val.Vint hse) ?_
  intro m' harr hu hk hg
  refine hQ m' (hm.setMk2 hok hu hk _ (harr.congr fun i _ => ?_) (fun q hq => ?_) (mc2_pos hok))
    (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))
  · simp only [upd, markVals, setMark]; split <;> rfl
  · simp only [setMark]
    split
    · have := hM.val1; exact ⟨by omega, Int.le_refl _⟩
    · exact hM.bounds q hq

end NautyVerified.Proofs.Sparse.Refine.Trivial
