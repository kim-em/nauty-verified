import NautyVerified.Proofs.Sparse.Refine.Nontrivial.Clear

/-!
# `vmark1` in `refine_sg`

`eval_mark1`: `vmark1[a]` reads the first mark array; `eval_stamp1`:
`vmark1_val`; `wp_storeMark1`: `vmark1[a] = vmark1_val` (`MARK1`) sets entry
`a` to the stamp, as a `Frame` step.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Nontrivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Alloc (Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem eval_mark1 {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    {a : expr} {c : Nat} (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c)))
    (hty : typeof a = tint) (hc : c < n) :
    Exec.evalExpr sge empty_env le m (mk id.«nausparse:vmark1» a) = some (.Vint (ir (S.mk1 c))) := by
  have h0 : 0 < L.mc1 := by have := hok.mc1; omega
  exact eval_idx hm.k1.arr hm.k1.dyn.capLt (eval_vmark1 (hm.k1.dyn.ptr h0)) rfl rfl rfl a c
    (by have := hok.mc1; omega) ha hty

theorem eval_stamp1 {le : temp_env} {m : mem} (hm : Mem m L G t S) :
    Exec.evalExpr sge empty_env le m (.Evar id.«nausparse:vmark1_val» tshort) =
      some (.Vint (ir S.st1)) :=
  eval_val hm.k1.valLd

/-- `MARK1(a)`. -/
theorem wp_storeMark1 {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < n)
    (hQ : ∀ m', Mem m' L G t { S with mk1 := fun x => if x = c then (S.st1 : Int) else S.mk1 x } →
      Frame L m m' → Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (mk id.«nausparse:vmark1» a) (.Evar id.«nausparse:vmark1_val» tshort))
      Q empty_env le m := by
  have h0 : 0 < L.mc1 := by have := hok.mc1; omega
  have hM := hm.k1
  have hse := Search.sign_ext16_ir (a := (S.st1 : Int)) (by omega) (by have := hM.val32; omega)
  refine wp_idx_store (chunk := .Mint16signed) (bo := L.mb1) (ofs := Ptrofs.zero) hM.arr
    hM.dyn.capLt (eval_vmark1 (hM.dyn.ptr h0)) rfl rfl rfl a c (by have := hok.mc1; omega) ha hty
    _ tshort rfl (.Vint (ir S.st1)) (.Vint (ir S.st1)) (eval_stamp1 hm)
    (by rw [Search.cast_ss, hse]) (by exact congrArg val.Vint hse) ?_
  intro m' harr hu hk hg
  refine hQ m' (hm.setMk1 hok hu hk _ (harr.congr fun i _ => ?_) (fun i hi => ?_) h0)
    (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))
  · by_cases hic : i = c
    · subst hic; simp [upd, markVals]
    · simp [upd, markVals, hic]
  · by_cases hic : i = c
    · simp only [hic, ite_true]; exact ⟨by omega, Int.le_refl _⟩
    · simp only [hic, ite_false]; exact hM.bounds i hi

end NautyVerified.Proofs.Sparse.Refine.Nontrivial
