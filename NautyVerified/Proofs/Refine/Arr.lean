import NautyVerified.Program.Env
import NautyVerified.Proofs.Alloc.KeepV
import NautyVerified.Proofs.Refine.State

/-!
# `int` arrays with arbitrary contents

`eval_atV` and `wp_storeV`: reading and writing `p[a]` for an `int *`
temporary `p`, for an array whose values are any `vals` (nauty's `count`
work array), as `eval_at`/`wp_store` do for arrays of `ints o`.
-/

namespace NautyVerified.Proofs.Refine

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word

variable {xi : ExternalCalls}

theorem addr_int_at (ofs : ptrofs) {m : mem} {b : block} {vals : Nat → val} {n : Nat}
    (harr : ArrayAt m .Mint32 b (intOfZ (Ptrofs.unsigned ofs)) vals n) {c : Nat} (hc : c < n)
    (hn : n < 2147483648) :
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tint)) (Ptrofs.of_ints (ir c)))) =
      elemOfs .Mint32 (intOfZ (Ptrofs.unsigned ofs)) c := by
  apply addr_elem ofs _ .Mint32 rfl rfl (by omega)
  have hf := harr.fits
  have h4 : csize .Mint32 = 4 := rfl
  rw [h4] at hf ⊢
  omega

theorem eval_atV {e : env} {le : temp_env} {m : mem} {bo : block} {ofs : ptrofs}
    {vals : Nat → val} {n : Nat}
    (harr : ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) vals n)
    (hn : n < 2147483648) (p : Common.AST.ident) (hp : PTree.get p le = some (.Vptr bo ofs))
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge e le m
      (.Ederef (.Ebinop .Oadd (.Etempvar p (tptr tint)) a (tptr tint)) tint) = some (vals c) := by
  simp only [Exec.evalExpr, hp, ha, hty]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  exact load_array harr hc (addr_int_at ofs harr hc hn)

theorem wp_storeV {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bo : block}
    {ofs : ptrofs} {vals : Nat → val} {n : Nat}
    (harr : ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) vals n)
    (hn : n < 2147483648) (p : Common.AST.ident) (hp : PTree.get p le = some (.Vptr bo ofs))
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (rhs : expr) (x : Int) (hrhs : Exec.evalExpr ge e le m rhs = some (.Vint (ir x)))
    (hrty : typeof rhs = tint)
    (hQ : ∀ m', ArrayAt m' .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (upd vals c (.Vint (ir x))) n →
      Unch m m' (· = bo) → Alloc.KeepA m m' → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar p (tptr tint)) a (tptr tint)) tint) rhs)
      Q e le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array harr hc (.Vint (ir x)) rfl
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, ha, hty, hrhs, hrty]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode]
  show match Mem.store .Mint32 m bo (Ptrofs.unsigned _) _ with
    | some m' => Q.normal E0 e le m' | none => False
  rw [addr_int_at ofs harr hc hn, hst]
  exact hQ m' harr' (Unch.store hst rfl) (Alloc.KeepA.storeArr harr hst)

end NautyVerified.Proofs.Refine
