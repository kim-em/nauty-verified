import NautyVerified.Proofs.Alloc.Dyn
import NautyVerified.Logic.Ints

/-!
# `int` arrays through a static pointer

nauty reaches its `DYNALLSTAT` arrays as `name[e]`, reloading the static
pointer `name` each time. `eval_gat` reads such an element and `wp_gstore`
writes one, for a pointer global (block `bg`) holding `Vptr b 0`.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs

variable {xi : ExternalCalls}

/-- `g[a]` for an `int *` global `g`. -/
abbrev gat (g : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar g (tptr tint)) a (tptr tint)) tint

theorem addr_int (c : Nat) (hc : c < 2147483648) :
    Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.mul
      (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tint)) (Ptrofs.of_ints (ir c)))) =
      elemOfs .Mint32 0 c := by
  apply addr_elem Ptrofs.zero _ .Mint32 rfl (base := 0) rfl (by omega)
  have h4 : csize .Mint32 = 4 := rfl
  rw [h4]; omega

theorem eval_gat {e : env} {le : temp_env} {m : mem} {g : Common.AST.ident} {bg b : block}
    {vals : Nat → val} {n : Nat} (hge : PTree.get g e = none)
    (hg : Genv.find_symbol ge.genv_genv g = some bg)
    (hp : Mem.load .Mint64 m bg (zOfInt 0) = some (.Vptr b Ptrofs.zero))
    (harr : ArrayAt m .Mint32 b 0 vals n) (hn : n < 2147483648)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge e le m (gat g a) = some (vals c) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, hg, ha, hty]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp]
  show Mem.load _ _ _ (Ptrofs.unsigned _) = _
  rw [addr_int c (by omega)]
  exact harr.load c hc

theorem wp_gstore {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {g : Common.AST.ident} {bg b : block} {vals : Nat → val} {n : Nat}
    (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some bg)
    (hp : Mem.load .Mint64 m bg (zOfInt 0) = some (.Vptr b Ptrofs.zero))
    (harr : ArrayAt m .Mint32 b 0 vals n) (hn : n < 2147483648)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (rhs : expr) (x : Int) (hrhs : Exec.evalExpr ge e le m rhs = some (.Vint (ir x)))
    (hrty : typeof rhs = tint)
    (hQ : ∀ m', ArrayAt m' .Mint32 b 0 (upd vals c (.Vint (ir x))) n → Unch m m' (· = b) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (gat g a) rhs) Q e le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array harr hc (.Vint (ir x)) rfl
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hge, hg, ha, hty, hrhs, hrty]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp, Exec.assignLoc, Mem.storev]
  show match Mem.store .Mint32 m b (Ptrofs.unsigned _) _ with
    | some m' => Q.normal E0 e le m' | none => False
  rw [addr_int c (by omega), hst]
  exact hQ m' harr' (Unch.store hst rfl)

end NautyVerified.Proofs.Alloc
