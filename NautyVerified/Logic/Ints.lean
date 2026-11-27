import NautyVerified.Logic.Array
import NautyVerified.Logic.Wp
import NautyVerified.Logic.Simp
import NautyVerified.Exec.Cop
import NautyVerified.Proofs.Syntax

/-!
# Arrays of `int`

An `int` array holding `o : Array Nat` (`ints o`): reading `p[a]` through an
`int *` temporary (`eval_at`), and storing to it (`wp_store`).
-/

namespace NautyVerified.Logic

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Word NautyVerified.Proofs

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable {xi : ExternalCalls} {ge : genv}

/-- The values of an `int` array holding `o`. -/
def ints (o : Array Nat) (i : Nat) : val := .Vint (ir (o[i]! : Int))

/-- Reading `p[e]` for an `int *` temporary `p` and an index `e` holding `c < n`. -/
theorem eval_at {e : env} {le : temp_env} {m : mem} {bo : block} {ofs : ptrofs}
    {o : Array Nat} {n : Nat} (harr : ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (ints o) n)
    (hn : n < 2147483648) (p : Common.AST.ident) (horb : PTree.get p le = some (.Vptr bo ofs))
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge e le m
      (.Ederef (.Ebinop .Oadd (.Etempvar p (tptr tint)) a (tptr tint)) tint) = some (ints o c) := by
  simp only [Exec.evalExpr, horb, ha, hty]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  apply load_array harr hc
  apply addr_elem ofs _ .Mint32 rfl rfl (by omega)
  have hf := harr.fits
  have h4 : csize .Mint32 = 4 := rfl
  rw [h4] at hf ⊢
  omega

omit binary64_certificate binary32_certificate in
theorem ints_set {o : Array Nat} {j : Nat} (hj : j < o.size) (v : Nat) :
    ints (o.set! j v) = upd (ints o) j (.Vint (ir (v : Int))) := by
  funext i
  simp only [ints, upd]
  by_cases h : i = j
  · subst h; rw [ite_eq_left rfl, Array.getElem!_set!_self _ _ _ hj]
  · rw [ite_eq_right h, Array.getElem!_set!_ne _ _ _ _ (Ne.symm h)]

/-- `p[a] = x;` for an `int *` temporary `p` and an index `a` holding `c < n`:
the array gets `x` at `c`, and every other block is unchanged. -/
theorem wp_store {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bo : block}
    {ofs : ptrofs} {o : Array Nat} {n : Nat}
    (harr : ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (ints o) n)
    (hn : n < 2147483648) (p : Common.AST.ident) (hp : PTree.get p le = some (.Vptr bo ofs))
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (rhs : expr) (x : Int) (hrhs : Exec.evalExpr ge e le m rhs = some (.Vint (ir x)))
    (hrty : typeof rhs = tint)
    (hQ : ∀ m', ArrayAt m' .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (upd (ints o) c (.Vint (ir x))) n →
      Unch m m' (· = bo) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar p (tptr tint)) a (tptr tint)) tint) rhs)
      Q e le m := by
  have haddr : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tint)) (Ptrofs.of_ints (ir c)))) =
      elemOfs .Mint32 (intOfZ (Ptrofs.unsigned ofs)) c := by
    apply addr_elem ofs _ .Mint32 rfl rfl (by omega)
    have hf := harr.fits
    have h4 : csize .Mint32 = 4 := rfl
    rw [h4] at hf ⊢
    omega
  obtain ⟨m', hst, harr', hfar⟩ := store_array harr hc (.Vint (ir x)) rfl
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, ha, hty, hrhs, hrty]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode]
  show match Mem.store .Mint32 m bo (Ptrofs.unsigned _) _ with
    | some m' => Q.normal E0 e le m' | none => False
  rw [haddr, hst]
  exact hQ m' harr' (Unch.store hst rfl)

end NautyVerified.Logic
