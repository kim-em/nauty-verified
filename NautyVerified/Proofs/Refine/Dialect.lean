import NautyVerified.Proofs.Alloc.KeepV
import NautyVerified.Proofs.Refine.State
import NautyVerified.Proofs.Set.One

/-!
# The two dialects of `refine`

naugraph.c has two copies of the refinement procedure: `refine`, for any
number `m` of words per set, and `refine1`, the same algorithm for `m = 1`
written with the one-word set macros (`ISELEMENT1`, `ADDELEMENT1`,
`DELELEMENT1`, no `>> 6` or `& 63`) and with the literal `1` for `m`. A
`Dialect` names the pieces in which they differ: the membership test `isE s a`
on a set held in a temporary `s`, `ADDELEMENT` (`addE`) and `DELELEMENT`
(`delE`), the expression `mE` the code uses for `m`, and the numbers of words
it is written for (`okM`). `Dialect.Sem` states what each piece does, against
the same words-level description (`SetwordsMem`, `addW`, `delW`), so proofs
written against a dialect apply to both functions. `D0` is `refine`'s dialect,
`D1` is `refine1`'s.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs
open NautyVerified.Proofs.Set (longs BitTable addW delW)

/-- The pieces of the refinement code that differ between `refine` and `refine1`. -/
structure Dialect where
  /-- `ISELEMENT(s, a)` for a set held in the temporary `s`. -/
  isE : Common.AST.ident → expr → expr
  /-- `ADDELEMENT(s, a)`. -/
  addE : Common.AST.ident → expr → statement
  /-- `DELELEMENT(s, a)`. -/
  delE : Common.AST.ident → expr → statement
  /-- The expression standing for `m`. -/
  mE : expr
  /-- The numbers of words per set the code is written for. -/
  okM : Nat → Prop

/-- What a dialect's pieces do, on `M` words with `D.okM M`. -/
structure Dialect.Sem (D : Dialect) : Prop where
  isTy : ∀ s a, typeof (D.isE s a) = tint
  isE : ∀ {e : env} {le : temp_env} {m : mem} {s : Common.AST.ident} {a : expr} {ba : block}
    {ofs : ptrofs} {ws : Nat → Lib.Integers.int64} {M c : Nat}, D.okM M → M < 33554432 →
    ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M →
    PTree.get s le = some (.Vptr ba ofs) →
    Exec.evalExpr ge e le m a = some (.Vint (ir c)) → typeof a = tint → c < 64 * M →
    BitTable m Block.naugraphBit → PTree.get dense.id.«naugraph:bit» e = none →
    Exec.evalExpr ge e le m (D.isE s a) = some (Val.of_bool (SetwordsMem (fun w => bv64 (ws w)) c))
  addE : ∀ {xi : ExternalCalls} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {s : Common.AST.ident} {a : expr} {ba : block} {ofs : ptrofs} {ws : Nat → Lib.Integers.int64}
    {M c : Nat}, D.okM M → M < 33554432 →
    ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M →
    PTree.get s le = some (.Vptr ba ofs) →
    Exec.evalExpr ge e le m a = some (.Vint (ir c)) → typeof a = tint → c < 64 * M →
    BitTable m Block.naugraphBit → PTree.get dense.id.«naugraph:bit» e = none →
    (∀ m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs (addW ws c)) M →
      Unch m m' (· = ba) → Alloc.KeepA m m' → Q.normal E0 e le m') →
    Wp xi ge f (D.addE s a) Q e le m
  delE : ∀ {xi : ExternalCalls} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {s : Common.AST.ident} {a : expr} {ba : block} {ofs : ptrofs} {ws : Nat → Lib.Integers.int64}
    {M c : Nat}, D.okM M → M < 33554432 →
    ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M →
    PTree.get s le = some (.Vptr ba ofs) →
    Exec.evalExpr ge e le m a = some (.Vint (ir c)) → typeof a = tint → c < 64 * M →
    BitTable m Block.naugraphBit → PTree.get dense.id.«naugraph:bit» e = none →
    (∀ m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs (delW ws c)) M →
      Unch m m' (· = ba) → Alloc.KeepA m m' → Q.normal E0 e le m') →
    Wp xi ge f (D.delE s a) Q e le m
  mE : ∀ {e : env} {le : temp_env} {m : mem} {M : Nat}, D.okM M →
    PTree.get dense.id.m le = some (.Vint (ir M)) →
    Exec.evalExpr ge e le m D.mE = some (.Vint (ir M)) ∧ typeof D.mE = tint

/-- `refine`'s dialect. -/
abbrev D0 : Dialect where
  isE s a := Set.isElement s dense.id.«naugraph:bit» a
  addE s a := Set.addElementB s dense.id.«naugraph:bit» a
  delE s a := Set.delElementB s dense.id.«naugraph:bit» a
  mE := tv dense.id.m
  okM _ := True

/-- `refine1`'s dialect. -/
abbrev D1 : Dialect where
  isE s a := Set.isElement1 s dense.id.«naugraph:bit» a
  addE s a := Set.addElement1 s dense.id.«naugraph:bit» a
  delE s a := Set.delElement1 s dense.id.«naugraph:bit» a
  mE := ci 1 tint
  okM M := M = 1

theorem D0_sem : D0.Sem where
  isTy _ _ := rfl
  isE := fun _ hM harr hs ha hty hc hbit he =>
    Set.eval_isElement harr (by omega) hs ha hty hc (by omega) hbit he find_naugraphBit
  addE := fun _ hM harr hs ha hty hc hbit he hQ =>
    Set.wp_addElementB harr (by omega) hs ha hty hc (by omega) find_naugraphBit hbit he
      fun m' h1 h2 h3 => hQ m' h1 h2 (Alloc.KeepA.of_outside h2 h3 harr.base_nonneg)
  delE := fun _ hM harr hs ha hty hc hbit he hQ =>
    Set.wp_delElementB harr (by omega) hs ha hty hc (by omega) find_naugraphBit hbit he
      fun m' h1 h2 h3 => hQ m' h1 h2 (Alloc.KeepA.of_outside h2 h3 harr.base_nonneg)
  mE := fun _ hm => ⟨hm, rfl⟩

theorem D1_sem : D1.Sem where
  isTy _ _ := rfl
  isE := fun hM _ harr hs ha hty hc hbit he => by
    obtain rfl : _ = 1 := hM
    exact Set.eval_isElement1 harr hs ha hty (by omega) hbit he find_naugraphBit
  addE := fun hM _ harr hs ha hty hc hbit he hQ => by
    obtain rfl : _ = 1 := hM
    exact Set.wp_addElement1 harr hs ha hty (by omega) find_naugraphBit hbit he
      fun m' h1 h2 h3 => hQ m' h1 h2 (Alloc.KeepA.of_outside h2 h3 harr.base_nonneg)
  delE := fun hM _ harr hs ha hty hc hbit he hQ => by
    obtain rfl : _ = 1 := hM
    exact Set.wp_delElement1 harr hs ha hty (by omega) find_naugraphBit hbit he
      fun m' h1 h2 h3 => hQ m' h1 h2 (Alloc.KeepA.of_outside h2 h3 harr.base_nonneg)
  mE := fun hM _ => by obtain rfl : _ = 1 := hM; exact ⟨rfl, rfl⟩

end NautyVerified.Proofs.Refine
