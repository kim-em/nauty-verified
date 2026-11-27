import NautyVerified.Proofs.Refine.Satisfies

/-!
# `refine` as a function pointer

nauty calls refinement through `dispatch.refine` (`refine`, or `refine1` when
`m = 1`), and `doref` receives it as `refproc`. `RefineFn xi M vf`: `vf` points
to a function of `refine`'s type satisfying `refineSpec` on every `Loc` with
`M` words per set.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Cfrontend.Ctypes CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Source
open Hex.GraphIso.Nauty

namespace Block
def refine : Common.Values.block := PArith.BinPos.Pos.of_nat 290
def refine1 : Common.Values.block := PArith.BinPos.Pos.of_nat 38
end Block

kernel_rfl find_refine : Genv.find_symbol ge.genv_genv dense.id.refine = some Block.refine
kernel_rfl find_refine1 : Genv.find_symbol ge.genv_genv dense.id.refine1 = some Block.refine1
kernel_rfl funct_refine :
  Genv.find_funct_ptr ge.genv_genv Block.refine = some (.Internal dense.fn.refine)
kernel_rfl funct_refine1 :
  Genv.find_funct_ptr ge.genv_genv Block.refine1 = some (.Internal dense.fn.refine1)

/-- The C type of a refinement procedure. -/
abbrev refprocType : type :=
  tfun [tptr tulong, tptr tint, tptr tint, tint, tptr tint, tptr tint, tptr tulong, tptr tint, tint,
    tint] .Tvoid

/-- `vf` points to a refinement procedure satisfying `refineSpec` for `M` words per set. -/
def RefineFn (xi : ExternalCalls) (M : Nat) (vf : val) : Prop :=
  ∃ fd, Genv.find_funct ge.genv_genv vf = some fd ∧ type_of_fundef fd = refprocType ∧
    ∀ {n : Nat} (L : Loc), L.M = M → ∀ (ctx : Ctx n) (lab ptn : Array Nat) (active : VSet n)
      (numcells : Nat) (aw : Nat → Lib.Integers.int64),
      Satisfies xi ge fd (refineSpec L ctx lab ptn active numcells aw)

theorem refineFn_refine {xi : ExternalCalls} (hT : TrivialPass xi) (hN : NontrivialPass xi)
    (M : Nat) : RefineFn xi M (.Vptr Block.refine Ptrofs.zero) :=
  ⟨_, by simp [Genv.find_funct, funct_refine], rfl,
    fun L _ ctx lab ptn active numcells aw => refine_satisfies_of hT hN L ctx lab ptn active numcells aw⟩

end NautyVerified.Proofs.Refine
