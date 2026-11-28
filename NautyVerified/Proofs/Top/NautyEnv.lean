import NautyVerified.Proofs.Top.NautySyntax
import NautyVerified.Proofs.Alloc.Dyn

/-!
# `nauty()`'s local environment

`nauty()` has one addressable local, `int initstatus` (its address is passed
to `dispatch.init`), so its body runs in the environment `nEnv bI` binding
`initstatus` to the block `bI`. Every other identifier is absent from it, so
reading a global looks up the global environment as in `empty_env`.
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Program NautyVerified.Source

/-- `nauty()`'s environment: `initstatus` at the block `bI`. -/
abbrev nEnv (bI : Common.Values.block) : env :=
  PTree.set dense.id.«initstatus» (bI, tint) empty_env

-- `initstatus` names no global.
kernel_rfl find_initstatus : Common.Globalenvs.Genv.find_symbol ge.genv_genv dense.id.«initstatus» = none

theorem noShadow_nEnv {bI : Common.Values.block} : Alloc.NoShadow (nEnv bI) := by
  intro i b hb
  by_cases h : i = dense.id.«initstatus»
  · subst h; rw [find_initstatus] at hb; cases hb
  · exact (PTree.gso _ _ h).trans rfl

end NautyVerified.Proofs.Top
