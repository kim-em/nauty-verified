import NautyVerified.Proofs.Sparse.Refine.Satisfies
import NautyVerified.Proofs.Sparse.Refine.Count.Cell
import NautyVerified.Proofs.Sparse.Refine.Trivial.Pass
import NautyVerified.Proofs.Sparse.Refine.Nontrivial.Pass

/-!
# `refine_sg` meets its specification

`refine_sg_satisfies`: `refine_sg_satisfies_of` with the three splitting
passes discharged (`Count.countPass`, `Trivial.trivialPass`,
`Nontrivial.nontrivialPass_of`).
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.ExternalCalls
open NautyVerified.Logic NautyVerified.Source NautyVerified.Proofs.Sparse
open Hex.GraphIso.Nauty (VSet)

attribute [local instance] NautyVerified.Program.NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat}

theorem refine_sg_satisfies (G : Hex.SparseGraph n) (L : Loc) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) :
    Satisfies xi sge (.Internal sparse.fn.refine_sg) (refineSgSpec G L lab ptn active numcells) :=
  refine_sg_satisfies_of Count.countPass Trivial.trivialPass
    (Nontrivial.nontrivialPass_of Count.countPass) G L lab ptn active numcells

end NautyVerified.Proofs.Sparse.Refine
