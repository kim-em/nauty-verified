import CompCert4Lean
import HexGraphIso

/-!
# The two sides of the refinement

nauty's C is reasoned about in CompCert4Lean's Clight semantics; the Lean
implementation it refines is `HexGraphIso`. This module only checks that both
build together on one toolchain; the development starts in later modules.
-/

namespace NautyVerified

/-- The end-to-end theorem's compiler result, from CompCert4Lean. -/
example : Prop := CompCert4Lean.Driver.Compiler.transf_c_program_correctStatement

/-- The search the C is shown to refine, from HexGraphIso. -/
example : ∀ {n k : Nat}, Hex.GraphIso.Colored n k → Hex.GraphIso.Colored n k :=
  fun G => Hex.GraphIso.canon G

end NautyVerified
