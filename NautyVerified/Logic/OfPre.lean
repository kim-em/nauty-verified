import NautyVerified.Logic.Call

/-! # Satisfying a specification through another one -/

namespace NautyVerified.Logic

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Flocq.IEEE754.Binary (BinaryNormalizeCertificate)

variable [binary64_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable {xi : ExternalCalls} {ge : genv}


/-- `fd` satisfies `S'` if each call meeting `S'.pre` meets the precondition of
a specification `fd` satisfies whose postcondition gives `S'.post`. -/
theorem Satisfies.of_pre {xi : ExternalCalls} {ge : genv} {fd : fundef}
    {S' : FunSpec}
    (h : ∀ args m, S'.pre args m → ∃ S : FunSpec, Satisfies xi ge fd S ∧ S.pre args m ∧
      ∀ t v m', S.post args m t v m' → S'.post args m t v m') :
    Satisfies xi ge fd S' := by
  intro args m hp k hk
  obtain ⟨S, hS, hpre, hpost⟩ := h args m hp
  obtain ⟨t, v, m', hs, hq⟩ := hS args m hpre k hk
  exact ⟨t, v, m', hs, hpost _ _ _ hq⟩

end NautyVerified.Logic
