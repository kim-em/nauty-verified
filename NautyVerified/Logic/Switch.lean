import NautyVerified.Logic.Wp

/-!
# `switch`

`wp_switch`: `switch (a)` with `a` selecting case `z` runs the statements from
that case on, a `break` out of them finishing the switch normally.
-/

namespace NautyVerified.Logic

open CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Cfrontend.Ctypes CompCert4Lean.Cfrontend.Cop CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open CompCert4Lean.Flocq.IEEE754.Binary (BinaryNormalizeCertificate)

variable [binary64_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable {xi : ExternalCalls} {ge : genv}

/-- The postcondition of a switch's cases: `break` finishes the switch. -/
def switchPost (Q : Post) : Post :=
  { normal := Q.normal, brk := Q.normal, cont := Q.cont, ret := Q.ret }

theorem wp_switch {f : function} {a : expr} {sl : labeled_statements} {Q : Post} {e le m}
    {v : val} {z : Z} (hv : Exec.evalExpr ge e le m a = some v)
    (harg : sem_switch_arg v (typeof a) = some z)
    (h : Wp xi ge f (seq_of_labeled_statement (select_switch z sl)) (switchPost Q) e le m) :
    Wp xi ge f (.Sswitch a sl) Q e le m := by
  intro k e' le' m' ⟨he, hle, hm⟩
  subst he hle hm
  have hstep : Step xi ge (.State f (.Sswitch a sl) k e' le' m') E0
      (.State f (seq_of_labeled_statement (select_switch z sl)) (.Kswitch k) e' le' m') :=
    .step_switch _ _ _ _ _ _ _ _ _ (Exec.evalExpr_sound hv) harg
  rcases h (.Kswitch k) e' le' m' ⟨rfl, rfl, rfl⟩ with ⟨t, le₂, m₂, hs, hq⟩ |
      ⟨t, le₂, m₂, hs, hq⟩ | ⟨t, le₂, m₂, hs, hq⟩ | ⟨t, v', m₂, hs, hq⟩
  · refine .inl ⟨t, le₂, m₂, ?_, hq⟩
    have := Steps.silent hstep (hs.trans (Steps.one (.step_skip_break_switch _ _ _ _ _ _ (.inl rfl))))
    simpa using this
  · refine .inl ⟨t, le₂, m₂, ?_, hq⟩
    have := Steps.silent hstep (hs.trans (Steps.one (.step_skip_break_switch _ _ _ _ _ _ (.inr rfl))))
    simpa using this
  · refine .inr (.inr (.inl ⟨t, le₂, m₂, ?_, hq⟩))
    have := Steps.silent hstep (hs.trans (Steps.one (.step_continue_switch _ _ _ _ _)))
    simpa using this
  · exact .inr (.inr (.inr ⟨t, v', m₂, Steps.silent hstep hs, hq⟩))

end NautyVerified.Logic
