import NautyVerified.Statement.Harness
import CompCert4Lean.Driver.ClightCompiler

/-!
# From the pinned Clight to the binary

`dense_backward`: every behaviour of the compiled binary is an improvement of
a behaviour of `dense.locals`, the kernel-pinned Clight of the linked
program, under Clight's `semantics2`. This is CompCert4Lean's
`transf_c_program_clight_correct` (Phase 3) instantiated with the driver
configuration of `nvCompile` and the equations `dense.clight_eq` and
`dense.locals_eq`.
-/

namespace NautyVerified.Statement

open CompCert4Lean CompCert4Lean.Common.Smallstep

theorem dense_backward (tp : X86.Asm.program)
    (hc : Build.compile Source.dense.fresh Source.dense.program = .ok tp)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls) :
    backward_simulation (Cfrontend.Clight.semantics2 xi Source.dense.locals)
      (X86.Asm.semantics Build.config xi tp) := by
  have hcomp : Driver.Compiler.transf_c_program Build.config (Prototype.selectionFor Build.config)
      Build.inlining (Allocator.regalloc Build.config .empty) Prototype.enumeration
      (Source.freshContext Source.dense.fresh) Source.dense.program = .OK tp := by
    unfold Build.compile at hc
    split at hc
    · cases hc; assumption
    · cases hc
  have hlocals := Source.dense.locals_eq Build.config.options Build.config.x86_64ABI
    Build.config.relocation
  exact Driver.Compiler.transf_c_program_clight_correct Build.config _ _ _ _ _ xi _ _ _ tp hcomp
    Source.dense.clight_eq hlocals

end NautyVerified.Statement
