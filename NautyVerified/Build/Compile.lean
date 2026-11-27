import NautyVerified.Source.Dense

/-!
# Compiling the linked program

`compileProgram` runs CompCert4Lean's `transf_c_program` on a linked
`Csyntax` program with the driver's O0 configuration, as
`Prototype.compileDecoded` does for one translation unit, and returns the
assembly interchange JSON together with the assembly name of every
identifier, for the bridge's `print_named` operation.
-/

namespace NautyVerified.Build

open Lean CompCert4Lean CompCert4Lean.Prototype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

/-- The configuration the theorem is about: O0, no PIC, no PIE, no common symbols. -/
def config : Config.CompilerConfig := Prototype.cfg

def inlining : Backend.Inlining.InliningConfig :=
  Prototype.inlineCfg

def compile (fresh : positive) (p : Cfrontend.Csyntax.program) :
    Except String X86.Asm.program :=
  match Driver.Compiler.transf_c_program config (selectionFor config) inlining
      (Allocator.regalloc config .empty) enumeration (Source.freshContext fresh) p with
  | .OK target => .ok target
  | .Error errors => .error ("Lean compiler: " ++ errorText errors)

/-- An assembler-safe symbol for a key: `unit:name` becomes `name.unit`. -/
def asmName (key : String) : String :=
  match key.splitOn ":" with
  | [unit, name] => s!"{name}.{unit}"
  | _ => key

def compileJson (fresh : positive) (p : Cfrontend.Csyntax.program) : Except String Json := do
  let target ← compile fresh p
  return Json.mkObj [("format", .str formatVersion), ("target", .str "x86_64-linux-sysv-O0"),
    ("allocator", .str "irc"), ("program", ← enc_AProgram codecFuel target)]

end NautyVerified.Build
