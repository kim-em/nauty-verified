import NautyVerified.Exec.Interp
import NautyVerified.Source.Sparse

/-! `nvInterp [--sparse]`: run the pinned Clight of the linked dense program
(`dense.locals`), or with `--sparse` of the linked sparse program
(`sparse.locals`), in the interpreter, reading the harness input from standard
input and writing its output as the native build's `io_stdio.c` does. -/

open NautyVerified NautyVerified.Exec

def main (args : List String) : IO UInt32 := do
  let prog := if args == ["--sparse"] then Source.sparse.locals else Source.dense.locals
  let text ← (← IO.getStdin).readToEnd
  let input := (text.splitOn " " |>.flatMap (·.splitOn "\n")).filterMap (·.trimAscii.toString.toInt?)
  match runProgram prog input 2000000000 with
  | none => IO.eprintln "nvInterp: no initial state"; return 1
  | some (.done code out steps) =>
      for x in out do IO.println x
      IO.eprintln s!"nvInterp: exit {code} after {steps} steps"
      return 0
  | some (.stuck w out steps) =>
      for x in out do IO.println x
      IO.eprintln s!"nvInterp: stuck at {w} after {steps} steps"; return 1
  | some (.outOfFuel _) => IO.eprintln "nvInterp: out of fuel"; return 1
