import NautyVerified.Exec.Interp
import NautyVerified.Source.Dense

/-! `nvInterp`: run the pinned Clight of the linked dense program (`dense.locals`)
in the interpreter, reading the harness input from standard input and writing
its output as the native build's `io_stdio.c` does. -/

open NautyVerified NautyVerified.Exec

def main : IO UInt32 := do
  let text ← (← IO.getStdin).readToEnd
  let input := (text.splitOn " " |>.flatMap (·.splitOn "\n")).filterMap (·.trimAscii.toString.toInt?)
  match runProgram Source.dense.locals input 2000000000 with
  | none => IO.eprintln "nvInterp: no initial state"; return 1
  | some (.done code out steps) =>
      for x in out do IO.println x
      IO.eprintln s!"nvInterp: exit {code} after {steps} steps"
      return 0
  | some (.stuck w out steps) =>
      for x in out do IO.println x
      IO.eprintln s!"nvInterp: stuck at {w} after {steps} steps"; return 1
  | some (.outOfFuel _) => IO.eprintln "nvInterp: out of fuel"; return 1
