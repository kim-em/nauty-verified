import NautyVerified.Build.Compile

/-! `nvCompile OUT_DIR`: write `asm.json` and `names.json` for the linked dense program. -/

open Lean NautyVerified NautyVerified.Build

def main (args : List String) : IO UInt32 := do
  let [dir] := args | IO.eprintln "usage: nvCompile OUT_DIR"; return 2
  IO.FS.createDirAll dir
  match compileJson Source.dense.fresh Source.dense.program with
  | .error e => IO.eprintln e; return 1
  | .ok asm =>
    IO.FS.writeFile (System.FilePath.mk dir / "asm.json") asm.compress
    let names := Source.dense.keys.mapIdx fun i k =>
      Json.arr #[.str (toString (i + 1)), .str (asmName k)]
    IO.FS.writeFile (System.FilePath.mk dir / "names.json") (Json.arr names.toArray).compress
    return 0
