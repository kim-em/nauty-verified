import NautyVerified.Build.Compile
import NautyVerified.Source.Sparse

/-! `nvCompile [--sparse] OUT_DIR`: write `asm.json` and `names.json` for the
linked dense program, or with `--sparse` for the linked sparse program. -/

open Lean NautyVerified NautyVerified.Build

def main (args : List String) : IO UInt32 := do
  let (sparse, dir) ← match args with
    | [dir] => pure (false, dir)
    | ["--sparse", dir] => pure (true, dir)
    | _ => IO.eprintln "usage: nvCompile [--sparse] OUT_DIR"; return 2
  IO.FS.createDirAll dir
  let (fresh, prog, names) := if sparse then
      (Source.sparse.fresh, Source.sparse.program, Source.sparse.names)
    else (Source.dense.fresh, Source.dense.program, Source.dense.names)
  match compileJson fresh prog with
  | .error e => IO.eprintln e; return 1
  | .ok asm =>
    IO.FS.writeFile (System.FilePath.mk dir / "asm.json") asm.compress
    let names := names.map fun (i, k) => Json.arr #[.str (toString i), .str (asmName k)]
    IO.FS.writeFile (System.FilePath.mk dir / "names.json") (Json.arr names.toArray).compress
    return 0
