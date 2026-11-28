import NautyVerified.Program.Sparse
/-! Prints `key ident dense-block sparse-block` for every key of the sparse link,
the input `gensparse.py` reads (`lake env lean scripts/env/blocks.lean > blocks.txt`). -/
open NautyVerified.Source NautyVerified.Program CompCert4Lean CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Foundation.Numbers
#eval show IO Unit from do
  for (j, s) in sparse.names do
    let p := PArith.BinPos.Pos.of_nat j
    let d := (Genv.find_symbol NautyVerified.Program.ge.genv_genv p).map PArith.BinPos.Pos.to_nat
    let q := (Genv.find_symbol sparseGe.genv_genv p).map PArith.BinPos.Pos.to_nat
    IO.println s!"{s} {j} {d} {q}"
