import NautyVerified.Statement.Sparse

/-! `nvSparseExpected`: read `sparse_main`'s input stream from standard input
and print `sparseOutput` of HexGraphIso's sparse search on it, the numbers
`expectedSparse G` gives for the graph `G` the stream encodes
(`sparseInput G`). CI compares them with the sparse harness's output. -/

open Hex.GraphIso.Nauty NautyVerified.Statement

def main : IO UInt32 := do
  let text ← (← IO.getStdin).readToEnd
  let xs := (text.splitOn "\n").filterMap (·.trimAscii.toString.toNat?)
  let some n := xs.head? | IO.eprintln "nvSparseExpected: empty input"; return 1
  let colours := (xs.drop 1).take n
  let degrees := (xs.drop (1 + n)).take n
  let nbrs := xs.drop (1 + 2 * n)
  unless colours.length = n ∧ degrees.length = n ∧ nbrs.length = degrees.sum do
    IO.eprintln "nvSparseExpected: malformed input"; return 1
  let some fins := nbrs.mapM (fun v => if h : v < n then some (⟨v, h⟩ : Fin n) else none)
    | IO.eprintln "nvSparseExpected: neighbour out of range"; return 1
  let offsets := degrees.scanl (· + ·) 0
  let g : Sparse.Graph n := ⟨offsets.toArray, fins.toArray⟩
  let k := colours.foldl max 0 + 1
  let (lab, ends) := Sparse.initialPartition n k colours.toArray
  for x in sparseOutput (Sparse.run g lab ends) do IO.println x
  return 0
