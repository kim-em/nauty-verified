import NautyVerified.Statement.Corollaries

/-!
# The end-to-end theorem for dense nauty: bounds, the binary, the output

`maxN` (the vertex bound), `Compiled` (the binary CompCert4Lean compiles from
the linked dense program) and the parts of `expected G` with HexGraphIso's
theorems about them. The end-to-end theorem `densenauty_binary_correct` is
stated in `Statement/Final.lean`, above the proofs about `main` that import
this file.

The corollaries restate HexGraphIso's correctness theorems for what the binary
writes: the canonical graph is a complete isomorphism invariant, the written
generators generate the automorphism group, and the orbits are its orbits.
-/

namespace NautyVerified.Statement

open CompCert4Lean CompCert4Lean.Common.Events CompCert4Lean.Common.Behaviors
open CompCert4Lean.Lib.Integers
open Hex.GraphIso

/-- The largest number of vertices covered. nauty's internal arithmetic is in
`int`; this bound keeps every product it forms (`m * n`, `2 * 500 * m`, the
refinement's hash sums) far from overflow. -/
def maxN : Nat := 65536

/-- The binary compiled from the linked dense program. -/
abbrev Compiled (tp : X86.Asm.program) : Prop :=
  Build.compile Source.dense.fresh Source.dense.program = .ok tp

/-! ## What the output means

The parts of `expected G`, and HexGraphIso's theorems about them. -/

/-- The canonical graph the binary writes (block 4). -/
def canonWords {n k : Nat} (G : Colored n k) : List Int :=
  (Nauty.runColoredTraced G).result.canong.toList.flatMap (rowWords (setwordsNeeded n))

/-- The number of vertices of each colour. -/
def colorCounts {n k : Nat} (G : Colored n k) : List Nat :=
  (List.range k).map fun c => (Nauty.colorClass G c).length

/-- The canonical graph, together with the colour-class sizes, is a complete
invariant: two coloured graphs get the same canonical graph and have the same
number of vertices of each colour exactly when they are isomorphic. (The
canonical graph alone does not see the colouring: three isolated vertices
coloured `0, 0, 1` and `0, 1, 1` have the same canonical graph.) -/
theorem canonWords_eq_iff {n k : Nat} (G H : Colored n k) :
    (canonWords G = canonWords H ∧ colorCounts G = colorCounts H) ↔ Isomorphic G H := by
  have hw : ∀ G : Colored n k,
      canonWords G = (Nauty.rowsOf (canon G)).toList.flatMap (rowWords (setwordsNeeded n)) :=
    fun G => by rw [canonWords, canong_toList]
  rw [colorCounts, colorCounts, counts_eq_iff, hw, hw, iso_iff_canon_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine canon_eq_of ((rowsOf_eq_iff _ _).mp ?_) h2
    exact flatMap_inj (fun _ _ => rowWords_inj) (length_rowWords _) _ _ (by simp [Nauty.rowsOf]) h1
  · intro h
    exact ⟨by rw [h], sortedColorSeq_eq h⟩

/-- The generators the binary writes (block 1) are automorphisms of `G`, and
every automorphism of `G` is a product of them. -/
theorem generators_correct {n k : Nat} (G : Colored n k) :
    (∀ p ∈ (Nauty.runColoredTraced G).autos.toList, ∃ q, (∀ i : Fin n, (q.get i).val = p[i.val]!) ∧
      IsIso G G q) ∧
    ∀ q, IsIso G G q → Perm.Generated (Aut.gens G) q := by
  refine ⟨fun p hp => ?_, fun q hq => Aut.complete G hq⟩
  obtain ⟨q, hq⟩ := Aut.trace_admitted G p hp
  exact ⟨q, autom?_val_get hq, autom?_isIso hq⟩

/-- The orbits the binary writes (block 3): two vertices get the same
representative exactly when an automorphism maps one to the other. -/
theorem orbits_correct {n k : Nat} (G : Colored n k) (u v : Fin n) :
    (finalState G).orbits[u.val]! = (finalState G).orbits[v.val]! ↔ SameOrbit G u v := by
  rw [finalState_orbits]
  exact Aut.orbits_eq_iff_sameOrbit G u v

end NautyVerified.Statement
