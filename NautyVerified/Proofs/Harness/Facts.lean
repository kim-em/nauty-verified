import NautyVerified.Proofs.Harness.Tail

/-!
# The facts about HexGraphIso's result that `main` needs

`resultFacts`: HexGraphIso's canonical labelling, orbits and canonical rows
have one entry per vertex, and the entries `main` writes as `int`s are below
`2^31`. The labelling is the untouched zero array or a reached labelling
(`canonlab_or`, `cellsReach_lt`), the orbits are sound (`runState_orbits`),
and the rows satisfy the store invariant (`canong_inv`).
-/

namespace NautyVerified.Proofs.Harness

open Hex.GraphIso Hex.GraphIso.Nauty

theorem resultFacts {n k : Nat} (G : Colored n k) (hn : n < 2147483648) : ResultFacts G := by
  have hfin : Statement.finalState G =
      (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2 := rfl
  have horb := runState_orbits G
  unfold OrbitsOk OrbSound at horb
  refine ⟨canonlab_size G, fun i hi => ?_, by rw [hfin]; exact horb.1, fun i hi => ?_,
    canongInv_size (canong_inv G)⟩
  · have hc : (runColoredTraced G).result.canonlab = (runColored G).canonlab := rfl
    rw [hc]
    have := cellsReach_lt (canonlab_cellsReach G) i hi
    omega
  · rw [hfin]
    have := (horb.2 i hi).1
    omega

end NautyVerified.Proofs.Harness
