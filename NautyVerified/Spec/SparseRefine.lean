import HexGraphIso.Nauty.Sparse.RefineLiteral

/-!
# Sparse refinement with retained scratch

HexGraphIso's sparse search refines with `refineWith`, reusing the cell
indices, hit counts and marks (`Scratch`) of earlier calls; `refine_sg`
allocates nothing per call but keeps its own `work1`..`work4` and `vmark`
arrays, so its specification is stated against `Sparse.refine`, which starts
from `Scratch.fresh`. `refineWith_refine`: for any `Scratch.Bounded` scratch,
the outputs `refine_sg` writes or returns (`lab`, `ptn`, `active`, the cell
count and the code) are `refine`'s. It is HexGraphIso's `refineWith_congr`
with the second scratch fresh.
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty Hex.GraphIso.Nauty.Sparse

theorem refineWith_refine {n : Nat} (G : Hex.SparseGraph n) (level : Nat)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) (s : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level)
    (ha : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level)
    (hb : Scratch.Bounded n s) :
    let a := refineWith (.ofGraph G) level lab ptn active numcells s
    let b := Sparse.refine (.ofGraph G) level lab ptn active numcells
    a.lab = b.lab ∧ a.ptn = b.ptn ∧ a.active = b.active ∧ a.numcells = b.numcells ∧
      a.longcode = b.longcode := by
  have h := refineWith_congr G level lab ptn active numcells s (.fresh n) hp hs hend ha hb
    (Scratch.fresh_valid n lab ptn level).toBounded
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end NautyVerified.Spec
