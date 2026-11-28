import NautyVerified.Proofs.Sparse.Refine.Nontrivial.Model

/-!
# The count phase, neighbour by neighbour

`edgesTo g s c q r`: the count state after the first `r` neighbours of the
vertex at position `q`, from `c`; at `r` the vertex's degree it is
`countVertex` (`edgesTo_deg`). `edgesTo_scan`: `CountScan` over the
neighbours seen so far. `count_le`: a vertex of a touched cell has been
counted at most once per splitter vertex seen.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Nontrivial

open Hex.GraphIso.Nauty.Sparse NautyVerified.Spec.SortC
open Hex.GraphIso.Nauty (VSet mash cleanup cellEnd IsCell)

variable {n : Nat}

/-- The degree of the vertex at position `q`. -/
def deg (g : Graph n) (s : RefineSt n) (q : Nat) : Nat :=
  g.offsets[s.lab[q]! + 1]! - g.offsets[s.lab[q]!]!

/-- The count state after `r` neighbours of the vertex at position `q`. -/
def edgesTo (g : Graph n) (s : RefineSt n) (c : CS) (q r : Nat) : CS :=
  (List.range' g.offsets[s.lab[q]!]! r).foldl (fun c e => countEdge s c (g.neighbor e)) c

theorem edgesTo_zero (g : Graph n) (s : RefineSt n) (c : CS) (q : Nat) : edgesTo g s c q 0 = c := rfl

theorem edgesTo_succ (g : Graph n) (s : RefineSt n) (c : CS) (q r : Nat) :
    edgesTo g s c q (r + 1) =
      countEdge s (edgesTo g s c q r) (g.neighbor (g.offsets[s.lab[q]!]! + r)) := by
  simp only [edgesTo, List.range'_concat, List.foldl_append, Nat.one_mul, List.foldl_cons,
    List.foldl_nil]

theorem edgesTo_deg (g : Graph n) (s : RefineSt n) (c : CS) (q : Nat) :
    edgesTo g s c q (deg g s q) = countVertex g s c q := rfl

/-- The neighbours of the vertices at the positions `[split, q)` and the first
`r` neighbours of the vertex at `q`. -/
def seenTo (g : Graph n) (s : RefineSt n) (split q r : Nat) : List Nat :=
  (List.range' split (q - split)).flatMap (fun p => g.row s.lab[p]!) ++ (g.row s.lab[q]!).take r

theorem take_row_succ (g : Graph n) (v r : Nat) (hr : r < g.offsets[v + 1]! - g.offsets[v]!) :
    (g.row v).take (r + 1) = (g.row v).take r ++ [g.neighbor (g.offsets[v]! + r)] := by
  have hl : r < (g.row v).length := by simp [Graph.row]; omega
  rw [List.take_add_one, List.getElem?_eq_getElem hl]
  simp [Graph.row, List.getElem_range']

theorem seenTo_succ (g : Graph n) (s : RefineSt n) (split q r : Nat) (hr : r < deg g s q) :
    seenTo g s split q (r + 1) = seenTo g s split q r ++ [g.neighbor (g.offsets[s.lab[q]!]! + r)] := by
  simp only [seenTo, take_row_succ g _ r hr, List.append_assoc]

theorem seenTo_next (g : Graph n) (s : RefineSt n) {split q : Nat} (hq : split ≤ q) :
    seenTo g s split q (deg g s q) = seenTo g s split (q + 1) 0 := by
  simp only [seenTo, List.take_zero, List.append_nil]
  rw [show q + 1 - split = (q - split) + 1 by omega, List.range'_concat, List.flatMap_append,
    Nat.one_mul, show split + (q - split) = q by omega]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  congr 1
  apply List.take_of_length_le
  simp [deg, Graph.row]

theorem edgesTo_scan (G : Hex.SparseGraph n) {level : Nat} {s : RefineSt n} (hv : s.Valid level)
    {c : CS} {seen : List Nat} {q : Nat} (hq : q < n) :
    ∀ r, r ≤ deg (.ofGraph G) s q →
      CountScan n s.stamp s.marks c.1 c.2.2 s.cellstart c.2.1 seen →
      let d := edgesTo (.ofGraph G) s c q r
      CountScan n s.stamp s.marks d.1 d.2.2 s.cellstart d.2.1
        (seen ++ ((Graph.ofGraph G).row s.lab[q]!).take r)
  | 0, _, h => by simpa [edgesTo] using h
  | r + 1, hr, h => by
    have ih := edgesTo_scan G hv hq r (by omega) h
    have hv' := perm_bound hv.lab hq
    have hj : (Graph.ofGraph G).neighbor ((Graph.ofGraph G).offsets[s.lab[q]!]! + r) < n := by
      have hlo := G.offset_mono (i := s.lab[q]!) (j := s.lab[q]! + 1) (by omega) (by omega)
      exact Graph.neighbor_lt G ⟨s.lab[q]!, hv'⟩ (by simp only [deg] at hr; simp only [Graph.ofGraph] at hr ⊢; omega)
    have := edge_scan hv hj ih
    rw [edgesTo_succ, take_row_succ _ _ _ (by simp only [deg] at hr; omega), ← List.append_assoc]
    exact this

/-- A vertex of a touched cell is counted at most once per splitter vertex. -/
theorem count_le (G : Hex.SparseGraph n) {level : Nat} {s : RefineSt n} (hv : s.Valid level)
    {c : CS} {split q r : Nat} (hq : q < n)
    (h : CountScan n s.stamp s.marks c.1 c.2.2 s.cellstart c.2.1 (seenTo (.ofGraph G) s split q r))
    {v : Nat} (hvn : v < n) (hk : s.cellstart[v]! < n)
    (hm : s.cellstart[v]! ∈ (seenTo (.ofGraph G) s split q r).map fun w => s.cellstart[w]!) :
    c.2.1[v]! ≤ q - split + 1 := by
  rw [h.counts.get v hvn hk hm, seenTo, List.count_append]
  have h1 := Graph.count_rows G s.lab hv.lab (List.range' split (q - split))
    (fun p hp => by simp only [List.mem_range'_1] at hp; omega) v
  have hl := perm_bound hv.lab hq
  have h2 := List.nodup_iff_count.mp ((Graph.row_nodup G ⟨s.lab[q]!, hl⟩).sublist
    (List.take_sublist r _)) v
  simp only [List.length_range'] at h1
  have : List.count v (List.take r ((Graph.ofGraph G).row s.lab[q]!)) ≤ 1 := h2
  omega

end NautyVerified.Proofs.Sparse.Refine.Nontrivial
