import NautyVerified.Proofs.Sparse.Graph

/-!
# The canonical store `canong`

nausparse.c keeps the canonical graph in a `sparsegraph` struct whose row
`i` starts at `v[i]` and has `d[i]` entries of `e`; HexGraphIso's
`Sparse.Rows` keeps `n + 1` offsets instead, row `i` being the entries of
`neighbors` from `offsets[i]` to `offsets[i + 1]`.
`CanonAt m bc cofs R samerows bv vo bd dofs be eo` ties the two on the
first `samerows` rows: for `i < samerows`, `v[i] = offsets[i]` and
`v[i] + d[i] = offsets[i + 1]`, and `e` agrees with `neighbors` below
`base R samerows` (HexGraphIso's `if samerows = 0 then 0 else
offsets[samerows]`, the offset where `updatecan` resumes), every such
neighbour being below `n`. The remaining entries of the three arrays hold
arbitrary values. The struct has `w = NULL` and writable `nde`, `nv`
fields, which `updatecan_sg` sets. With no edges `e` is `NULL`
(`cePtr`: `init_sg`'s `DYNALLOC1` of size 0 allocates nothing), and then
`CanonAt` says nothing about `be` and `eo` (`CanonAt.rebe`).
-/

namespace NautyVerified.Proofs.Sparse

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Source
open Hex.GraphIso.Nauty.Sparse (Rows)

/-- The offset where the rows after the first `samerows` start. -/
def base {n : Nat} (R : Rows n) (samerows : Nat) : Nat :=
  if samerows = 0 then 0 else R.offsets[samerows]!

/-- The `e` field of a store with `N` neighbour entries: `NULL` when there are none. -/
def cePtr (N : Nat) (b : block) (o : ptrofs) : val := if N = 0 then Vnullptr else .Vptr b o

theorem cePtr_pos {N : Nat} (h : 0 < N) (b : block) (o : ptrofs) : cePtr N b o = .Vptr b o :=
  if_neg (by omega)

theorem cePtr_zero (b : block) (o : ptrofs) : cePtr 0 b o = Vnullptr := rfl

/-- An empty array at a pointer's offset, in any block. -/
theorem arrayAt_empty (m : mem) (chunk : memory_chunk) (b : block) (o : ptrofs) (vals : Nat → val) :
    ArrayAt m chunk b (intOfZ (Ptrofs.unsigned o)) vals 0 :=
  ⟨by simp only [intOfZ_Ptrofs_unsigned]; omega,
   by simp only [intOfZ_Ptrofs_unsigned]; have := (bvp o).isLt; omega,
   fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- An array survives a step that leaves its block alone whenever it is nonempty. -/
theorem _root_.NautyVerified.Logic.ArrayAt.unchN {m m' : mem} {S : block → Prop} (hu : Unch m m' S) {chunk : memory_chunk}
    {b : block} {base : Int} {vals : Nat → val} {N : Nat} (h : ArrayAt m chunk b base vals N)
    (hb : 0 < N → ¬ S b) : ArrayAt m' chunk b base vals N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨h.base_nonneg, h.fits, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · exact h.unch hu (hb hN)

/-- The `v`, `d` and `e` arrays of `canong` hold the first `samerows` rows
of `R` (see the module docstring). -/
structure CanonRows {n : Nat} (R : Rows n) (samerows : Nat) (vv dv ev : Nat → val) : Prop where
  bound : samerows ≤ n
  mono : ∀ i < samerows, R.offsets[i]! ≤ R.offsets[i + 1]!
  v : ∀ i < samerows, vv i = .Vlong (lr R.offsets[i]!)
  d : ∀ i < samerows, dv i = .Vint (ir (R.degree i))
  e : ∀ j < base R samerows, ev j = .Vint (ir R.neighbors[j]!)
  base_le : base R samerows ≤ R.neighbors.size
  nde31 : R.neighbors.size < 2147483648
  small : ∀ j < base R samerows, R.neighbors[j]! < n

/-- The struct at `cofs` in `bc` holds `R` on its first `samerows` rows. -/
structure CanonAt {n : Nat} (m : mem) (bc : block) (cofs : ptrofs) (R : Rows n) (samerows : Nat)
    (bv : block) (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) : Prop where
  ndeW : Mem.valid_access m .Mint64 bc (fofs cofs 0) .Writable
  v : Mem.load .Mint64 m bc (fofs cofs 8) = some (.Vptr bv vo)
  nvW : Mem.valid_access m .Mint32 bc (fofs cofs 16) .Writable
  d : Mem.load .Mint64 m bc (fofs cofs 24) = some (.Vptr bd dofs)
  e : Mem.load .Mint64 m bc (fofs cofs 32) = some (cePtr R.neighbors.size be eo)
  w : Mem.load .Mint64 m bc (fofs cofs 40) = some Vnullptr
  rows : ∃ vv dv ev, ArrayAt m .Mint64 bv (intOfZ (Ptrofs.unsigned vo)) vv n ∧
    ArrayAt m .Mint32 bd (intOfZ (Ptrofs.unsigned dofs)) dv n ∧
    ArrayAt m .Mint32 be (intOfZ (Ptrofs.unsigned eo)) ev R.neighbors.size ∧
    CanonRows R samerows vv dv ev

theorem CanonAt.unch {n : Nat} {m m' : mem} {S : block → Prop} (hu : Unch m m' S)
    {bc : block} {cofs : ptrofs} {R : Rows n} {sr : Nat} {bv : block} {vo : ptrofs} {bd : block}
    {dofs : ptrofs} {be : block} {eo : ptrofs} (h : CanonAt m bc cofs R sr bv vo bd dofs be eo)
    (hs : ¬ S bc) (hv : ¬ S bv) (hd : ¬ S bd) (he : 0 < R.neighbors.size → ¬ S be) :
    CanonAt m' bc cofs R sr bv vo bd dofs be eo where
  ndeW := hu.access _ _ _ _ hs h.ndeW
  v := by rw [hu.load _ _ _ hs]; exact h.v
  nvW := hu.access _ _ _ _ hs h.nvW
  d := by rw [hu.load _ _ _ hs]; exact h.d
  e := by rw [hu.load _ _ _ hs]; exact h.e
  w := by rw [hu.load _ _ _ hs]; exact h.w
  rows := by
    obtain ⟨vv, dv, ev, hv', hd', he', hr⟩ := h.rows
    exact ⟨vv, dv, ev, hv'.unch hu hv, hd'.unch hu hd, he'.unchN hu he, hr⟩

/-- With no edges, `CanonAt` holds of any `e` block and offset. -/
theorem CanonAt.rebe {n : Nat} {m : mem} {bc : block} {cofs : ptrofs} {R : Rows n} {sr : Nat}
    {bv : block} {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs}
    (h : CanonAt m bc cofs R sr bv vo bd dofs be eo) (h0 : R.neighbors.size = 0) (be' : block)
    (eo' : ptrofs) : CanonAt m bc cofs R sr bv vo bd dofs be' eo' :=
  { h with
    e := by rw [h.e, h0]; rfl
    rows := by
      obtain ⟨vv, dv, ev, hv', hd', -, hr⟩ := h.rows
      exact ⟨vv, dv, ev, hv', hd', by rw [h0]; exact arrayAt_empty _ _ _ _ _, hr⟩ }

/-- `CanonAt` with the `e` block and offset replaced by `be'`, `eo'` when there are no edges. -/
theorem CanonAt.rebeIf {n : Nat} {m : mem} {bc : block} {cofs : ptrofs} {R : Rows n} {sr : Nat}
    {bv : block} {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs}
    (h : CanonAt m bc cofs R sr bv vo bd dofs be eo) (be' : block) (eo' : ptrofs) :
    CanonAt m bc cofs R sr bv vo bd dofs (if R.neighbors.size = 0 then be' else be)
      (if R.neighbors.size = 0 then eo' else eo) := by
  by_cases h0 : R.neighbors.size = 0
  · exact h.rebe h0 _ _
  · simp only [h0, ↓reduceIte]; exact h

/-- On the stored rows the offsets increase. -/
theorem CanonRows.offsets_le {n : Nat} {R : Rows n} {sr : Nat} {vv dv ev : Nat → val}
    (h : CanonRows R sr vv dv ev) {i j : Nat} (hij : i ≤ j) (hj : j ≤ sr) :
    R.offsets[i]! ≤ R.offsets[j]! := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hi | hi
    · exact Nat.le_trans (ih (by omega) (by omega)) (h.mono j (by omega))
    · rw [show i = j + 1 by omega]; exact Nat.le_refl _

/-- Every stored row ends at or below `base`. -/
theorem CanonRows.end_le {n : Nat} {R : Rows n} {sr : Nat} {vv dv ev : Nat → val}
    (h : CanonRows R sr vv dv ev) {i : Nat} (hi : i < sr) :
    R.offsets[i + 1]! ≤ base R sr := by
  have : base R sr = R.offsets[sr]! := by simp [base, show sr ≠ 0 by omega]
  rw [this]; exact h.offsets_le (by omega) (Nat.le_refl _)

end NautyVerified.Proofs.Sparse
