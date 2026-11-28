import NautyVerified.Proofs.Sparse.Arr
import HexGraphIso.Nauty.Sparse.Rows

/-!
# The `sparsegraph` struct

nausparse.h's
```
typedef struct { size_t nde; size_t *v; int nv; int *d; int *e; sg_weight *w;
                 size_t vlen, dlen, elen, wlen; } sparsegraph;
```
has its fields at byte offsets 0, 8, 16, 24, 32, 40, 48, 56, 64, 72
(`lval_*`). `SparseGraphAt m bsg sofs G pv pd pe`: the struct at `sofs` in
block `bsg` holds a graph `G` on `n` vertices with `w = NULL`: `nv = n`,
`nde` its number of directed edges, `v` (at `pv`) the row offsets, `d`
(at `pd`) the degrees and `e` (at `pe`) the neighbours, in the order of
HexGraphIso's `Sparse.Graph.ofGraph G`.
-/

namespace NautyVerified.Proofs.Sparse

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Source
open Hex.GraphIso.Nauty.Sparse (Graph)

/-- `sparsegraph`. -/
abbrev sgTy : Cfrontend.Ctypes.type := Tstruct sparse.id.«_1406» noattr

/-- `((sparsegraph*)p)->f`, as SimplExpr writes it for a `graph *p`. -/
abbrev sgField (p : ident) (f : ident) (ty : Cfrontend.Ctypes.type) : expr :=
  .Efield (.Ederef (.Ecast (.Etempvar p (tptr tulong)) (tptr sgTy)) sgTy) f ty

/-- The address of byte `k` of the struct at `sofs`. -/
abbrev fofs (sofs : ptrofs) (k : Int) : Z := Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr (zOfInt k)))

set_option maxRecDepth 100000 in
theorem lval_nde (b : block) (o : ptrofs) :
    Exec.lvalOfField sge sgTy sparse.id.nde (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt 0)), .Full) := rfl
set_option maxRecDepth 100000 in
theorem lval_v (b : block) (o : ptrofs) :
    Exec.lvalOfField sge sgTy sparse.id.v (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt 8)), .Full) := rfl
set_option maxRecDepth 100000 in
theorem lval_nv (b : block) (o : ptrofs) :
    Exec.lvalOfField sge sgTy sparse.id.nv (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt 16)), .Full) := rfl
set_option maxRecDepth 100000 in
theorem lval_d (b : block) (o : ptrofs) :
    Exec.lvalOfField sge sgTy sparse.id.d (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt 24)), .Full) := rfl
set_option maxRecDepth 100000 in
theorem lval_e (b : block) (o : ptrofs) :
    Exec.lvalOfField sge sgTy sparse.id.e (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt 32)), .Full) := rfl
set_option maxRecDepth 100000 in
theorem lval_w (b : block) (o : ptrofs) :
    Exec.lvalOfField sge sgTy sparse.id.w (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt 40)), .Full) := rfl
set_option maxRecDepth 100000 in
theorem lval_vlen (b : block) (o : ptrofs) :
    Exec.lvalOfField sge sgTy sparse.id.vlen (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt 48)), .Full) := rfl
set_option maxRecDepth 100000 in
theorem lval_dlen (b : block) (o : ptrofs) :
    Exec.lvalOfField sge sgTy sparse.id.dlen (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt 56)), .Full) := rfl
set_option maxRecDepth 100000 in
theorem lval_elen (b : block) (o : ptrofs) :
    Exec.lvalOfField sge sgTy sparse.id.elen (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt 64)), .Full) := rfl

/-- The row offsets (`v`), degrees (`d`) and neighbours (`e`) of `G`. -/
def vVals {n : Nat} (G : Hex.SparseGraph n) (i : Nat) : val := .Vlong (lr ((Graph.ofGraph G).offsets[i]!))
def dVals {n : Nat} (G : Hex.SparseGraph n) (i : Nat) : val := .Vint (ir ((Graph.ofGraph G).degree i))
def eVals {n : Nat} (G : Hex.SparseGraph n) (j : Nat) : val := .Vint (ir ((Graph.ofGraph G).neighbor j))

/-- The struct at `sofs` in `bsg` holds `G` (see the module docstring). -/
structure SparseGraphAt {n : Nat} (m : mem) (bsg : block) (sofs : ptrofs) (G : Hex.SparseGraph n)
    (bv : block) (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) : Prop where
  nde : Mem.load .Mint64 m bsg (fofs sofs 0) = some (.Vlong (lr G.neighbors.size))
  v : Mem.load .Mint64 m bsg (fofs sofs 8) = some (.Vptr bv vo)
  nv : Mem.load .Mint32 m bsg (fofs sofs 16) = some (.Vint (ir n))
  d : Mem.load .Mint64 m bsg (fofs sofs 24) = some (.Vptr bd dofs)
  e : Mem.load .Mint64 m bsg (fofs sofs 32) = some (.Vptr be eo)
  w : Mem.load .Mint64 m bsg (fofs sofs 40) = some Vnullptr
  varr : ArrayAt m .Mint64 bv (intOfZ (Ptrofs.unsigned vo)) (vVals G) n
  darr : ArrayAt m .Mint32 bd (intOfZ (Ptrofs.unsigned dofs)) (dVals G) n
  earr : ArrayAt m .Mint32 be (intOfZ (Ptrofs.unsigned eo)) (eVals G) G.neighbors.size

theorem SparseGraphAt.unch {n : Nat} {m m' : mem} {S : block → Prop} (hu : Unch m m' S)
    {bsg : block} {sofs : ptrofs} {G : Hex.SparseGraph n} {bv : block} {vo : ptrofs} {bd : block}
    {dofs : ptrofs} {be : block} {eo : ptrofs} (h : SparseGraphAt m bsg sofs G bv vo bd dofs be eo)
    (hs : ¬ S bsg) (hv : ¬ S bv) (hd : ¬ S bd) (he : ¬ S be) :
    SparseGraphAt m' bsg sofs G bv vo bd dofs be eo where
  nde := by rw [hu.load _ _ _ hs]; exact h.nde
  v := by rw [hu.load _ _ _ hs]; exact h.v
  nv := by rw [hu.load _ _ _ hs]; exact h.nv
  d := by rw [hu.load _ _ _ hs]; exact h.d
  e := by rw [hu.load _ _ _ hs]; exact h.e
  w := by rw [hu.load _ _ _ hs]; exact h.w
  varr := h.varr.unch hu hv
  darr := h.darr.unch hu hd
  earr := h.earr.unch hu he

/-- Reading field `f` (at byte `k`) of the struct a `graph *` temporary points to. -/
theorem eval_sgField {e : env} {le : temp_env} {m : mem} {p f : ident} {ty : Cfrontend.Ctypes.type}
    {chunk : memory_chunk} {bsg : block} {sofs : ptrofs} {k : Int} {x : val}
    (hp : Lib.Maps.PTree.get p le = some (.Vptr bsg sofs))
    (hlv : Exec.lvalOfField sge sgTy f (.Vptr bsg sofs) =
      some (bsg, Ptrofs.add sofs (Ptrofs.repr (zOfInt k)), .Full))
    (hmode : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hld : Mem.load chunk m bsg (fofs sofs k) = some x) :
    Exec.evalExpr sge e le m (sgField p f ty) = some x := by
  simp only [Exec.evalExpr, hp, typeof, cop, Exec.derefLoc,
    show Cfrontend.Ctypes.access_mode sgTy = .By_copy from rfl, hlv, hmode, Mem.loadv]
  exact hld

/-! ## Facts about `Graph.ofGraph G` -/

theorem length_le_of_pairwise : ∀ (l : List Nat) (lo hi : Nat), l.Pairwise (· < ·) →
    (∀ x ∈ l, lo ≤ x ∧ x < hi) → l.length ≤ hi - lo
  | [], _, _, _, _ => Nat.zero_le _
  | a :: t, lo, hi, hp, hb => by
    rw [List.pairwise_cons] at hp
    have ha := hb a (List.mem_cons_self ..)
    have := length_le_of_pairwise t (a + 1) hi hp.2 fun x hx =>
      ⟨hp.1 x hx, (hb x (List.mem_cons_of_mem _ hx)).2⟩
    simp only [List.length_cons]
    omega

theorem degree_lt {n : Nat} (G : Hex.SparseGraph n) {i : Nat} (hi : i < n) :
    (Graph.ofGraph G).degree i ≤ n := by
  have hd : (Graph.ofGraph G).degree i = (G.nbrs ⟨i, hi⟩).size := G.degree_eq_size ⟨i, hi⟩
  rw [hd]
  have hs := G.sorted ⟨i, hi⟩
  have hl := length_le_of_pairwise ((G.nbrs ⟨i, hi⟩).toList.map Fin.val) 0 n
    (List.pairwise_map.2 hs) (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      exact ⟨Nat.zero_le _, y.isLt⟩)
  simpa using hl

theorem offsets_le {n : Nat} (G : Hex.SparseGraph n) {i j : Nat} (hij : i ≤ j) (hj : j ≤ n) :
    (Graph.ofGraph G).offsets[i]! ≤ (Graph.ofGraph G).offsets[j]! :=
  G.offset_mono hij hj

theorem offsets_last {n : Nat} (G : Hex.SparseGraph n) {i : Nat} (hi : i ≤ n) :
    (Graph.ofGraph G).offsets[i]! ≤ G.neighbors.size :=
  G.offset_le hi

theorem neighbor_lt {n : Nat} (G : Hex.SparseGraph n) {j : Nat} (hj : j < G.neighbors.size) :
    (Graph.ofGraph G).neighbor j < n := by
  rw [Hex.GraphIso.Nauty.Sparse.Graph.neighbor_ofGraph G j hj]; exact (G.neighbors[j]).isLt

end NautyVerified.Proofs.Sparse
