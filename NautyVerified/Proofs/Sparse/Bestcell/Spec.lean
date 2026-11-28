import NautyVerified.Proofs.Sparse.Freedyn
import NautyVerified.Proofs.Sparse.Targetcell.Syntax
import HexGraphIso.Nauty.Sparse.Target

/-!
# `bestcell_sg`'s specification

`bestcellSpec`: called with a sparse graph `G` (`SparseGraphAt`), a
labelling `lab` that is a permutation of `0 .. n-1` and a partition `ptn`
whose last cell is closed at `level`, nausparse.c's `bestcell_sg` returns
HexGraphIso's `Sparse.bestcell (ofGraph G) lab ptn level`. Its four
`DYNALLOC1`s may replace `work1` to `work4` (`Works`); nothing else visible
changes (`worksSet`).

`lab` must be onto: `bestcell_sg` writes `NNTCELL[lab[j]]` for every
position `j` and then reads `NNTCELL[e[vi+j]]` for every neighbour, so a
vertex missing from `lab` would be read from whatever `work2` held before
and then used as an index into `HITS`.
-/

namespace NautyVerified.Proofs.Sparse.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty.Sparse (Graph)

/-- The pointer global of `work(k+1)`. -/
def wp : Fin 4 → block
  | 0 => Block.work1 | 1 => Block.work2 | 2 => Block.work3 | 3 => Block.work4

/-- The capacity global of `work(k+1)`. -/
def ws : Fin 4 → block
  | 0 => Block.work1Sz | 1 => Block.work2Sz | 2 => Block.work3Sz | 3 => Block.work4Sz

/-- The eight globals of the four pairs. -/
def wglobs : List block := [Block.work1, Block.work1Sz, Block.work2, Block.work2Sz, Block.work3,
  Block.work3Sz, Block.work4, Block.work4Sz]

theorem wp_mem : ∀ k, wp k ∈ wglobs := by decide

theorem ws_mem : ∀ k, ws k ∈ wglobs := by decide

/-- `work1` to `work4` with capacities `c` and blocks `b`, the blocks in use
pairwise distinct and apart from the eight globals. -/
structure Works (m : mem) (c : Fin 4 → Nat) (b : Fin 4 → block) : Prop where
  dyn : ∀ k, DynAt m (wp k) (ws k) 4 (c k) (b k)
  apart : ∀ k, 0 < c k → b k ∉ wglobs
  distinct : ∀ k k', k ≠ k' → 0 < c k → 0 < c k' → b k ≠ b k'

/-- The blocks a call may change: the eight globals, the blocks in use and new blocks. -/
def worksSet (m : mem) (c : Fin 4 → Nat) (b : Fin 4 → block) (z : block) : Prop :=
  z ∈ wglobs ∨ (∃ k, 0 < c k ∧ z = b k) ∨ ¬ Mem.valid_block m z

/-- A caller's block: valid and none of the blocks `worksSet` allows to change. -/
structure Apart (m : mem) (c : Fin 4 → Nat) (b : Fin 4 → block) (z : block) : Prop where
  valid : Mem.valid_block m z
  glob : z ∉ wglobs
  blk : ∀ k, 0 < c k → z ≠ b k

theorem Apart.not_mem {m : mem} {c : Fin 4 → Nat} {b : Fin 4 → block} {z : block}
    (h : Apart m c b z) : ¬ worksSet m c b z := by
  rintro (h' | ⟨k, hk, rfl⟩ | h')
  · exact h.glob h'
  · exact h.blk k hk rfl
  · exact h' h.valid

/-- What `bestcell_sg` and `targetcell_sg` need of the caller's memory. -/
structure Pre {n : Nat} (m : mem) (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs)
    (bv : block) (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs)
    (bl : block) (lofs : ptrofs) (lab : Array Nat) (bp : block) (pofs : ptrofs) (ptn : Array Nat)
    (level : Nat) (c : Fin 4 → Nat) (b : Fin 4 → block) : Prop where
  graph : SparseGraphAt m bsg sofs G bv vo bd dofs be eo
  larr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n
  lsmall : ∀ j < n, lab[j]! < n
  lonto : ∀ p < n, ∃ j < n, lab[j]! = p
  parr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n
  psize : ptn.size = n
  psmall : ∀ x < n, ptn[x]! < 2147483648
  plast : ptn[n - 1]! ≤ level
  levlt : level < 2147483648
  works : Works m c b
  caller : ∀ z ∈ [bsg, bv, bd, be, bl, bp], Apart m c b z
  n0 : 0 < n
  nlt : n < 1073741824

/-- What they leave: the four pairs, each as before or a block not valid
before, with room for `n` entries, only `worksSet` changed, and `HITS`
(`work3`) holding naturals below `2^31` up to its capacity if it did before. -/
def Post (m m' : mem) (c : Fin 4 → Nat) (b : Fin 4 → block) : Prop :=
  ∃ c' b', Works m' c' b' ∧ (∀ k, (c' k = c k ∧ b' k = b k) ∨ ¬ Mem.valid_block m (b' k)) ∧
    Unch m m' (worksSet m c b) ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    (HitsOk m (c 2) (b 2) → HitsOk m' (c' 2) (b' 2))

theorem Post.refl {m : mem} {c : Fin 4 → Nat} {b : Fin 4 → block} (h : Works m c b) :
    Post m m c b :=
  ⟨c, b, h, fun _ => .inl ⟨rfl, rfl⟩, Unch.refl _ _, fun _ h => h, fun h => h⟩

def bestcellSpec {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs) (bv : block)
    (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (bl : block)
    (lofs : ptrofs) (lab : Array Nat) (bp : block) (pofs : ptrofs) (ptn : Array Nat)
    (level tcLevel M : Nat) (c : Fin 4 → Nat) (b : Fin 4 → block) : FunSpec where
  pre args m := args = [.Vptr bsg sofs, .Vptr bl lofs, .Vptr bp pofs, .Vint (ir level),
      .Vint (ir tcLevel), .Vint (ir M), .Vint (ir n)] ∧
    Pre m G bsg sofs bv vo bd dofs be eo bl lofs lab bp pofs ptn level c b
  post _ m t v m' := t = E0 ∧
    v = .Vint (ir (Hex.GraphIso.Nauty.Sparse.bestcell (Graph.ofGraph G) lab ptn level : Int)) ∧
    Post m m' c b

end NautyVerified.Proofs.Sparse.Bestcell
