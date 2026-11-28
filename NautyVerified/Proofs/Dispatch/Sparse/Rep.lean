import NautyVerified.Proofs.Dispatch.DenseRep
import NautyVerified.Proofs.Sparse.Init.Satisfies
import NautyVerified.Proofs.Sparse.Refine.Marks2
import NautyVerified.Proofs.Sparse.Freedyn
import NautyVerified.Proofs.Sparse.Targetcell.Syntax
import NautyVerified.Proofs.Sparse.Updatecan.Rows
import HexGraphIso.Nauty.Sparse.Search

/-!
# nausparse.c's dispatch representation

`sparseOps`: HexGraphIso's sparse operations (graph `Sparse.Graph`, store
`Sparse.Rows`, the search's store `Sparse.Storage` with its ghost scratch),
refinement through the fresh `Sparse.refine`.

`sparseRep`: `dispatch_sparse`'s procedures in the sparse program, the graph
as the `sparsegraph` struct with its `v`, `d`, `e` arrays (`SparseGraphAt`,
the arrays' blocks in `GLoc`), the canonical store as `canong`'s struct
(`CanonAt`, its arrays in `CLoc`; with no edges `e` is `NULL` and its block
is not one of the store's, `CArrs.es`), the scratch state as nausparse.c's six
`DYNALLSTAT` pairs `vmark1`, `vmark2`, `work1` to `work4` with the two mark
invariants (`MarksAt`), the table as nausparse.c's `bit`, the workspace as the
`snwork` pair, `init = init_sg`.

`Dispatch/Sparse.lean` adds the specifications.
-/

namespace NautyVerified.Proofs.Dispatch

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep Slot InUse SlotsOk)
open NautyVerified.Proofs.Set (BitTable longs)
open NautyVerified.Proofs.Sparse (SparseGraphAt CanonAt CanonRows MarksAt base start)
open Hex.GraphIso.Nauty

attribute [local instance] NautyEnv.sparse

local notation "VM1" => Sparse.Block.vmark1
local notation "VM1S" => Sparse.Block.vmark1Sz
local notation "VM1V" => Sparse.Block.vmark1Val
local notation "VM2" => Sparse.Refine.Block.vmark2
local notation "VM2S" => Sparse.Refine.Block.vmark2Sz
local notation "VM2V" => Sparse.Refine.Block.vmark2Val
local notation "W1" => Sparse.Block.work1
local notation "W1S" => Sparse.Block.work1Sz
local notation "W2" => Sparse.Refine.Block.work2
local notation "W2S" => Sparse.Refine.Block.work2Sz
local notation "W3" => Sparse.Refine.Block.work3
local notation "W3S" => Sparse.Refine.Block.work3Sz
local notation "W4" => Sparse.Refine.Block.work4
local notation "W4S" => Sparse.Refine.Block.work4Sz
local notation "BIT" => Sparse.Refine.Block.bit
local notation "SN" => Sparse.Block.snwork
local notation "SNS" => Sparse.Block.snworkSz

/-! ### The operations -/

/-- The outputs of a sparse refinement `refine_sg` writes, as a dense `RefineSt`. -/
def ofSparseSt {n : Nat} (r : Sparse.RefineSt n) : RefineSt n :=
  { lab := r.lab, ptn := r.ptn, active := r.active, numcells := r.numcells, hint := 0, maxpos := 0,
    longcode := r.longcode }

/-- Sparse nauty's operations. -/
@[reducible] def sparseOps : Ops where
  Gr := Sparse.Graph
  Store := Sparse.Rows
  StoreOk {n} g c := c.offsets.size = n + 1 ∧ c.neighbors.size = g.neighbors.size
  GraphOk g := g.neighbors.size < 2147483648
  blank g := g.blank
  refine g level lab ptn active numcells := ofSparseSt (Sparse.refine g level lab ptn active numcells)
  targetcell := Sparse.targetcell
  isautom := Sparse.isautom
  testcanlab := Sparse.testcanlab
  updatecan := Sparse.updatecan
  Fits {n} g c lab sr := start g lab sr (base c sr) (n - sr) ≤ c.neighbors.size
  cheapautom := cheapautom
  Canon := Sparse.Storage
  rows c := c.toRows
  classify := Sparse.classify

/-! ### The globals -/

/-- nausparse.c's scratch pairs. -/
def sparseSlots : List Slot :=
  [(VM1, VM1S, 2), (VM2, VM2S, 2), (W1, W1S, 4), (W2, W2S, 4), (W3, W3S, 4), (W4, W4S, 4)]

/-- The globals nausparse.c's procedures write. -/
def sparseWGlobs : List block :=
  [VM1, VM1S, VM1V, VM2, VM2S, VM2V, W1, W1S, W2, W2S, W3, W3S, W4, W4S]

/-- nausparse.c's globals. -/
def sparseGlobs : List block := sparseWGlobs ++ [BIT, SN, SNS]

kernel_rfl sparseGlobs_distinct_dec : decide (sparseGlobs.Pairwise (· ≠ ·)) = true
kernel_rfl sparseGlobs_env_dec :
  decide (∀ z ∈ sparseGlobs, z ∉ (NautyEnv.sparse.blocks)) = true

/-- What nausparse.c's scratch blocks avoid. -/
abbrev sparseL : List block := sparseGlobs ++ envAvoid

kernel_rfl slots_globs_dec : decide (∀ p ∈ sparseSlots, p.1 ∈ sparseWGlobs ∧ p.2.1 ∈ sparseWGlobs) = true

theorem slot_globs {p : Slot} (hp : p ∈ sparseSlots) : p.1 ∈ sparseWGlobs ∧ p.2.1 ∈ sparseWGlobs :=
  of_decide_eq_true slots_globs_dec p hp

theorem wglobs_L {z : block} (h : z ∈ sparseWGlobs) : z ∈ sparseL :=
  List.mem_append_left _ (List.mem_append_left _ h)

/-! ### The representations -/

/-- The blocks and offsets of a `sparsegraph`'s `v`, `d` and `e` arrays. -/
structure Arrs where
  bv : block
  vo : ptrofs
  bd : block
  dofs : ptrofs
  be : block
  eo : ptrofs

/-- The arrays of `canong`, and `es`, the `e` block as a list: empty when the
store has no neighbour entries (`e` is then `NULL`). -/
structure CArrs extends Arrs where
  es : List block

/-- The `e` block list of a store with `N` neighbour entries. -/
def esOf (N : Nat) (be : block) : List block := if N = 0 then [] else [be]

theorem mem_esOf {N : Nat} {be z : block} (h : z ∈ esOf N be) : 0 < N ∧ z = be := by
  unfold esOf at h
  by_cases h0 : N = 0
  · rw [if_pos h0] at h; exact absurd h List.not_mem_nil
  · rw [if_neg h0, List.mem_singleton] at h; exact ⟨by omega, h⟩

theorem esOf_mem {N : Nat} (be : block) (h : 0 < N) : be ∈ esOf N be := by
  unfold esOf; rw [if_neg (by omega)]; exact List.mem_singleton_self _

/-- The graph `g` at `bg`: a `sparsegraph` holding a `Hex.SparseGraph` whose view
is `g`; its edge array has at least one readable entry (`sparse_main`
allocates one for an edgeless graph). -/
def sparseGraphRep {n : Nat} (m : mem) (gl : Arrs) (bg : block) (gofs : ptrofs) (g : Sparse.Graph n) :
    Prop :=
  ∃ G : Hex.SparseGraph n, Sparse.Graph.ofGraph G = g ∧
    SparseGraphAt m bg gofs G gl.bv gl.vo gl.bd gl.dofs gl.be gl.eo ∧
    Mem.valid_access m .Mint32 gl.be (Ptrofs.unsigned gl.eo) .Readable

/-- The store `c` at `bc`, its first `sr` rows meaningful. -/
def sparseCanonRep {n : Nat} (m : mem) (cl : CArrs) (bc : block) (cofs : ptrofs) (c : Sparse.Rows n)
    (sr : Nat) : Prop :=
  CanonAt m bc cofs c sr cl.bv cl.vo cl.bd cl.dofs cl.be cl.eo ∧
    intOfZ (Ptrofs.unsigned cofs) + 72 < 2 ^ 64 ∧ cl.es = esOf c.neighbors.size cl.be

/-- `canong` before `init_sg`. -/
def sparseCanonPre (m : mem) (bc : block) (cofs : ptrofs) : Prop :=
  Sparse.Init.SgInit m bc cofs ∧ intOfZ (Ptrofs.unsigned cofs) + 72 < 2 ^ 64

/-- Fewer stored rows. -/
theorem _root_.NautyVerified.Proofs.Sparse.CanonRows.le {n : Nat} {R : Sparse.Rows n} {sr sr' : Nat} {vv dv ev : Nat → val}
    (h : CanonRows R sr vv dv ev) (hle : sr' ≤ sr) : CanonRows R sr' vv dv ev := by
  have hb : base R sr' ≤ base R sr := by
    unfold base
    by_cases h0 : sr' = 0
    · simp [h0]
    · rw [if_neg h0, if_neg (by omega)]; exact h.offsets_le hle (Nat.le_refl _)
  exact ⟨Nat.le_trans hle h.bound, fun i hi => h.mono i (by omega), fun i hi => h.v i (by omega),
    fun i hi => h.d i (by omega), fun j hj => h.e j (by omega), Nat.le_trans hb h.base_le, h.nde31,
    fun j hj => h.small j (by omega)⟩

theorem valid_of_load {m : mem} {chunk : memory_chunk} {b : block} {ofs : Z} {v : val}
    (h : Mem.load chunk m b ofs = some v) : Mem.valid_block m b :=
  Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h)

/-- The scratch state: the six pairs, the globals valid, and both mark invariants. -/
def sparseWork (m : mem) : Prop :=
  SlotsOk m sparseSlots sparseL ∧ (∀ z ∈ sparseL, Mem.valid_block m z) ∧
    (∃ c b s k, MarksAt m c b s k) ∧ (∃ c b s k, Sparse.Marks2.MarksAt m c b s k)

theorem vm1_inUse {m : mem} {c : Nat} {b : block} {s : Nat} {k : Nat → Int} (h : MarksAt m c b s k)
    (hc : 0 < c) : InUse m sparseSlots b := ⟨(VM1, VM1S, 2), by simp [sparseSlots], c, hc, h.dyn⟩

theorem vm2_inUse {m : mem} {c : Nat} {b : block} {s : Nat} {k : Nat → Int}
    (h : Sparse.Marks2.MarksAt m c b s k) (hc : 0 < c) : InUse m sparseSlots b :=
  ⟨(VM2, VM2S, 2), by simp [sparseSlots], c, hc, h.dyn⟩

theorem init_ne : Vptr Sparse.Block.init Ptrofs.zero ≠ Vnullptr := by
  simp [Vnullptr, CompCert4Lean.X86_64.Archi.ptr64]

/-- `dispatch_sparse`'s representation. -/
def sparseRep : DispatchRep sparseGe sparseOps where
  isautom := Sparse.Block.isautom
  testcanlab := Sparse.Block.testcanlab
  updatecan := Sparse.Block.updatecan
  refine := Sparse.Refine.Block.refine
  refine1 := Sparse.Refine.Block.refine
  cheapautom := PArith.BinPos.Pos.of_nat 306
  targetcell := Sparse.Block.targetcell
  freedyn := PArith.BinPos.Pos.of_nat 227
  check := PArith.BinPos.Pos.of_nat 40
  init := .Vptr Sparse.Block.init Ptrofs.zero
  wsP := SN
  wsS := SNS
  globs := sparseGlobs
  wglobs := sparseWGlobs
  Work := sparseWork
  IsWork m z := InUse m sparseSlots z
  Tables m := BitTable m BIT
  GLoc := Arrs
  CLoc := CArrs
  graphBlocks gl bg := [bg, gl.bv, gl.bd, gl.be]
  canonBlocks cl bc := bc :: cl.bv :: cl.bd :: cl.es
  GraphRep m gl bg gofs g _ := sparseGraphRep m gl bg gofs g
  CanonRep m cl bc cofs _ c sr := sparseCanonRep m cl bc cofs c sr
  CanonPre m bc cofs _ _ := sparseCanonPre m bc cofs
  globs_distinct := of_decide_eq_true sparseGlobs_distinct_dec
  globs_env := of_decide_eq_true sparseGlobs_env_dec
  wglobs_sub z hz := List.mem_append_left _ hz
  wsP_mem := by simp [sparseGlobs]
  wsS_mem := by simp [sparseGlobs]
  wsP_nw := by decide
  wsS_nw := by decide
  isWork_valid h := h.valid
  isWork_globs hw hz := by
    have := hw.1.notin _ hz
    simp only [List.mem_append, not_or] at this
    exact this
  globs_valid hw z hz := hw.2.1 z (List.mem_append_left _ hz)
  work_unch hw hu hg hk hv := by
    obtain ⟨hs, hL, ⟨c1, b1, s1, k1, h1⟩, ⟨c2, b2, s2, k2, h2⟩⟩ := hw
    have h := hs.unch hu (fun p hp => ⟨hg _ (slot_globs hp).1, hg _ (slot_globs hp).2⟩) hk
    refine ⟨⟨h.1, fun z hz => hv z (hL z hz), ⟨c1, b1, s1, k1, ?_⟩, ⟨c2, b2, s2, k2, ?_⟩⟩, h.2⟩
    · exact h1.unch hu (hg _ (by decide)) (hg _ (by decide)) (hg _ (by decide))
        fun hc => hk _ (vm1_inUse h1 hc)
    · exact h2.unch hu (hg _ (by decide)) (hg _ (by decide)) (hg _ (by decide))
        fun hc => hk _ (vm2_inUse h2 hc)
  tables_unch ht hu hg := fun i hi => by
    rw [hu.load _ _ _ (hg _ (by simp [sparseGlobs]) (by decide))]; exact ht i hi
  graphBlocks_head _ _ := List.mem_cons_self
  canonBlocks_head _ _ := List.mem_cons_self
  graph_unch h hu hb := by
    obtain ⟨G, hG, hs, ha⟩ := h
    exact ⟨G, hG, hs.unch hu (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp)),
      hu.access _ _ _ _ (hb _ (by simp)) ha⟩
  canon_unch h hu hb :=
    ⟨h.1.unch hu (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp))
      (fun hp => hb _ (by rw [h.2.2]; simp [esOf_mem _ hp])), h.2⟩
  canon_le h hle := by
    obtain ⟨hc, h72, hn⟩ := h
    obtain ⟨vv, dv, ev, a1, a2, a3, hr⟩ := hc.rows
    exact ⟨{ hc with rows := ⟨vv, dv, ev, a1, a2, a3, hr.le hle⟩ }, h72, hn⟩
  graph_valid h hn _ z hz := by
    obtain ⟨G, -, hs, ha⟩ := h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact valid_of_load hs.nv
    · exact arrayAt_valid hs.varr hn
    · exact arrayAt_valid hs.darr hn
    · exact Alloc.valid_of_access ha
  canon_valid h hn _ z hz := by
    obtain ⟨hc, -, hes⟩ := h
    obtain ⟨vv, dv, ev, a1, a2, a3, -⟩ := hc.rows
    simp only [List.mem_cons] at hz
    rcases hz with rfl | rfl | rfl | hz
    · exact Alloc.valid_of_access hc.ndeW
    · exact arrayAt_valid a1 hn
    · exact arrayAt_valid a2 hn
    · rw [hes] at hz
      obtain ⟨hp, rfl⟩ := mem_esOf hz
      exact arrayAt_valid a3 hp
  init_null h := absurd h init_ne

@[simp] theorem sparseRep_graphBlocks (gl : sparseRep.GLoc) (bg : block) :
    sparseRep.graphBlocks gl bg = [bg, gl.bv, gl.bd, gl.be] := rfl
@[simp] theorem sparseRep_canonBlocks (cl : sparseRep.CLoc) (bc : block) :
    sparseRep.canonBlocks cl bc = bc :: cl.bv :: cl.bd :: cl.es := rfl

/-! ### The scratch state across a call -/

theorem slot_L {p : Slot} (hp : p ∈ sparseSlots) : p.1 ∈ sparseL ∧ p.2.1 ∈ sparseL :=
  ⟨wglobs_L (slot_globs hp).1, wglobs_L (slot_globs hp).2⟩

theorem inUse_sub {m : mem} {Ps : List Slot} {z : block} (h : InUse m Ps z)
    (hPs : ∀ p ∈ Ps, p ∈ sparseSlots) : InUse m sparseSlots z :=
  let ⟨p, hp, c, hc, d⟩ := h; ⟨p, hPs p hp, c, hc, d⟩

/-- A pair outside the changed pairs `Ps`, under a step writing only `Gs`, the
blocks of `Ps`, new blocks and `out`, keeps its globals and block. -/
theorem keep_pair {m : mem} (hw : sparseWork m) {W out : block → Prop} {Gs : List block}
    {Ps : List Slot} (hGs : ∀ z ∈ Gs, z ∈ sparseWGlobs) (hPs : ∀ p ∈ Ps, p ∈ sparseSlots)
    (hW : ∀ z, W z → z ∈ Gs ∨ InUse m Ps z ∨ ¬ Mem.valid_block m z ∨ out z)
    (hout : ∀ z, out z → Mem.valid_block m z → z ∉ sparseWGlobs ∧ ¬ InUse m sparseSlots z)
    {q : Slot} (hq : q ∈ sparseSlots) (hqP : q ∉ Ps) (hg1 : q.1 ∉ Gs) (hg2 : q.2.1 ∉ Gs) :
    ¬ W q.1 ∧ ¬ W q.2.1 ∧ ∀ c b, 0 < c → q.At m c b → ¬ W b := by
  have glob : ∀ z, z ∈ sparseWGlobs → z ∉ Gs → ¬ W z := by
    intro z hz hg hwz
    have hv := hw.2.1 z (wglobs_L hz)
    rcases hW z hwz with h | h | h | h
    · exact hg h
    · exact hw.1.notin z (inUse_sub h hPs) (wglobs_L hz)
    · exact h hv
    · exact (hout z h hv).1 hz
  refine ⟨glob _ (slot_globs hq).1 hg1, glob _ (slot_globs hq).2 hg2, fun c b hc d hwb => ?_⟩
  have hu : InUse m sparseSlots b := ⟨q, hq, c, hc, d⟩
  rcases hW b hwb with h | ⟨p, hp, c', hc', d'⟩ | h | h
  · exact hw.1.notin b hu (wglobs_L (hGs b h))
  · exact hqP (hw.1.sep p (hPs p hp) q hq c' c b hc' hc d' d ▸ hp)
  · exact h hu.valid
  · exact (hout b h hu.valid).2 hu

/-- The pairs after a call that may reallocate the pairs `Ps`, each to its old
block or a new one, new blocks of different pairs differing. -/
theorem slots_step {m m' : mem} (hw : sparseWork m) {W out : block → Prop} (hu : Unch m m' W)
    {Gs : List block} {Ps : List Slot} (hGs : ∀ z ∈ Gs, z ∈ sparseWGlobs)
    (hPs : ∀ p ∈ Ps, p ∈ sparseSlots)
    (hGq : ∀ q ∈ sparseSlots, q ∉ Ps → q.1 ∉ Gs ∧ q.2.1 ∉ Gs)
    (hW : ∀ z, W z → z ∈ Gs ∨ InUse m Ps z ∨ ¬ Mem.valid_block m z ∨ out z)
    (hout : ∀ z, out z → Mem.valid_block m z → z ∉ sparseWGlobs ∧ ¬ InUse m sparseSlots z)
    (hch : ∀ p ∈ Ps, ∃ c b c' b', p.At m c b ∧ p.At m' c' b' ∧ ((c' = c ∧ b' = b) ∨ ¬ Mem.valid_block m b'))
    (hfresh : ∀ p ∈ Ps, ∀ q ∈ Ps, ∀ c c' z, 0 < c → 0 < c' → p.At m' c z → q.At m' c' z →
      ¬ Mem.valid_block m z → p = q) :
    SlotsOk m' sparseSlots sparseL ∧
      ∀ z, InUse m' sparseSlots z → InUse m sparseSlots z ∨ ¬ Mem.valid_block m z := by
  have kept : ∀ q ∈ sparseSlots, q ∉ Ps → ∃ c b, q.At m c b ∧ q.At m' c b := by
    intro q hq hqP
    obtain ⟨c, b, d⟩ := hw.1.dyn q hq
    obtain ⟨k1, k2, k3⟩ := keep_pair hw hGs hPs hW hout hq hqP (hGq q hq hqP).1 (hGq q hq hqP).2
    exact ⟨c, b, d, d.keep hu k1 k2 fun hc => Keep.unch hu (k3 c b hc d)⟩
  refine hw.1.next hw.2.1 (fun q hq => ?_) ?_
  · by_cases hqP : q ∈ Ps
    · obtain ⟨c, b, c', b', d, d', h⟩ := hch q hqP
      exact Alloc.Slot.next_of d d' h
    · obtain ⟨c, b, d, d'⟩ := kept q hq hqP
      exact Alloc.Slot.next_of d d' (.inl ⟨rfl, rfl⟩)
  · intro p hp q hq c c' z hc hc' dp dq hnv
    have old : ∀ r ∈ sparseSlots, r ∉ Ps → ∀ c z, 0 < c → r.At m' c z → Mem.valid_block m z := by
      intro r hr hrP c z hc d
      obtain ⟨c0, b0, d0, d0'⟩ := kept r hr hrP
      have e1 : c = c0 := d0'.same_cap d
      subst e1
      rw [d0'.same_block d hc]
      exact Alloc.Malloced.valid (d0.mal hc)
    by_cases hpP : p ∈ Ps
    · by_cases hqP : q ∈ Ps
      · exact hfresh p hpP q hqP c c' z hc hc' dp dq hnv
      · exact absurd (old q hq hqP c' z hc' dq) hnv
    · exact absurd (old p hp hpP c z hc dp) hnv

/-- A call's `Step`, from the pairs and marks after it. -/
theorem sparse_step {m m' : mem} {out : block → Prop} (hw : sparseWork m)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) {W : block → Prop} (hu : Unch m m' W)
    (Gs : List block) (Ps : List Slot) (hGs : ∀ z ∈ Gs, z ∈ sparseWGlobs)
    (hPs : ∀ p ∈ Ps, p ∈ sparseSlots)
    (hGq : ∀ q ∈ sparseSlots, q ∉ Ps → q.1 ∉ Gs ∧ q.2.1 ∉ Gs)
    (hW : ∀ z, W z → z ∈ Gs ∨ InUse m Ps z ∨ ¬ Mem.valid_block m z ∨ out z)
    (hout : ∀ z, out z → Mem.valid_block m z → z ∉ sparseWGlobs ∧ ¬ InUse m sparseSlots z)
    (hch : ∀ p ∈ Ps, ∃ c b c' b', p.At m c b ∧ p.At m' c' b' ∧ ((c' = c ∧ b' = b) ∨ ¬ Mem.valid_block m b'))
    (hfresh : ∀ p ∈ Ps, ∀ q ∈ Ps, ∀ c c' z, 0 < c → 0 < c' → p.At m' c z → q.At m' c' z →
      ¬ Mem.valid_block m z → p = q)
    (hm1 : ∃ c b s k, MarksAt m' c b s k) (hm2 : ∃ c b s k, Sparse.Marks2.MarksAt m' c b s k)
    (hk : ∀ z, out z → Mem.valid_block m z → Keep m m' z) : sparseRep.Step m m' out := by
  have h := slots_step hw hu hGs hPs hGq hW hout hch hfresh
  refine ⟨hu.mono fun z hz => ?_, hv, ⟨h.1, fun z hz => hv z (hw.2.1 z hz), hm1, hm2⟩, h.2, hk⟩
  rcases hW z hz with h | h | h | h
  · exact .inr (.inl (hGs z h))
  · exact .inr (.inr (.inl (inUse_sub h hPs)))
  · exact .inr (.inr (.inr h))
  · exact .inl h

/-- The first mark invariant survives a call that leaves `vmark1` alone. -/
theorem marks1_keep {m m' : mem} (hw : sparseWork m) {W out : block → Prop} (hu : Unch m m' W)
    {Gs : List block} {Ps : List Slot} (hGs : ∀ z ∈ Gs, z ∈ sparseWGlobs)
    (hPs : ∀ p ∈ Ps, p ∈ sparseSlots)
    (hW : ∀ z, W z → z ∈ Gs ∨ InUse m Ps z ∨ ¬ Mem.valid_block m z ∨ out z)
    (hout : ∀ z, out z → Mem.valid_block m z → z ∉ sparseWGlobs ∧ ¬ InUse m sparseSlots z)
    (hP : (VM1, VM1S, 2) ∉ Ps) (h1 : VM1 ∉ Gs) (h2 : VM1S ∉ Gs) (h3 : VM1V ∉ Gs) :
    ∃ c b s k, MarksAt m' c b s k := by
  obtain ⟨c, b, s, k, hM⟩ := hw.2.2.1
  obtain ⟨k1, k2, k3⟩ := keep_pair hw hGs hPs hW hout (q := (VM1, VM1S, 2)) (by simp [sparseSlots])
    hP h1 h2
  have k4 : ¬ W VM1V := by
    intro hwz
    have hG : VM1V ∈ sparseWGlobs := by decide
    have hL := wglobs_L hG
    rcases hW _ hwz with h | h | h | h
    · exact h3 h
    · exact hw.1.notin _ (inUse_sub h hPs) hL
    · exact h (hw.2.1 _ hL)
    · exact (hout _ h (hw.2.1 _ hL)).1 hG
  exact ⟨c, b, s, k, hM.unch hu k1 k2 k4 fun hc => k3 c b hc hM.dyn⟩

/-- The second mark invariant survives a call that leaves `vmark2` alone. -/
theorem marks2_keep {m m' : mem} (hw : sparseWork m) {W out : block → Prop} (hu : Unch m m' W)
    {Gs : List block} {Ps : List Slot} (hGs : ∀ z ∈ Gs, z ∈ sparseWGlobs)
    (hPs : ∀ p ∈ Ps, p ∈ sparseSlots)
    (hW : ∀ z, W z → z ∈ Gs ∨ InUse m Ps z ∨ ¬ Mem.valid_block m z ∨ out z)
    (hout : ∀ z, out z → Mem.valid_block m z → z ∉ sparseWGlobs ∧ ¬ InUse m sparseSlots z)
    (hP : (VM2, VM2S, 2) ∉ Ps) (h1 : VM2 ∉ Gs) (h2 : VM2S ∉ Gs) (h3 : VM2V ∉ Gs) :
    ∃ c b s k, Sparse.Marks2.MarksAt m' c b s k := by
  obtain ⟨c, b, s, k, hM⟩ := hw.2.2.2
  obtain ⟨k1, k2, k3⟩ := keep_pair hw hGs hPs hW hout (q := (VM2, VM2S, 2)) (by simp [sparseSlots])
    hP h1 h2
  have k4 : ¬ W VM2V := by
    intro hwz
    have hG : VM2V ∈ sparseWGlobs := by decide
    have hL := wglobs_L hG
    rcases hW _ hwz with h | h | h | h
    · exact h3 h
    · exact hw.1.notin _ (inUse_sub h hPs) hL
    · exact h (hw.2.1 _ hL)
    · exact (hout _ h (hw.2.1 _ hL)).1 hG
  exact ⟨c, b, s, k, hM.unch hu k1 k2 k4 fun hc => k3 c b hc hM.dyn⟩

/-- What the separation of a call's arguments gives for one of them. -/
theorem sep_z {m : mem} {bs : List block} (h : sparseRep.Sep m bs) {z : block} (hz : z ∈ bs) :
    Mem.valid_block m z ∧ z ∉ sparseGlobs ∧ ¬ InUse m sparseSlots z ∧
      (∀ {b}, InUse m sparseSlots b → z ≠ b) :=
  ⟨h.valid z hz, h.notGlobs z hz, h.notWork z hz, fun hb e => h.notWork z hz (e ▸ hb)⟩

theorem sep_out {m : mem} {bs : List block} (h : sparseRep.Sep m bs) {z : block} (hz : z ∈ bs) :
    z ∉ sparseWGlobs ∧ ¬ InUse m sparseSlots z :=
  ⟨fun hG => h.notGlobs z hz (List.mem_append_left _ hG), h.notWork z hz⟩

end NautyVerified.Proofs.Dispatch
