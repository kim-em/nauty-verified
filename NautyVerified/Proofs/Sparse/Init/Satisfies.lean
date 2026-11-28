import NautyVerified.Proofs.Sparse.Init.Syntax
import NautyVerified.Proofs.Sparse.Updatecan.Satisfies

/-!
# `init_sg` meets its specification

`initSpec`: called by `nauty()` with `options->getcanon = 1`, the input
graph `G` at `gin` (`SparseGraphAt`, of which `init_sg` reads only `nv` and
`nde`) and at `hin` a `sparsegraph` as `SG_INIT` leaves it (`SgInit`: `v`,
`d`, `e`, `w` `NULL` and the capacities 0), `init_sg` runs
`SG_ALLOC(*hin, n, nde)`, which allocates three new zero-filled blocks
(`FieldDyn` with capacities `n`, `n`, `nde`), sets `hin->nv = n` and
`hin->nde = nde`, and writes `*status = 0`. The struct then holds
HexGraphIso's `Graph.blank` with no meaningful rows (`CanonAt … blank 0 …`),
which is what `updatecan_sg` and `testcanlab_sg` start from; no zero fill
is needed for that.

With `nde = 0` the third `DYNALLOC1` does nothing: `canong.e` stays `NULL`
(`cePtr`), its capacity 0, and the facts about the new `e` block hold only
when there are edges.
-/

namespace NautyVerified.Proofs.Sparse.Init

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse NautyVerified.Program
open NautyVerified.Proofs.Alloc (fld FieldDyn FieldFrame Apart wp_dynalloc1F eval_fld lval_fld)
open NautyVerified.Proofs.Sparse.Updatecan (fofs_int)
open Hex.GraphIso.Nauty.Sparse (Graph Rows)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

abbrev F := sparse.fn.init_sg

/-- Byte `k` of the struct at `cofs`, as a pointer offset. -/
abbrev fo (cofs : ptrofs) (k : Int) : ptrofs := Ptrofs.add cofs (Ptrofs.repr (zOfInt k))

/-- The `sparsegraph` at `cofs` in `bc` as `SG_INIT` leaves it, with writable fields. -/
structure SgInit (m : mem) (bc : block) (cofs : ptrofs) : Prop where
  ndeW : Mem.valid_access m .Mint64 bc (fofs cofs 0) .Writable
  nvW : Mem.valid_access m .Mint32 bc (fofs cofs 16) .Writable
  w : Mem.load .Mint64 m bc (fofs cofs 40) = some Vnullptr
  v : Mem.load .Mint64 m bc (fofs cofs 8) = some Vnullptr
  d : Mem.load .Mint64 m bc (fofs cofs 24) = some Vnullptr
  e : Mem.load .Mint64 m bc (fofs cofs 32) = some Vnullptr
  vW : Mem.valid_access m .Mint64 bc (fofs cofs 8) .Writable
  dW : Mem.valid_access m .Mint64 bc (fofs cofs 24) .Writable
  eW : Mem.valid_access m .Mint64 bc (fofs cofs 32) .Writable
  vlen : Mem.load .Mint64 m bc (fofs cofs 48) = some (.Vlong (lr 0))
  dlen : Mem.load .Mint64 m bc (fofs cofs 56) = some (.Vlong (lr 0))
  elen : Mem.load .Mint64 m bc (fofs cofs 64) = some (.Vlong (lr 0))
  vlenW : Mem.valid_access m .Mint64 bc (fofs cofs 48) .Writable
  dlenW : Mem.valid_access m .Mint64 bc (fofs cofs 56) .Writable
  elenW : Mem.valid_access m .Mint64 bc (fofs cofs 64) .Writable

/-- The specification of `init_sg`. -/
def initSpec {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs) (bv : block)
    (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (gout : val) (bc : block)
    (cofs : ptrofs) (hout lab ptn active : val) (bo : block) (oofs : ptrofs) (bst : block)
    (stofs : ptrofs) (mv : val) : FunSpec where
  pre args m := args = [.Vptr bsg sofs, gout, .Vptr bc cofs, hout, lab, ptn, active, .Vptr bo oofs,
      .Vptr bst stofs, mv, .Vint (ir n)] ∧
    SparseGraphAt m bsg sofs G bv vo bd dofs be eo ∧ SgInit m bc cofs ∧
    intOfZ (Ptrofs.unsigned cofs) + 72 < 2 ^ 64 ∧
    Mem.load .Mint32 m bo (fofs oofs 0) = some (.Vint (ir 1)) ∧
    Mem.valid_access m .Mint32 bst (Ptrofs.unsigned stofs) .Writable ∧
    0 < n ∧ n < 2147483648 ∧ G.neighbors.size < 2147483648 ∧
    bc ≠ bsg ∧ bc ≠ bst
  post _ m t _ m' := t = E0 ∧ ∃ capV bV capD bD capE bE,
    FieldDyn m' bc (fo cofs 8) (fo cofs 48) 8 capV bV ∧
    FieldDyn m' bc (fo cofs 24) (fo cofs 56) 4 capD bD ∧
    FieldDyn m' bc (fo cofs 32) (fo cofs 64) 4 capE bE ∧
    n ≤ capV ∧ n ≤ capD ∧ G.neighbors.size ≤ capE ∧
    ¬ Mem.valid_block m bV ∧ ¬ Mem.valid_block m bD ∧
    (0 < G.neighbors.size → ¬ Mem.valid_block m bE) ∧
    bV ≠ bD ∧ (0 < G.neighbors.size → bV ≠ bE) ∧ (0 < G.neighbors.size → bD ≠ bE) ∧
    CanonAt m' bc cofs (Graph.ofGraph G).blank 0 bV Ptrofs.zero bD Ptrofs.zero bE Ptrofs.zero ∧
    Mem.load .Mint32 m' bc (fofs cofs 16) = some (.Vint (ir n)) ∧
    Mem.load .Mint64 m' bc (fofs cofs 0) = some (.Vlong (lr G.neighbors.size)) ∧
    Mem.load .Mint32 m' bst (Ptrofs.unsigned stofs) = some (.Vint (ir 0)) ∧
    Mem.valid_access m' .Mint32 bst (Ptrofs.unsigned stofs) .Writable ∧
    Unch m m' (fun z => z = bc ∨ z = bst ∨ ¬ Mem.valid_block m z) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧ Alloc.Keep m m' bc ∧ Alloc.Keep m m' bst

def entryTemps (bsg : block) (sofs : ptrofs) (gout : val) (bc : block) (cofs : ptrofs)
    (hout lab ptn active : val) (bo : block) (oofs : ptrofs) (bst : block) (stofs : ptrofs)
    (mv : val) (n : Nat) : temp_env :=
  PTree.set sparse.id.n (.Vint (ir n)) (PTree.set sparse.id.m mv
    (PTree.set id.status (.Vptr bst stofs) (PTree.set id.options (.Vptr bo oofs)
      (PTree.set sparse.id.active active (PTree.set sparse.id.ptn ptn (PTree.set sparse.id.lab lab
        (PTree.set sparse.id.hout hout (PTree.set id.hin (.Vptr bc cofs)
          (PTree.set sparse.id.gout gout (PTree.set id.gin (.Vptr bsg sofs)
            (create_undef_temps F.fn_temps)))))))))))

set_option maxRecDepth 100000 in
theorem lval_getcanon (b : block) (o : ptrofs) :
    Exec.lvalOfField sge (Tstruct sparse.id.optionstruct noattr) sparse.id.getcanon (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt 0)), .Full) := rfl

/-- Fields at struct bytes `k1` and `k2` do not overlap. -/
theorem apart {cofs : ptrofs} (hw : intOfZ (Ptrofs.unsigned cofs) + 72 < 2 ^ 64) (chunk : memory_chunk)
    {k1 k2 : Int} (h1 : 0 ≤ k1) (h1' : k1 ≤ 64) (h2 : 0 ≤ k2) (h2' : k2 ≤ 64)
    (h : k1 + csize chunk ≤ k2 ∨ k2 + 8 ≤ k1) : Apart chunk (fofs cofs k1) (fo cofs k2) := by
  unfold Apart
  have e1 := fofs_int (sofs := cofs) (k := k1) (by omega) h1
  have e2 := fofs_int (sofs := cofs) (k := k2) (by omega) h2
  rw [e1, show Ptrofs.unsigned (fo cofs k2) = fofs cofs k2 from rfl, e2]
  omega

theorem SgInit.dyn {m : mem} {bc : block} {cofs : ptrofs} (h : SgInit m bc cofs)
    (hw : intOfZ (Ptrofs.unsigned cofs) + 72 < 2 ^ 64) (c : Nat) (b : block) :
    FieldDyn m bc (fo cofs 8) (fo cofs 48) c 0 b ∧ FieldDyn m bc (fo cofs 24) (fo cofs 56) c 0 b ∧
      FieldDyn m bc (fo cofs 32) (fo cofs 64) c 0 b :=
  ⟨⟨h.vlen, h.vlenW, h.vW, fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0),
      apart hw .Mint64 (by decide) (by decide) (by decide) (by decide) (by decide),
      fun h => absurd h (Nat.lt_irrefl 0), by omega, by omega, fun _ => h.v⟩,
   ⟨h.dlen, h.dlenW, h.dW, fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0),
      apart hw .Mint64 (by decide) (by decide) (by decide) (by decide) (by decide),
      fun h => absurd h (Nat.lt_irrefl 0), by omega, by omega, fun _ => h.d⟩,
   ⟨h.elen, h.elenW, h.eW, fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0),
      apart hw .Mint64 (by decide) (by decide) (by decide) (by decide) (by decide),
      fun h => absurd h (Nat.lt_irrefl 0), by omega, by omega, fun _ => h.e⟩⟩

/-- `do { ... } while (0)`. -/
theorem wp_once {f : function} {body : statement} {Q : Post} {e : env} {le : temp_env} {m : mem}
    (h : Wp xi sge f body { normal := Q.normal, cont := Q.normal, brk := Q.normal, ret := Q.ret } e le m) :
    Wp xi sge f (.Sloop body (Alloc.sk .Sbreak)) Q e le m := by
  refine wp_loop (I := fun _ t e' le' m' => t = E0 ∧ e' = e ∧ le' = le ∧ m' = m)
    (J := fun _ t e' le' m' => Q.normal t e' le' m') ?_ ?_ (n := 0) ⟨rfl, rfl, rfl, rfl⟩
  · rintro - t e' le' m' ⟨rfl, rfl, rfl, rfl⟩
    exact h
  · rintro - t e' le' m' hJ
    wp_step; wp_step
    apply wp_break
    simpa using hJ

theorem init_satisfies {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs) (bv : block)
    (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (gout : val) (bc : block)
    (cofs : ptrofs) (hout lab ptn active : val) (bo : block) (oofs : ptrofs) (bst : block)
    (stofs : ptrofs) (mv : val) :
    Satisfies xi sge (.Internal F) (initSpec G bsg sofs bv vo bd dofs be eo gout bc cofs hout lab ptn
      active bo oofs bst stofs mv) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bsg sofs gout bc cofs hout lab ptn active bo oofs bst stofs mv n ∧
      m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bsg sofs gout bc cofs hout lab ptn active bo oofs bst stofs mv n, m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hgr, hsi, hw, hgc, hstW, hn0, hn31, hd31, hcg, hcs⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [sparse.fn.init_sg.fn_body_eq, body_eq]
    let le0 := entryTemps bsg sofs gout bc cofs hout lab ptn active bo oofs bst stofs mv n
    have hbsg : Mem.valid_block m bsg :=
      Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ hgr.nv)
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [eval_fld (by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      (lval_getcanon _ _) rfl hgc]
    simp only [typeof, cop]
    rw [show Int.eq (ir 1) Int.zero = false from rfl]
    simp only [Bool.not_false, ite_true]
    have hst0 : Mem.valid_block m bst := Alloc.valid_of_access hstW
    -- `sg = (sparsegraph*)gin; sh = (sparsegraph*)hin;`
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop]
    let le2 := PTree.set id.sh (.Vptr bc cofs) (PTree.set id.sg (.Vptr bsg sofs) le0)
    have hsh2 : PTree.get id.sh le2 = some (.Vptr bc cofs) := temps_gss _ _ _
    have hsg2 : PTree.get id.sg le2 = some (.Vptr bsg sofs) := by
      simp (config := {decide := true}) only [le2, temps_gso, temps_gss]
    have hstat2 : PTree.get id.status le2 = some (.Vptr bst stofs) := by
      simp (config := {decide := true}) only [le2, le0, entryTemps, temps_gso, temps_gss]
    have hV0 := (hsi.dyn hw 8 bc).1
    have hD0 := (hsi.dyn hw 4 bc).2.1
    have hE0 := (hsi.dyn hw 4 bc).2.2
    have nS : ∀ {mm : mem} {b' z : block}, Mem.valid_block mm z → z ≠ bc →
        ¬ (z = bc ∨ (0 < 0 ∧ z = bc) ∨ (¬ Mem.valid_block mm b' ∧ z = b')) := by
      rintro mm b' z hv hne (h | ⟨h, -⟩ | ⟨h1, h2⟩)
      · exact hne h
      · exact Nat.lt_irrefl 0 h
      · exact h1 (h2 ▸ hv)
    have nS0 : ∀ {z : block}, z ≠ bc → ¬ (z = bc ∨ (0 < 0 ∧ z = bc)) := by
      rintro z hne (h | ⟨h, -⟩)
      · exact hne h
      · exact Nat.lt_irrefl 0 h
    have hcN : ∀ m', Cfrontend.Cop.sem_cast (.Vint (ir n)) (typeof (fld id.sg id.sid sparse.id.nv tint))
        tulong m' = some (.Vlong (lr n)) := fun _ => by
      simp only [typeof, cop, cast_int_long_ir (a := n) ⟨by omega, by omega⟩]
    have hcE : ∀ m', Cfrontend.Cop.sem_cast (.Vlong (lr G.neighbors.size))
        (typeof (fld id.sg id.sid sparse.id.nde tulong)) tulong m' = some (.Vlong (lr G.neighbors.size)) :=
      fun _ => by simp only [typeof, cop]
    wp_step
    apply wp_once
    wp_step
    refine wp_dynalloc1F (p := id.sh) hsh2 (lval_v _ _) (lval_vlen _ _) (c := 8) rfl hV0
      (fun m' hu => eval_fld hsg2 (lval_nv _ _) rfl (by rw [hu.load _ _ _ (nS0 hcg.symm)]; exact hgr.nv))
      hcN hn31 (by omega) (by decide) (by decide) ?_
    intro le1 m1 capV bV hV1 hnV hu1 hf1 hor1 hg1 hle1
    simp only [E0_append]
    have hVp : 0 < capV := by omega
    have hVnew : ¬ Mem.valid_block m bV := by
      rcases hor1 with ⟨h, -⟩ | ⟨h, -⟩
      · omega
      · exact h
    have hsh1 : PTree.get id.sh le1 = some (.Vptr bc cofs) := by
      rw [hle1 _ (by decide) (by decide)]; exact hsh2
    have hsg1 : PTree.get id.sg le1 = some (.Vptr bsg sofs) := by
      rw [hle1 _ (by decide) (by decide)]; exact hsg2
    have hD1 : FieldDyn m1 bc (fo cofs 24) (fo cofs 56) 4 0 bc :=
      hD0.frame hf1 (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (fun h => absurd h (Nat.lt_irrefl 0))
    have hE1 : FieldDyn m1 bc (fo cofs 32) (fo cofs 64) 4 0 bc :=
      hE0.frame hf1 (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (fun h => absurd h (Nat.lt_irrefl 0))
    have hnv1 : Mem.load .Mint32 m1 bsg (fofs sofs 16) = some (.Vint (ir n)) := by
      rw [hu1.load _ _ _ (nS hbsg hcg.symm)]; exact hgr.nv
    wp_step
    refine wp_dynalloc1F (p := id.sh) hsh1 (lval_d _ _) (lval_dlen _ _) (c := 4) rfl hD1
      (fun m' hu => eval_fld hsg1 (lval_nv _ _) rfl (by rw [hu.load _ _ _ (nS0 hcg.symm)]; exact hnv1))
      hcN hn31 (by omega) (by decide) (by decide) ?_
    intro le2' m2 capD bD hD2 hnD hu2 hf2 hor2 hg2 hle2
    simp only [E0_append]
    have hDp : 0 < capD := by omega
    have hDnew : ¬ Mem.valid_block m1 bD := by
      rcases hor2 with ⟨h, -⟩ | ⟨h, -⟩
      · omega
      · exact h
    have hsh2' : PTree.get id.sh le2' = some (.Vptr bc cofs) := by
      rw [hle2 _ (by decide) (by decide)]; exact hsh1
    have hsg2' : PTree.get id.sg le2' = some (.Vptr bsg sofs) := by
      rw [hle2 _ (by decide) (by decide)]; exact hsg1
    have hE2 : FieldDyn m2 bc (fo cofs 32) (fo cofs 64) 4 0 bc :=
      hE1.frame hf2 (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (fun h => absurd h (Nat.lt_irrefl 0))
    have hV2 : FieldDyn m2 bc (fo cofs 8) (fo cofs 48) 8 capV bV :=
      hV1.after hf2 hu2 (fun h => absurd h (Nat.lt_irrefl 0))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
    have hbsg1 := hg1 _ hbsg
    have hnde2 : Mem.load .Mint64 m2 bsg (fofs sofs 0) = some (.Vlong (lr G.neighbors.size)) := by
      rw [hu2.load _ _ _ (nS hbsg1 hcg.symm), hu1.load _ _ _ (nS hbsg hcg.symm)]; exact hgr.nde
    refine wp_dynalloc1F (p := id.sh) hsh2' (lval_e _ _) (lval_elen _ _) (c := 4) rfl hE2
      (fun m' hu => eval_fld hsg2' (lval_nde _ _) rfl (by rw [hu.load _ _ _ (nS0 hcg.symm)]; exact hnde2))
      hcE hd31 (by omega) (by decide) (by decide) ?_
    intro le3 m3 capE bE hE3 hnE hu3 hf3 hor3 hg3 hle3
    have hEnew : 0 < capE → ¬ Mem.valid_block m2 bE := fun hEp => by
      rcases hor3 with ⟨h, -⟩ | ⟨h, -⟩
      · omega
      · exact h
    have hEz : G.neighbors.size = 0 → capE = 0 := fun h0 => by
      rcases hor3 with ⟨h, -⟩ | ⟨-, h, -⟩
      · exact h
      · omega
    have hV3 : FieldDyn m3 bc (fo cofs 8) (fo cofs 48) 8 capV bV :=
      hV2.after hf3 hu3 (fun h => absurd h (Nat.lt_irrefl 0))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
    have hD3 : FieldDyn m3 bc (fo cofs 24) (fo cofs 56) 4 capD bD :=
      hD2.after hf3 hu3 (fun h => absurd h (Nat.lt_irrefl 0))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))
    dsimp only
    have hsh3 : PTree.get id.sh le3 = some (.Vptr bc cofs) := by
      rw [hle3 _ (by decide) (by decide)]; exact hsh2'
    have hsg3 : PTree.get id.sg le3 = some (.Vptr bsg sofs) := by
      rw [hle3 _ (by decide) (by decide)]; exact hsg2'
    have hstat3 : PTree.get id.status le3 = some (.Vptr bst stofs) := by
      rw [hle3 _ (by decide) (by decide), hle2 _ (by decide) (by decide), hle1 _ (by decide) (by decide)]
      exact hstat2
    have hbsg2 := hg2 _ hbsg1
    have hnv3 : Mem.load .Mint32 m3 bsg (fofs sofs 16) = some (.Vint (ir n)) := by
      rw [hu3.load _ _ _ (nS hbsg2 hcg.symm), hu2.load _ _ _ (nS hbsg1 hcg.symm)]; exact hnv1
    have hnde3 : Mem.load .Mint64 m3 bsg (fofs sofs 0) = some (.Vlong (lr G.neighbors.size)) := by
      rw [hu3.load _ _ _ (nS hbsg2 hcg.symm)]; exact hnde2
    have hnvW3 : Mem.valid_access m3 .Mint32 bc (fofs cofs 16) .Writable :=
      hf3.access _ _ _ (hf2.access _ _ _ (hf1.access _ _ _ hsi.nvW))
    obtain ⟨m4, hst4⟩ := Mem.valid_access_store _ _ _ _ (.Vint (ir n)) hnvW3
    wp_step; wp_step; wp_step
    apply wp_assign_eval
    rw [lval_fld hsh3 (lval_nv _ _), eval_fld hsg3 (lval_nv _ _) rfl hnv3]
    simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
    rw [show Ptrofs.unsigned (Ptrofs.add cofs (Ptrofs.repr (zOfInt 16))) = fofs cofs 16 from rfl, hst4]
    simp only [E0_append]
    have hndeW4 := Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _
      (hf3.access _ _ _ (hf2.access _ _ _ (hf1.access _ _ _ hsi.ndeW)))
    obtain ⟨m5, hst5⟩ := Mem.valid_access_store _ _ _ _ (.Vlong (lr G.neighbors.size)) hndeW4
    have hnde4 : Mem.load .Mint64 m4 bsg (fofs sofs 0) = some (.Vlong (lr G.neighbors.size)) := by
      rw [Mem.load_store_other _ _ _ _ _ _ hst4 _ _ _ (.inl hcg.symm)]; exact hnde3
    wp_step; wp_step
    apply wp_assign_eval
    rw [lval_fld hsh3 (lval_nde _ _), eval_fld hsg3 (lval_nde _ _) rfl hnde4]
    simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
    rw [show Ptrofs.unsigned (Ptrofs.add cofs (Ptrofs.repr (zOfInt 0))) = fofs cofs 0 from rfl, hst5]
    simp only [E0_append]
    have hbst1 := hg1 _ hst0
    have hbst2 := hg2 _ hbst1
    have hstW5 : Mem.valid_access m5 .Mint32 bst (Ptrofs.unsigned stofs) .Writable :=
      Mem.store_valid_access_1 _ _ _ _ _ _ hst5 _ _ _ _ (Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _
        (hu3.access _ _ _ _ (nS hbst2 hcs.symm) (hu2.access _ _ _ _ (nS hbst1 hcs.symm)
          (hu1.access _ _ _ _ (nS hst0 hcs.symm) hstW))))
    obtain ⟨m6, hst6⟩ := Mem.valid_access_store _ _ _ _ (.Vint (ir 0)) hstW5
    wp_step; wp_step
    apply wp_assign_eval
    simp only [Exec.evalLvalue, Exec.evalExpr, hstat3, typeof, cop, Exec.assignLoc,
      Cfrontend.Ctypes.access_mode, Mem.storev]
    rw [show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl, hst6]
    dsimp only
    have hu6 : Unch m5 m6 (· = bst) := Unch.store hst6 rfl
    have hcs' : ¬ bc = bst := hcs
    have hVs : bV ≠ bst := fun h => hVnew (h ▸ hst0)
    have hDs : bD ≠ bst := fun h => hDnew (h ▸ hbst1)
    have hEs : 0 < capE → bE ≠ bst := fun hEp h => hEnew hEp (h ▸ hbst2)
    have hV6 : FieldDyn m6 bc (fo cofs 8) (fo cofs 48) 8 capV bV :=
      ((hV3.store hst4 (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide)) (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))).store hst5 (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide)) (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))).unch hu6 hcs' (fun _ => hVs)
    have hD6 : FieldDyn m6 bc (fo cofs 24) (fo cofs 56) 4 capD bD :=
      ((hD3.store hst4 (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide)) (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))).store hst5 (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide)) (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))).unch hu6 hcs' (fun _ => hDs)
    have hE6 : FieldDyn m6 bc (fo cofs 32) (fo cofs 64) 4 capE bE :=
      ((hE3.store hst4 (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide)) (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))).store hst5 (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide)) (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))).unch hu6 hcs' hEs
    have hw48 : intOfZ (Ptrofs.unsigned cofs) + 48 < 2 ^ 64 := by omega
    have hw6 : Mem.load .Mint64 m6 bc (fofs cofs 40) = some Vnullptr := by
      rw [hu6.load _ _ _ hcs']
      refine Updatecan.load_field_other hw48 (by decide) (by decide) (by decide) (by decide)
        (.inr (by decide)) hst5 ?_
      refine Updatecan.load_field_other hw48 (by decide) (by decide) (by decide) (by decide)
        (.inr (by decide)) hst4 ?_
      rw [hf3.load _ _ (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide)) (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide)), hf2.load _ _ (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide)) (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide)), hf1.load _ _ (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide)) (apart hw _ (by decide) (by decide) (by decide) (by decide) (by decide))]; exact hsi.w
    have hbV1 : Mem.valid_block m1 bV := (hV1.mal hVp).valid
    have hbD2 : Mem.valid_block m2 bD := (hD2.mal hDp).valid
    have hnb : ∀ {mm : mem} {b' : block}, (∀ z, Mem.valid_block m z → Mem.valid_block mm z) →
        ∀ z, (z = bc ∨ (0 < 0 ∧ z = bc) ∨ (¬ Mem.valid_block mm b' ∧ z = b')) →
          (z = bc ∨ z = bst ∨ ¬ Mem.valid_block m z) := by
      rintro mm b' hg z (h | ⟨h, -⟩ | ⟨h1, rfl⟩)
      · exact .inl h
      · exact absurd h (Nat.lt_irrefl 0)
      · exact .inr (.inr fun h => h1 (hg _ h))
    obtain ⟨vv, hvv⟩ := Alloc.malloced_array (hV6.mal hVp) .Mint64 8 rfl rfl n (Nat.mul_le_mul_left 8 hnV)
    obtain ⟨dv, hdv⟩ := Alloc.malloced_array (hD6.mal hDp) .Mint32 4 rfl rfl n (Nat.mul_le_mul_left 4 hnD)
    obtain ⟨ev, hev⟩ : ∃ ev, ArrayAt m6 .Mint32 bE (intOfZ (Ptrofs.unsigned Ptrofs.zero)) ev
        G.neighbors.size := by
      rcases Nat.eq_zero_or_pos G.neighbors.size with h0 | hp
      · rw [h0]; exact ⟨fun _ => Vundef, arrayAt_empty _ _ _ _ _⟩
      · exact Alloc.malloced_array (hE6.mal (by omega)) .Mint32 4 rfl rfl G.neighbors.size
          (Nat.mul_le_mul_left 4 hnE)
    have hEe : Mem.load .Mint64 m6 bc (fofs cofs 32) = some (cePtr G.neighbors.size bE Ptrofs.zero) := by
      rcases Nat.eq_zero_or_pos G.neighbors.size with h0 | hp
      · rw [h0, cePtr_zero]; exact hE6.null (hEz h0)
      · rw [cePtr_pos hp]; exact hE6.ptr (by omega)
    have hbsz : (Graph.ofGraph G).blank.neighbors.size = G.neighbors.size := by
      simp [Graph.blank, Graph.ofGraph]
    have hb0 : base (Graph.ofGraph G).blank 0 = 0 := rfl
    refine ⟨m6, Isautom.free_empty _, rfl, capV, bV, capD, bD, capE, bE, hV6, hD6, hE6, hnV, hnD, hnE,
      hVnew, fun h => hDnew (hg1 _ h), fun hp h => hEnew (by omega) (hg2 _ (hg1 _ h)),
      fun h => hDnew (h ▸ hbV1), fun hp h => hEnew (by omega) (h ▸ hg2 _ hbV1),
      fun hp h => hEnew (by omega) (h ▸ hbD2),
      ?_, ?_, ?_, Mem.load_store_same _ _ _ _ _ _ hst6,
      Mem.store_valid_access_1 _ _ _ _ _ _ hst6 _ _ _ _ hstW5, ?_, ?_, ?_, ?_⟩
    · exact
        { ndeW := hu6.access _ _ _ _ hcs' (Mem.store_valid_access_1 _ _ _ _ _ _ hst5 _ _ _ _ hndeW4)
          v := hV6.ptr hVp
          nvW := hu6.access _ _ _ _ hcs' (Mem.store_valid_access_1 _ _ _ _ _ _ hst5 _ _ _ _
            (Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _ hnvW3))
          d := hD6.ptr hDp
          e := by rw [hbsz]; exact hEe
          w := hw6
          rows := ⟨vv, dv, ev, hvv, hdv, by rw [hbsz]; exact hev,
            ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
              fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (by rw [hb0]; exact Nat.not_lt_zero _),
              by rw [hb0]; exact Nat.zero_le _, by rw [hbsz]; exact hd31,
              fun _ h => absurd h (by rw [hb0]; exact Nat.not_lt_zero _)⟩⟩ }
    · rw [hu6.load _ _ _ hcs']
      refine Updatecan.load_field_other hw48 (by decide) (by decide) (by decide) (by decide)
        (.inr (by decide)) hst5 ?_
      rw [Mem.load_store_same _ _ _ _ _ _ hst4]; rfl
    · rw [hu6.load _ _ _ hcs', Mem.load_store_same _ _ _ _ _ _ hst5]; rfl
    · exact ((((((hu1.mono (hnb fun _ h => h)).trans (hu2.mono (hnb hg1))).trans
        (hu3.mono (hnb fun z h => hg2 _ (hg1 _ h)))).trans (Unch.store hst4 (.inl rfl))).trans
        (Unch.store hst5 (.inl rfl))).trans (hu6.mono fun z h => .inr (.inl h)))
    · intro z h
      exact Mem.store_valid_block_1 _ _ _ _ _ _ hst6 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hst5 _
        (Mem.store_valid_block_1 _ _ _ _ _ _ hst4 _ (hg3 _ (hg2 _ (hg1 _ h)))))
    · exact ((((hf1.keep.trans hf2.keep).trans hf3.keep).trans
        (Alloc.Keep.store hst4 (by simp only [fofs, intOfZ_Ptrofs_unsigned]; omega))).trans
        (Alloc.Keep.store hst5 (by simp only [fofs, intOfZ_Ptrofs_unsigned]; omega))).trans
        (Alloc.Keep.unch hu6 hcs')
    · exact (((((Alloc.Keep.unch hu1 (nS hst0 hcs.symm)).trans (Alloc.Keep.unch hu2 (nS hbst1 hcs.symm))).trans
        (Alloc.Keep.unch hu3 (nS hbst2 hcs.symm))).trans
        (Alloc.Keep.unch (Unch.store (S := (· = bc)) hst4 rfl) (fun h => hcs h.symm))).trans
        (Alloc.Keep.unch (Unch.store (S := (· = bc)) hst5 rfl) (fun h => hcs h.symm))).trans
        (Alloc.Keep.store hst6 (by simp only [intOfZ_Ptrofs_unsigned]; omega))

end NautyVerified.Proofs.Sparse.Init
