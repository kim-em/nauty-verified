import NautyVerified.Proofs.Sparse.Distvals.Search
import NautyVerified.Proofs.Alloc.Dyn3

/-!
# `distvals` meets its specification

`distvalsSpec`: called on a sparse graph `G` (`SparseGraphAt`, the
`sparsegraph *` itself), a vertex `v0 < n` and an array `dist` of `n`
`int`s, nausparse.c's `distvals` leaves `dist` holding HexGraphIso's
`Sparse.distvals (ofGraph G) v0`. It uses `work4` as the queue, reallocated
by `DYNALLOC1` to at least `n` entries (`refine_sg` has already allocated
it, so there the allocation does nothing); nothing else changes. Its
block and `find_funct_ptr` fact are `Refine.Block.distvals` and
`Refine.funct_distvals`.

The C and HexGraphIso's loop differ in three ways that do not change the
result: the C reads `dist[i] + 1` at each new vertex where HexGraphIso
computes it once per dequeued vertex (`dist[i]` does not change while `i`'s
row is scanned, `scan_keep`); the queue's entries at and above `tail` differ
(neither reads them); and HexGraphIso bounds its loop by `n` iterations,
which suffices since `head` grows by one per iteration and stays below
`tail ≤ n` (`run (n - head)` is the invariant).
-/

namespace NautyVerified.Proofs.Sparse.Distvals

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse NautyVerified.Program
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat)
open Hex.GraphIso.Nauty.Sparse (Graph distvals)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

/-- The caller's blocks. -/
def Ext (bsg bv bd be bD : block) (z : block) : Prop := z = bsg ∨ z = bv ∨ z = bd ∨ z = be ∨ z = bD

/-- The specification of `distvals`. -/
def distvalsSpec {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs) (bv : block)
    (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (v0 : Nat) (bD : block)
    (Dofs : ptrofs) (capQ : Nat) (bQ : block) : FunSpec where
  pre args m := args = [.Vptr bsg sofs, .Vint (ir v0), .Vptr bD Dofs, .Vint (ir n)] ∧
    SparseGraphAt m bsg sofs G bv vo bd dofs be eo ∧
    (∃ dv, ArrayAt m .Mint32 bD (intOfZ (Ptrofs.unsigned Dofs)) dv n) ∧
    v0 < n ∧ n < 2147483648 ∧ Alloc.DynAt m Block.work4 Block.work4Sz 4 capQ bQ ∧
    (∀ z, Ext bsg bv bd be bD z → Mem.valid_block m z ∧ z ≠ Block.work4 ∧ z ≠ Block.work4Sz ∧
      (0 < capQ → z ≠ bQ)) ∧
    bD ≠ bsg ∧ bD ≠ bv ∧ bD ≠ bd ∧ bD ≠ be
  post _ m t _ m' := t = E0 ∧
    ArrayAt m' .Mint32 bD (intOfZ (Ptrofs.unsigned Dofs)) (ints (distvals (Graph.ofGraph G) v0)) n ∧
    Alloc.Keep m m' bD ∧ DOut m m' bD Dofs n ∧
    ∃ capQ' bQ', Alloc.DynAt m' Block.work4 Block.work4Sz 4 capQ' bQ' ∧ n ≤ capQ' ∧
      ((capQ' = capQ ∧ bQ' = bQ) ∨ ¬ Mem.valid_block m bQ') ∧
      Unch m m' (fun z => z = bD ∨ z = Block.work4 ∨ z = Block.work4Sz ∨ (0 < capQ ∧ z = bQ) ∨
        (¬ Mem.valid_block m bQ' ∧ z = bQ')) ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z)

def entryTemps (bsg : block) (sofs : ptrofs) (v0 : Nat) (bD : block) (Dofs : ptrofs) (n : Nat) :
    temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.dist (.Vptr bD Dofs)
    (PTree.set id.v0 (.Vint (ir v0)) (PTree.set id.g (.Vptr bsg sofs)
      (create_undef_temps F.fn_temps))))

/-- Reading field `f` (at byte `k`) of the struct a `sparsegraph *` temporary points to. -/
theorem eval_sgFieldS {e : env} {le : temp_env} {m : mem} {p f : ident} {ty : Cfrontend.Ctypes.type}
    {chunk : memory_chunk} {bsg : block} {sofs : ptrofs} {k : Int} {x : val}
    (hp : Lib.Maps.PTree.get p le = some (.Vptr bsg sofs))
    (hlv : Exec.lvalOfField sge sgTy f (.Vptr bsg sofs) =
      some (bsg, Ptrofs.add sofs (Ptrofs.repr (zOfInt k)), .Full))
    (hmode : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hld : Mem.load chunk m bsg (fofs sofs k) = some x) :
    Exec.evalExpr sge e le m (sgFieldS p f ty) = some x := by
  simp only [Exec.evalExpr, hp, typeof, cop, Exec.derefLoc,
    show Cfrontend.Ctypes.access_mode sgTy = .By_copy from rfl, hlv, hmode, Mem.loadv]
  exact hld

/-- `SG_VDE(g, v, d, e)`. -/
theorem wp_vde {Q : Post} {le : temp_env} {m : mem} {bsg : block} {sofs : ptrofs}
    {bv : block} {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs}
    (hp : PTree.get id.g le = some (.Vptr bsg sofs))
    (hv : Mem.load .Mint64 m bsg (fofs sofs 8) = some (.Vptr bv vo))
    (hd : Mem.load .Mint64 m bsg (fofs sofs 24) = some (.Vptr bd dofs))
    (he : Mem.load .Mint64 m bsg (fofs sofs 32) = some (.Vptr be eo))
    (hQ : Q.normal E0 empty_env
      (PTree.set id.e (.Vptr be eo) (PTree.set id.d (.Vptr bd dofs) (PTree.set id.v (.Vptr bv vo) le))) m) :
    Wp xi sge F vde Q empty_env le m := by
  let le1 := PTree.set id.e (.Vptr be eo) (PTree.set id.d (.Vptr bd dofs) (PTree.set id.v (.Vptr bv vo) le))
  refine wp_loop (I := fun _ t e' le' m' => t = E0 ∧ e' = empty_env ∧ le' = le ∧ m' = m)
    (J := fun _ t e' le' m' => t = E0 ∧ e' = empty_env ∧ le' = le1 ∧ m' = m) ?_ ?_ (n := 0)
    ⟨rfl, rfl, rfl, rfl⟩
  · rintro - t e' le' m' ⟨rfl, rfl, rfl, hm⟩
    subst m'
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_sgFieldS hp (lval_v _ _) rfl hv]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_sgFieldS (by rw [temps_gso _ _ (by decide)]; exact hp) (lval_d _ _) rfl hd]
    wp_step; wp_step
    apply wp_set_eval
    rw [eval_sgFieldS (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hp)
      (lval_e _ _) rfl he]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro - t e' le' m' ⟨rfl, rfl, rfl, hm⟩
    subst m'
    wp_step; wp_step
    apply wp_break
    simpa only [E0_append] using hQ

theorem distvals_satisfies {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs)
    (bv : block) (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (v0 : Nat)
    (bD : block) (Dofs : ptrofs) (capQ : Nat) (bQ : block) :
    Satisfies xi sge (.Internal F) (distvalsSpec G bsg sofs bv vo bd dofs be eo v0 bD Dofs capQ bQ) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bsg sofs v0 bD Dofs n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bsg sofs v0 bD Dofs n, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩,
      rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hgr, ⟨dv, hdarr⟩, hv0n, hn31, hDW, hsep, hDs, hDv, hDd, hDe⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [sparse.fn.distvals.fn_body_eq, body_eq]
    let le0 := entryTemps bsg sofs v0 bD Dofs n
    have hext : ∀ z, Ext bsg bv bd be bD z → Mem.valid_block m z ∧ z ≠ Block.work4 ∧
        z ≠ Block.work4Sz ∧ (0 < capQ → z ≠ bQ) := hsep
    wp_step
    refine wp_vde (bsg := bsg) (sofs := sofs)
      (by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      hgr.v hgr.d hgr.e ?_
    let leV := PTree.set id.e (.Vptr be eo) (PTree.set id.d (.Vptr bd dofs) (PTree.set id.v (.Vptr bv vo) le0))
    have hnV : PTree.get id.n leV = some (.Vint (ir n)) := by
      simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss]
    wp_step
    refine Alloc.wp_dynalloc1 (E := NautyEnv.sparse) find_work4Sz find_work4 rfl hDW hnV hn31
      (show 4 * n < 2 ^ 62 by omega) ?_
    intro le1 m1 capQ1 bQ1 hDW1 hnQ hu1 hor1 hg1 ho1
    have hcQ1 : 0 < capQ1 := by omega
    have hnot1 : ∀ z, Ext bsg bv bd be bD z → ¬ (z = Block.work4Sz ∨ z = Block.work4 ∨
        (0 < capQ ∧ z = bQ) ∨ (¬ Mem.valid_block m bQ1 ∧ z = bQ1)) := fun z hz =>
      Alloc.not_dynSet (hext z hz).1 (hext z hz).2.2.1 (hext z hz).2.1 (hext z hz).2.2.2
    have hneQ1 : ∀ z, Ext bsg bv bd be bD z → z ≠ bQ1 := fun z hz =>
      Alloc.ne_new hor1 (hext z hz).1 (hext z hz).2.2.2 hcQ1
    obtain ⟨qv, hqarr⟩ := Alloc.malloced_array (hDW1.mal hcQ1) .Mint32 4 rfl rfl n
      (Nat.mul_le_mul_left 4 hnQ)
    have hdistV : PTree.get id.dist leV = some (.Vptr bD Dofs) := by
      simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss]
    have hv0V : PTree.get id.v0 leV = some (.Vint (ir v0)) := by
      simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss]
    have hdarr1 := hdarr.unch hu1 (hnot1 bD (by simp [Ext]))
    have hget1 : ∀ x, x ≠ idOf 703 → x ≠ idOf 704 → PTree.get x le1 = PTree.get x leV := ho1
    wp_step
    refine wp_fill (by rw [hget1 _ (by decide) (by decide)]; exact hdistV)
      (by rw [hget1 _ (by decide) (by decide)]; exact hnV) hn31 hdarr1 ?_
    intro le2 m2 hda2 hu2 hout2 hk2 hg2 ho2
    have hbQ1D : bQ1 ≠ bD := fun h => hneQ1 bD (by simp [Ext]) h.symm
    have hgr2 : SparseGraphAt m2 bsg sofs G bv vo bd dofs be eo :=
      (hgr.unch hu1 (hnot1 bsg (by simp [Ext])) (hnot1 bv (by simp [Ext])) (hnot1 bd (by simp [Ext]))
        (hnot1 be (by simp [Ext]))).unch hu2 (fun h => hDs h.symm) (fun h => hDv h.symm)
        (fun h => hDd h.symm) (fun h => hDe h.symm)
    have hW4D : Block.work4 ≠ bD := fun h => (hext bD (by simp [Ext])).2.1 h.symm
    have hwptr2 : Mem.load .Mint64 m2 Block.work4 (zOfInt 0) = some (.Vptr bQ1 Ptrofs.zero) := by
      rw [hu2.load _ _ _ hW4D]; exact hDW1.ptr hcQ1
    have hqarr2 := hqarr.unch hu2 hbQ1D
    have hget2 : ∀ x, x ≠ id.i → x ≠ idOf 703 → x ≠ idOf 704 → PTree.get x le2 = PTree.get x leV :=
      fun x a b c => by rw [ho2 x a, hget1 x b c]
    have hc : SCtx m2 le2 G bv vo bd dofs be eo bD Dofs bQ1 :=
      { hv := by rw [hget2 _ (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [leV, temps_gso, temps_gss]
        hd := by rw [hget2 _ (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [leV, temps_gso, temps_gss]
        he := by rw [hget2 _ (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [leV, temps_gss]
        hdist := by rw [hget2 _ (by decide) (by decide) (by decide)]; exact hdistV
        hn := by rw [hget2 _ (by decide) (by decide) (by decide)]; exact hnV
        varr := hgr2.varr, darr := hgr2.darr, earr := hgr2.earr, wptr := hwptr2, n31 := hn31
        sep := by
          rintro z (rfl | rfl | rfl | rfl)
          · exact ⟨hDv ∘ Eq.symm, hneQ1 _ (by simp [Ext])⟩
          · exact ⟨hDd ∘ Eq.symm, hneQ1 _ (by simp [Ext])⟩
          · exact ⟨hDe ∘ Eq.symm, hneQ1 _ (by simp [Ext])⟩
          · exact ⟨hW4D, fun h => (hDW1.bne hcQ1).2 h.symm⟩
        bDQ := hbQ1D.symm }
    refine wp_search hc (by rw [hget2 _ (by decide) (by decide) (by decide)]; exact hv0V)
      hv0n hda2 hqarr2 ?_
    intro le' m' hda' _ hu' hout' hkD' hkQ' hg' _
    have hDW' : Alloc.DynAt m' Block.work4 Block.work4Sz 4 capQ1 bQ1 :=
      hDW1.keep ((hu2.mono fun z hz => .inl hz).trans hu')
        (by rintro (h | h); exact hW4D h; exact (hDW1.bne hcQ1).2 h.symm)
        (by rintro (h | h)
            · exact (hext bD (by simp [Ext])).2.2.1 h.symm
            · exact (hDW1.bne hcQ1).1 h.symm)
        (fun _ => (Alloc.Keep.unch hu2 hbQ1D).trans hkQ')
    refine ⟨m', Isautom.free_empty m', rfl, hda',
      ((Alloc.Keep.unch hu1 (hnot1 bD (by simp [Ext]))).trans hk2).trans hkD',
      ((Outside.of_unch hu1 (hnot1 bD (by simp [Ext])) _ _).trans hout2).trans
        (hout'.trans (Outside.refl _ _ _ _)),
      capQ1, bQ1, hDW', hnQ, hor1, ?_, fun z h => hg' _ (hg2 _ (hg1 _ h))⟩
    refine (hu1.mono fun z hz => ?_).trans ((hu2.mono fun z hz => .inl hz).trans (hu'.mono fun z hz => ?_))
    · rcases hz with h | h | h | h
      · exact .inr (.inr (.inl h))
      · exact .inr (.inl h)
      · exact .inr (.inr (.inr (.inl h)))
      · exact .inr (.inr (.inr (.inr h)))
    · rcases hz with h | h
      · exact .inl h
      · rcases hor1 with ⟨h1, h2⟩ | hnv
        · exact .inr (.inr (.inr (.inl ⟨by omega, h.trans h2⟩)))
        · exact .inr (.inr (.inr (.inr ⟨hnv, h⟩)))

end NautyVerified.Proofs.Sparse.Distvals
