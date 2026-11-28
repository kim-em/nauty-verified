import NautyVerified.Proofs.Top.Ptn

/-!
# `nauty()`'s `g`, `canong` and `dispatch.init` (`tInit`)

`g = canong = NULL; initstatus = 0;` then `dispatch.init` is NULL for the
dense dispatch, so `initstatus` stays 0; `g` and `canong` become the
arguments; `doschreier` is 0. `wp_lset` is `wp_gset` for the local `initstatus`.

`wp_tInitG` is `tInit` for any dispatch `D`: with `init = NULL` the store at
`canong` is `D`'s blank store (`D.init_null` on `D.CanonPre`); otherwise the
call of `D.init` (`D.init_fn`, `initSpec`) makes it blank and sets
`initstatus` to 0. Both continue through `wp_tInitRest`.
-/

namespace NautyVerified.Proofs.Top

variable {bI : CompCert4Lean.Common.Values.block}

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search (FieldAt IntAt PtrAt)

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

/-- A store to a local variable `g` at the block `b`. -/
theorem wp_lset {ge : genv} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {g : ident}
    {ty : Cfrontend.Ctypes.type} {chunk : memory_chunk} {b : block}
    (hge : PTree.get g e = some (b, ty))
    (hacc : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hw : Mem.valid_access m chunk b (zOfInt 0) .Writable) {rhs : expr} {v : val}
    (hr : Exec.evalExpr ge e le m rhs = some v) (hrt : typeof rhs = ty)
    (hc : Cfrontend.Cop.sem_cast v ty ty m = some v) (hlr : Val.load_result chunk v = v)
    (hQ : ∀ m', FieldAt m' chunk b 0 v → Unch m m' (· = b) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ p, Mem.valid_access m chunk b (zOfInt 0) p → Mem.valid_access m' chunk b (zOfInt 0) p) →
      (∀ z o k p, Mem.perm m z o k p → Mem.perm m' z o k p) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar g ty) rhs) Q e le m := by
  obtain ⟨m', hst⟩ := Mem.valid_access_store _ _ _ _ v hw
  apply wp_assign_eval
  simp only [hr, hrt, hc]
  simp only [Exec.evalLvalue, Exec.lvalOfVar, hge, typeof, Exec.assignLoc, ↓reduceIte]
  simp only [hacc]
  simp only [Mem.storev, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]
  rw [hc]
  simp only [hst]
  exact hQ m' ⟨by rw [Mem.load_store_same _ _ _ _ _ _ hst, hlr],
    Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ hw⟩ (Unch.store hst rfl)
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)
    (fun p hp => Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ hp)
    (fun z o k p h => Mem.perm_store_1 _ _ _ _ _ _ hst _ _ _ _ h)

/-- `g`, `canong`, `initstatus` and `dispatch.init` (`tInit`). -/
theorem wp_tInit {Q : Post} {le : temp_env} {m : mem} {bg bc : block} {M : Nat}
    (hga : PTree.get dense.id.«g_arg» le = some (.Vptr bg Ptrofs.zero))
    (hca : PTree.get dense.id.«canong_arg» le = some (.Vptr bc Ptrofs.zero))
    (hD : DispatchAt m M)
    (hwg : Mem.valid_access m .Mint64 Search.Block.g (zOfInt 0) .Writable)
    (hwc : Mem.valid_access m .Mint64 Search.Block.canong (zOfInt 0) .Writable)
    (hfi : Mem.valid_access m .Mint32 bI (zOfInt 0) .Freeable)
    (hds : IntAt m Search.Block.doschreier 0)
    (hsep : bI ≠ Search.Block.g ∧ bI ≠ Search.Block.canong ∧ bI ≠ Search.Block.doschreier ∧
      bI ≠ Search.Block.dispatch)
    (hQ : ∀ le' m', FieldAt m' .Mint64 Search.Block.g 0 (.Vptr bg Ptrofs.zero) →
      FieldAt m' .Mint64 Search.Block.canong 0 (.Vptr bc Ptrofs.zero) → IntAt m' bI 0 →
      Mem.valid_access m' .Mint32 bI (zOfInt 0) .Freeable →
      Unch m m' (fun z => z = Search.Block.g ∨ z = Search.Block.canong ∨ z = bI) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 732 → PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tOrbits Q (nEnv bI) le' m') :
    Wp xi ge dense.fn.nauty Nauty.tInit Q (nEnv bI) le m := by
  have hwi : Mem.valid_access m .Mint32 bI (zOfInt 0) .Writable :=
    Mem.valid_access_implies _ _ _ _ _ _ hfi (.perm_F_any _)
  simp only [Nauty.tInit, Set.sk]
  wp_step; wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof]
  rw [show Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) tint
      (tptr Cfrontend.Ctypes.Tvoid) m = some nullArg from rfl]
  simp only []
  rw [show Cfrontend.Cop.sem_cast nullArg (tptr Cfrontend.Ctypes.Tvoid) (tptr tulong) m = some nullArg from rfl]
  simp only []
  have hnul : ∀ m', Cfrontend.Cop.sem_cast nullArg (tptr tulong) (tptr tulong) m' = some nullArg :=
    fun _ => rfl
  obtain ⟨hgi, hgc, hgd, hgD⟩ := hsep
  refine wp_gset rfl Search.find_canong rfl hwc (by simp [Exec.evalExpr, Set.pv, temps_gss]) rfl
    (hnul _) rfl ?_
  intro m1 hc1 hu1 hv1 ha1 _
  simp only [seqPost, Post.after, E0_append]
  refine wp_gset rfl Search.find_g rfl (ha1 _ _ _ _ hwg) (by simp [Exec.evalExpr, Set.pv, temps_gss]) rfl
    (hnul _) rfl ?_
  intro m2 hg2 hu2 hv2 ha2 _
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_lset rfl rfl (ha2 _ _ _ _ (ha1 _ _ _ _ hwi)) (v := .Vint (ir 0)) rfl rfl rfl rfl ?_
  intro m3 hi3 hu3 hv3 hf3 _
  have hfi3 := hf3 _ (ha2 _ _ _ _ (ha1 _ _ _ _ hfi))
  simp only [seqPost, Post.after, E0_append]
  have hu123 : Unch m m3 (fun z => z = Search.Block.g ∨ z = Search.Block.canong ∨ z = bI) :=
    ((hu1.mono fun _ h => .inr (.inl h)).trans (hu2.mono fun _ h => .inl h)).trans
      (hu3.mono fun _ h => .inr (.inr h))
  have hv123 : ∀ z, Mem.valid_block m z → Mem.valid_block m3 z := fun z h => hv3 _ (hv2 _ (hv1 _ h))
  have hD9 : FieldAt m .Mint64 Search.Block.dispatch 72 (.Vlong (lr 0)) := by
    have := hD 9 (by decide)
    simpa [dispatchOf, dispatchVals] using this
  have hD9' := hD9.unch hu123 (by
    simp only [not_or]; exact ⟨by decide, by decide, Ne.symm hgD⟩)
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_dispF field_dInit (by decide) (by decide) hD9'.load]
  simp only [Exec.evalExpr, typeof]
  rw [show Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) tint
      (tptr Cfrontend.Ctypes.Tvoid) m3 = some nullArg from rfl]
  simp only []
  rw [show ∀ t1 t2 : Cfrontend.Ctypes.type, Cfrontend.Cop.sem_binary_operation ge.genv_cenv
      Cfrontend.Cop.One (.Vlong (lr 0)) (tptr t1) nullArg (tptr t2) m3 = some Vfalse from fun _ _ => rfl]
  simp only []
  rw [show Cfrontend.Cop.bool_val Vfalse tint m3 = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  -- if (initstatus)
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get dense.id.«initstatus» (nEnv bI) = some (bI, tint)
    from rfl, ↓reduceIte, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hi3.load, typeof]
  rw [show Cfrontend.Cop.bool_val (.Vint (ir 0)) tint m3 = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  have hg3 := hg2.unch hu3 (Ne.symm hgi)
  have hc3 := (hc1.unch hu2 (by decide)).unch hu3 (Ne.symm hgc)
  have hcmp : ∀ m', Cfrontend.Cop.sem_binary_operation ge.genv_cenv Cfrontend.Cop.Oeq nullArg
      (tptr tulong) nullArg (tptr Cfrontend.Ctypes.Tvoid) m' = some Vtrue := fun _ => rfl
  have hcast0 : ∀ m', Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) tint
      (tptr Cfrontend.Ctypes.Tvoid) m' = some nullArg := fun _ => rfl
  have hpc : ∀ (b : block) m', Cfrontend.Cop.sem_cast (.Vptr b Ptrofs.zero) (tptr tulong) (tptr tulong) m' =
      some (.Vptr b Ptrofs.zero) := fun _ _ => rfl
  -- if (g == NULL) g = g_arg;
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get dense.id.«nauty:g» (nEnv bI) = none from rfl,
    Search.find_g, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hg3.load, typeof, hcast0, hcmp]
  rw [show Cfrontend.Cop.bool_val Vtrue tint m3 = some true from rfl]
  simp only [ite_true]
  wp_step; wp_step
  refine wp_gset (v := .Vptr bg Ptrofs.zero) rfl Search.find_g rfl hg3.writable
    (by simp only [Exec.evalExpr, Set.pv, temps_gso _ _ (show dense.id.«g_arg» ≠ idOf 732 by decide), hga])
    rfl (hpc _ _) rfl ?_
  intro m4 hg4 hu4 hv4 ha4 _
  simp only [seqPost, Post.after, E0_append]
  have hc4 := hc3.unch hu4 (by decide)
  -- if (canong == NULL) canong = canong_arg;
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get dense.id.«nauty:canong» (nEnv bI) = none from rfl,
    Search.find_canong, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hc4.load, typeof, hcast0, hcmp]
  rw [show Cfrontend.Cop.bool_val Vtrue tint m4 = some true from rfl]
  simp only [ite_true]
  wp_step; wp_step
  refine wp_gset (v := .Vptr bc Ptrofs.zero) rfl Search.find_canong rfl hc4.writable
    (by simp only [Exec.evalExpr, Set.pv, temps_gso _ _ (show dense.id.«canong_arg» ≠ idOf 732 by decide), hca])
    rfl (hpc _ _) rfl ?_
  intro m5 hc5 hu5 hv5 ha5 _
  simp only [seqPost, Post.after, E0_append]
  have hu15 : Unch m m5 (fun z => z = Search.Block.g ∨ z = Search.Block.canong ∨ z = bI) :=
    (hu123.trans (hu4.mono fun _ h => .inl h)).trans (hu5.mono fun _ h => .inr (.inl h))
  -- if (doschreier) newgroup(...)
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Search.eval_gint (e := nEnv bI) rfl Search.find_doschreier (hds.unch hu15 (by
    simp only [not_or]; exact ⟨by decide, by decide, Ne.symm hgd⟩))]
  simp only [typeof]
  rw [show Cfrontend.Cop.bool_val (.Vint (ir 0)) tint m5 = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  exact hQ _ m5 (hg4.unch hu5 (by decide)) hc5 ((hi3.unch hu4 hgi).unch hu5 hgc)
    (hu5.access _ _ _ _ hgc (hu4.access _ _ _ _ hgi hfi3)) hu15
    (fun z h => hv5 _ (hv4 _ (hv123 z h))) (fun x hx => temps_gso _ _ hx)

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] [T : TopEnv ge] {O : Ops}

/-- `tInit` after the `dispatch.init` call: the `initstatus` check, `g`,
`canong` and the `doschreier` test. -/
def tInitRest : statement :=
  match Nauty.tInit with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ r)) => r
  | _ => .Sskip

theorem IntAt.arr {m : mem} {b : block} {v : Int} (h : IntAt m b v) :
    ArrayAt m .Mint32 b 0 (fun _ => .Vint (ir v)) 1 :=
  ⟨Int.le_refl _, by decide, fun i hi => by
    obtain rfl : i = 0 := by omega
    exact h.load, fun i hi => by
    obtain rfl : i = 0 := by omega
    exact h.writable⟩

theorem ArrayAt.int {m : mem} {b : block} {v : Int} (h : ArrayAt m .Mint32 b 0 (fun _ => .Vint (ir v)) 1) :
    IntAt m b v :=
  ⟨h.load 0 (by decide), h.writable 0 (by decide)⟩

/-- The rest of `tInit` (`tInitRest`), with `initstatus` 0 and `g`, `canong` `NULL`. -/
theorem wp_tInitRest {Q : Post} {le : temp_env} {m : mem} {bg bc : block}
    (hga : PTree.get dense.id.«g_arg» le = some (.Vptr bg Ptrofs.zero))
    (hca : PTree.get dense.id.«canong_arg» le = some (.Vptr bc Ptrofs.zero))
    (hi3 : IntAt m bI 0)
    (hg3 : FieldAt m .Mint64 E.g 0 nullArg) (hc3 : FieldAt m .Mint64 E.canong 0 nullArg)
    (hds : IntAt m E.doschreier 0)
    (hQ : ∀ m', FieldAt m' .Mint64 E.g 0 (.Vptr bg Ptrofs.zero) →
      FieldAt m' .Mint64 E.canong 0 (.Vptr bc Ptrofs.zero) →
      Unch m m' (fun z => z = E.g ∨ z = E.canong) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ z o k p, Mem.perm m z o k p → Mem.perm m' z o k p) →
      Wp xi ge dense.fn.nauty Nauty.tOrbits Q (nEnv bI) (PTree.set (idOf 732) nullArg le) m') :
    Wp xi ge dense.fn.nauty tInitRest Q (nEnv bI) (PTree.set (idOf 732) nullArg le) m := by
  simp only [tInitRest, Nauty.tInit, Set.sk]
  -- if (initstatus)
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get dense.id.«initstatus» (nEnv bI) = some (bI, tint)
    from rfl, ↓reduceIte, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hi3.load, typeof]
  rw [show Cfrontend.Cop.bool_val (.Vint (ir 0)) tint m = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  have hcmp : ∀ m', Cfrontend.Cop.sem_binary_operation ge.genv_cenv Cfrontend.Cop.Oeq nullArg
      (tptr tulong) nullArg (tptr Cfrontend.Ctypes.Tvoid) m' = some Vtrue := fun _ => rfl
  have hcast0 : ∀ m', Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) tint
      (tptr Cfrontend.Ctypes.Tvoid) m' = some nullArg := fun _ => rfl
  have hpc : ∀ (b : block) m', Cfrontend.Cop.sem_cast (.Vptr b Ptrofs.zero) (tptr tulong) (tptr tulong) m' =
      some (.Vptr b Ptrofs.zero) := fun _ _ => rfl
  -- if (g == NULL) g = g_arg;
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get dense.id.«nauty:g» (nEnv bI) = none from rfl,
    E.find_g, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hg3.load, typeof, hcast0, hcmp]
  rw [show Cfrontend.Cop.bool_val Vtrue tint m = some true from rfl]
  simp only [ite_true]
  wp_step; wp_step
  refine wp_gset (v := .Vptr bg Ptrofs.zero) rfl E.find_g rfl hg3.writable
    (by simp only [Exec.evalExpr, Set.pv, temps_gso _ _ (show dense.id.«g_arg» ≠ idOf 732 by decide), hga])
    rfl (hpc _ _) rfl ?_
  intro m4 hg4 hu4 hv4 ha4 hp4
  simp only [seqPost, Post.after, E0_append]
  have hc4 := hc3.unch hu4 (by env_ne)
  -- if (canong == NULL) canong = canong_arg;
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get dense.id.«nauty:canong» (nEnv bI) = none from rfl,
    E.find_canong, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hc4.load, typeof, hcast0, hcmp]
  rw [show Cfrontend.Cop.bool_val Vtrue tint m4 = some true from rfl]
  simp only [ite_true]
  wp_step; wp_step
  refine wp_gset (v := .Vptr bc Ptrofs.zero) rfl E.find_canong rfl hc4.writable
    (by simp only [Exec.evalExpr, Set.pv, temps_gso _ _ (show dense.id.«canong_arg» ≠ idOf 732 by decide), hca])
    rfl (hpc _ _) rfl ?_
  intro m5 hc5 hu5 hv5 ha5 hp5
  simp only [seqPost, Post.after, E0_append]
  have hu45 : Unch m m5 (fun z => z = E.g ∨ z = E.canong) :=
    (hu4.mono fun _ h => .inl h).trans (hu5.mono fun _ h => .inr h)
  -- if (doschreier) newgroup(...)
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Search.eval_gint (e := nEnv bI) rfl E.find_doschreier (hds.unch hu45 (by
    simp only [not_or]; exact ⟨by env_ne, by env_ne⟩))]
  simp only [typeof]
  rw [show Cfrontend.Cop.bool_val (.Vint (ir 0)) tint m5 = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  exact hQ m5 (hg4.unch hu5 (by env_ne)) hc5 hu45 (fun z h => hv5 _ (hv4 _ h))
    (fun z o k p h => hp5 _ _ _ _ (hp4 _ _ _ _ h))

set_option maxHeartbeats 1000000 in
variable {xi : ExternalCalls} in
/-- `g`, `canong`, `initstatus` and `dispatch.init` (`tInit`) for the dispatch
`D`: with `init = NULL` the store at `bc` is `D`'s blank store by
`D.init_null` on `D.CanonPre`; otherwise `D.init` (`D.init_fn`, `initSpec`)
makes it blank and leaves `initstatus` 0. `hpre` gives `init`'s preconditions
in any memory differing from `m` only at `g`, `canong` and `initstatus`. -/
theorem wp_tInitG (D : DispatchC ge O) {n : Nat} (G : O.Gr n) (gl : D.GLoc) {Q : Post}
    {le : temp_env} {m : mem} {bg bc bl bp bA bopt : block} {lofs pofs : ptrofs} {M : Nat}
    (hga : PTree.get dense.id.«g_arg» le = some (.Vptr bg Ptrofs.zero))
    (hca : PTree.get dense.id.«canong_arg» le = some (.Vptr bc Ptrofs.zero))
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr bl lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr bp pofs))
    (hopt : PTree.get dense.id.«options» le = some (.Vptr bopt Ptrofs.zero))
    (hD : DispatchAtG D.toDispatchRep m M)
    (hwg : Mem.valid_access m .Mint64 E.g (zOfInt 0) .Writable)
    (hwc : Mem.valid_access m .Mint64 E.canong (zOfInt 0) .Writable)
    (hfi : Mem.valid_access m .Mint32 bI (zOfInt 0) .Freeable)
    (hds : IntAt m E.doschreier 0)
    (hA : FieldAt m .Mint64 E.nautyActive 0 (.Vptr bA Ptrofs.zero))
    (hMm : IntAt m E.m M) (hNn : IntAt m E.n n)
    (hgc1 : FieldAt m .Mint32 bopt 0 (.Vint (ir 1)))
    (hsep : ∀ z ∈ [E.g, E.canong, E.doschreier, E.dispatch, E.nautyActive, E.m, E.n],
      bI ≠ z ∧ bc ≠ z ∧ bopt ≠ z ∧ ¬ D.IsWork m z)
    (hbo : bopt ≠ bI)
    (hip : ∀ b o, D.init = .Vptr b o → Mem.perm m b (zOfInt 0) .Cur .Nonempty)
    (hgo : O.GraphOk G)
    (hpre : ∀ m', Unch m m' (fun z => z = E.g ∨ z = E.canong ∨ z = bI) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      D.Ctx m' n M ∧ D.GraphRep m' gl bg Ptrofs.zero G M ∧ D.CanonPre m' bc Ptrofs.zero M n ∧
        D.Sep m' (D.graphBlocks gl bg ++ [bc, bopt, bI]))
    (hQ : ∀ m' cl, FieldAt m' .Mint64 E.g 0 (.Vptr bg Ptrofs.zero) →
      FieldAt m' .Mint64 E.canong 0 (.Vptr bc Ptrofs.zero) → IntAt m' bI 0 →
      Mem.valid_access m' .Mint32 bI (zOfInt 0) .Freeable →
      D.CanonRep m' cl bc Ptrofs.zero M (O.blank G) 0 →
      (D.init ≠ Vnullptr → ∀ z ∈ D.canonBlocks cl bc, z = bc ∨ ¬ Mem.valid_block m z) →
      Unch m m' (fun z => z = E.g ∨ z = E.canong ∨ z = bI ∨
        (D.init ≠ Vnullptr ∧ (z = bc ∨ z ∈ D.wglobs ∨ D.IsWork m z ∨ ¬ Mem.valid_block m z))) →
      D.Work m' → (∀ z, D.IsWork m' z → D.IsWork m z ∨ ¬ Mem.valid_block m z) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Wp xi ge dense.fn.nauty Nauty.tOrbits Q (nEnv bI) (PTree.set (idOf 732) nullArg le) m') :
    Wp xi ge dense.fn.nauty Nauty.tInit Q (nEnv bI) le m := by
  have hS := fun z hz => hsep z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hS
  obtain ⟨⟨hgi, hbcg, hog, hwg'⟩, ⟨hgc, hbcc, hoc, hwc'⟩, ⟨hgd, -, -, -⟩, ⟨hgD, -, -, -⟩,
    ⟨hiA, -, -, -⟩, ⟨him, -, -, -⟩, ⟨hin, -, -, -⟩⟩ := hS
  have hwi : Mem.valid_access m .Mint32 bI (zOfInt 0) .Writable :=
    Mem.valid_access_implies _ _ _ _ _ _ hfi (.perm_F_any _)
  obtain ⟨hctx0, -, -, hsp0⟩ := hpre m (Unch.refl _ _) (fun _ h => h)
  -- the scratch state across writes to `g`, `canong` and `initstatus`
  have hW : ∀ {m'}, Unch m m' (fun z => z = E.g ∨ z = E.canong ∨ z = bI) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      D.Work m' ∧ ∀ z, D.IsWork m' z → D.IsWork m z := fun hu hv =>
    D.work_unch hctx0.work hu
      (fun z hz h => by
        have hg := D.globs_env z (D.wglobs_sub z hz)
        rcases h with rfl | rfl | rfl
        · exact hg (by simp [NautyEnv.blocks])
        · exact hg (by simp [NautyEnv.blocks])
        · exact hsp0.notGlobs _ (by simp) (D.wglobs_sub _ hz))
      (fun z hz h => by
        rcases h with rfl | rfl | rfl
        · exact hwg' hz
        · exact hwc' hz
        · exact hsp0.notWork _ (by simp) hz) hv
  simp only [Nauty.tInit, Set.sk]
  wp_step; wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof]
  rw [show Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) tint
      (tptr Cfrontend.Ctypes.Tvoid) m = some nullArg from rfl]
  simp only []
  rw [show Cfrontend.Cop.sem_cast nullArg (tptr Cfrontend.Ctypes.Tvoid) (tptr tulong) m = some nullArg from rfl]
  simp only []
  have hnul : ∀ m', Cfrontend.Cop.sem_cast nullArg (tptr tulong) (tptr tulong) m' = some nullArg :=
    fun _ => rfl
  refine wp_gset rfl E.find_canong rfl hwc (by simp [Exec.evalExpr, Set.pv, temps_gss]) rfl
    (hnul _) rfl ?_
  intro m1 hc1 hu1 hv1 ha1 hp1
  simp only [seqPost, Post.after, E0_append]
  refine wp_gset rfl E.find_g rfl (ha1 _ _ _ _ hwg) (by simp [Exec.evalExpr, Set.pv, temps_gss]) rfl
    (hnul _) rfl ?_
  intro m2 hg2 hu2 hv2 ha2 hp2
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_lset rfl rfl (ha2 _ _ _ _ (ha1 _ _ _ _ hwi)) (v := .Vint (ir 0)) rfl rfl rfl rfl ?_
  intro m3 hi3 hu3 hv3 hf3 hp3
  have hfi3 := hf3 _ (ha2 _ _ _ _ (ha1 _ _ _ _ hfi))
  simp only [seqPost, Post.after, E0_append]
  have hu123 : Unch m m3 (fun z => z = E.g ∨ z = E.canong ∨ z = bI) :=
    ((hu1.mono fun _ h => .inr (.inl h)).trans (hu2.mono fun _ h => .inl h)).trans
      (hu3.mono fun _ h => .inr (.inr h))
  have hv123 : ∀ z, Mem.valid_block m z → Mem.valid_block m3 z := fun z h => hv3 _ (hv2 _ (hv1 _ h))
  have hp123 : ∀ z o k p, Mem.perm m z o k p → Mem.perm m3 z o k p :=
    fun z o k p h => hp3 _ _ _ _ (hp2 _ _ _ _ (hp1 _ _ _ _ h))
  have hg3 := hg2.unch hu3 (Ne.symm hgi)
  have hc3 := (hc1.unch hu2 (by env_ne)).unch hu3 (Ne.symm hgc)
  have hds3 := hds.unch hu123 (by simp only [not_or]; exact ⟨by env_ne, by env_ne, Ne.symm hgd⟩)
  have hD9 : FieldAt m .Mint64 E.dispatch 72 D.init := by
    have := hD 9 (by decide)
    rwa [dispatchOfG_get _ _ (by decide) (by decide)] at this
  have hD9' := hD9.unch hu123 (by simp only [not_or]; exact ⟨by env_ne, by env_ne, Ne.symm hgD⟩)
  obtain ⟨hctx3, hgr3, hcp3, hsp3⟩ := hpre m3 hu123 hv123
  obtain ⟨hwk3, hwm3⟩ := hW hu123 hv123
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_dispF T.field_dInit (by decide) (by decide) hD9'.load]
  by_cases hnull : D.init = Vnullptr
  · -- `init = NULL`: the store is blank already
    rw [hnull]
    simp only [Exec.evalExpr, typeof]
    rw [show Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) tint
        (tptr Cfrontend.Ctypes.Tvoid) m3 = some nullArg from rfl]
    simp only []
    rw [show ∀ t1 t2 : Cfrontend.Ctypes.type, Cfrontend.Cop.sem_binary_operation ge.genv_cenv
        Cfrontend.Cop.One Vnullptr (tptr t1) nullArg (tptr t2) m3 = some Vfalse from fun _ _ => rfl]
    simp only []
    rw [show Cfrontend.Cop.bool_val Vfalse tint m3 = some false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    refine wp_tInitRest hga hca hi3 hg3 hc3 hds3 fun m5 hg5 hc5 hu5 hv5 hp5 => ?_
    have hu15 : Unch m m5 (fun z => z = E.g ∨ z = E.canong ∨ z = bI) :=
      hu123.trans (hu5.mono fun _ h => h.elim .inl (fun h => .inr (.inl h)))
    have hv15 : ∀ z, Mem.valid_block m z → Mem.valid_block m5 z := fun z h => hv5 _ (hv123 z h)
    obtain ⟨cl, hcl⟩ := D.init_null hnull (hpre m5 hu15 hv15).2.2.1
    obtain ⟨hwk5, hwm5⟩ := hW hu15 hv15
    exact hQ m5 cl hg5 hc5 (hi3.unch hu5 (by simp only [not_or]; exact ⟨hgi, hgc⟩))
      ⟨fun o ho => hp5 _ _ _ _ (hfi3.1 o ho), hfi3.2⟩ (hcl G) (fun h => absurd hnull h)
      (hu15.mono fun _ h => h.elim .inl fun h => h.elim (fun h => .inr (.inl h)) fun h => .inr (.inr (.inl h)))
      hwk5 (fun z h => .inl (hwm5 z h)) hv15
  · -- `init` is a procedure: call it
    obtain ⟨fd, hfd, hty, hsat⟩ := D.init_fn xi hnull
    obtain ⟨bi, hbi⟩ : ∃ bi, D.init = .Vptr bi Ptrofs.zero := by
      revert hfd
      unfold Genv.find_funct
      split
      · next bb o heq =>
        split
        · next ho =>
          intro _
          have e := Ptrofs.eq_spec_proof o Ptrofs.zero
          rw [ho] at e
          exact ⟨bb, by rw [heq, e]⟩
        · intro h; cases h
      · intro h; cases h
    have hpi : Mem.perm m3 bi (zOfInt 0) .Cur .Nonempty := hp123 _ _ _ _ (hip bi _ hbi)
    rw [hbi]
    simp only [Exec.evalExpr, typeof, cop, ne_pl, cmp_null_ne hpi]
    simp only [Option.map, Val.of_bool, cop]
    rw [ite_eq_left (by decide)]
    wp_step; wp_step
    refine wp_call (vf := .Vptr bi Ptrofs.zero)
      (targs := [tptr tulong, tptr (tptr tulong), tptr tulong, tptr (tptr tulong), tptr tint, tptr tint,
        tptr tulong, tptr (.Tstruct dense.id.«optionstruct» Cfrontend.Ctypes.noattr), tptr tint, tint, tint])
      (tres := .Tvoid) (cc := Common.AST.cc_default)
      (vargs := [.Vptr bg Ptrofs.zero, .Vptr E.g Ptrofs.zero, .Vptr bc Ptrofs.zero,
        .Vptr E.canong Ptrofs.zero, .Vptr bl lofs, .Vptr bp pofs, .Vptr bA Ptrofs.zero,
        .Vptr bopt Ptrofs.zero, .Vptr bI Ptrofs.zero, .Vint (ir M), .Vint (ir n)])
      fd (D.initSpec G gl bg Ptrofs.zero (.Vptr E.g Ptrofs.zero) bc Ptrofs.zero
        (.Vptr E.canong Ptrofs.zero) (.Vptr bl lofs) (.Vptr bp pofs) (.Vptr bA Ptrofs.zero) bopt
        Ptrofs.zero bI Ptrofs.zero M)
      (hsat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) rfl ?_ ?_ (by rw [← hbi]; exact hfd) hty ?_ ?_
    · rw [Exec.evalExpr, eval_dispF T.field_dInit (by decide) (by decide) hD9'.load, hbi]
      simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode]
    · have hA3 := hA.unch hu123 (by simp only [not_or]; exact ⟨by env_ne, by env_ne, Ne.symm hiA⟩)
      have hM3 := hMm.unch hu123 (by simp only [not_or]; exact ⟨by env_ne, by env_ne, Ne.symm him⟩)
      have hN3 := hNn.unch hu123 (by simp only [not_or]; exact ⟨by env_ne, by env_ne, Ne.symm hin⟩)
      simp only [Exec.evalExprlist, Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar, Set.pv, Refine.pi,
        temps_gso _ _ (show dense.id.«g_arg» ≠ idOf 732 by decide),
        temps_gso _ _ (show dense.id.«canong_arg» ≠ idOf 732 by decide),
        temps_gso _ _ (show dense.id.«lab» ≠ idOf 732 by decide),
        temps_gso _ _ (show dense.id.«ptn» ≠ idOf 732 by decide),
        temps_gso _ _ (show dense.id.«options» ≠ idOf 732 by decide), hga, hca, hlab, hptn, hopt,
        show PTree.get dense.id.«nauty:g» (nEnv bI) = none from rfl,
        show PTree.get dense.id.«nauty:canong» (nEnv bI) = none from rfl,
        show PTree.get dense.id.«nauty:active» (nEnv bI) = none from rfl,
        show PTree.get dense.id.«nauty:m» (nEnv bI) = none from rfl,
        show PTree.get dense.id.«nauty:n» (nEnv bI) = none from rfl,
        show PTree.get dense.id.«initstatus» (nEnv bI) = some (bI, tint) from rfl, ↓reduceIte,
        E.find_g, E.find_canong, E.find_nautyActive, E.find_m, E.find_n, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
        show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hA3.load, hM3.load, hN3.load, typeof]
      rfl
    · refine ⟨rfl, hctx3, hgr3, hgo, hcp3, ?_, ⟨_, IntAt.arr hi3⟩, hsp3⟩
      exact (hgc1.unch hu123 (by simp only [not_or]; exact ⟨hog, hoc, hbo⟩)).load
    rintro t v m4 ⟨rfl, hst4, cl, hcr, hcb, hstep⟩
    simp only [set_opttemp, seqPost, Post.after, E0_append]
    have hout : ∀ z ∈ E.blocks, z ≠ bc → z ≠ bI → ¬ D.IsWork m z → Mem.valid_block m3 z →
        ¬ (z ∈ [bc, bI] ∨ z ∈ D.wglobs ∨ D.IsWork m3 z ∨ ¬ Mem.valid_block m3 z) := by
      intro z hz h1 h2 h3 h4 h
      rcases h with h | h | h | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h
        · exact h1 h
        · exact h2 h
      · exact D.globs_env z (D.wglobs_sub z h) hz
      · exact h3 (hwm3 z h)
      · exact h h4
    have hvg3 : Mem.valid_block m3 E.g := Alloc.valid_of_access hg3.writable
    have hvc3 : Mem.valid_block m3 E.canong := Alloc.valid_of_access hc3.writable
    have hg4 := hg3.unch hstep.unch
      (hout _ (by simp [NautyEnv.blocks]) (Ne.symm hbcg) (Ne.symm hgi) hwg' hvg3)
    have hc4 := hc3.unch hstep.unch
      (hout _ (by simp [NautyEnv.blocks]) (Ne.symm hbcc) (Ne.symm hgc) hwc' hvc3)
    have hS := fun z hz => hsep z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hS
    have hds4 := hds3.unch hstep.unch
      (hout _ (by simp [NautyEnv.blocks]) (Ne.symm hS.2.2.1.2.1) (Ne.symm hgd) hS.2.2.1.2.2.2
        (Alloc.valid_of_access hds3.writable))
    have hi4 : IntAt m4 bI 0 := ArrayAt.int hst4
    have hk4 := hstep.keep bI (by simp) (hv123 bI (Alloc.valid_of_access hfi))
    refine wp_tInitRest hga hca hi4 hg4 hc4 hds4 fun m5 hg5 hc5 hu5 hv5 hp5 => ?_
    have hnW : ∀ z, D.IsWork m4 z → ¬ (z = E.g ∨ z = E.canong) := fun z hz h => by
      rcases hstep.mono z hz with h' | h'
      · rcases h with rfl | rfl
        · exact hwg' (hwm3 _ h')
        · exact hwc' (hwm3 _ h')
      · rcases h with rfl | rfl
        · exact h' hvg3
        · exact h' hvc3
    obtain ⟨hwk5, hwm5⟩ := D.work_unch hstep.work hu5
      (fun z hz h => by
        have hg := D.globs_env z (D.wglobs_sub z hz)
        rcases h with rfl | rfl
        · exact hg (by simp [NautyEnv.blocks])
        · exact hg (by simp [NautyEnv.blocks])) hnW hv5
    have hcr5 := D.canon_unch hcr hu5 (fun z hz h => by
      rcases hcb z hz with rfl | h'
      · rcases h with h | h
        · exact hbcg h
        · exact hbcc h
      · rcases h with rfl | rfl
        · exact h' hvg3
        · exact h' hvc3)
    refine hQ m5 cl hg5 hc5 ((hi4.unch hu5 (by simp only [not_or]; exact ⟨hgi, hgc⟩)))
      ⟨fun o ho => hp5 _ _ _ _ (hk4.perm _ _ (hfi3.1 o ho)), hfi3.2⟩ hcr5
      (fun _ z hz => (hcb z hz).imp_right fun h h' => h (hv123 z h')) ?_ hwk5
      (fun z hz => (hstep.mono z (hwm5 z hz)).elim (fun h => .inl (hwm3 z h))
        fun h => .inr fun h' => h (hv123 z h'))
      (fun z h => hv5 _ (hstep.valid _ (hv123 z h)))
    refine ((hu123.mono fun z h => ?_).trans ((hstep.unch.mono fun z h => ?_).trans
      (hu5.mono fun z h => ?_)))
    · exact h.elim .inl fun h => h.elim (fun h => .inr (.inl h)) fun h => .inr (.inr (.inl h))
    · rcases h with h | h | h | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h
        · exact .inr (.inr (.inr ⟨hnull, .inl h⟩))
        · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr ⟨hnull, .inr (.inl h)⟩))
      · exact .inr (.inr (.inr ⟨hnull, .inr (.inr (.inl (hwm3 z h)))⟩))
      · exact .inr (.inr (.inr ⟨hnull, .inr (.inr (.inr fun h' => h (hv123 z h')))⟩))
    · exact h.elim .inl fun h => .inr (.inl h)

end Generic

end NautyVerified.Proofs.Top
