import NautyVerified.Proofs.Top.Ptn

/-!
# `nauty()`'s `g`, `canong` and `dispatch.init` (`tInit`)

`g = canong = NULL; initstatus = 0;` then `dispatch.init` is NULL for the
dense dispatch, so `initstatus` stays 0; `g` and `canong` become the
arguments; `doschreier` is 0. `wp_lset` is `wp_gset` for the local `initstatus`.
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
theorem wp_lset {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {g : ident}
    {ty : Cfrontend.Ctypes.type} {chunk : memory_chunk} {b : block}
    (hge : PTree.get g e = some (b, ty))
    (hacc : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hw : Mem.valid_access m chunk b (zOfInt 0) .Writable) {rhs : expr} {v : val}
    (hr : Exec.evalExpr ge e le m rhs = some v) (hrt : typeof rhs = ty)
    (hc : Cfrontend.Cop.sem_cast v ty ty m = some v) (hlr : Val.load_result chunk v = v)
    (hQ : ∀ m', FieldAt m' chunk b 0 v → Unch m m' (· = b) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ p, Mem.valid_access m chunk b (zOfInt 0) p → Mem.valid_access m' chunk b (zOfInt 0) p) →
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
  intro m3 hi3 hu3 hv3 hf3
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

end NautyVerified.Proofs.Top
