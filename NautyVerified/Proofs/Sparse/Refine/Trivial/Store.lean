import NautyVerified.Proofs.Sparse.Refine.Ops
import NautyVerified.Proofs.Alloc.KeepV

/-!
# Stores with their memory change as a `Frame`

`Refine/Access.lean`'s stores, reporting the change as a `Frame` (the stored
block keeps its permissions and header).
-/

namespace NautyVerified.Proofs.Sparse.Refine.Trivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- `lab[a] = x`. -/
theorem wp_lab {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (ht : Tmp le L t) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < n) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hsize : t.lab.size = n)
    (hQ : ∀ m', Mem m' L G { t with lab := t.lab.set! c x } S → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (ix id.lab a) rhs) Q empty_env le m := by
  refine wp_idx_store (pe := .Etempvar id.lab (tptr tint)) hm.lab (by have := hok.nlt; omega)
    ht.lab rfl rfl rfl a c hc ha hty rhs tint hrty _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr hu hk hg
  refine hQ m' (hm.setLab hok hu _ ?_ rfl rfl rfl)
    (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))
  rw [ints_set (by omega) x]; exact harr

/-- `ptn[a] = x`. -/
theorem wp_ptn {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (ht : Tmp le L t) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < n) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hsize : t.ptn.size = n)
    (hQ : ∀ m', Mem m' L G { t with ptn := t.ptn.set! c x } S → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (ix id.ptn a) rhs) Q empty_env le m := by
  refine wp_idx_store (pe := .Etempvar id.ptn (tptr tint)) hm.ptn (by have := hok.nlt; omega)
    ht.ptn rfl rfl rfl a c hc ha hty rhs tint hrty _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr hu hk hg
  refine hQ m' (hm.setPtn hok hu _ ?_ rfl rfl rfl)
    (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))
  rw [ints_set (by omega) x]; exact harr

/-- `work1[a] = x`. -/
theorem wp_w1 {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < L.c1) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G t { S with w1 := upd S.w1 c (.Vint (ir x)) } → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (gix id.«nausparse:work1» a) rhs) Q empty_env le m := by
  refine wp_idx_store hm.w1 hm.d1.capLt (eval_w1 hok hm) rfl rfl rfl a c hc ha hty rhs tint hrty
    _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr hu hk hg
  exact hQ m' (hm.setW1 hok hu hk _ harr) (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))

/-- `work2[a] = x`. -/
theorem wp_w2 {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < L.c2) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G t { S with w2 := upd S.w2 c (.Vint (ir x)) } → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (gix id.«nausparse:work2» a) rhs) Q empty_env le m := by
  refine wp_idx_store hm.w2 hm.d2.capLt (eval_w2 hok hm) rfl rfl rfl a c hc ha hty rhs tint hrty
    _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr hu hk hg
  exact hQ m' (hm.setW2 hok hu hk _ harr) (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))

/-- `work3[a] = x`. -/
theorem wp_w3 {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (hsize : S.w3.size = n) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < n) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G t { S with w3 := S.w3.set! c x } → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (gix id.«nausparse:work3» a) rhs) Q empty_env le m := by
  obtain ⟨T, hT, htl⟩ := hm.hi
  refine wp_idx_store_far hm.w3 (by have := hok.nlt; omega) htl (Int.le_refl _) (eval_w3 hok hm) rfl rfl rfl a c hc ha hty
    rhs tint hrty _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr htl' hu hk hg
  refine hQ m' (hm.setW3 hok hu hk _ ?_ ⟨T, hT, htl'⟩) (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))
  rw [ints_set (by omega) x]; exact harr

/-- `work4[a] = x`. -/
theorem wp_w4 {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < L.c4) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G t { S with w4 := upd S.w4 c (.Vint (ir x)) } → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (gix id.«nausparse:work4» a) rhs) Q empty_env le m := by
  refine wp_idx_store hm.w4 hm.d4.capLt (eval_w4 hok hm) rfl rfl rfl a c hc ha hty rhs tint hrty
    _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr hu hk hg
  exact hQ m' (hm.setW4 hok hu hk _ harr) (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))

/-- `*numcells = x`. -/
theorem wp_nc {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (ht : Tmp le L t) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G { t with numcells := x } S → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (.Ederef (pi id.numcells) tint) rhs) Q empty_env le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array hm.nc (show 0 < 1 by decide) (.Vint (ir x)) rfl
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, ht.numcells, hrhs, hrty]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
  have he : elemOfs .Mint32 L.nb 0 = Ptrofs.unsigned L.nofs := by
    unfold elemOfs
    rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ]
  rw [← he, hst]
  have hu : Unch m m' (· = L.bn) := Unch.store hst rfl
  refine hQ m' (hm.setNc hok hu _ ?_ rfl rfl rfl)
    (Frame.ofOne hu (Alloc.KeepA.storeArr hm.nc hst L.bn)
      (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz) (by simp [Loc.writes, Loc.wblocks]))
  refine harr'.congr fun i hi => ?_
  have : i = 0 := by omega
  subst this; rfl

end NautyVerified.Proofs.Sparse.Refine.Trivial
