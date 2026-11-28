import NautyVerified.Proofs.Sparse.Refine.Count.Run

/-!
# Stores with their memory change

The stores of a count split (`lab[a]`, `ptn[a]`, `work1[a]`, `work2[a]`,
`*numcells`), each with the memory afterwards as `Mem` and the change as a
`Frame`; `Rep.setStart`, `Rep.setQueue`, `Rep.setPtn` for the scratch.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Alloc (Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem wb (z : block) (h : z ∈ [L.bl, L.bp, L.bn, L.ba, L.bk, L.b1, L.b2, L.b3, L.b4]) : L.writes z := by
  simp only [Loc.writes, Loc.wblocks, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]

/-- `lab[a] = x`. -/
theorem wp_labF {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
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
  refine hQ m' (hm.setLab hok hu _ ?_ rfl rfl rfl) (Frame.ofOne hu hk hg (wb _ (by simp)))
  rw [ints_set (by omega) x]; exact harr

/-- `ptn[a] = x`. -/
theorem wp_ptnF {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
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
  refine hQ m' (hm.setPtn hok hu _ ?_ rfl rfl rfl) (Frame.ofOne hu hk hg (wb _ (by simp)))
  rw [ints_set (by omega) x]; exact harr

/-- `work1[a] = x`. -/
theorem wp_w1F {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
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
  exact hQ m' (hm.setW1 hok hu hk _ harr) (Frame.ofOne hu hk hg (wb _ (by simp)))

/-- `work2[a] = x`. -/
theorem wp_w2F {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
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
  exact hQ m' (hm.setW2 hok hu hk _ harr) (Frame.ofOne hu hk hg (wb _ (by simp)))

/-- `*numcells = x`. -/
theorem wp_ncF {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
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
  have hk : Keep m m' L.bn := Alloc.Keep.store hst (by
    have := hm.nc.base_nonneg
    simp only [elemOfs, intOfZ_zOfInt]; omega)
  refine hQ m' (hm.setNc hok hu _ ?_ rfl rfl rfl)
    (Frame.ofOne hu hk (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz) (wb _ (by simp)))
  refine harr'.congr fun i hi => ?_
  have : i = 0 := by omega
  subst this; rfl

/-- A cell start written. -/
theorem Rep.setStart (hr : Rep L t S) (hs : t.cellstart.size = n) {c x : Nat} (hc : c < n) :
    Rep L { t with cellstart := t.cellstart.set! c x } { S with w1 := upd S.w1 c (.Vint (ir x)) } :=
  { hr with
    starts := fun v hv => by
      show upd S.w1 c _ v = _
      by_cases hvc : v = c
      · subst hvc
        rw [Array.getElem!_set!_self _ _ _ (by omega : v < t.cellstart.size)]; simp [upd]
      · rw [upd_ne _ _ hvc, Array.getElem!_set!_ne _ _ _ _ (Ne.symm hvc)]; exact hr.starts v hv }

/-- A boundary at `level` written. -/
theorem Rep.setPtn (hr : Rep L t S) (hl : L.level < 2147483648) (c : Nat) :
    Rep L { t with ptn := t.ptn.set! c L.level } S :=
  { hr with
    ptnSmall := fun i hi => by
      show (t.ptn.set! c L.level)[i]! < _
      by_cases hic : i = c
      · subst hic
        by_cases hs : i < t.ptn.size
        · rw [Array.getElem!_set!_self _ _ _ hs]; exact hl
        · rw [show t.ptn.set! i L.level = t.ptn by simp [Array.set!, Array.setIfInBounds, hs]]
          exact hr.ptnSmall i hi
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hic)]; exact hr.ptnSmall i hi }

end NautyVerified.Proofs.Sparse.Refine.Count
