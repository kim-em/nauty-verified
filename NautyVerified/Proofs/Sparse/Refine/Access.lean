import NautyVerified.Proofs.Sparse.Refine.State

/-!
# Reading and writing `refine_sg`'s arrays

Evaluation of the array reads `refine_sg` makes (`lab[a]`, `ptn[a]`,
`work1[a]` to `work4[a]`, `*numcells`) and the stores (`lab[a] = x`,
`ptn[a] = x`, `work1[a] = x` to `work4[a] = x`, `*numcells = x`), with the
memory afterwards as `Mem` with the one component replaced (`Mem.set*`).
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- A pointer global holding the array of a `DYNALLSTAT` pair. -/
theorem eval_gptr {le : temp_env} {m : mem} {gid : ident} {ty : Cfrontend.Ctypes.type}
    {bp bs b : block} {c cap : Nat} (hfind : Genv.find_symbol sge.genv_genv gid = some bp)
    (hD : DynAt m bp bs c cap b) (hc : 0 < cap) :
    Exec.evalExpr sge empty_env le m (.Evar gid (tptr ty)) = some (.Vptr b Ptrofs.zero) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get gid (empty_env : env) = none from rfl,
    hfind, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq]
  exact hD.ptr hc

theorem eval_w1 {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S) :
    Exec.evalExpr sge empty_env le m (.Evar id.«nausparse:work1» (tptr tint)) =
      some (.Vptr L.b1 Ptrofs.zero) :=
  eval_gptr find_work1 hm.d1 (by have := hok.c1; have := hok.n0; omega)

theorem eval_w2 {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S) :
    Exec.evalExpr sge empty_env le m (.Evar id.«nausparse:work2» (tptr tint)) =
      some (.Vptr L.b2 Ptrofs.zero) :=
  eval_gptr find_work2 hm.d2 (by have := hok.c2; have := hok.n0; omega)

theorem eval_w3 {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S) :
    Exec.evalExpr sge empty_env le m (.Evar id.«nausparse:work3» (tptr tint)) =
      some (.Vptr L.b3 Ptrofs.zero) :=
  eval_gptr find_work3 hm.d3 (by have := hok.c3; have := hok.n0; omega)

theorem eval_w4 {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S) :
    Exec.evalExpr sge empty_env le m (.Evar id.«nausparse:work4» (tptr tint)) =
      some (.Vptr L.b4 Ptrofs.zero) :=
  eval_gptr find_work4 hm.d4 (by have := hok.c4; have := hok.n0; omega)

/-- `lab[a]`. -/
theorem eval_lab {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S) (ht : Tmp le L t)
    {a : expr} {c : Nat} (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c)))
    (hty : typeof a = tint) (hc : c < n) :
    Exec.evalExpr sge empty_env le m (ix id.lab a) = some (.Vint (ir t.lab[c]!)) :=
  eval_idx (pe := .Etempvar id.lab (tptr tint)) hm.lab (by have := hok.nlt; omega) ht.lab rfl rfl rfl
    a c hc ha hty

/-- `ptn[a]`. -/
theorem eval_ptn {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S) (ht : Tmp le L t)
    {a : expr} {c : Nat} (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c)))
    (hty : typeof a = tint) (hc : c < n) :
    Exec.evalExpr sge empty_env le m (ix id.ptn a) = some (.Vint (ir t.ptn[c]!)) :=
  eval_idx (pe := .Etempvar id.ptn (tptr tint)) hm.ptn (by have := hok.nlt; omega) ht.ptn rfl rfl rfl
    a c hc ha hty

/-- `work1[a]`. -/
theorem eval_gw1 {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    {a : expr} {c : Nat} (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c)))
    (hty : typeof a = tint) (hc : c < L.c1) :
    Exec.evalExpr sge empty_env le m (gix id.«nausparse:work1» a) = some (S.w1 c) :=
  eval_idx hm.w1 hm.d1.capLt (eval_w1 hok hm) rfl rfl rfl a c hc ha hty

/-- `work2[a]`. -/
theorem eval_gw2 {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    {a : expr} {c : Nat} (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c)))
    (hty : typeof a = tint) (hc : c < L.c2) :
    Exec.evalExpr sge empty_env le m (gix id.«nausparse:work2» a) = some (S.w2 c) :=
  eval_idx hm.w2 hm.d2.capLt (eval_w2 hok hm) rfl rfl rfl a c hc ha hty

/-- `work3[a]`. -/
theorem eval_gw3 {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    {a : expr} {c : Nat} (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c)))
    (hty : typeof a = tint) (hc : c < n) :
    Exec.evalExpr sge empty_env le m (gix id.«nausparse:work3» a) =
      some (.Vint (ir S.w3[c]!)) :=
  eval_idx hm.w3 (by have := hok.nlt; omega) (eval_w3 hok hm) rfl rfl rfl a c hc ha hty

/-- `work4[a]`. -/
theorem eval_gw4 {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    {a : expr} {c : Nat} (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c)))
    (hty : typeof a = tint) (hc : c < L.c4) :
    Exec.evalExpr sge empty_env le m (gix id.«nausparse:work4» a) = some (S.w4 c) :=
  eval_idx hm.w4 hm.d4.capLt (eval_w4 hok hm) rfl rfl rfl a c hc ha hty

/-- `*numcells`. -/
theorem eval_nc {le : temp_env} {m : mem} (hm : Mem m L G t S) (ht : Tmp le L t) :
    Exec.evalExpr sge empty_env le m (.Ederef (pi id.numcells) tint) =
      some (.Vint (ir t.numcells)) := by
  simp only [Exec.evalExpr, ht.numcells, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  apply load_array hm.nc (show 0 < 1 by decide)
  unfold elemOfs
  rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ]

/-- `lab[a] = x`. -/
theorem wp_storeLab {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (ht : Tmp le L t) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < n) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hsize : t.lab.size = n)
    (hQ : ∀ m', Mem m' L G { t with lab := t.lab.set! c x } S → Unch m m' (· = L.bl) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (ix id.lab a) rhs) Q empty_env le m := by
  refine wp_idx_store (pe := .Etempvar id.lab (tptr tint)) hm.lab (by have := hok.nlt; omega)
    ht.lab rfl rfl rfl a c hc ha hty rhs tint hrty _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr hu _ hg
  refine hQ m' (hm.setLab hok hu _ ?_ rfl rfl rfl) hu hg
  rw [ints_set (by omega) x]; exact harr

/-- `ptn[a] = x`. -/
theorem wp_storePtn {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (ht : Tmp le L t) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < n) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hsize : t.ptn.size = n)
    (hQ : ∀ m', Mem m' L G { t with ptn := t.ptn.set! c x } S → Unch m m' (· = L.bp) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (ix id.ptn a) rhs) Q empty_env le m := by
  refine wp_idx_store (pe := .Etempvar id.ptn (tptr tint)) hm.ptn (by have := hok.nlt; omega)
    ht.ptn rfl rfl rfl a c hc ha hty rhs tint hrty _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr hu _ hg
  refine hQ m' (hm.setPtn hok hu _ ?_ rfl rfl rfl) hu hg
  rw [ints_set (by omega) x]; exact harr

/-- `work1[a] = x`. -/
theorem wp_storeW1 {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < L.c1) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G t { S with w1 := upd S.w1 c (.Vint (ir x)) } → Unch m m' (· = L.b1) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (gix id.«nausparse:work1» a) rhs) Q empty_env le m := by
  refine wp_idx_store hm.w1 hm.d1.capLt (eval_w1 hok hm) rfl rfl rfl a c hc ha hty rhs tint hrty
    _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr hu hk hg
  exact hQ m' (hm.setW1 hok hu hk _ harr) hu hg

/-- `work2[a] = x`. -/
theorem wp_storeW2 {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < L.c2) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G t { S with w2 := upd S.w2 c (.Vint (ir x)) } → Unch m m' (· = L.b2) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (gix id.«nausparse:work2» a) rhs) Q empty_env le m := by
  refine wp_idx_store hm.w2 hm.d2.capLt (eval_w2 hok hm) rfl rfl rfl a c hc ha hty rhs tint hrty
    _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr hu hk hg
  exact hQ m' (hm.setW2 hok hu hk _ harr) hu hg

/-- `work3[a] = x`. -/
theorem wp_storeW3 {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (hsize : S.w3.size = n) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < n) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G t { S with w3 := S.w3.set! c x } → Unch m m' (· = L.b3) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (gix id.«nausparse:work3» a) rhs) Q empty_env le m := by
  obtain ⟨T, hT, htl⟩ := hm.hi
  refine wp_idx_store_far hm.w3 (by have := hok.nlt; omega) htl (Int.le_refl _) (eval_w3 hok hm) rfl rfl rfl a c hc ha hty rhs tint hrty
    _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr htl' hu hk hg
  refine hQ m' (hm.setW3 hok hu hk _ ?_ ⟨T, hT, htl'⟩) hu hg
  rw [ints_set (by omega) x]; exact harr

/-- `work4[a] = x`. -/
theorem wp_storeW4 {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < L.c4) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G t { S with w4 := upd S.w4 c (.Vint (ir x)) } → Unch m m' (· = L.b4) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (gix id.«nausparse:work4» a) rhs) Q empty_env le m := by
  refine wp_idx_store hm.w4 hm.d4.capLt (eval_w4 hok hm) rfl rfl rfl a c hc ha hty rhs tint hrty
    _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr hu hk hg
  exact hQ m' (hm.setW4 hok hu hk _ harr) hu hg

/-- `*numcells = x`. -/
theorem wp_storeNc {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (ht : Tmp le L t) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G { t with numcells := x } S → Unch m m' (· = L.bn) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 empty_env le m') :
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
  refine hQ m' (hm.setNc hok hu _ ?_ rfl rfl rfl) hu
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)
  refine harr'.congr fun i hi => ?_
  have : i = 0 := by omega
  subst this; rfl

end NautyVerified.Proofs.Sparse.Refine
