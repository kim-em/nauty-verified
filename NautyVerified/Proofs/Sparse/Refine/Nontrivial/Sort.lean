import NautyVerified.Proofs.Sparse.Refine.Nontrivial.Call
import NautyVerified.Proofs.Sparse.Ints.Satisfies
import NautyVerified.Logic.Grow

/-!
# `sortints(HITCELL, hitcells)` in `refine_sg`

`wp_sortHitcell`: with `HITCELL[0..hitcells)` holding distinct vertices
`X`, the call leaves `HITCELL[0..hitcells)` holding HexGraphIso's
`sortCells X`, as a `Frame` step.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Nontrivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Alloc (Keep DynAt)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph sortCells)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {S : Scr}

/-- The first `k'` entries of an array. -/
theorem arr_take {m : mem} {c : memory_chunk} {b : block} {base : Int} {vals vals' : Nat → val}
    {k k' : Nat} (h : ArrayAt m c b base vals k) (hk : k' ≤ k) (he : ∀ i < k', vals i = vals' i) :
    ArrayAt m c b base vals' k' := by
  refine ⟨h.base_nonneg, ?_, fun i hi => by rw [← he i hi]; exact h.load i (by omega),
    fun i hi => h.writable i (by omega)⟩
  have := h.fits
  have : csize c * k' ≤ csize c * k := Int.mul_le_mul_of_nonneg_left (by omega)
    (by have := csize_pos c; omega)
  omega

/-- `sortints(HITCELL, hitcells)`. -/
theorem wp_sortHitcell {Q : Post} {le : temp_env} {m : mem} {t : RefineSt n} {X : Array Nat}
    (hok : Ok n L) (hm : Mem m L G t S) (hX1 : 0 < X.size) (hXn : X.size ≤ n)
    (hw : ∀ i < X.size, S.w4 i = .Vint (ir X[i]!)) (hXv : ∀ i < X.size, X[i]! < n)
    (hnd : X.toList.Nodup) (hhc : PTree.get id.«hitcells» le = some (.Vint (ir X.size)))
    (hQ : ∀ m' w, Mem m' L G t { S with w4 := w } →
      (∀ i < X.size, w i = .Vint (ir (sortCells X)[i]!)) → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge F (.Scall none (.Evar id.«nausparse:sortints» (tfun [(tptr tint), tint] .Tvoid))
      [(.Evar id.«nausparse:work4» (tptr tint)), (tv id.«hitcells»)]) Q empty_env le m := by
  have hnl := hok.nlt
  have hc4 := hok.c4
  let C : Sort.Ints.Ctx := ⟨L.b4, 0, X.size, Sort.Ints.idY⟩
  have hC : C.Ok := ⟨show X.size < 2147483648 by omega, hX1, Sort.Ints.idY_size,
    fun i hi => Sort.Ints.idY_get hi⟩
  have harr : Sort.Ints.Arr m C X :=
    ⟨arr_take hm.w4 (show X.size ≤ L.c4 by omega) (fun i hi => (hw i hi)), rfl,
      fun i hi => by
        show X[i]! < Sort.Ints.idY.size
        rw [Sort.Ints.idY_size]; have := hXv i hi; omega⟩
  refine wp_call (vf := .Vptr Block.sortints Ptrofs.zero) (targs := [tptr tint, tint])
    (tres := .Tvoid) (cc := Common.AST.cc_default) _ _
    (Satisfies.grow (Sort.Ints.sortints_satisfies (xi := xi) C X 0 X.size)) rfl ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_sortints]) rfl
    ⟨rfl, hC, harr, .inr (by simpa [NautyVerified.Spec.SortC.Win] using hnd), by simp [C]⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, find_sortints, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
    rfl
  · simp only [Exec.evalExprlist, eval_w4 hok hm]
    simp only [Exec.evalExpr, hhc, typeof, cop]
    rfl
  rintro tr v m' ⟨⟨rfl, ⟨Z, hZ, hZe, -⟩, hu, hk⟩, hg⟩
  have hZs : Z.size = X.size := hZ.size
  have hZX : Z = sortCells X := by
    have h1 : Z.extract 0 X.size = Z := by rw [← hZs]; simp
    have h2 : X.extract 0 X.size = X := by simp
    simp only [Nat.zero_add] at hZe
    rw [← h1, hZe, h2]
  have hv := Mem.valid hok hm
  have hk4 := hk L.b4 (hv _ (by simp [Loc.wblocks]))
  obtain ⟨w, hwa, hwe⟩ := arr_keep hm.w4 hk4 hZ.arr
  refine hQ m' w (Mem.setW4Call hok hm hv (fun h0 => ?_) hu hk4 w hwa) (fun i hi => by
    rw [hwe i hi, ← hZX]; rfl) ⟨hu.mono fun z hz => hz.imp_left fun h => by
      rw [show z = L.b4 from h]; simp [Loc.writes, Loc.wblocks], fun z hz => hk z hz, ?_⟩
  · exact arr_valid hm.graph.earr h0
  · exact hg

end NautyVerified.Proofs.Sparse.Refine.Nontrivial
