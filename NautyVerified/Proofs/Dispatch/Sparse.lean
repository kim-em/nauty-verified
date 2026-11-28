import NautyVerified.Proofs.Dispatch.Sparse.Canon

/-!
# nausparse.c's dispatch procedures

`sparseDispatch`: `sparseRep` (`Dispatch/Sparse/Rep.lean`) with the
specifications, from the proofs of nausparse.c's procedures
(`Dispatch/Sparse/Fns.lean`, `Dispatch/Sparse/Canon.lean`, and here
`init_sg` and `nausparse_freedyn`). `refine_sg` (both `refine` and `refine1`)
enters as the hypothesis `hRef` until its proof lands.
-/

namespace NautyVerified.Proofs.Dispatch

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep Slot InUse SlotsOk FreeD)
open NautyVerified.Proofs.Sparse (SparseGraphAt CanonAt CanonRows MarksAt base start)
open Hex.GraphIso.Nauty

attribute [local instance] NautyEnv.sparse

local notation "VM1" => Sparse.Block.vmark1
local notation "VM1S" => Sparse.Block.vmark1Sz
local notation "VM2" => Sparse.Refine.Block.vmark2
local notation "VM2S" => Sparse.Refine.Block.vmark2Sz
local notation "W1" => Sparse.Block.work1
local notation "W1S" => Sparse.Block.work1Sz
local notation "W2" => Sparse.Refine.Block.work2
local notation "W2S" => Sparse.Refine.Block.work2Sz
local notation "W3" => Sparse.Refine.Block.work3
local notation "W3S" => Sparse.Refine.Block.work3Sz
local notation "W4" => Sparse.Refine.Block.work4
local notation "W4S" => Sparse.Refine.Block.work4Sz
local notation "SN" => Sparse.Block.snwork
local notation "SNS" => Sparse.Block.snworkSz

/-! ### `init_sg` -/

theorem fofs_zero (o : ptrofs) : Sparse.fofs o 0 = Ptrofs.unsigned o := by
  apply intOfZ_injective
  rw [Sparse.Updatecan.fofs_int (by simp only [intOfZ_Ptrofs_unsigned]; have := (bvp o).isLt; omega)
    (Int.le_refl _)]
  omega

theorem sparse_init (xi : ExternalCalls) : sparseRep.InitFn xi sparseRep.init := by
  refine ⟨_, by simp [Genv.find_funct, sparseRep, Sparse.funct_init], type_initS,
    fun g gl bg gofs gout bc cofs hout lab ptn act bopt oofs bs so M => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hc, ⟨G, hG, hg, hacc⟩, hok, ⟨hsi, h72⟩, hopt, ⟨sv, hs⟩,
    hsep⟩ => ?_
  subst hG
  have hw := hc.work
  have hd := hsep.distinct
  have e0 : elemOfs .Mint32 (intOfZ (Ptrofs.unsigned so)) 0 = Ptrofs.unsigned so := by
    show zOfInt (intOfZ (Ptrofs.unsigned so) + 4 * 0) = _
    rw [Int.mul_zero, Int.add_zero, zOfInt_intOfZ]
  refine ⟨_, Satisfies.grow (Sparse.Init.init_satisfies G bg gofs gl.bv gl.vo gl.bd gl.dofs gl.be
    gl.eo gout bc cofs hout lab ptn act bopt oofs bs so (.Vint (ir M))),
    ⟨hargs, hg, hsi, h72, by rw [fofs_zero]; exact hopt, e0 ▸ hs.writable 0 (by decide), hc.n0,
      by have := hc.nlt; omega, hok, (pw_ab hd (a := bg) (by simp) (by simp)).symm,
      (List.pairwise_cons.1 (pw_right hd)).1 bs (by simp)⟩, ?_⟩
  rintro t v m' ⟨⟨rfl, capV, bV, capD, bD, capE, bE, -, -, -, -, -, -, nV, nD, nE, -, -, -, hcan, -,
    -, hstld, hstW, hu, -, kbc, kbs⟩, hval⟩
  have hout : ∀ z, z ∈ [bc, bs] → Mem.valid_block m z → z ∉ sparseWGlobs ∧
      ¬ InUse m sparseSlots z := fun z hz _ => sep_out hsep (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl <;> simp)
  have hW : ∀ z, (z = bc ∨ z = bs ∨ ¬ Mem.valid_block m z) → z ∈ ([] : List block) ∨
      InUse m ([] : List Slot) z ∨ ¬ Mem.valid_block m z ∨ z ∈ [bc, bs] := by
    rintro z (rfl | rfl | h)
    · exact .inr (.inr (.inr (by simp)))
    · exact .inr (.inr (.inr (by simp)))
    · exact .inr (.inr (.inl h))
  have hPs : ∀ p ∈ ([] : List Slot), p ∈ sparseSlots := fun _ h => absurd h List.not_mem_nil
  refine ⟨rfl, ⟨hs.base_nonneg, hs.fits, fun i hi => ?_, fun i hi => ?_⟩,
    { bv := bV, vo := Ptrofs.zero, bd := bD, dofs := Ptrofs.zero, be := bE, eo := Ptrofs.zero,
      es := esOf (Sparse.Graph.ofGraph G).blank.neighbors.size bE },
    ⟨hcan, h72, rfl⟩,
    fun z hz => ?_,
    sparse_step hw hval hu [] [] (fun _ h => absurd h List.not_mem_nil) hPs (by decide) hW hout
      (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
      (marks1_keep hw hu (fun _ h => absurd h List.not_mem_nil) hPs hW hout (by decide) (by decide)
        (by decide) (by decide))
      (marks2_keep hw hu (fun _ h => absurd h List.not_mem_nil) hPs hW hout (by decide) (by decide)
        (by decide) (by decide))
      (hits_keep hw hu (fun _ h => absurd h List.not_mem_nil) hPs hW hout (by decide) (by decide)
        (by decide)) fun z hz _ => ?_⟩
  · rw [show i = 0 by omega, e0]; exact hstld
  · rw [show i = 0 by omega, e0]; exact hstW
  · change z ∈ bc :: bV :: bD :: esOf (Sparse.Graph.ofGraph G).blank.neighbors.size bE at hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | rfl | rfl | hz
    · exact .inl rfl
    · exact .inr nV
    · exact .inr nD
    · obtain ⟨hp, rfl⟩ := mem_esOf hz
      exact .inr (nE (by simpa [Sparse.Graph.blank, Sparse.Graph.ofGraph] using hp))
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · exact kbc
    · exact kbs

/-! ### `nausparse_freedyn` -/

theorem pw_of_bp {ds : List FreeD} {R : FreeD → FreeD → Prop}
    (hbp : (ds.map FreeD.bp).Pairwise (· ≠ ·))
    (h : ∀ d ∈ ds, ∀ d' ∈ ds, d.bp ≠ d'.bp → R d d') : ds.Pairwise R := by
  induction ds with
  | nil => exact .nil
  | cons d ds ih =>
    rw [List.map_cons, List.pairwise_cons] at hbp
    refine .cons (fun d' hd' => h d List.mem_cons_self d' (List.mem_cons_of_mem _ hd')
      (hbp.1 _ (List.mem_map_of_mem hd'))) (ih hbp.2 fun a ha b hb =>
        h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))

theorem sparse_freedyn (xi : ExternalCalls) : sparseRep.FreedynFn xi sparseRep.freedyn := by
  refine ⟨_, by simp [Genv.find_funct, sparseRep, funct_freedynS], type_freedynS,
    fun capD bD => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hw, dsn, hbD⟩ => ?_
  obtain ⟨c1, b1, d1⟩ := hw.1.dyn (VM1, VM1S, 2) (by simp [sparseSlots])
  obtain ⟨c2, b2, d2⟩ := hw.1.dyn (VM2, VM2S, 2) (by simp [sparseSlots])
  obtain ⟨w1, bw1, e1⟩ := hw.1.dyn (W1, W1S, 4) (by simp [sparseSlots])
  obtain ⟨w2, bw2, e2⟩ := hw.1.dyn (W2, W2S, 4) (by simp [sparseSlots])
  obtain ⟨w3, bw3, e3⟩ := hw.1.dyn (W3, W3S, 4) (by simp [sparseSlots])
  obtain ⟨w4, bw4, e4⟩ := hw.1.dyn (W4, W4S, 4) (by simp [sparseSlots])
  let ds := Sparse.sparseDs c1 b1 c2 b2 w1 bw1 w2 bw2 w3 bw3 w4 bw4 capD bD
  have hcls : ∀ d ∈ ds, ((d.bp, d.bs, d.c) ∈ sparseSlots ∧ DynAt m d.bp d.bs d.c d.cap d.blk) ∨
      (d.bp = SN ∧ d.bs = SNS ∧ d.c = 8 ∧ d.cap = capD ∧ d.blk = bD) := by
    intro d hd
    simp only [ds, Sparse.sparseDs, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inl ⟨by dsimp only; decide, d1⟩
    · exact .inl ⟨by dsimp only; decide, d2⟩
    · exact .inl ⟨by dsimp only; decide, e1⟩
    · exact .inl ⟨by dsimp only; decide, e2⟩
    · exact .inl ⟨by dsimp only; decide, e3⟩
    · exact .inl ⟨by dsimp only; decide, e4⟩
    · exact .inr ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hglob : FreeD.globals ds = [VM1S, VM1, VM2S, VM2, W1S, W1, W2S, W2, W3S, W3, W4S, W4, SNS, SN] :=
    rfl
  have hgl : ∀ z ∈ FreeD.globals ds, z ∈ sparseWGlobs ∨ z = SN ∨ z = SNS := by
    rw [hglob]; decide
  have hgL : ∀ z ∈ FreeD.globals ds, z ∈ sparseGlobs := by rw [hglob]; decide
  have hbp : (ds.map FreeD.bp).Pairwise (· ≠ ·) := by
    rw [show ds.map FreeD.bp = [VM1, VM2, W1, W2, W3, W4, SN] from rfl]; decide
  have hok : FreeD.Ok m ds := by
    refine ⟨Sparse.sparseDs_sym _ _ _ _ _ _ _ _ _ _ _ _ _ _, fun d hd => ?_,
      Sparse.sparseDs_glob _ _ _ _ _ _ _ _ _ _ _ _ _ _, fun d hd hc hm => ?_, pw_of_bp hbp ?_⟩
    · rcases hcls d hd with ⟨-, h⟩ | ⟨h1, h2, h3, h4, h5⟩
      · exact h
      · rw [h1, h2, h3, h4, h5]; exact dsn
    · rcases hcls d hd with ⟨hs, h⟩ | ⟨-, -, -, h4, h5⟩
      · exact hw.1.notin _ ⟨_, hs, _, hc, h⟩ (List.mem_append_left _ (hgL _ hm))
      · rw [h5] at hm; rw [h4] at hc; exact (hbD hc).2 (hgL _ hm)
    · intro d hd d' hd' hne hc hc' e
      rcases hcls d hd with ⟨hs, h⟩ | ⟨h1, -, -, h4, h5⟩ <;>
        rcases hcls d' hd' with ⟨hs', h'⟩ | ⟨h1', -, -, h4', h5'⟩
      · have := hw.1.sep _ hs _ hs' _ _ _ hc hc' h (e ▸ h')
        exact hne (congrArg Prod.fst this)
      · rw [h4'] at hc'; exact (hbD hc').1 (h5' ▸ e ▸ ⟨_, hs, _, hc, h⟩)
      · rw [h4] at hc; exact (hbD hc).1 (h5 ▸ e.symm ▸ ⟨_, hs', _, hc', h'⟩)
      · exact hne (h1.trans h1'.symm)
  refine ⟨_, Sparse.freedyn_satisfies c1 b1 c2 b2 w1 bw1 w2 bw2 w3 bw3 w4 bw4 capD bD,
    ⟨hargs, hok⟩, ?_⟩
  rintro t v m' ⟨rfl, hD', hu, hnb⟩
  refine ⟨rfl, hu.mono fun z hz => ?_, fun b => hD' ⟨sparse.id.«nausparse:snwork», sparse.id.«nausparse:snwork_sz», SN, SNS, tulong, 8,
    capD, bD⟩ (by simp [ds, Sparse.sparseDs]) 8 b, hnb⟩
  rcases hz with hz | ⟨d, hd, hc, rfl⟩
  · rcases hgl z hz with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  · rcases hcls d hd with ⟨hs, h⟩ | ⟨-, -, -, h4, h5⟩
    · exact .inr (.inr (.inr (.inl ⟨_, hs, _, hc, h⟩)))
    · exact .inr (.inr (.inr (.inr ⟨h4 ▸ hc, h5⟩)))

/-! ### The dispatch record -/

/-- `dispatch_sparse`'s procedures with their specifications, given `refine_sg`'s. -/
def sparseDispatch
    (hRef : ∀ xi M, sparseRep.RefineFn xi M (.Vptr (sparseRep.refineAt M) Ptrofs.zero)) :
    DispatchC sparseGe sparseOps where
  toDispatchRep := sparseRep
  isautom_fn := sparse_isautom
  testcanlab_fn := sparse_testcanlab
  updatecan_fn := sparse_updatecan
  refine_fn := hRef
  cheapautom_fn := sparse_cheapautom
  targetcell_fn := sparse_targetcell
  check_fn := sparse_check
  freedyn_fn := sparse_freedyn
  init_fn xi _ := sparse_init xi

end NautyVerified.Proofs.Dispatch
