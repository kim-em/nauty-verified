import NautyVerified.Proofs.Dispatch.Sparse.Rep
import NautyVerified.Proofs.Sparse.Isautom.Satisfies
import NautyVerified.Proofs.Sparse.Testcanlab.Satisfies
import NautyVerified.Proofs.Sparse.Targetcell.Satisfies
import NautyVerified.Proofs.Sparse.Check
import NautyVerified.Proofs.Sparse.Refine.State
import NautyVerified.Proofs.Cheapautom.Satisfies
import NautyVerified.Logic.Grow

/-!
# nausparse.c's procedures meet the dispatch specifications

`isautom_sg`, `testcanlab_sg`, `updatecan_sg`, `cheapautom_sg`,
`targetcell_sg`, `nausparse_check`, `nausparse_freedyn` and `init_sg` meet the
specifications of `Dispatch/Spec.lean` at `sparseRep`, from their proofs in
`Proofs/Sparse/*`.
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
open NautyVerified.Proofs.Sparse (HitsOk SparseGraphAt CanonAt CanonRows MarksAt base start)
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
local notation "SN" => Sparse.Block.snwork
local notation "SNS" => Sparse.Block.snworkSz

kernel_rfl type_isautomS : type_of_fundef (.Internal sparse.fn.isautom_sg) = isautomType
kernel_rfl type_testcanlabS : type_of_fundef (.Internal sparse.fn.testcanlab_sg) = testcanlabType
kernel_rfl type_updatecanS : type_of_fundef (.Internal sparse.fn.updatecan_sg) = updatecanType
kernel_rfl type_cheapautomS : type_of_fundef (.Internal dense.fn.cheapautom) = cheapautomType
kernel_rfl type_targetcellS : type_of_fundef (.Internal sparse.fn.targetcell_sg) = targetcellType
kernel_rfl type_checkS : type_of_fundef (.Internal sparse.fn.nausparse_check) = checkType
kernel_rfl type_freedynS : type_of_fundef (.Internal sparse.fn.nausparse_freedyn) = freedynType
kernel_rfl type_initS : type_of_fundef (.Internal sparse.fn.init_sg) = initType
kernel_rfl type_refineS : type_of_fundef (.Internal sparse.fn.refine_sg) = refineType

kernel_rfl funct_cheapautomS : Genv.find_funct_ptr sparseGe.genv_genv (PArith.BinPos.Pos.of_nat 306) =
  some (.Internal sparse.fn.cheapautom_sg)
kernel_rfl funct_checkS : Genv.find_funct_ptr sparseGe.genv_genv (PArith.BinPos.Pos.of_nat 40) =
  some (.Internal sparse.fn.nausparse_check)
kernel_rfl funct_freedynS : Genv.find_funct_ptr sparseGe.genv_genv (PArith.BinPos.Pos.of_nat 227) =
  some (.Internal sparse.fn.nausparse_freedyn)

theorem ng {z x : block} (h : z ∉ sparseGlobs) (hx : x ∈ sparseGlobs := by decide) : z ≠ x :=
  fun e => h (e ▸ hx)

theorem slot_sep {m : mem} (hw : sparseWork m) {p q : Slot} (hp : p ∈ sparseSlots)
    (hq : q ∈ sparseSlots) (hpq : p ≠ q) {c c' : Nat} {b b' : block} (hc : 0 < c) (hc' : 0 < c')
    (d : p.At m c b) (d' : q.At m c' b') : b ≠ b' := by
  rintro rfl
  exact hpq (hw.1.sep p hp q hq c c' b hc hc' d d')

theorem inUse_L {m : mem} (hw : sparseWork m) {b z : block} (hb : InUse m sparseSlots b)
    (hz : z ∈ sparseL := by decide) : b ≠ z := by
  rintro rfl; exact hw.1.notin _ hb hz

/-! ### `isautom_sg` -/

theorem sparse_isautom (xi : ExternalCalls) : sparseRep.IsautomFn xi sparseRep.isautom := by
  refine ⟨_, by simp [Genv.find_funct, sparseRep, Sparse.funct_isautom], type_isautomS,
    fun g gl bg gofs bpm pofs perm M => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hc, ⟨G, hG, hg, _⟩, _, hp, hps, hsep⟩ => ?_
  subst hG
  have hw := hc.work
  obtain ⟨cap, b, st, mk, hM⟩ := hw.2.2.1
  refine ⟨_, Satisfies.grow (Sparse.Isautom.isautom_satisfies G bg gofs gl.bv gl.vo gl.bd gl.dofs
    gl.be gl.eo bpm pofs perm M cap b st mk),
    ⟨hargs, hg, hp, hps, hM, hc.n0, by have := hc.nlt; omega, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨hv, hgl, -, hne⟩ := sep_z hsep (z := z)
      (by rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp)
    exact ⟨hv, ng hgl, ng hgl, ng hgl, fun h0 => hne (vm1_inUse hM h0)⟩
  · rintro t v m' ⟨⟨rfl, hv, cap', b', st', mk', hM', -, hr, hu, -⟩, hval⟩
    have hW : ∀ z, Sparse.MarksS m cap b b' z → z ∈ [VM1, VM1S, VM1V] ∨
        InUse m [(VM1, VM1S, 2)] z ∨ ¬ Mem.valid_block m z ∨ False := by
      rintro z (rfl | rfl | rfl | ⟨h0, rfl⟩ | ⟨h0, rfl⟩)
      · exact .inl (by simp)
      · exact .inl (by simp)
      · exact .inl (by simp)
      · exact .inr (.inl ⟨_, List.mem_singleton_self _, cap, h0, hM.dyn⟩)
      · exact .inr (.inr (.inl h0))
    refine ⟨rfl, hv, sparse_step hw hval hu [VM1, VM1S, VM1V] [(VM1, VM1S, 2)] (by decide)
      (by simp [sparseSlots]) (by decide) hW (fun _ h => h.elim) ?_ ?_ ⟨_, _, _, _, hM'⟩
      (marks2_keep hw hu (by decide) (by simp [sparseSlots]) hW (fun _ h => h.elim) (by decide)
        (by decide) (by decide) (by decide))
      (hits_keep hw hu (by decide) (by simp [sparseSlots]) hW (fun _ h => h.elim) (by decide)
        (by decide) (by decide)) (fun _ h => h.elim)⟩
    · intro p hp
      rw [List.mem_singleton] at hp; subst hp
      exact ⟨cap, b, cap', b', hM.dyn, hM'.dyn, hr⟩
    · intro p hp q hq _ _ _ _ _ _ _ _
      rw [List.mem_singleton] at hp hq; rw [hp, hq]

/-! ### `cheapautom_sg`, `nausparse_check` -/

theorem sparse_cheapautom (xi : ExternalCalls) : sparseRep.CheapautomFn xi sparseRep.cheapautom := by
  refine ⟨_, by simp [Genv.find_funct, sparseRep, funct_cheapautomS, sparse.fn.cheapautom_sg_eq],
    type_cheapautomS, fun bp pofs ptn level n => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hw, ha, hs, hsm, hl, hn, hlev⟩ =>
    ⟨_, Cheapautom.cheapautom_satisfies bp pofs ptn level n, ⟨hargs, ha, hs, hsm, hl, hn, hlev⟩, ?_⟩
  rintro t v m' ⟨rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, DispatchRep.Step.refl _ hw _⟩

theorem sparse_check (xi : ExternalCalls) : @DispatchRep.CheckFn sparseGe xi sparseRep.check :=
  ⟨_, by simp [Genv.find_funct, sparseRep, funct_checkS], type_checkS,
    fun mv nv => Sparse.check_satisfies mv nv⟩

/-! ### `targetcell_sg` -/

/-- Four values, indexed by `Fin 4`. -/
def f4 {α : Type} (a0 a1 a2 a3 : α) (k : Fin 4) : α :=
  match k.val with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | _ => a3

theorem fin4 {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ k, P k := by
  intro ⟨k, hk⟩
  match k, hk with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3

/-- The pairs `work1` to `work4` as slots. -/
abbrev workSlots : List Slot := [(W1, W1S, 4), (W2, W2S, 4), (W3, W3S, 4), (W4, W4S, 4)]

theorem workSlot_mem : ∀ k : Fin 4,
    (Sparse.Bestcell.wp k, Sparse.Bestcell.ws k, 4) ∈ workSlots := by decide

theorem workSlot_inv {p : Slot} (hp : p ∈ workSlots) :
    ∃ k, p = (Sparse.Bestcell.wp k, Sparse.Bestcell.ws k, 4) := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

theorem wp_inj : ∀ k k' : Fin 4, Sparse.Bestcell.wp k = Sparse.Bestcell.wp k' → k = k' := by
  decide

theorem bwglobs_sub : ∀ z ∈ Sparse.Bestcell.wglobs, z ∈ sparseWGlobs := by decide

theorem works_of {m : mem} (hw : sparseWork m) :
    ∃ c b, Sparse.Bestcell.Works m c b ∧ ∀ k, 0 < c k → InUse m sparseSlots (b k) := by
  obtain ⟨c1, b1, d1⟩ := hw.1.dyn (W1, W1S, 4) (by simp [sparseSlots])
  obtain ⟨c2, b2, d2⟩ := hw.1.dyn (W2, W2S, 4) (by simp [sparseSlots])
  obtain ⟨c3, b3, d3⟩ := hw.1.dyn (W3, W3S, 4) (by simp [sparseSlots])
  obtain ⟨c4, b4, d4⟩ := hw.1.dyn (W4, W4S, 4) (by simp [sparseSlots])
  have hd : ∀ k, DynAt m (Sparse.Bestcell.wp k) (Sparse.Bestcell.ws k) 4 (f4 c1 c2 c3 c4 k)
      (f4 b1 b2 b3 b4 k) :=
    fin4 (P := fun k => DynAt m (Sparse.Bestcell.wp k) (Sparse.Bestcell.ws k) 4 (f4 c1 c2 c3 c4 k)
      (f4 b1 b2 b3 b4 k)) d1 d2 d3 d4
  have hsub : ∀ k, (Sparse.Bestcell.wp k, Sparse.Bestcell.ws k, 4) ∈ sparseSlots := by decide
  have hu : ∀ k, 0 < f4 c1 c2 c3 c4 k → InUse m sparseSlots (f4 b1 b2 b3 b4 k) :=
    fun k hk => ⟨_, hsub k, _, hk, hd k⟩
  refine ⟨f4 c1 c2 c3 c4, f4 b1 b2 b3 b4, ⟨hd, fun k hk hm => ?_, fun k k' hkk hk hk' e => ?_⟩, hu⟩
  · exact hw.1.notin _ (hu k hk) (wglobs_L (bwglobs_sub _ hm))
  · have := hw.1.sep _ (hsub k) _ (hsub k') _ _ _ hk hk' (hd k) (e ▸ hd k')
    exact hkk (wp_inj _ _ (congrArg Prod.fst this))

theorem sparse_targetcell (xi : ExternalCalls) : sparseRep.TargetcellFn xi sparseRep.targetcell := by
  refine ⟨_, by simp [Genv.find_funct, sparseRep, Sparse.funct_targetcell], type_targetcellS,
    fun g gl bg gofs bl lofs lab bp pofs ptn level tcLevel dg hint M => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hc, ⟨G, hG, hg, _⟩, _, hl, hlsm, hlon, hp, hps, hpsm,
    hpl, hlev, hh, hh0, htc, hsep⟩ => ?_
  subst hG
  have hw := hc.work
  obtain ⟨c, b, hW4, hu4⟩ := works_of hw
  refine ⟨_, Satisfies.grow (Sparse.Targetcell.targetcell_satisfies G bg gofs gl.bv gl.vo gl.bd
    gl.dofs gl.be gl.eo bl lofs lab bp pofs ptn level tcLevel dg hint M c b),
    ⟨hargs, ⟨hg, hl, hlsm, hlon, hp, hps, hpsm, hpl, hlev, hW4, fun z hz => ?_, hc.n0, hc.nlt⟩,
      hh, hh0, htc⟩, ?_⟩
  · have hz' : z ∈ sparseRep.graphBlocks gl bg ++ [bl, bp] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    obtain ⟨hv, hgl, -, hne⟩ := sep_z hsep hz'
    exact ⟨hv, fun hm => hgl (List.mem_append_left _ (bwglobs_sub _ hm)), fun k hk e =>
      hne (hu4 k hk) e⟩
  · rintro t v m' ⟨⟨rfl, hv, c', b', hW4', hr, hu, -, hH⟩, hval⟩
    have hH2 : HitsOk m (c 2) (b 2) := by
      obtain ⟨c3, b3, d3, hH3⟩ := hw.2.2.2.2
      have e := (hW4.dyn 2).same_cap d3
      by_cases hc : 0 < c 2
      · rw [← (hW4.dyn 2).same_block d3 hc, ← e]; exact hH3
      · rw [show c 2 = 0 by omega]; exact HitsOk.zero _ _
    have hW : ∀ z, Sparse.Bestcell.worksSet m c b z → z ∈ Sparse.Bestcell.wglobs ∨
        InUse m workSlots z ∨ ¬ Mem.valid_block m z ∨ False := by
      rintro z (h | ⟨k, hk, rfl⟩ | h)
      · exact .inl h
      · exact .inr (.inl ⟨_, workSlot_mem k, _, hk, hW4.dyn k⟩)
      · exact .inr (.inr (.inl h))
    have hPs : ∀ p ∈ workSlots, p ∈ sparseSlots := by decide
    refine ⟨rfl, hv, sparse_step hw hval hu Sparse.Bestcell.wglobs workSlots (by decide) hPs
      (by decide) hW (fun _ h => h.elim) ?_ ?_
      (marks1_keep hw hu (by decide) hPs hW (fun _ h => h.elim) (by decide) (by decide) (by decide)
        (by decide))
      (marks2_keep hw hu (by decide) hPs hW (fun _ h => h.elim) (by decide) (by decide) (by decide)
        (by decide)) ⟨c' 2, b' 2, hW4'.dyn 2, hH hH2⟩ (fun _ h => h.elim)⟩
    · intro p hp
      obtain ⟨k, rfl⟩ := workSlot_inv hp
      exact ⟨c k, b k, c' k, b' k, hW4.dyn k, hW4'.dyn k, hr k⟩
    · intro p hp q hq e e' z he he' dp dq _
      obtain ⟨k, rfl⟩ := workSlot_inv hp
      obtain ⟨k', rfl⟩ := workSlot_inv hq
      by_cases hkk : k = k'
      · rw [hkk]
      · have e1 := (hW4'.dyn k).same_cap dp
        have e2 := (hW4'.dyn k').same_cap dq
        subst e1; subst e2
        exact absurd (((hW4'.dyn k).same_block dp he).symm.trans ((hW4'.dyn k').same_block dq he'))
          (hW4'.distinct k k' hkk he he')

end NautyVerified.Proofs.Dispatch
