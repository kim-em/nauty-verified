import NautyVerified.Proofs.Dispatch.Sparse.Fns
import NautyVerified.Proofs.Sparse.Updatecan.Satisfies

/-!
# The sparse procedures on the canonical store, and `nausparse_freedyn`

`testcanlab_sg`, `updatecan_sg` and `init_sg` (on `canong`, `CanonAt`) and
`nausparse_freedyn` meet the dispatch specifications at `sparseRep`.
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
local notation "VM1V" => Sparse.Block.vmark1Val
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

/-- Entries of the first and second part of a pairwise distinct list differ. -/
theorem pw_ab {A B : List block} (h : (A ++ B).Pairwise (· ≠ ·)) {a b : block} (ha : a ∈ A)
    (hb : b ∈ B) : a ≠ b :=
  (List.pairwise_append.1 h).2.2 a ha b hb

theorem pw_left {A B : List block} (h : (A ++ B).Pairwise (· ≠ ·)) : A.Pairwise (· ≠ ·) :=
  (List.pairwise_append.1 h).1

theorem pw_right {A B : List block} (h : (A ++ B).Pairwise (· ≠ ·)) : B.Pairwise (· ≠ ·) :=
  (List.pairwise_append.1 h).2.1

theorem pw4s {a b c d : block} (h : [a, b, c, d].Pairwise (· ≠ ·)) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false] at h
  exact ⟨h.1 _ (.inl rfl), h.1 _ (.inr (.inl rfl)), h.1 _ (.inr (.inr rfl)), h.2.1 _ (.inl rfl),
    h.2.1 _ (.inr rfl), h.2.2.1 _ rfl⟩

/-! ### `testcanlab_sg` -/

theorem sparse_testcanlab (xi : ExternalCalls) : sparseRep.TestcanlabFn xi sparseRep.testcanlab := by
  refine ⟨_, by simp [Genv.find_funct, sparseRep, Sparse.funct_testcanlab], type_testcanlabS,
    fun g gl bg gofs c cl bc cofs bl lofs lab bs so M => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hc, ⟨G, hG, hg, _⟩, _, ⟨hca, _, hes⟩, _, hl, hls, hlsm,
    hsurj, hinj, ⟨sv, hs⟩, hsep⟩ => ?_
  subst hG
  -- the `e` block for `testcanlab_sg`: the store's, or with no edges (`e` is `NULL`) the graph's
  let cbe := if c.neighbors.size = 0 then gl.be else cl.be
  let ceo := if c.neighbors.size = 0 then gl.eo else cl.eo
  have hca' := hca.rebeIf gl.be gl.eo
  have hcbe : cbe ∈ sparseRep.graphBlocks gl bg ++ sparseRep.canonBlocks cl bc := by
    by_cases h0 : c.neighbors.size = 0
    · simp [cbe, h0]
    · have : cl.be ∈ cl.es := hes ▸ esOf_mem _ (by omega)
      simp [cbe, h0, this]
  have hw := hc.work
  obtain ⟨cap, b, st, mk, hM⟩ := hw.2.2.1
  obtain ⟨capW, bW, dW⟩ := hw.1.dyn (W1, W1S, 4) (by simp [sparseSlots])
  have hd := hsep.distinct
  have hAB := pw_left hd
  have hbs_e : bs ≠ cbe := (pw_ab hd (b := bs) hcbe (by simp)).symm
  have hbs_ge : bs ≠ gl.be := (pw_ab hd (b := bs) (by simp) (by simp)).symm
  have hWu : 0 < capW → InUse m sparseSlots bW := fun h => ⟨_, by simp [sparseSlots], _, h, dW⟩
  have hbW : 0 < capW → 0 < cap → bW ≠ b := fun h1 h2 =>
    slot_sep hw (p := (W1, W1S, 4)) (q := (VM1, VM1S, 2)) (by simp [sparseSlots])
      (by simp [sparseSlots]) (by decide) h1 h2 dW hM.dyn
  refine ⟨_, Satisfies.grow (Sparse.Testcanlab.testcanlab_satisfies G bg gofs gl.bv gl.vo gl.bd
    gl.dofs gl.be gl.eo c bc cofs cl.bv cl.vo cl.bd cl.dofs cbe ceo lab bl lofs bs so sv M capW
    bW cap b st mk),
    ⟨hargs, hg, hca', hl, hls, hlsm, fun a a' ha ha' h => hinj a ha a' ha' h, hsurj, hs, dW, hM, hc.n0,
      by have := hc.nlt; omega, ?_, hbs_e, hbs_ge,
      fun h => ⟨inUse_L hw (hWu h), inUse_L hw (hWu h), inUse_L hw (hWu h), hbW h⟩,
      fun h => ⟨inUse_L hw (vm1_inUse hM h), inUse_L hw (vm1_inUse hM h)⟩⟩, ?_⟩
  · intro z hz
    have hz' : z ∈ sparseRep.graphBlocks gl bg ++ sparseRep.canonBlocks cl bc ++ [bl, bs] := by
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · exact List.mem_append_left _ hcbe
      · simp
      · simp
    obtain ⟨hv, hgl, -, hne⟩ := sep_z hsep hz'
    exact ⟨hv, ng hgl, ng hgl, ng hgl, ng hgl, ng hgl, fun h0 => hne (vm1_inUse hM h0),
      fun h0 => hne (hWu h0)⟩
  · rintro t v m' ⟨⟨rfl, hv, harr, capW', bW', cap', b', st', mk', dW', -, rW, hM', -, rM, hu, -,
      hbb, hK⟩, hval⟩
    have hW : ∀ z, (z = bs ∨ z = W1 ∨ z = W1S ∨ (0 < capW ∧ z = bW) ∨
        (¬ Mem.valid_block m bW' ∧ z = bW') ∨ Sparse.MarksS m cap b b' z) →
        z ∈ [VM1, VM1S, VM1V, W1, W1S] ∨ InUse m [(VM1, VM1S, 2), (W1, W1S, 4)] z ∨
          ¬ Mem.valid_block m z ∨ z = bs := by
      rintro z (h | rfl | rfl | ⟨h0, rfl⟩ | ⟨h0, rfl⟩ | (rfl | rfl | rfl | ⟨h0, rfl⟩ | ⟨h0, rfl⟩))
      · exact .inr (.inr (.inr h))
      · exact .inl (by simp)
      · exact .inl (by simp)
      · exact .inr (.inl ⟨(W1, W1S, 4), by simp, _, h0, dW⟩)
      · exact .inr (.inr (.inl h0))
      · exact .inl (by simp)
      · exact .inl (by simp)
      · exact .inl (by simp)
      · exact .inr (.inl ⟨(VM1, VM1S, 2), by simp, _, h0, hM.dyn⟩)
      · exact .inr (.inr (.inl h0))
    have hout : ∀ z, z = bs → Mem.valid_block m z → z ∉ sparseWGlobs ∧ ¬ InUse m sparseSlots z :=
      fun z hz _ => sep_out hsep (by rw [hz]; simp)
    have hPs : ∀ p ∈ [(VM1, VM1S, 2), (W1, W1S, 4)], p ∈ sparseSlots := by decide
    refine ⟨rfl, hv, harr, sparse_step hw hval hu [VM1, VM1S, VM1V, W1, W1S]
      [(VM1, VM1S, 2), (W1, W1S, 4)] (by decide) hPs (by decide) hW hout ?_ ?_ ⟨_, _, _, _, hM'⟩
      (marks2_keep hw hu (by decide) hPs hW hout (by decide) (by decide) (by decide) (by decide))
      (fun z hz _ => hz ▸ hK)⟩
    · intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨cap, b, cap', b', hM.dyn, hM'.dyn, rM⟩
      · exact ⟨capW, bW, capW', bW', dW, dW', rW⟩
    · intro p hp q hq e e' z he he' dp dq _
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp hq
      have zM : ∀ {e}, 0 < e → Slot.At m' (VM1, VM1S, 2) e z → z = b' := fun he d =>
        hM'.dyn.same_block d (hM'.dyn.same_cap d ▸ he)
      have zW : ∀ {e}, 0 < e → Slot.At m' (W1, W1S, 4) e z → z = bW' := fun he d =>
        dW'.same_block d (dW'.same_cap d ▸ he)
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · rfl
      · exact absurd ((zM he dp).symm.trans (zW he' dq)) hbb
      · exact absurd ((zM he' dq).symm.trans (zW he dp)) hbb
      · rfl

/-! ### `updatecan_sg` -/

theorem sparse_updatecan (xi : ExternalCalls) : sparseRep.UpdatecanFn xi sparseRep.updatecan := by
  refine ⟨_, by simp [Genv.find_funct, sparseRep, Sparse.funct_updatecan], type_updatecanS,
    fun g gl bg gofs c cl bc cofs bl lofs lab sr M => ?_⟩
  refine Satisfies.of_pre fun args m ⟨hargs, hc, ⟨G, hG, hg, _⟩, _, ⟨hca, h72, hes⟩, hok, hl, hls,
    hlsm, hsurj, hinj, _, hsep, hfit⟩ => ?_
  subst hG
  have hw := hc.work
  obtain ⟨capW, bW, dW⟩ := hw.1.dyn (W1, W1S, 4) (by simp [sparseSlots])
  have hd := hsep.distinct
  have hAB := pw_left hd
  have hbeC : 0 < c.neighbors.size → cl.be ∈ cl.es := fun hp => hes ▸ esOf_mem _ hp
  have hC := pw_right hAB
  simp only [sparseRep_canonBlocks, List.pairwise_cons, List.mem_cons] at hC
  have hB1 : bc ≠ cl.bv := hC.1 _ (.inl rfl)
  have hB2 : bc ≠ cl.bd := hC.1 _ (.inr (.inl rfl))
  have hB3 : 0 < c.neighbors.size → bc ≠ cl.be := fun hp => hC.1 _ (.inr (.inr (hbeC hp)))
  have hB4 : cl.bv ≠ cl.bd := hC.2.1 _ (.inl rfl)
  have hB5 : 0 < c.neighbors.size → cl.bv ≠ cl.be := fun hp => hC.2.1 _ (.inr (hbeC hp))
  have hB6 : 0 < c.neighbors.size → cl.bd ≠ cl.be := fun hp => hC.2.2.1 _ (hbeC hp)
  have hWC : ∀ z, Sparse.Updatecan.Wr bc cl.bv cl.bd cl.be c.neighbors.size z →
      z ∈ sparseRep.canonBlocks cl bc := by
    rintro z (rfl | rfl | rfl | ⟨hp, rfl⟩)
    · simp
    · simp
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hbeC hp)))
  have hWu : 0 < capW → InUse m sparseSlots bW := fun h => ⟨_, by simp [sparseSlots], _, h, dW⟩
  have hmem : ∀ z, Sparse.Updatecan.Rd bg gl.bv gl.bd gl.be bl z ∨
      Sparse.Updatecan.Wr bc cl.bv cl.bd cl.be c.neighbors.size z →
      z ∈ sparseRep.graphBlocks gl bg ++ sparseRep.canonBlocks cl bc ++ [bl] := by
    rintro z ((rfl | rfl | rfl | rfl | rfl) | hz)
    · simp
    · simp
    · simp
    · simp
    · simp
    · exact List.mem_append_left _ (List.mem_append_right _ (hWC z hz))
  refine ⟨_, Satisfies.grow (Sparse.Updatecan.updatecan_satisfies G bg gofs gl.bv gl.vo gl.bd
    gl.dofs gl.be gl.eo c bc cofs cl.bv cl.vo cl.bd cl.dofs cl.be cl.eo lab bl lofs sr M capW bW),
    ⟨hargs, hg, hca, hok.1, hfit, by omega, hl, hls, hlsm, fun a a' ha ha' h => hinj a ha a' ha' h,
      hsurj, dW, hc.n0, by have := hc.nlt; omega, fun z hz => ?_, ?_, hB1, hB2, hB3, hB4, hB5, hB6⟩,
      ?_⟩
  · obtain ⟨hv, hgl, -, hne⟩ := sep_z hsep (hmem z hz)
    exact ⟨hv, ng hgl, ng hgl, fun h0 => hne (hWu h0)⟩
  · rintro z hwz hrz
    have hzB := hWC z hwz
    rcases hrz with h | h | h | h | h
    · exact pw_ab hAB (a := bg) (by simp) hzB h.symm
    · exact pw_ab hAB (a := gl.bv) (by simp) hzB h.symm
    · exact pw_ab hAB (a := gl.bd) (by simp) hzB h.symm
    · exact pw_ab hAB (a := gl.be) (by simp) hzB h.symm
    · exact pw_ab hd (b := bl) (List.mem_append_right _ hzB) (by simp) h
  · rintro t v m' ⟨⟨rfl, capW', bW', dW', -, rW, hcan, -, -, hu, -, kbc, kv, kd, ke⟩, hval⟩
    have hsz := Sparse.updatecan_sizes (Sparse.Graph.ofGraph G) c lab sr
    have hW : ∀ z, (Sparse.Updatecan.Wr bc cl.bv cl.bd cl.be c.neighbors.size z ∨ z = W1 ∨
        z = W1S ∨ (0 < capW ∧ z = bW) ∨ (¬ Mem.valid_block m bW' ∧ z = bW')) →
        z ∈ [W1, W1S] ∨ InUse m [(W1, W1S, 4)] z ∨ ¬ Mem.valid_block m z ∨
          z ∈ sparseRep.canonBlocks cl bc := by
      rintro z (h | rfl | rfl | ⟨h0, rfl⟩ | ⟨h0, rfl⟩)
      · exact .inr (.inr (.inr (hWC z h)))
      · exact .inl (by simp)
      · exact .inl (by simp)
      · exact .inr (.inl ⟨(W1, W1S, 4), by simp, _, h0, dW⟩)
      · exact .inr (.inr (.inl h0))
    have hout : ∀ z, z ∈ sparseRep.canonBlocks cl bc → Mem.valid_block m z →
        z ∉ sparseWGlobs ∧ ¬ InUse m sparseSlots z :=
      fun z hz _ => sep_out hsep (List.mem_append_left _ (List.mem_append_right _ hz))
    have hPs : ∀ p ∈ [(W1, W1S, 4)], p ∈ sparseSlots := by decide
    refine ⟨rfl, ⟨hcan, h72, by rw [hsz.2]; exact hes⟩, ⟨by rw [hsz.1]; exact hok.1,
      by rw [hsz.2]; exact hok.2⟩,
      sparse_step hw hval hu [W1, W1S] [(W1, W1S, 4)] (by decide) hPs (by decide) hW hout ?_ ?_
        (marks1_keep hw hu (by decide) hPs hW hout (by decide) (by decide) (by decide) (by decide))
        (marks2_keep hw hu (by decide) hPs hW hout (by decide) (by decide) (by decide) (by decide))
        ?_⟩
    · intro p hp
      rw [List.mem_singleton] at hp; subst hp
      exact ⟨capW, bW, capW', bW', dW, dW', rW⟩
    · intro p hp q hq _ _ _ _ _ _ _ _
      rw [List.mem_singleton] at hp hq; rw [hp, hq]
    · intro z hz _
      simp only [sparseRep_canonBlocks, List.mem_cons] at hz
      rcases hz with rfl | rfl | rfl | hz
      · exact kbc
      · exact kv
      · exact kd
      · rw [hes] at hz
        obtain ⟨hp, rfl⟩ := mem_esOf hz
        exact ke hp

end NautyVerified.Proofs.Dispatch
