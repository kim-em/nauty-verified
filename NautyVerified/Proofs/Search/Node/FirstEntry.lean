import NautyVerified.Proofs.Search.Node.FirstHead
import NautyVerified.Proofs.Search.Node.OtherEntry

/-!
# Entering `firstpathnode0`

`fEnv O`: the local environment binding `numcells`, `tcellsize`, `tc`,
`qinvar` and `refcode` to the blocks of `O`, as `alloc_variables` builds it
from `fn_vars`; `blocks_fEnv`: the blocks `return` frees. `fTemps`: the
temporaries on entry. `fpn_entry`: entering the function allocates five fresh,
distinct, freeable `int` blocks and changes nothing else.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open Hex.GraphIso.Nauty

/-- `firstpathnode0`'s local environment. -/
abbrev fEnv (O : OLocs) : env :=
  PTree.set dense.id.refcode (O.bk, tint) (PTree.set dense.id.qinvar (O.bq, tint)
    (PTree.set dense.id.tc (O.bc, tint) (PTree.set dense.id.tcellsize (O.bz, tint)
      (PTree.set dense.id.numcells (O.bnc, tint) empty_env))))

theorem blocks_fEnv (O : OLocs) :
    blocks_of_env ge (fEnv O) = [O.bq, O.bnc, O.bc, O.bz, O.bk].map
      fun b => (b, zOfInt 0, Cfrontend.Ctypes.sizeof ge.genv_cenv tint) := rfl

/-- The temporaries on entry. -/
def fTemps (bl : block) (lofs : ptrofs) (bp : block) (pofs : ptrofs) (level nc : Nat)
    (par : block) : temp_env :=
  PTree.set dense.id.tcnode_parent (.Vptr par Ptrofs.zero)
    (PTree.set dense.id.numcells (.Vint (ir nc)) (PTree.set dense.id.level (.Vint (ir level))
      (PTree.set dense.id.ptn (.Vptr bp pofs) (PTree.set dense.id.lab (.Vptr bl lofs)
        (create_undef_temps dense.fn.«nauty:firstpathnode0».fn_temps)))))

theorem fpn_vars : dense.fn.«nauty:firstpathnode0».fn_vars =
    [dense.id.numcells, dense.id.tcellsize, dense.id.tc, dense.id.qinvar, dense.id.refcode].map
      fun x => (x, tint) := by decide

/-- Entering `firstpathnode0`. -/
theorem fpn_entry (bl : block) (lofs : ptrofs) (bp : block) (pofs : ptrofs) (level nc : Nat)
    (par : block) (m₀ : mem) :
    ∃ e le m, function_entry2 ge dense.fn.«nauty:firstpathnode0»
        [.Vptr bl lofs, .Vptr bp pofs, .Vint (ir level), .Vint (ir nc), .Vptr par Ptrofs.zero]
        m₀ e le m ∧
      ∃ O : OLocs, e = fEnv O ∧ le = fTemps bl lofs bp pofs level nc par ∧
        (∀ z ∈ O.list, ¬ Mem.valid_block m₀ z ∧ Mem.valid_block m z ∧
          Mem.valid_access m .Mint32 z (zOfInt 0) .Freeable) ∧
        O.list.Pairwise (· ≠ ·) ∧ Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z) ∧
        (∀ z, Mem.valid_block m₀ z → Mem.valid_block m z) := by
  obtain ⟨e, m, hav, -, hin, hdist, hu, hg⟩ := alloc_ints
    [dense.id.numcells, dense.id.tcellsize, dense.id.tc, dense.id.qinvar, dense.id.refcode]
    empty_env m₀ (by decide)
  have hav' := hav
  simp only [List.map_cons, List.map_nil] at hav'
  rcases hav' with _ | ⟨_, _, _, _, _, m1, b1, _, _, -, hav'⟩
  rcases hav' with _ | ⟨_, _, _, _, _, m2, b2, _, _, -, hav'⟩
  rcases hav' with _ | ⟨_, _, _, _, _, m3, b3, _, _, -, hav'⟩
  rcases hav' with _ | ⟨_, _, _, _, _, m4, b4, _, _, -, hav'⟩
  rcases hav' with _ | ⟨_, _, _, _, _, m5, b5, _, _, -, hav'⟩
  cases hav'
  let O : OLocs := ⟨b1, b5, b2, b3, b4⟩
  have hE : fEnv O = PTree.set dense.id.refcode (b5, tint) (PTree.set dense.id.qinvar (b4, tint)
      (PTree.set dense.id.tc (b3, tint) (PTree.set dense.id.tcellsize (b2, tint)
        (PTree.set dense.id.numcells (b1, tint) empty_env)))) := rfl
  refine ⟨fEnv O, fTemps bl lofs bp pofs level nc par, m, ⟨?_, ?_, ?_, ?_, rfl⟩, O, rfl, rfl, ?_,
    ?_, hu, hg⟩
  · exact Nextelement.norepet_of_nodup (by decide)
  · exact Nextelement.norepet_of_nodup (by decide)
  · exact Nextelement.disjoint_of (by decide)
  · rw [fpn_vars]; exact hav
  · have key : ∀ x ∈ [dense.id.numcells, dense.id.tcellsize, dense.id.tc, dense.id.qinvar,
        dense.id.refcode], ∀ b, PTree.get x (fEnv O) = some (b, tint) →
        ¬ Mem.valid_block m₀ b ∧ Mem.valid_block m b ∧
          Mem.valid_access m .Mint32 b (zOfInt 0) .Freeable := by
      intro x hx b hb
      obtain ⟨b', hb', h1, h2, h3⟩ := hin x hx
      rw [hE] at hb
      rw [hb'] at hb
      cases hb
      exact ⟨h1, h2, h3⟩
    intro z hz
    simp only [OLocs.list, O, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact key dense.id.numcells (by simp) _ rfl
    · exact key dense.id.refcode (by simp) _ rfl
    · exact key dense.id.tcellsize (by simp) _ rfl
    · exact key dense.id.tc (by simp) _ rfl
    · exact key dense.id.qinvar (by simp) _ rfl
  · have d : ∀ x y, x ∈ [dense.id.numcells, dense.id.tcellsize, dense.id.tc, dense.id.qinvar,
        dense.id.refcode] → y ∈ [dense.id.numcells, dense.id.tcellsize, dense.id.tc, dense.id.qinvar,
        dense.id.refcode] → x ≠ y → ∀ bx by_, PTree.get x (fEnv O) = some (bx, tint) →
        PTree.get y (fEnv O) = some (by_, tint) → bx ≠ by_ := fun x y hx hy hxy bx by_ h1 h2 =>
      hdist x hx y hy hxy bx by_ (by rw [hE] at h1; exact h1) (by rw [hE] at h2; exact h2)
    simp only [OLocs.list, O, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · exact d dense.id.numcells dense.id.refcode (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.numcells dense.id.tcellsize (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.numcells dense.id.tc (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.numcells dense.id.qinvar (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.refcode dense.id.tcellsize (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.refcode dense.id.tc (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.refcode dense.id.qinvar (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.tcellsize dense.id.tc (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.tcellsize dense.id.qinvar (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.tc dense.id.qinvar (by simp) (by simp) (by decide) _ _ rfl rfl

/-! ### Over any program environment -/

section Generic

variable {ge : genv} [E : NautyEnv ge]

theorem blocks_fEnvG (O : OLocs) :
    blocks_of_env ge (fEnv O) = [O.bq, O.bnc, O.bc, O.bz, O.bk].map
      fun b => (b, zOfInt 0, Cfrontend.Ctypes.sizeof ge.genv_cenv tint) := rfl

/-- Entering `firstpathnode0`, over any program environment. -/
theorem fpn_entryG (bl : block) (lofs : ptrofs) (bp : block) (pofs : ptrofs) (level nc : Nat)
    (par : block) (m₀ : mem) :
    ∃ e le m, function_entry2 ge dense.fn.«nauty:firstpathnode0»
        [.Vptr bl lofs, .Vptr bp pofs, .Vint (ir level), .Vint (ir nc), .Vptr par Ptrofs.zero]
        m₀ e le m ∧
      ∃ O : OLocs, e = fEnv O ∧ le = fTemps bl lofs bp pofs level nc par ∧
        (∀ z ∈ O.list, ¬ Mem.valid_block m₀ z ∧ Mem.valid_block m z ∧
          Mem.valid_access m .Mint32 z (zOfInt 0) .Freeable) ∧
        O.list.Pairwise (· ≠ ·) ∧ Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z) ∧
        (∀ z, Mem.valid_block m₀ z → Mem.valid_block m z) := by
  obtain ⟨e, m, hav, -, hin, hdist, hu, hg⟩ := alloc_ints (ge := ge)
    [dense.id.numcells, dense.id.tcellsize, dense.id.tc, dense.id.qinvar, dense.id.refcode]
    empty_env m₀ (by decide)
  have hav' := hav
  simp only [List.map_cons, List.map_nil] at hav'
  rcases hav' with _ | ⟨_, _, _, _, _, m1, b1, _, _, -, hav'⟩
  rcases hav' with _ | ⟨_, _, _, _, _, m2, b2, _, _, -, hav'⟩
  rcases hav' with _ | ⟨_, _, _, _, _, m3, b3, _, _, -, hav'⟩
  rcases hav' with _ | ⟨_, _, _, _, _, m4, b4, _, _, -, hav'⟩
  rcases hav' with _ | ⟨_, _, _, _, _, m5, b5, _, _, -, hav'⟩
  cases hav'
  let O : OLocs := ⟨b1, b5, b2, b3, b4⟩
  have hE : fEnv O = PTree.set dense.id.refcode (b5, tint) (PTree.set dense.id.qinvar (b4, tint)
      (PTree.set dense.id.tc (b3, tint) (PTree.set dense.id.tcellsize (b2, tint)
        (PTree.set dense.id.numcells (b1, tint) empty_env)))) := rfl
  refine ⟨fEnv O, fTemps bl lofs bp pofs level nc par, m, ⟨?_, ?_, ?_, ?_, rfl⟩, O, rfl, rfl, ?_,
    ?_, hu, hg⟩
  · exact Nextelement.norepet_of_nodup (by decide)
  · exact Nextelement.norepet_of_nodup (by decide)
  · exact Nextelement.disjoint_of (by decide)
  · rw [fpn_vars]; exact hav
  · have key : ∀ x ∈ [dense.id.numcells, dense.id.tcellsize, dense.id.tc, dense.id.qinvar,
        dense.id.refcode], ∀ b, PTree.get x (fEnv O) = some (b, tint) →
        ¬ Mem.valid_block m₀ b ∧ Mem.valid_block m b ∧
          Mem.valid_access m .Mint32 b (zOfInt 0) .Freeable := by
      intro x hx b hb
      obtain ⟨b', hb', h1, h2, h3⟩ := hin x hx
      rw [hE] at hb
      rw [hb'] at hb
      cases hb
      exact ⟨h1, h2, h3⟩
    intro z hz
    simp only [OLocs.list, O, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact key dense.id.numcells (by simp) _ rfl
    · exact key dense.id.refcode (by simp) _ rfl
    · exact key dense.id.tcellsize (by simp) _ rfl
    · exact key dense.id.tc (by simp) _ rfl
    · exact key dense.id.qinvar (by simp) _ rfl
  · have d : ∀ x y, x ∈ [dense.id.numcells, dense.id.tcellsize, dense.id.tc, dense.id.qinvar,
        dense.id.refcode] → y ∈ [dense.id.numcells, dense.id.tcellsize, dense.id.tc, dense.id.qinvar,
        dense.id.refcode] → x ≠ y → ∀ bx by_, PTree.get x (fEnv O) = some (bx, tint) →
        PTree.get y (fEnv O) = some (by_, tint) → bx ≠ by_ := fun x y hx hy hxy bx by_ h1 h2 =>
      hdist x hx y hy hxy bx by_ (by rw [hE] at h1; exact h1) (by rw [hE] at h2; exact h2)
    simp only [OLocs.list, O, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · exact d dense.id.numcells dense.id.refcode (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.numcells dense.id.tcellsize (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.numcells dense.id.tc (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.numcells dense.id.qinvar (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.refcode dense.id.tcellsize (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.refcode dense.id.tc (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.refcode dense.id.qinvar (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.tcellsize dense.id.tc (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.tcellsize dense.id.qinvar (by simp) (by simp) (by decide) _ _ rfl rfl
    · exact d dense.id.tc dense.id.qinvar (by simp) (by simp) (by decide) _ _ rfl rfl

end Generic

end NautyVerified.Proofs.Search
