import NautyVerified.Proofs.Top.Globals
import NautyVerified.Proofs.Top.NautyEnv
import NautyVerified.Proofs.Top.Spec
import NautyVerified.Proofs.Search.Node.Env
import NautyVerified.Proofs.Nextelement.Satisfies

/-!
# Entering `nauty()`

`nauty_entryG`: entering `nauty()`, in any program linking nauty.c, allocates
its one addressable local `initstatus` (a fresh block `bI`) and binds the
twelve parameters (`nTempsG`, the options block at `bopt`); the dense
`nauty_entry` (`nTemps`) is its instance.
`valid_init`: in the initial memory every block below 313 is valid (the
program has 312 globals), so `valid_init hm (by decide)` gives the validity
of a global's block.
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Source

kernel_rfl genv_next_eq : (Genv.globalenv Init.prog).genv_next = PArith.BinPos.Pos.of_nat 313

theorem valid_init {m : mem} (hm : Genv.init_mem Init.prog = some m) {b : block}
    (hb : posToNat b < 313) : Mem.valid_block m b := by
  show PArith.BinPos.Pos.lt b m.nextblock
  rw [← Genv.init_mem_genv_next _ _ _ _ hm, genv_next_eq]
  exact hb

/-- The temporaries on entry, the options block at `bopt`. -/
def nTempsG (bg bl bp bo bopt bst bD bc : block) (W M n : Nat) : temp_env :=
  PTree.set dense.id.canong_arg (.Vptr bc Ptrofs.zero) (PTree.set dense.id.n_arg (.Vint (ir n))
    (PTree.set dense.id.m_arg (.Vint (ir M)) (PTree.set dense.id.worksize (.Vint (ir W))
      (PTree.set dense.id.ws_arg (.Vptr bD Ptrofs.zero)
        (PTree.set dense.id.stats_arg (.Vptr bst Ptrofs.zero)
          (PTree.set dense.id.options (.Vptr bopt Ptrofs.zero)
            (PTree.set dense.id.orbits_arg (.Vptr bo Ptrofs.zero)
              (PTree.set dense.id.active_arg nullArg
                (PTree.set dense.id.ptn (.Vptr bp Ptrofs.zero)
                  (PTree.set dense.id.lab (.Vptr bl Ptrofs.zero)
                    (PTree.set dense.id.g_arg (.Vptr bg Ptrofs.zero)
                      (create_undef_temps dense.fn.nauty.fn_temps))))))))))))

/-- The temporaries on entry. -/
def nTemps (bg bl bp bo bst bD bc : block) (W M n : Nat) : temp_env :=
  PTree.set dense.id.canong_arg (.Vptr bc Ptrofs.zero) (PTree.set dense.id.n_arg (.Vint (ir n))
    (PTree.set dense.id.m_arg (.Vint (ir M)) (PTree.set dense.id.worksize (.Vint (ir W))
      (PTree.set dense.id.ws_arg (.Vptr bD Ptrofs.zero)
        (PTree.set dense.id.stats_arg (.Vptr bst Ptrofs.zero)
          (PTree.set dense.id.options (.Vptr Harness.Block.options Ptrofs.zero)
            (PTree.set dense.id.orbits_arg (.Vptr bo Ptrofs.zero)
              (PTree.set dense.id.active_arg nullArg
                (PTree.set dense.id.ptn (.Vptr bp Ptrofs.zero)
                  (PTree.set dense.id.lab (.Vptr bl Ptrofs.zero)
                    (PTree.set dense.id.g_arg (.Vptr bg Ptrofs.zero)
                      (create_undef_temps dense.fn.nauty.fn_temps))))))))))))

theorem nauty_vars : dense.fn.nauty.fn_vars = [dense.id.initstatus].map fun x => (x, tint) := by
  decide

/-- Entering `nauty()`, in any program linking nauty.c (`TopEnv`: `initstatus`
names no global). -/
theorem nauty_entryG {ge : genv} [NautyEnv ge] [TopEnv ge] (bg bl bp bo bopt bst bD bc : block)
    (W M n : Nat) (m₀ : mem) :
    ∃ e le m, function_entry2 ge dense.fn.nauty
        [.Vptr bg Ptrofs.zero, .Vptr bl Ptrofs.zero, .Vptr bp Ptrofs.zero, nullArg,
          .Vptr bo Ptrofs.zero, .Vptr bopt Ptrofs.zero, .Vptr bst Ptrofs.zero,
          .Vptr bD Ptrofs.zero, .Vint (ir W), .Vint (ir M), .Vint (ir n), .Vptr bc Ptrofs.zero]
        m₀ e le m ∧
      ∃ bI, e = nEnv bI ∧ le = nTempsG bg bl bp bo bopt bst bD bc W M n ∧
        ¬ Mem.valid_block m₀ bI ∧ Mem.valid_access m .Mint32 bI (zOfInt 0) .Freeable ∧
        Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z) ∧
        (∀ z, Mem.valid_block m₀ z → Mem.valid_block m z) := by
  obtain ⟨e, m, hav, hout, hin, -, hu, hg⟩ := Search.alloc_ints (ge := ge) [dense.id.initstatus]
    empty_env m₀ (by decide)
  obtain ⟨bI, hb, h1, -, h3⟩ := hin _ (List.mem_singleton_self _)
  have he : e = nEnv bI := by
    apply PTree.extensionality
    intro x
    by_cases hx : x = dense.id.initstatus
    · subst hx; rw [hb]; rfl
    · rw [hout x (by simpa using hx)]; exact (PTree.gso _ _ hx).symm
  refine ⟨e, nTempsG bg bl bp bo bopt bst bD bc W M n, m, ⟨?_, ?_, ?_, ?_, rfl⟩, bI, he, rfl, h1, h3,
    hu, hg⟩
  · exact Nextelement.norepet_of_nodup (by decide)
  · exact Nextelement.norepet_of_nodup (by decide)
  · exact Nextelement.disjoint_of (by decide)
  · rw [nauty_vars]; exact hav

/-- Entering `nauty()`. -/
theorem nauty_entry (bg bl bp bo bst bD bc : block) (W M n : Nat) (m₀ : mem) :
    ∃ e le m, function_entry2 ge dense.fn.nauty
        [.Vptr bg Ptrofs.zero, .Vptr bl Ptrofs.zero, .Vptr bp Ptrofs.zero, nullArg,
          .Vptr bo Ptrofs.zero, .Vptr Harness.Block.options Ptrofs.zero, .Vptr bst Ptrofs.zero,
          .Vptr bD Ptrofs.zero, .Vint (ir W), .Vint (ir M), .Vint (ir n), .Vptr bc Ptrofs.zero]
        m₀ e le m ∧
      ∃ bI, e = nEnv bI ∧ le = nTemps bg bl bp bo bst bD bc W M n ∧ ¬ Mem.valid_block m₀ bI ∧
        Mem.valid_access m .Mint32 bI (zOfInt 0) .Freeable ∧
        Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z) ∧
        (∀ z, Mem.valid_block m₀ z → Mem.valid_block m z) :=
  nauty_entryG bg bl bp bo Harness.Block.options bst bD bc W M n m₀

end NautyVerified.Proofs.Top
