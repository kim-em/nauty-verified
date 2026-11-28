import NautyVerified.Program.Env
import NautyVerified.Proofs.Set.Inter
import NautyVerified.Proofs.Nextelement.Satisfies

/-!
# `shortprune` meets its specification

`shortpruneSpec`: called with sets `set1` (words `w1`) and `set2` (words `w2`,
in another block) of `m` words, nauty's `shortprune` leaves `set1` holding the
word-wise conjunction, which represents the intersection (`setRep_andW`). It
changes only `set1`'s block and emits no events.
-/

namespace NautyVerified.Proofs.Prune

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (longs andW andWord)
open NautyVerified.Source

namespace Short
abbrev set1 : Common.AST.ident := dense.id.set1
abbrev set2 : Common.AST.ident := dense.id.set2
abbrev m : Common.AST.ident := dense.id.m
abbrev i : Common.AST.ident := dense.id.i

kernel_rfl body_eq : dense.body.shortprune = forLoop i m (andWord set1 set2 i)
end Short

/-- The specification of `shortprune`. -/
def shortpruneSpec (b1 : block) (o1 : ptrofs) (b2 : block) (o2 : ptrofs) (M : Nat)
    (w1 w2 : Nat → Lib.Integers.int64) : FunSpec where
  pre args m := args = [.Vptr b1 o1, .Vptr b2 o2, .Vint (ir M)] ∧
    ArrayAt m .Mint64 b1 (intOfZ (Ptrofs.unsigned o1)) (longs w1) M ∧
    ArrayAt m .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2) M ∧
    b2 ≠ b1 ∧ M < 2147483648
  post _ m t _ m' := t = E0 ∧
    ArrayAt m' .Mint64 b1 (intOfZ (Ptrofs.unsigned o1)) (longs (andW w1 w2)) M ∧ Unch m m' (· = b1) ∧
    Alloc.KeepA m m'

theorem shortprune_satisfies {xi : ExternalCalls} (b1 : block) (o1 : ptrofs) (b2 : block)
    (o2 : ptrofs) (M : Nat) (w1 w2 : Nat → Lib.Integers.int64) :
    Satisfies xi ge (.Internal dense.fn.shortprune) (shortpruneSpec b1 o1 b2 o2 M w1 w2) := by
  let le0 := PTree.set Short.m (.Vint (ir M)) (PTree.set Short.set2 (.Vptr b2 o2)
    (PTree.set Short.set1 (.Vptr b1 o1) (create_undef_temps dense.fn.shortprune.fn_temps)))
  refine satisfies_internal (Entry := fun _ m₀ e le m => e = empty_env ∧ le = le0 ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, le0, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, h1, h2, hne, hM⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [dense.fn.shortprune.fn_body_eq, Short.body_eq]
    refine Set.wp_interLoop h1 h2 hne hM
      (by simp (config := {decide := true}) only [le0, temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [le0, temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [le0, temps_gss])
      (by decide) (by decide) (by decide) ?_
    intro le' m' harr hu hk _
    exact ⟨m', Nextelement.free_empty m', rfl, harr, hu, hk⟩

end NautyVerified.Proofs.Prune
