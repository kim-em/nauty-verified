import NautyVerified.Proofs.Permset.One
import NautyVerified.Proofs.Nextelement.Satisfies

/-!
# `permset` meets its specification

`permsetSpec`: called with `set1` representing `s`, a `set2` of `m` words
and an array `perm` of vertices, nauty's `permset` leaves `set2` representing
HexGraphIso's `s.permset perm`, changing only `set2`'s block.
-/

namespace NautyVerified.Proofs.Permset

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (BitTable longs)
open NautyVerified.Proofs.Nextelement (LeftbitTable)
open Hex.GraphIso.Nauty (VSet)

def permsetSpec {n : Nat} (b1 : block) (o1 : ptrofs) (w1 : Nat → Lib.Integers.int64) (s : VSet n)
    (b2 : block) (o2 : ptrofs) (w2 : Nat → Lib.Integers.int64) (bp : block) (po : ptrofs)
    (perm : Array Nat) (M : Nat) : FunSpec where
  pre args m := args = [.Vptr b1 o1, .Vptr b2 o2, .Vint (ir M), .Vptr bp po] ∧
    ArrayAt m .Mint64 b1 (intOfZ (Ptrofs.unsigned o1)) (longs w1) M ∧
    SetRep (fun w => bv64 (w1 w)) M s ∧
    ArrayAt m .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2) M ∧
    ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned po)) (ints perm) n ∧
    (∀ u < n, perm[u]! < n) ∧ LeftbitTable m ∧ BitTable m Block.nautilBit ∧
    b2 ≠ b1 ∧ b2 ≠ bp ∧ b2 ≠ Block.nautilBit ∧ b2 ≠ Block.leftbit ∧ 0 < M ∧ M < 33554432
  post _ m t _ m' := t = E0 ∧ ∃ w2',
    ArrayAt m' .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2') M ∧
    SetRep (fun w => bv64 (w2' w)) M (s.permset perm) ∧ Unch m m' (· = b2)

def entryTemps (b1 : block) (o1 : ptrofs) (b2 : block) (o2 : ptrofs) (bp : block) (po : ptrofs)
    (M : Nat) : temp_env :=
  PTree.set id.perm (.Vptr bp po) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.set2 (.Vptr b2 o2) (PTree.set id.set1 (.Vptr b1 o1)
      (create_undef_temps Source.dense.fn.permset.fn_temps))))

theorem permset_satisfies {xi : ExternalCalls} {n : Nat} (b1 : block) (o1 : ptrofs)
    (w1 : Nat → Lib.Integers.int64) (s : VSet n) (b2 : block) (o2 : ptrofs)
    (w2 : Nat → Lib.Integers.int64) (bp : block) (po : ptrofs) (perm : Array Nat) (M : Nat) :
    Satisfies xi ge (.Internal Source.dense.fn.permset)
      (permsetSpec b1 o1 w1 s b2 o2 w2 bp po perm M) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps b1 o1 b2 o2 bp po M ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps b1 o1 b2 o2 bp po M, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, harr1, hrep1, harr2, hparr, hps, hlb, hbit, h21, h2p, h2bit, h2lb, hM, hM2⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.permset.fn_body_eq, body_eq]
    have hf : Frame m (entryTemps b1 o1 b2 o2 bp po M) b1 o1 w1 s bp po perm b2 o2 M :=
      { hset1 := by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hset2 := by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hperm := by simp (config := {decide := true}) only [entryTemps, temps_gss]
        hm := by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        arr1 := harr1, rep1 := hrep1, parr := hparr, psmall := hps, lb := hlb, bit := hbit,
        Mlt := hM2, b21 := h21, b2p := h2p, b2bit := h2bit, b2lb := h2lb }
    simp only [body]
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge empty_env _ m (tv id.m) = _ from hf.hm]
    simp only [Exec.evalExpr, typeof, cop]
    rw [ir_eq (a := (M : Int)) (b := 1) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
    by_cases h1 : M = 1
    · subst h1
      rw [ite_eq_left (by simp)]
      refine wp_one hf harr2 ?_
      intro le' m' w2' harr' hrep' hu
      exact ⟨m', Nextelement.free_empty m', rfl, w2', harr', hrep', hu⟩
    · rw [ite_eq_right (by simp; omega)]
      refine wp_many hf hM harr2 ?_
      intro le' m' w2' harr' hrep' hu
      exact ⟨m', Nextelement.free_empty m', rfl, w2', harr', hrep', hu⟩

end NautyVerified.Proofs.Permset
