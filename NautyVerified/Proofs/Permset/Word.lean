import NautyVerified.Proofs.Permset.Take
import NautyVerified.Logic.Ints

/-!
# One word of `permset`

`Covers acc s perm D`: `acc` holds exactly the images `perm[u]` of the
members `u` of `s` with `D u`. `wp_word`: the loop over the set bits of word
`w0` of `set1` adds the images of that word's members to `set2`.
-/

namespace NautyVerified.Proofs.Permset

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (BitTable longs addW)
open NautyVerified.Proofs.Nextelement (LeadBit LeftbitTable)
open Hex.GraphIso.Nauty (VSet)

/-- `acc` holds the images of the members of `s` satisfying `D`. -/
def Covers {n : Nat} (acc s : VSet n) (perm : Array Nat) (D : Nat → Prop) : Prop :=
  ∀ t, acc.mem t = true ↔ ∃ u, D u ∧ s.mem u = true ∧ perm[u]! = t

theorem Covers.insert {n : Nat} {acc s : VSet n} {perm : Array Nat} {D : Nat → Prop}
    (h : Covers acc s perm D) {u0 : Nat} (hu0 : s.mem u0 = true) (hp : perm[u0]! < n)
    (D' : Nat → Prop) (hD' : ∀ u, D' u ↔ D u ∨ u = u0) :
    Covers (acc.insert perm[u0]!) s perm D' := by
  intro t
  rw [VSet.mem_insert_of_lt acc hp, Bool.or_eq_true, h t]
  constructor
  · rintro (⟨u, hu, hs, rfl⟩ | ht)
    · exact ⟨u, (hD' u).2 (.inl hu), hs, rfl⟩
    · refine ⟨u0, (hD' u0).2 (.inr rfl), hu0, ?_⟩
      simpa using ht
  · rintro ⟨u, hu, hs, rfl⟩
    rcases (hD' u).1 hu with hu | rfl
    · exact .inl ⟨u, hu, hs, rfl⟩
    · exact .inr (by simp)

theorem Covers.congr {n : Nat} {acc s : VSet n} {perm : Array Nat} {D D' : Nat → Prop}
    (h : Covers acc s perm D) (hD : ∀ u, s.mem u = true → (D u ↔ D' u)) : Covers acc s perm D' :=
  fun t => (h t).trans ⟨fun ⟨u, hu, hs, ht⟩ => ⟨u, (hD u hs).1 hu, hs, ht⟩,
    fun ⟨u, hu, hs, ht⟩ => ⟨u, (hD u hs).2 hu, hs, ht⟩⟩

theorem covers_empty {n : Nat} (s : VSet n) (perm : Array Nat) :
    Covers (VSet.empty : VSet n) s perm (fun u => u < 0) := fun t => by
  simp

/-- Covering every member is the image. -/
theorem covers_image {n : Nat} {acc s : VSet n} {perm : Array Nat}
    (h : Covers acc s perm (fun _ => True)) (hp : ∀ u < n, perm[u]! < n) :
    acc = s.permset perm := by
  apply VSet.ext
  intro t
  rw [VSet.permset, VSet.mem_image]
  cases hac : acc.mem t with
  | true =>
    obtain ⟨u, -, hs, rfl⟩ := (h t).1 hac
    have hu := VSet.mem_lt hs
    symm
    rw [List.any_eq_true]
    exact ⟨u, List.mem_range.2 hu, by simp [hs, hp u hu]⟩
  | false =>
    symm
    rw [List.any_eq_false]
    intro u hu hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    have := (h t).2 ⟨u, trivial, hc.1.1, hc.1.2⟩
    rw [hac] at this; cases this

end NautyVerified.Proofs.Permset
