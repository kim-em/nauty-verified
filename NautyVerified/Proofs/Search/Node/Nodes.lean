import NautyVerified.Proofs.Search.Node.OtherBody

/-!
# Both search nodes meet their specifications

`nodes_satisfies`: for an emission `Em` obeying both laws, `firstpathnode0`
and `othernode0` satisfy `firstpathnodeSpecG` and `othernodeSpecG` at every
level, by induction downward from `n + 1` (above `n` the specifications'
preconditions fail). The step for `othernode0` is `othernode_body`; the step
for `firstpathnode0` is the hypothesis `hFpn` (that node's body, from both
specifications at `level + 1`).
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Source
open Hex.GraphIso Hex.GraphIso.Nauty

variable {xi : ExternalCalls} {n : Nat}

theorem nodes_satisfies {k : Nat} (G : Colored n k) (Em : Bool → Nat → Nat → Search n → List Int)
    (hOff : EmLawOff Em ⟨rowsOf G⟩) (S : SLoc)
    (hRef : Refine.RefineFn xi S.M (.Vptr S.refineBlock Ptrofs.zero))
    (hFpn : ∀ level,
      (∀ s nc ch, Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
        (firstpathnodeSpecG xi G Em S s (level + 1) nc ch)) →
      (∀ s nc ch, Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
        (othernodeSpecG xi G Em S s (level + 1) nc ch)) →
      ∀ s nc ch, Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
        (firstpathnodeSpecG xi G Em S s level nc ch)) :
    ∀ level s nc ch,
      Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
        (firstpathnodeSpecG xi G Em S s level nc ch) ∧
      Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
        (othernodeSpecG xi G Em S s level nc ch) := by
  suffices H : ∀ d level, n + 1 - level ≤ d → ∀ s nc ch,
      Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
        (firstpathnodeSpecG xi G Em S s level nc ch) ∧
      Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
        (othernodeSpecG xi G Em S s level nc ch) from
    fun level => H (n + 1 - level) level (Nat.le_refl _)
  -- above `n`, the preconditions fail
  have high : ∀ level, n < level → ∀ s nc ch,
      Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
        (firstpathnodeSpecG xi G Em S s level nc ch) ∧
      Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
        (othernodeSpecG xi G Em S s level nc ch) := fun level hl s nc ch =>
    ⟨fun _ _ hp => absurd hp.2.2.2.2.2.2.2.1 (by omega),
     fun _ _ hp => absurd hp.2.2.2.2.2.2.2.1 (by omega)⟩
  intro d
  induction d with
  | zero => intro level hd; exact high level (by omega)
  | succ d ih =>
    intro level hd
    by_cases hl : n < level
    · exact high level hl
    have hnext := ih (level + 1) (by omega)
    have hO : ∀ s nc ch, Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
        (othernodeSpecG xi G Em S s level nc ch) := fun s nc ch =>
      othernode_body G Em hOff S s level nc ch hRef fun s' nc' ch' => (hnext s' nc' ch').2
    exact fun s nc ch => ⟨hFpn level (fun s' nc' ch' => (hnext s' nc' ch').1)
      (fun s' nc' ch' => (hnext s' nc' ch').2) s nc ch, hO s nc ch⟩

end NautyVerified.Proofs.Search
