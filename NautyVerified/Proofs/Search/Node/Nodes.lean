import NautyVerified.Proofs.Search.Node.FirstBody

/-!
# Both search nodes meet their specifications

`nodes_satisfiesG`: for any dispatch `D`, classifier `C` and search policy with
link `L` and laws `Lw`, and an emission `Em` obeying both laws (`EmLawOffG`,
`EmLawFirstG`), `firstpathnode0` and `othernode0` satisfy `nodeSpecG` at every
level, by induction downward from `n + 1` (above `n` the specifications'
preconditions fail). The steps are the two node bodies, `firstpathnode_bodyG`
and `othernode_bodyG`, each from both specifications at `level + 1`.

`nodes_satisfies` is the dense form: the same induction with `othernode_body`
(the dense instance of `othernode_bodyG`) as the off-path step and the
first-path step `hFpn` taken as a hypothesis.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Values
open CompCert4Lean.Common.ExternalCalls CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Source
open Hex.GraphIso Hex.GraphIso.Nauty

variable {xi : ExternalCalls} {n : Nat}

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}
variable [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]

/-- Both node functions meet `nodeSpecG` at every level, for the dispatch `D`, the
classifier `C`, the policy with link `L` and laws `Lw` on `G`, and an emission
obeying both laws. -/
theorem nodes_satisfiesG (D : DispatchC ge O) (C : Classifier O) (L : PolicyLink O n)
    {G : O.Gr n} (Lw : NodeLaws L G) (Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int)
    (hOff : EmLawOffG Em G) (hFirst : EmLawFirstG Em G) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) :
    ∀ level st nc ch,
      Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
        (nodeSpecG D.toDispatchRep xi Lw.NodeOk Em true S gl cl G st level nc ch) ∧
      Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
        (nodeSpecG D.toDispatchRep xi Lw.NodeOk Em false S gl cl G st level nc ch) := by
  suffices H : ∀ d level, n + 1 - level ≤ d → ∀ st nc ch,
      Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
        (nodeSpecG D.toDispatchRep xi Lw.NodeOk Em true S gl cl G st level nc ch) ∧
      Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
        (nodeSpecG D.toDispatchRep xi Lw.NodeOk Em false S gl cl G st level nc ch) from
    fun level => H (n + 1 - level) level (Nat.le_refl _)
  -- above `n`, the preconditions fail
  have high : ∀ level, n < level → ∀ st nc ch,
      Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
        (nodeSpecG D.toDispatchRep xi Lw.NodeOk Em true S gl cl G st level nc ch) ∧
      Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
        (nodeSpecG D.toDispatchRep xi Lw.NodeOk Em false S gl cl G st level nc ch) :=
    fun level hl st nc ch =>
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
    exact fun st nc ch =>
      ⟨firstpathnode_bodyG D L G Lw Em hFirst S gl cl level
        (fun s nc' ch' => (hnext s nc' ch').1) (fun s nc' ch' => (hnext s nc' ch').2) st nc ch,
       othernode_bodyG D C L Lw Em hOff S gl cl st level nc ch
        fun s nc' ch' => (hnext s nc' ch').2⟩

end Generic

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
