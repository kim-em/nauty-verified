import NautyVerified.Proofs.Sparse.Refine.Count.Starts

/-!
# The later fragments, model side

`fragStep_eq`: a step of the later-fragment loop stops at the cell's last
position and otherwise splits off `fragNext`, which adds one queue entry and
one cell (`fragNext_size`); so along the loop the queue and the cell count
only grow (`frag_mono`), which bounds the C's writes by the loop's result.
The run loop changes only cell starts and ends between its start and
`k + F` (`iterF_runStep_fields`).
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Spec.SortC (iterF)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- The run loop keeps everything but the cell starts, and ends between
`k` and `k + F`. -/
theorem iterF_runStep_fields (l w : Nat) : ∀ (F : Nat) (s : RefineSt n) (k : Nat),
    (iterF (runStep l w) F (s, k)).1.queue = s.queue ∧ (iterF (runStep l w) F (s, k)).1.numcells = s.numcells ∧
      k ≤ (iterF (runStep l w) F (s, k)).2 ∧ (iterF (runStep l w) F (s, k)).2 ≤ k + F
  | 0, s, k => by simp only [iterF]; exact ⟨True.intro, True.intro, Nat.le_refl _, by omega⟩
  | F + 1, s, k => by
    simp only [iterF, runStep]
    by_cases hc : (s.hits[s.lab[k + 1]!]! != w) = true
    · simp only [hc, ite_true]; exact ⟨True.intro, True.intro, Nat.le_refl _, by omega⟩
    · simp only [hc, Bool.false_eq_true, ite_false]
      obtain ⟨h1, h2, h3, h4⟩ := iterF_runStep_fields l w F
        { s with cellstart := s.cellstart.set! s.lab[k + 1]! l } (k + 1)
      exact ⟨h1, h2, by omega, by omega⟩

/-- A later fragment split off, when there is one. -/
def fragNext (level last : Nat) (d : Bool) (st : RefineSt n × Option Nat × Nat × Nat) :
    RefineSt n × Option Nat × Nat × Nat :=
  let (s, bigpos, bigsize, k) := st
  let s := { s with ptn := s.ptn.set! k level, numcells := s.numcells + 1 }
  let s := if d then s.hash k else s
  let l := k + 1
  let s := s.push l
  let w3 := s.hits[s.lab[l]!]!
  let s := if !d then s.hash w3 else s
  let r := iterF (runStep l w3) (last - 1 - l) (s, l)
  let s := { r.1 with cellend := r.1.cellend.set! l r.2 }
  if r.2 - l + 1 == 1 then ({ s with cellstart := s.cellstart.set! s.lab[l]! n }, bigpos, bigsize, r.2)
  else
    let s := { s with cellstart := s.cellstart.set! s.lab[l]! l }
    if r.2 - l + 1 > bigsize then (s, some (s.queue.size - 1), r.2 - l + 1, r.2)
    else (s, bigpos, bigsize, r.2)

theorem fragStep_eq (level last : Nat) (d : Bool) (st : RefineSt n × Option Nat × Nat × Nat) :
    fragStep level last d st =
      if st.2.2.2 ≥ last - 1 then .done st else .yield (fragNext level last d st) := by
  rcases st with ⟨s, bp, bs, k⟩
  by_cases hk : k ≥ last - 1
  · simp only [fragStep, hk, ↓reduceIte]
  · simp only [fragStep, fragNext, hk, ↓reduceIte]
    rw [apply_ite (f := ForInStep.yield), apply_ite (f := ForInStep.yield)]

/-- A later fragment adds one queue entry and one cell. -/
theorem fragNext_size (level last : Nat) (d : Bool) (st : RefineSt n × Option Nat × Nat × Nat) :
    (fragNext level last d st).1.queue.size = st.1.queue.size + 1 ∧
      (fragNext level last d st).1.numcells = st.1.numcells + 1 := by
  rcases st with ⟨s, bp, bs, k⟩
  cases d <;> simp only [fragNext, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;>
    split <;> (try split) <;>
    simp [RefineSt.push, RefineSt.hash, (iterF_runStep_fields _ _ _ _ _).1,
      (iterF_runStep_fields _ _ _ _ _).2.1]

/-- Along the fragment loop the queue and the cell count only grow. -/
theorem frag_mono (level last : Nat) (d : Bool) : ∀ (F : Nat) (st : RefineSt n × Option Nat × Nat × Nat),
    st.1.queue.size ≤ (iterF (fragStep level last d) F st).1.queue.size ∧
      st.1.numcells ≤ (iterF (fragStep level last d) F st).1.numcells
  | 0, _ => ⟨Nat.le_refl _, Nat.le_refl _⟩
  | F + 1, st => by
    by_cases hk : st.2.2.2 ≥ last - 1
    · simp only [iterF, fragStep_eq, hk, ↓reduceIte]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · simp only [iterF, fragStep_eq, hk, ↓reduceIte]
      have h1 := fragNext_size level last d st
      have h2 := frag_mono level last d F (fragNext level last d st)
      exact ⟨by omega, by omega⟩

end NautyVerified.Proofs.Sparse.Refine.Count
