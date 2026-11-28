import NautyVerified.Spec.SearchInfRun

/-!
# The level counters at a node

`GcaOk level st`: at an off-path node of `level`, the greatest common
ancestors with the first and best leaves lie strictly above it and the
noncheap level does not exceed it. `GcaSw level st`: the weaker form a sweep of
that node keeps (`≤ level`, noncheap `≤ level + 1`). These are what
`leafExit_bound` needs to send every unwind of an off-path leaf strictly above
the node. The field lemmas below hold for any `inf`.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {n : Nat} {κ : Type}

/-- The counters at an off-path node call. -/
def GcaOk (level : Nat) (st : SearchState n κ) : Prop :=
  st.gcaFirst < level ∧ st.gcaCanon < level ∧ st.noncheaplevel ≤ level

/-- The counters during a sweep at `level`. -/
def GcaSw (level : Nat) (st : SearchState n κ) : Prop :=
  st.gcaFirst ≤ level ∧ st.gcaCanon ≤ level ∧ st.noncheaplevel ≤ level + 1

/-- The three counters. -/
def gcaF (st : SearchState n κ) : Nat × Nat × Nat := (st.gcaFirst, st.gcaCanon, st.noncheaplevel)

theorem gcaF_visit (ctx : Ctx n) (level nc : Nat) (st : Search n) :
    gcaF (visit ctx level nc st).2.2 = gcaF st := rfl

theorem gcaF_compare (level code : Nat) (st : SearchState n κ) :
    gcaF (compareCodes level code st) = gcaF st := by
  unfold gcaF compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.gcaFirst,
    apply_ite SearchState.gcaCanon, apply_ite SearchState.noncheaplevel, ite_self]

theorem gcaF_target (ctx : Ctx n) (tl level nc : Nat) (st : Search n) :
    gcaF (chooseTarget false ctx tl level nc st).2.2.2 = gcaF st := by
  have h := chooseTarget_fields ctx tl level nc st
  dsimp only at h
  unfold gcaF
  rw [h]

theorem gcaF_classify (ctx : Ctx n) (level nc : Nat) (st : Search n) :
    gcaF (classify ctx level nc st).2 = gcaF st := by
  unfold gcaF classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.gcaFirst, apply_ite SearchState.gcaCanon,
    apply_ite SearchState.noncheaplevel, ite_self]

theorem leafExit_internal (level : Nat) (st : SearchState n κ) :
    leafExit .internal level st = (.done, st) := rfl

theorem gcaF_child (first : Bool) (level tc tv : Nat) (st : SearchState n κ) :
    gcaF (child first level tc tv st) = gcaF st := by
  cases first <;> rfl

theorem gcaOk_child {level : Nat} {st : SearchState n κ} (h : GcaSw level st) (first : Bool)
    (tc tv : Nat) : GcaOk (level + 1) (child first level tc tv st) := by
  have := gcaF_child first level tc tv st
  unfold gcaF at this
  simp only [Prod.mk.injEq] at this
  obtain ⟨e1, e2, e3⟩ := this
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [e1]; omega, by rw [e2]; omega, by rw [e3]; omega⟩

/-- An off-path node that continues to its sweep starts the sweep in `GcaSw`. -/
theorem gcaSw_sweepOff (ctx : Ctx n) (tl level nc : Nat) (st : Search n) (h : GcaOk level st) :
    let v := visit ctx level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := chooseTarget false ctx tl level v.1 st₁
    let cl := classify ctx level v.1 ct.2.2.2
    let lx := leafExit cl.1 level cl.2
    lx.1 = .done → GcaSw level (cheapCheck false level lx.2) := by
  intro v st₁ ct cl lx hd
  have hint : cl.1 = .internal := (leafExit_done _ _ _).1 hd
  have hlx : lx.2 = cl.2 := by
    show (leafExit cl.1 level cl.2).2 = cl.2
    rw [hint]; rfl
  have hf : gcaF cl.2 = gcaF st := by
    show gcaF (classify ctx level v.1 ct.2.2.2).2 = gcaF st
    rw [gcaF_classify, gcaF_target, gcaF_compare, gcaF_visit]
  unfold gcaF at hf
  simp only [Prod.mk.injEq] at hf
  obtain ⟨h1, h2, h3⟩ := hf
  obtain ⟨g1, g2, g3⟩ := h
  rw [hlx]
  unfold cheapCheck
  split
  · exact ⟨by rw [h1]; omega, by rw [h2]; omega, by simp⟩
  · exact ⟨by rw [h1]; omega, by rw [h2]; omega, by rw [h3]; omega⟩

end NautyVerified.Spec.SearchInf
