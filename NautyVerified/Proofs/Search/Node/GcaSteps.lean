import NautyVerified.Spec.Gca
import NautyVerified.Proofs.Search.Node.OtherHex
import NautyVerified.Proofs.Search.Node.FirstHex

/-!
# The level counters across a sweep step

`GcaSw` survives every child step of an off-path sweep (`gcaSw_otherChild`)
and every first-path child step once the first child is done
(`gcaSw_firstChild`); a child of a sweep in `GcaSw` is called in `GcaOk`
(`gcaOk_child`).
-/

namespace NautyVerified.Proofs.Search

open Hex.GraphIso Hex.GraphIso.Nauty NautyVerified.Spec.SearchInf

set_option linter.unusedSimpArgs false

variable {n : Nat}

theorem recover_gcaFirst (inf level : Nat) (st : Search n) :
    (Hex.GraphIso.Nauty.recover inf level st).gcaFirst = st.gcaFirst :=
  (gcaPolicy (Ctx.mk #[]) inf 0).recover level st

theorem gcaSw_recover {inf level : Nat} {st : Search n} (h : st.gcaFirst ≤ level) :
    GcaSw level (Hex.GraphIso.Nauty.recover inf level st) := by
  refine ⟨by rw [recover_gcaFirst]; exact h, recover_canon_le level st, ?_⟩
  rw [recover_noncheap]; split <;> omega

theorem gcaSw_otherChild {ctx : Ctx n} {inf tl fuel level nc tc tv1 tv : Nat} {cell : VSet n}
    {st : Search n} (h : GcaSw level st)
    (hd : (otherChild ctx inf tl fuel level nc tc tv1 tv cell st).1 = .done) :
    GcaSw level (otherChild ctx inf tl fuel level nc tc tv1 tv cell st).2.2 := by
  have hg : ({ (node false ctx inf tl fuel (level + 1) (nc + 1) (child false level tc tv st)).2 with
      fixedpts := (node false ctx inf tl fuel (level + 1) (nc + 1)
        (child false level tc tv st)).2.fixedpts.erase tv } : Search n).gcaFirst ≤ level := by
    show (node false ctx inf tl fuel (level + 1) (nc + 1) (child false level tc tv st)).2.gcaFirst ≤ level
    rw [node_gca]
    have := gcaF_child false level tc tv st
    unfold gcaF at this; simp only [Prod.mk.injEq] at this
    rw [this.1]; exact h.1
  unfold otherChild at hd ⊢
  generalize node false ctx inf tl fuel (level + 1) (nc + 1) (child false level tc tv st) = r at hg hd ⊢
  obtain ⟨e, s⟩ := r
  cases e with
  | fuel => cases hd
  | done => exact gcaSw_recover hg
  | unwind target short =>
    dsimp only at hd ⊢
    by_cases ht : target < level
    · simp only [ht, ite_true] at hd; cases hd
    · simp only [ht, ite_false]; exact gcaSw_recover hg

theorem gcaSw_firstChild {ctx : Ctx n} {inf tl fuel level nc tc tv1 tv : Nat} {cell : VSet n}
    {st : Search n} (h : tv ≠ tv1 → GcaSw level st)
    (hd : (firstChild ctx inf tl fuel level nc tc tv1 tv cell st).1 = .done)
    (hskip : (st.orbits[tv]! == tv) = false → tv ≠ tv1) :
    GcaSw level (firstChild ctx inf tl fuel level nc tc tv1 tv cell st).2.2 := by
  unfold firstChild at hd ⊢
  by_cases ho : (st.orbits[tv]! == tv) = true
  · simp only [ho, ite_true] at hd ⊢
    have hg : (if (tv == tv1) = true then afterChildFirst level tv1
        (node (tv == tv1) ctx inf tl fuel (level + 1) (nc + 1) (child true level tc tv st)).2 else
        (node (tv == tv1) ctx inf tl fuel (level + 1) (nc + 1) (child true level tc tv st)).2).gcaFirst
        ≤ level := by
      by_cases he : (tv == tv1) = true
      · simp only [he, ite_true]; exact Nat.le_refl _
      · have hne : tv ≠ tv1 := by simpa using he
        simp only [he, Bool.false_eq_true, ite_false]
        have hf : (tv == tv1) = false := by simpa using he
        rw [node_gca]
        have := gcaF_child true level tc tv st
        unfold gcaF at this; simp only [Prod.mk.injEq] at this
        rw [this.1]; exact (h hne).1
    generalize node (tv == tv1) ctx inf tl fuel (level + 1) (nc + 1) (child true level tc tv st) = r
      at hg hd ⊢
    obtain ⟨e, s⟩ := r
    cases e with
    | fuel => cases hd
    | done => exact gcaSw_recover hg
    | unwind target short =>
      dsimp only at hd ⊢
      by_cases ht : target < level
      · simp only [ht, ite_true] at hd; cases hd
      · simp only [ht, ite_false]; exact gcaSw_recover hg
  · have hf : (st.orbits[tv]! == tv) = false := by simpa using ho
    simp only [ho, Bool.false_eq_true, ite_false]
    exact h (hskip hf)

end NautyVerified.Proofs.Search
