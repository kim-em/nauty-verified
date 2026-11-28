import NautyVerified.Spec.NodeOk
import NautyVerified.Spec.PartOk
import HexGraphIso.Nauty.Policy.Filters

/-!
# How an off-path node's leaf code can exit

For an off-path node call in `NodeOk`, with `v := visit ctx level nc st`,
`st₁ := compareCodes level v.2.1 v.2.2`, `ct := chooseTarget false ctx tl level
v.1 st₁`, and the leaf code `leafExit` of `classify ctx level v.1 ct.2.2.2`
(`processnode` in nauty.c):

- `node_hnf`: the leaf code never exits with `.fuel`;
- `node_hlt`: every unwind it asks for goes strictly above the node
  (the counters `GcaOk` and Hex's `leafExit_bound`);
- `node_hDone`: if it continues the node (`.done`), the node chose a target
  cell (`v.1 < n` and `eqlevFirst = level ∨ 0 ≤ compCanon` before the choice),
  so nauty.c's `tcell` holds the chosen cell.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {n k : Nat}

theorem node_hnf (ctx : Ctx n) (level nc : Nat) (s : Search n) :
    (leafExit (classify ctx level nc s).1 level (classify ctx level nc s).2).1 ≠ .fuel :=
  leafExit_noFuel _ _ _

theorem node_hlt {G : Colored n k} {level nc : Nat} {st : Search n}
    (h : NodeOk G false level nc st) (ctx : Ctx n) (tl : Nat) :
    let v := visit ctx level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := chooseTarget false ctx tl level v.1 st₁
    ∀ tg s, (leafExit (classify ctx level v.1 ct.2.2.2).1 level
      (classify ctx level v.1 ct.2.2.2).2).1 = .unwind tg s → tg < level := by
  intro v st₁ ct tg s he
  have hf : gcaF (classify ctx level v.1 ct.2.2.2).2 = gcaF st := by
    rw [gcaF_classify, gcaF_target, gcaF_compare, gcaF_visit]
  unfold gcaF at hf
  simp only [Prod.mk.injEq] at hf
  obtain ⟨h1, h2, h3⟩ := hf
  obtain ⟨g1, g2, g3⟩ := h.2 rfl
  exact leafExit_bound (by rw [h1]; exact g1) (by rw [h2]; exact g2) (by rw [h3]; exact g3) he

/-- `chooseTarget false` changes nothing when it does not choose. -/
theorem chooseTarget_false_skip (ctx : Ctx n) (tl level nc : Nat) (st : Search n)
    (h : ¬ (nc < n ∧ (st.eqlevFirst = level ∨ 0 ≤ st.compCanon))) :
    (chooseTarget false ctx tl level nc st).2.2.2 = st := by
  unfold chooseTarget
  simp only [Bool.false_eq_true, ite_false, Id.run]
  split
  · rename_i hc
    exfalso
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, ge_iff_le] at hc
    exact h hc
  · rfl

theorem node_hDone {G : Colored n k} {level nc : Nat} {st : Search n}
    (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : NodeOk G false level nc st)
    (ctx : Ctx n) (tl : Nat) :
    let v := visit ctx level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := chooseTarget false ctx tl level v.1 st₁
    (leafExit (classify ctx level v.1 ct.2.2.2).1 level (classify ctx level v.1 ct.2.2.2).2).1 =
        .done →
      v.1 < n ∧ (st₁.eqlevFirst = level ∨ 0 ≤ st₁.compCanon) := by
  intro v st₁ ct hd
  have hint := (classify_internal ctx level v.1 ct.2.2.2).1 ((leafExit_done _ _ _).1 hd)
  have hlevel : 1 ≤ level := by obtain ⟨⟨_, _, _, h1, _⟩, _⟩ := h; exact h1
  have hfacts := (PartOk.visit hn0 hn hlevel (PartOk.of_nodeOk hn h) ctx).facts hn0 hn
  have hle := hfacts.numcellsLe
  have hlt : v.1 < n := by
    have := hint.2
    show (visit ctx level nc st).1 < n
    change (visit ctx level nc st).1 ≤ n at hle
    change (visit ctx level nc st).1 ≠ n at this
    omega
  refine ⟨hlt, ?_⟩
  apply Classical.byContradiction
  intro hno
  have hskip := chooseTarget_false_skip ctx tl level v.1 st₁ (fun hc => hno hc.2)
  have h1 := hint.1
  rw [show ct.2.2.2 = st₁ from hskip] at h1
  apply h1
  constructor
  · exact fun he => hno (.inl he)
  · have : ¬ 0 ≤ st₁.compCanon := fun hc => hno (.inr hc)
    omega

end NautyVerified.Spec.SearchInf
