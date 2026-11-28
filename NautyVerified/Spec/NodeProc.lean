import NautyVerified.Spec.NodeOk

/-!
# What an off-path node's `processnode` call may rely on

At an off-path node (`NodeOk G false level numcells st`), after the refinement,
the code comparison and the target choice, the state `s` passed to
`processnode` has: the first and best labellings as permutations
(`proc_firstlab`, `proc_canonlab`), `eqlevCanon ≥ 0` (`proc_eqlevCanon`),
`noncheaplevel ≥ 1` (`proc_noncheap`) and a vertex as coset index
(`proc_cosetindex`). They come from the run invariant `LeafI` inside `Inv`:
off the first path the first leaf has been reached (`Depth` puts its sentinel
in `firstcode`), and the three steps keep `LeafI` and the sentinel.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The state an off-path node passes to `processnode` satisfies `LeafI` with
the first-leaf sentinel present. -/
theorem proc_leafI {G : Colored n k} {level nc : Nat} {st : Search n}
    (h : NodeOk G false level nc st) (ctx : Ctx n) (tcLevel : Nat) :
    let v := visit ctx level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := chooseTarget false ctx tcLevel level v.1 st₁
    LeafI ct.2.2.2 ∧ Sent ct.2.2.2 := by
  intro v st₁ ct
  obtain ⟨⟨t, st₂, rfl, -, -, hinv, -, hoff⟩, -⟩ := h
  obtain ⟨last, hd, -⟩ := hoff rfl
  have hl : LeafI (tw (phi (n + 2) nautyInfinity) t st₂) := hinv.2.2.congr rfl rfl rfl rfl rfl rfl
  have hs : Sent (tw (phi (n + 2) nautyInfinity) t st₂) := ⟨last + 1, hd.2⟩
  refine ⟨leafI_target (leafI_compare (leafI_visit hl ctx level nc) _ _) false ctx tcLevel _ _, ?_⟩
  have e := chooseTarget_fields ctx tcLevel level v.1 st₁
  dsimp only at e
  apply Sent.congr hs
  show ct.2.2.2.firstcode = _
  rw [show ct.2.2.2 = (chooseTarget false ctx tcLevel level v.1 st₁).2.2.2 from rfl, e]
  exact compare_firstcode _ _ _

theorem proc_firstlab {G : Colored n k} {level nc : Nat} {st : Search n}
    (h : NodeOk G false level nc st) (ctx : Ctx n) (tcLevel : Nat) :
    let v := visit ctx level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := chooseTarget false ctx tcLevel level v.1 st₁
    (∀ i < n, ct.2.2.2.firstlab[i]! < n) ∧ ∀ u < n, ∃ i < n, ct.2.2.2.firstlab[i]! = u :=
  let ⟨hl, hs⟩ := proc_leafI h ctx tcLevel
  (hl.2.2 hs).1

theorem proc_canonlab {G : Colored n k} {level nc : Nat} {st : Search n}
    (h : NodeOk G false level nc st) (ctx : Ctx n) (tcLevel : Nat) :
    let v := visit ctx level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := chooseTarget false ctx tcLevel level v.1 st₁
    (∀ i < n, ct.2.2.2.canonlab[i]! < n) ∧ ∀ u < n, ∃ i < n, ct.2.2.2.canonlab[i]! = u :=
  let ⟨hl, hs⟩ := proc_leafI h ctx tcLevel
  (hl.2.2 hs).2.1

theorem proc_eqlevCanon {G : Colored n k} {level nc : Nat} {st : Search n}
    (h : NodeOk G false level nc st) (ctx : Ctx n) (tcLevel : Nat) :
    let v := visit ctx level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := chooseTarget false ctx tcLevel level v.1 st₁
    0 ≤ ct.2.2.2.eqlevCanon :=
  let ⟨hl, hs⟩ := proc_leafI h ctx tcLevel
  (hl.2.2 hs).2.2

theorem proc_noncheap {G : Colored n k} {level nc : Nat} {st : Search n}
    (h : NodeOk G false level nc st) (ctx : Ctx n) (tcLevel : Nat) :
    let v := visit ctx level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := chooseTarget false ctx tcLevel level v.1 st₁
    1 ≤ ct.2.2.2.noncheaplevel :=
  (proc_leafI h ctx tcLevel).1.1

theorem proc_cosetindex {G : Colored n k} {level nc : Nat} {st : Search n}
    (h : NodeOk G false level nc st) (ctx : Ctx n) (tcLevel : Nat) :
    let v := visit ctx level nc st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := chooseTarget false ctx tcLevel level v.1 st₁
    ct.2.2.2.cosetindex < n :=
  (proc_leafI h ctx tcLevel).1.2.1

end NautyVerified.Spec.SearchInf
