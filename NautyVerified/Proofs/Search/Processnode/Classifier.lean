import NautyVerified.Proofs.Dispatch.Spec
import NautyVerified.Spec.Processnode

/-!
# The leaf classification over any dispatch operations

`classifyBy O upd G level numcells st` is `classify_eq`'s restatement of
HexGraphIso's `classify`, in the order of nauty's `processnode`, with `O`'s
automorphism test and canonical comparison and `upd` updating the carried
canonical store. `Classifier O` says that `O.classify` is it: the store update
`update`, whose rows are `O.updatecan`'s, the range of `O.testcanlab`'s result
and `classify_eq`. The dense instance is `denseClassifier`.

`Keeps.classifyBy` and `classifyBy_cases` are `Keeps.classify` and
`classify_cases` for it.
-/

namespace NautyVerified.Proofs.Search

open NautyVerified.Spec NautyVerified.Proofs.Dispatch
open Hex.GraphIso.Nauty

variable {n : Nat} (O : Ops)

/-- `canonTestS` for `O`: the state after the comparison with the best leaf, and `sr`. -/
def canonTestG (upd : O.Canon n → Array Nat → Nat → O.Canon n) (G : O.Gr n) (level : Nat)
    (st : SearchState n (O.Canon n)) : SearchState n (O.Canon n) × Nat :=
  if st.compCanon = 0 then
    if level < st.canonlevel then ({ st with compCanon := 1 }, 0)
    else
      let st' := { st with canong := upd st.canong st.canonlab st.samerows, samerows := n }
      ({ st' with compCanon := (O.testcanlab G (O.rows st'.canong) st'.lab).1 },
        (O.testcanlab G (O.rows st'.canong) st'.lab).2)
  else (st, 0)

/-- The end of the best-leaf comparison, from the state after it and `sr`. -/
def pickCanon {κ : Type} (st : SearchState n κ) (sr : Nat) : Leaf × SearchState n κ :=
  if st.compCanon = 0 then (.autoCanon, scatter st.canonlab st)
  else if st.compCanon > 0 then (.better sr, st)
  else (.bad, st)

/-- `classifyCanon` for `O`. -/
def classifyCanonG (upd : O.Canon n → Array Nat → Nat → O.Canon n) (G : O.Gr n) (level : Nat)
    (st : SearchState n (O.Canon n)) : Leaf × SearchState n (O.Canon n) :=
  pickCanon (canonTestG O upd G level st).1 (canonTestG O upd G level st).2

/-- `classify` in the order of nauty's `processnode`, for `O`. -/
def classifyBy (upd : O.Canon n → Array Nat → Nat → O.Canon n) (G : O.Gr n)
    (level numcells : Nat) (st : SearchState n (O.Canon n)) : Leaf × SearchState n (O.Canon n) :=
  if st.eqlevFirst ≠ level ∧ st.compCanon < 0 then (.bad, st)
  else if numcells ≠ n then (.internal, st)
  else if st.eqlevFirst = level then
    if st.gcaFirst ≥ st.noncheaplevel ∨ O.isautom G (scatter st.firstlab st).workperm = true then
      (.autoFirst, scatter st.firstlab st)
    else classifyCanonG O upd G level (scatter st.firstlab st)
  else classifyCanonG O upd G level st

/-- How `O.classify` is built from `O`'s procedures. -/
structure Classifier where
  /-- The update of the carried canonical store; its rows are `O.updatecan`'s. -/
  update : {n : Nat} → O.Gr n → O.Canon n → Array Nat → Nat → O.Canon n
  rows_update : ∀ {n : Nat} (G : O.Gr n) (c : O.Canon n) (lab : Array Nat) (sr : Nat),
    O.rows (update G c lab sr) = O.updatecan G (O.rows c) lab sr
  testcanlab_range : ∀ {n : Nat} (G : O.Gr n) (c : O.Store n) (lab : Array Nat),
    -1 ≤ (O.testcanlab G c lab).1 ∧ (O.testcanlab G c lab).1 ≤ 1 ∧ (O.testcanlab G c lab).2 ≤ n
  classify_eq : ∀ {n : Nat} (G : O.Gr n) (level numcells : Nat) (st : SearchState n (O.Canon n)),
    O.classify G level numcells st = classifyBy O (update G) G level numcells st

variable {O}

theorem Keeps.canonTestG (upd : O.Canon n → Array Nat → Nat → O.Canon n) (G : O.Gr n)
    (level : Nat) (st : SearchState n (O.Canon n)) : Keeps st (canonTestG O upd G level st).1 := by
  unfold Search.canonTestG; split
  · split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact Keeps.refl _

theorem Keeps.classifyCanonG (upd : O.Canon n → Array Nat → Nat → O.Canon n) (G : O.Gr n)
    (level : Nat) (st : SearchState n (O.Canon n)) :
    Keeps st (classifyCanonG O upd G level st).2 := by
  have h := Keeps.canonTestG upd G level st
  unfold Search.classifyCanonG pickCanon
  split
  · exact h.trans (Keeps.scatter _ _)
  · split <;> exact h

theorem Keeps.classifyBy (upd : O.Canon n → Array Nat → Nat → O.Canon n) (G : O.Gr n)
    (level numcells : Nat) (st : SearchState n (O.Canon n)) :
    Keeps st (classifyBy O upd G level numcells st).2 := by
  unfold Search.classifyBy
  split
  · exact Keeps.refl _
  · split
    · exact Keeps.refl _
    · split
      · split
        · exact Keeps.scatter _ _
        · exact (Keeps.scatter _ _).trans (Keeps.classifyCanonG _ _ _ _)
      · exact Keeps.classifyCanonG _ _ _ _

theorem canonTestG_sr (C : Classifier O) (G : O.Gr n) (level : Nat)
    (st : SearchState n (O.Canon n)) :
    (canonTestG O (C.update G) G level st).2 ≤ (canonTestG O (C.update G) G level st).1.samerows := by
  unfold canonTestG; split
  · split
    · simp
    · exact (C.testcanlab_range G _ _).2.2
  · simp

theorem classifyCanonG_cases (C : Classifier O) (G : O.Gr n) (level : Nat)
    (st : SearchState n (O.Canon n)) :
    ((classifyCanonG O (C.update G) G level st).1 = .autoCanon ∧
        (classifyCanonG O (C.update G) G level st).2.workperm =
          scatterW (canonTestG O (C.update G) G level st).1.canonlab
            (canonTestG O (C.update G) G level st).1.lab
            (canonTestG O (C.update G) G level st).1.workperm n) ∨
      (∃ s, (classifyCanonG O (C.update G) G level st).1 = .better s ∧
        s ≤ (classifyCanonG O (C.update G) G level st).2.samerows) ∨
      (classifyCanonG O (C.update G) G level st).1 = .bad := by
  unfold classifyCanonG pickCanon
  split
  · left; exact ⟨rfl, by rw [scatter_eq]⟩
  · split
    · right; left; exact ⟨_, rfl, canonTestG_sr C G level st⟩
    · right; right; rfl

/-- The classifications and what the C needs of each (`classify_cases` for `O`). -/
theorem classifyBy_cases (C : Classifier O) (G : O.Gr n) (level numcells : Nat)
    (st : SearchState n (O.Canon n)) :
    let r := classifyBy O (C.update G) G level numcells st
    r.1 = .internal ∨ (r.1 = .autoFirst ∧ r.2.workperm = scatterW st.firstlab st.lab st.workperm n) ∨
      (r.1 = .autoCanon ∧ ∃ w : Array Nat, w.size = st.workperm.size ∧
        r.2.workperm = scatterW st.canonlab st.lab w n) ∨
      (∃ s, r.1 = .better s ∧ s ≤ r.2.samerows) ∨ r.1 = .bad := by
  simp only []
  have hc : ∀ st' : SearchState n (O.Canon n), Keeps st st' →
      (classifyCanonG O (C.update G) G level st').1 = .autoCanon ∧
        (∃ w : Array Nat, w.size = st.workperm.size ∧
          (classifyCanonG O (C.update G) G level st').2.workperm = scatterW st.canonlab st.lab w n) ∨
      (∃ s, (classifyCanonG O (C.update G) G level st').1 = .better s ∧
        s ≤ (classifyCanonG O (C.update G) G level st').2.samerows) ∨
      (classifyCanonG O (C.update G) G level st').1 = .bad := by
    intro st' hk
    have hk2 := hk.trans (Keeps.canonTestG (C.update G) G level st')
    rcases classifyCanonG_cases C G level st' with ⟨h1, h2⟩ | h | h
    · left; refine ⟨h1, _, hk2.workperm, ?_⟩; rw [h2, hk2.canonlab, hk2.lab]
    · right; left; exact h
    · right; right; exact h
  unfold classifyBy
  split
  · right; right; right; right; rfl
  · split
    · left; rfl
    · split
      · split
        · right; left; exact ⟨rfl, by rw [scatter_eq]⟩
        · rcases hc _ (Keeps.scatter _ _) with h | h | h
          · right; right; left; exact h
          · right; right; right; left; exact h
          · right; right; right; right; exact h
      · rcases hc _ (Keeps.refl _) with h | h | h
        · right; right; left; exact h
        · right; right; right; left; exact h
        · right; right; right; right; exact h

/-- Dense nauty's classification. -/
def denseClassifier : Classifier denseOps where
  update G c lab sr := updatecan G c lab sr
  rows_update _ _ _ _ := rfl
  testcanlab_range G c lab := testcanlab_range G c lab
  classify_eq G level numcells st := by
    show classify G level numcells st = _
    rw [classify_eq]; rfl

end NautyVerified.Proofs.Search
