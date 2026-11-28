import NautyVerified.Spec.SearchInf
import HexGraphIso.Nauty.Policy.Boundary
import HexGraphIso.Nauty.Policy.Bounds
import HexGraphIso.Nauty.Policy.Effect
import HexGraphIso.Nauty.Policy.Coset
import HexGraphIso.Nauty.Policy.Controls

/-!
# What a leaf of the search may rely on

`LeafI st`: the noncheap level is at least 1 and the coset index is a vertex;
and once a first-leaf sentinel is in `firstcode` (`Sent`), the first and best
labellings are permutations and `eqlevCanon` is nonnegative. Every search step
keeps it: the noncheap level is only ever set to a level plus one, the coset
index to a vertex of the target cell, `firstterminal` writes the sentinel
together with both labellings and a level for `eqlevCanon`, and later writes
of `eqlevCanon` and `canonlab` are levels and the current labelling.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {n : Nat}

/-- Some entry of `firstcode` is the sentinel `firstterminal` writes. -/
def Sent (st : Search n) : Prop := ∃ i : Nat, st.firstcode[i]! = codeSentinel

/-- `a` holds a permutation of `0 … n-1` in its first `n` entries. -/
def LabPerm (a : Array Nat) (n : Nat) : Prop :=
  (∀ i < n, a[i]! < n) ∧ ∀ v < n, ∃ i < n, a[i]! = v

/-- What a leaf of the search may rely on. -/
def LeafI (st : Search n) : Prop :=
  1 ≤ st.noncheaplevel ∧ st.cosetindex < n ∧
    (Sent st → LabPerm st.firstlab n ∧ LabPerm st.canonlab n ∧ 0 ≤ st.eqlevCanon)

theorem LeafI.congr {a b : Search n} (h : LeafI a) (e1 : b.noncheaplevel = a.noncheaplevel)
    (e2 : b.cosetindex = a.cosetindex) (e3 : b.firstcode = a.firstcode)
    (e4 : b.firstlab = a.firstlab) (e5 : b.canonlab = a.canonlab)
    (e6 : b.eqlevCanon = a.eqlevCanon) : LeafI b := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [e1]; exact h1, by rw [e2]; exact h2, fun hs => ?_⟩
  have hs' : Sent a := by obtain ⟨i, hi⟩ := hs; exact ⟨i, by rw [← e3]; exact hi⟩
  rw [e4, e5, e6]; exact h3 hs'

/-- A labelling reached from the initial colour cells is a permutation. -/
theorem labPerm_of_ok {k : Nat} {G : Colored n k} {level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hok : SearchOk G level numcells st) : LabPerm st.lab n := by
  have hperm := isPerm_of_cellsReach hok.labSize hn0 hok.reach
  refine ⟨fun i hi => cellsReach_lt hok.reach i hi, fun v hv => ?_⟩
  have hm : v ∈ st.lab.toList := hperm.mem_iff.2 (List.mem_range.2 hv)
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
  have hi' : i < n := by simpa [hok.labSize] using hi
  refine ⟨i, hi', ?_⟩
  rw [getElem!_pos _ i (by rw [hok.labSize]; exact hi')]
  exact he

theorem leafI_visit {st : Search n} (h : LeafI st) (ctx : Ctx n) (level numcells : Nat) :
    LeafI (visit ctx level numcells st).2.2 := h.congr rfl rfl rfl rfl rfl rfl

theorem leafI_record {st : Search n} (h : LeafI st) {level code : Nat} (hc : code < codeSentinel) :
    LeafI (recordFirst level code st) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun ⟨i, hi⟩ => h3 ⟨i, ?_⟩⟩
  change (st.firstcode.set! level code)[i]! = codeSentinel at hi
  by_cases hil : i = level
  · subst hil
    by_cases hs : i < st.firstcode.size
    · rw [Array.getElem!_set!_self _ _ _ hs] at hi; omega
    · rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dite_eq_right_of_eq_false (eq_false hs)] at hi
      exact hi
  · rwa [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hil)] at hi

theorem leafI_compare {st : Search n} (h : LeafI st) (level code : Nat) :
    LeafI (compareCodes level code st) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hf : (compareCodes level code st).noncheaplevel = st.noncheaplevel ∧
      (compareCodes level code st).cosetindex = st.cosetindex ∧
      (compareCodes level code st).firstcode = st.firstcode ∧
      (compareCodes level code st).firstlab = st.firstlab ∧
      (compareCodes level code st).canonlab = st.canonlab ∧
      ((compareCodes level code st).eqlevCanon = st.eqlevCanon ∨
        (compareCodes level code st).eqlevCanon = Int.ofNat level) := by
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.noncheaplevel,
      apply_ite SearchState.cosetindex, apply_ite SearchState.firstcode,
      apply_ite SearchState.firstlab, apply_ite SearchState.canonlab,
      apply_ite SearchState.eqlevCanon, ite_self]
    repeat' split
    all_goals simp
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hf
  refine ⟨by rw [e1]; exact h1, by rw [e2]; exact h2, fun ⟨i, hi⟩ => ?_⟩
  rw [e3] at hi
  obtain ⟨p1, p2, p3⟩ := h3 ⟨i, hi⟩
  refine ⟨by rw [e4]; exact p1, by rw [e5]; exact p2, ?_⟩
  rcases e6 with e | e <;> rw [e]
  · exact p3
  · exact Int.natCast_nonneg _

theorem leafI_target {st : Search n} (h : LeafI st) (first : Bool) (ctx : Ctx n)
    (tcLevel level numcells : Nat) : LeafI (chooseTarget first ctx tcLevel level numcells st).2.2.2 := by
  cases first
  · rw [chooseTarget_fields]; exact h.congr rfl rfl rfl rfl rfl rfl
  · rw [chooseFirst_fields]; exact h.congr rfl rfl rfl rfl rfl rfl

theorem leafI_firstterminal {st : Search n} (h : LeafI st) (level : Nat) (hl : LabPerm st.lab n) :
    LeafI (firstterminal level st) := by
  obtain ⟨h1, h2, -⟩ := h
  have e1 : (firstterminal level st).noncheaplevel = st.noncheaplevel := by
    rw [firstterminal]; simp only [Id.run_bind, Id.run_pure]
  have e2 : (firstterminal level st).cosetindex = st.cosetindex := by
    rw [firstterminal]; simp only [Id.run_bind, Id.run_pure]
  have e3 : (firstterminal level st).firstlab = st.lab := by
    rw [firstterminal]; simp only [Id.run_bind, Id.run_pure]
  have e4 : (firstterminal level st).canonlab = st.lab := by
    rw [firstterminal]; simp only [Id.run_bind, Id.run_pure]
  have e5 : (firstterminal level st).eqlevCanon = Int.ofNat level := by
    rw [firstterminal]; simp only [Id.run_bind, Id.run_pure]
  refine ⟨by rw [e1]; exact h1, by rw [e2]; exact h2, fun _ => ?_⟩
  rw [e3, e4, e5]
  exact ⟨hl, hl, Int.natCast_nonneg _⟩

/-- The fields `LeafI` reads. -/
def leafF (st : Search n) : Nat × Nat × Array Nat × Array Nat × Array Nat × Int :=
  (st.noncheaplevel, st.cosetindex, st.firstcode, st.firstlab, st.canonlab, st.eqlevCanon)

theorem LeafI.of_leafF {a b : Search n} (h : LeafI a) (e : leafF b = leafF a) : LeafI b := by
  unfold leafF at e
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := e
  exact h.congr e1 e2 e3 e4 e5 e6

theorem leafF_classify (ctx : Ctx n) (level nc : Nat) (st : Search n) :
    leafF (classify ctx level nc st).2 = leafF st := by
  unfold leafF classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.noncheaplevel, apply_ite SearchState.cosetindex,
    apply_ite SearchState.firstcode, apply_ite SearchState.firstlab,
    apply_ite SearchState.canonlab, apply_ite SearchState.eqlevCanon, ite_self]

theorem leafI_classify {st : Search n} (h : LeafI st) (ctx : Ctx n) (level nc : Nat) :
    LeafI (classify ctx level nc st).2 := h.of_leafF (leafF_classify ctx level nc st)

theorem leafI_admit {st : Search n} (h : LeafI st) : LeafI (admit st) := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split
  · exact h.congr rfl rfl rfl rfl rfl rfl
  · exact h.congr rfl rfl rfl rfl rfl rfl

theorem leafI_pruneReturn {st : Search n} (h : LeafI st) (level : Nat) :
    LeafI (pruneReturn level st).2 := by
  unfold pruneReturn pushAuto
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  repeat' split
  all_goals exact h.congr rfl rfl rfl rfl rfl rfl

theorem leafI_install {st : Search n} (h : LeafI st) (level sr : Nat) (hl : LabPerm st.lab n) :
    LeafI (install level sr st) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun hs => ?_⟩
  obtain ⟨p1, -, -⟩ := h3 hs
  exact ⟨p1, hl, Int.natCast_nonneg _⟩

/-- The fields `leafExit` never writes among those `LeafI` reads. -/
def leafG (st : Search n) : Nat × Array Nat × Array Nat := (st.cosetindex, st.firstcode, st.firstlab)

theorem leafG_admit (st : Search n) : leafG (admit st) = leafG st := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

theorem leafF_pruneReturn (level : Nat) (st : Search n) :
    leafF (pruneReturn level st).2 = leafF st := by
  unfold pruneReturn pushAuto
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  repeat' split
  all_goals rfl

theorem leafG_leafExit (leaf : Leaf) (level : Nat) (st : Search n) :
    leafG (leafExit leaf level st).2 = leafG st := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | rfl
    | exact leafG_admit _
    | exact congrArg (fun x : Nat × Nat × Array Nat × Array Nat × Array Nat × Int =>
        (x.2.1, x.2.2.1, x.2.2.2.1)) (leafF_pruneReturn level _)

theorem admit_canon (st : Search n) :
    (admit st).canonlab = st.canonlab ∧ (admit st).eqlevCanon = st.eqlevCanon := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> exact ⟨rfl, rfl⟩

theorem leafExit_canon (leaf : Leaf) (level : Nat) (st : Search n) :
    ((leafExit leaf level st).2.canonlab = st.canonlab ∧
      (leafExit leaf level st).2.eqlevCanon = st.eqlevCanon) ∨
    ((leafExit leaf level st).2.canonlab = st.lab ∧
      (leafExit leaf level st).2.eqlevCanon = Int.ofNat level) := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | exact .inl ⟨rfl, rfl⟩
    | exact .inl ⟨congrArg (fun x : Nat × Nat × Array Nat × Array Nat × Array Nat × Int => x.2.2.2.2.1)
          (leafF_pruneReturn level _),
        congrArg (fun x : Nat × Nat × Array Nat × Array Nat × Array Nat × Int => x.2.2.2.2.2)
          (leafF_pruneReturn level _)⟩
    | exact .inr ⟨congrArg (fun x : Nat × Nat × Array Nat × Array Nat × Array Nat × Int => x.2.2.2.2.1)
          (leafF_pruneReturn level _),
        congrArg (fun x : Nat × Nat × Array Nat × Array Nat × Array Nat × Int => x.2.2.2.2.2)
          (leafF_pruneReturn level _)⟩
    | exact .inl (admit_canon _)

theorem leafI_leafExit {st : Search n} (h : LeafI st) (leaf : Leaf) (level : Nat)
    (hl : LabPerm st.lab n) : LeafI (leafExit leaf level st).2 := by
  have hg := leafG_leafExit leaf level st
  unfold leafG at hg
  simp only [Prod.mk.injEq] at hg
  obtain ⟨e2, e3, e4⟩ := hg
  have e1 := leafExit_noncheap leaf level st
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [e1]; exact h1, by rw [e2]; exact h2, fun ⟨i, hi⟩ => ?_⟩
  rw [e3] at hi
  obtain ⟨p1, p2, p3⟩ := h3 ⟨i, hi⟩
  rw [e4]
  rcases leafExit_canon leaf level st with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;> rw [c1, c2]
  · exact ⟨p1, p2, p3⟩
  · exact ⟨p1, hl, Int.natCast_nonneg _⟩

theorem leafI_cheap {st : Search n} (h : LeafI st) (first : Bool) (level : Nat) :
    LeafI (cheapCheck first level st) := by
  unfold cheapCheck
  split
  · obtain ⟨-, h2, h3⟩ := h
    exact ⟨by show 1 ≤ level + 1; omega, h2, h3⟩
  · exact h

theorem leafI_child {st : Search n} (h : LeafI st) (first : Bool) (level tc tv : Nat)
    (htv : first = true → tv < n) : LeafI (child first level tc tv st) := by
  cases first
  · exact h.congr rfl rfl rfl rfl rfl rfl
  · obtain ⟨h1, -, h3⟩ := h
    exact ⟨h1, htv rfl, h3⟩

theorem leafI_leave {st : Search n} (h : LeafI st) (tv : Nat) :
    LeafI ({ st with fixedpts := st.fixedpts.erase tv } : Search n) := h.congr rfl rfl rfl rfl rfl rfl

theorem leafI_recover {st : Search n} (h : LeafI st) (inf level : Nat) :
    LeafI (Hex.GraphIso.Nauty.recover inf level st) := by
  have e : ∀ x : Search n, (Hex.GraphIso.Nauty.recover inf level x).firstcode = x.firstcode ∧
      (Hex.GraphIso.Nauty.recover inf level x).firstlab = x.firstlab ∧
      (Hex.GraphIso.Nauty.recover inf level x).eqlevCanon =
        if Int.ofNat level ≤ x.eqlevCanon then Int.ofNat level else x.eqlevCanon := by
    intro x
    unfold Hex.GraphIso.Nauty.recover recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.firstcode,
      apply_ite SearchState.firstlab, apply_ite SearchState.eqlevCanon, ite_self]
    exact ⟨trivial, trivial, trivial⟩
  obtain ⟨e3, e4, e6⟩ := e st
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, by rw [recover_coset]; exact h2, fun ⟨i, hi⟩ => ?_⟩
  · rw [recover_noncheap]; split <;> omega
  rw [e3] at hi
  obtain ⟨p1, p2, p3⟩ := h3 ⟨i, hi⟩
  rw [e4, recover_ref, e6]
  refine ⟨p1, p2, ?_⟩
  split
  · exact Int.natCast_nonneg _
  · exact p3

theorem leafI_afterSweep {st : Search n} (h : LeafI st) (first : Bool) (level size index : Nat) :
    LeafI (afterSweep first level size index st) := by
  unfold afterSweep
  split
  · exact h.congr rfl rfl rfl rfl rfl rfl
  · exact h

theorem leafI_afterChildFirst {st : Search n} (h : LeafI st) (level tv1 : Nat) :
    LeafI (afterChildFirst level tv1 st) := h.congr rfl rfl rfl rfl rfl rfl

theorem Sent.congr {a b : Search n} (h : Sent a) (e : b.firstcode = a.firstcode) : Sent b := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by rw [e]; exact hi⟩

theorem compare_firstcode (level code : Nat) (st : Search n) :
    (compareCodes level code st).firstcode = st.firstcode := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.firstcode, ite_self]

end NautyVerified.Spec.SearchInf
