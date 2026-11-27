import NautyVerified.Spec.Orbjoin
import NautyVerified.Spec.Fmptn
import NautyVerified.Spec.Cycle

/-!
# HexGraphIso's leaf classification, unrolled

`scatter_eq` writes `scatter` as a fold (`scatterW`); `scatterW_at` and
`scatterW_inj` show that scattering through a permutation `ref` puts `lab[j]`
at `ref[j]` and yields a permutation. `surj_inj`: a map of `0 .. n-1` onto
itself is injective.

`classify_eq` restates `classify` in the order of nauty's `processnode`:
first the bad-node test, then the leaf test, the first-leaf comparison and the
best-leaf comparison (`classifyCanon`).
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty

variable {n : Nat}

/-- `scatter`'s loop. -/
def scatterW (ref lab w : Array Nat) (N : Nat) : Array Nat :=
  (List.range N).foldl (fun w i => w.set! ref[i]! lab[i]!) w

theorem scatter_eq {κ : Type} (ref : Array Nat) (st : SearchState n κ) :
    scatter ref st = { st with workperm := scatterW ref st.lab st.workperm n } := by
  simp only [scatter, Id.run, scatterW]
  rw [forIn_range_eq, forIn_foldl]
  rfl

theorem scatterW_size (ref lab w : Array Nat) : ∀ N, (scatterW ref lab w N).size = w.size
  | 0 => rfl
  | N + 1 => by
    simp only [scatterW, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Array.size_set!]
    exact scatterW_size ref lab w N

theorem scatterW_small {ref lab w : Array Nat} {B : Nat} (hl : ∀ i, i < n → lab[i]! < B)
    (hw : ∀ x, x < w.size → w[x]! < B) :
    ∀ N, N ≤ n → ∀ x, x < w.size → (scatterW ref lab w N)[x]! < B
  | 0, _ => hw
  | N + 1, hN => by
    intro x hx
    have ih := scatterW_small (ref := ref) hl hw N (by omega)
    simp only [scatterW, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change ((scatterW ref lab w N).set! ref[N]! lab[N]!)[x]! < B
    by_cases hxr : ref[N]! = x
    · subst hxr
      rw [Array.getElem!_set!_self _ _ _ (by rw [scatterW_size]; exact hx)]
      exact hl N (by omega)
    · rw [Array.getElem!_set!_ne _ _ _ _ hxr]; exact ih x hx

/-- Scattering through an injective `ref` puts `lab[j]` at `ref[j]`. -/
theorem scatterW_at {ref lab w : Array Nat} (hsz : w.size = n) (hr : ∀ i, i < n → ref[i]! < n)
    (hi : ∀ i j, i < n → j < n → ref[i]! = ref[j]! → i = j) :
    ∀ N, N ≤ n → ∀ j, j < N → (scatterW ref lab w N)[ref[j]!]! = lab[j]!
  | 0, _ => fun _ h => absurd h (Nat.not_lt_zero _)
  | N + 1, hN => by
    intro j hj
    simp only [scatterW, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change ((scatterW ref lab w N).set! ref[N]! lab[N]!)[ref[j]!]! = lab[j]!
    by_cases hjN : j = N
    · subst hjN
      rw [Array.getElem!_set!_self _ _ _ (by rw [scatterW_size, hsz]; exact hr j (by omega))]
    · rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hjN (hi N j (by omega) (by omega) h).symm)]
      exact scatterW_at hsz hr hi N (by omega) j (by omega)

/-- A map of `0 .. n-1` onto itself is injective there. -/
theorem surj_inj {f : Nat → Nat} (hsm : ∀ i, i < n → f i < n)
    (hs : ∀ v, v < n → ∃ i, i < n ∧ f i = v) :
    ∀ i j, i < n → j < n → f i = f j → i = j := by
  have key : ∀ a b, a < b → b < n → f a = f b → False := by
    intro a b hab hb he
    have pre : ∀ v, ∃ i, (v < n → i < n ∧ f i = v) := fun v => by
      by_cases hv : v < n
      · obtain ⟨i, hi, hfi⟩ := hs v hv; exact ⟨i, fun _ => ⟨hi, hfi⟩⟩
      · exact ⟨0, fun h => absurd h hv⟩
    let p := fun v => Classical.choose (pre v)
    have hp : ∀ v, v < n → p v < n ∧ f (p v) = v := fun v hv => Classical.choose_spec (pre v) hv
    let g := fun v => if p v = b then a else p v
    have hg : ∀ v, v < n → g v < n ∧ g v ≠ b ∧ f (g v) = v := by
      intro v hv
      obtain ⟨h1, h2⟩ := hp v hv
      simp only [g]
      split
      · rename_i h; exact ⟨by omega, by omega, by rw [he, ← h, h2]⟩
      · rename_i h; exact ⟨h1, h, h2⟩
    let h := fun v => if g v < b then g v else g v - 1
    obtain ⟨v1, v2, h12, hv2, heq⟩ := pigeon (n - 1) h fun k hk => by
      obtain ⟨g1, g2, -⟩ := hg k (by omega)
      simp only [h]; split <;> omega
    obtain ⟨a1, a2, a3⟩ := hg v1 (by omega)
    obtain ⟨b1, b2, b3⟩ := hg v2 (by omega)
    have hgg : g v1 = g v2 := by
      simp only [h] at heq; split at heq <;> split at heq <;> omega
    have : v1 = v2 := by rw [← a3, ← b3, hgg]
    omega
  intro i j hi hj he
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact (key i j h hj he).elim
  · exact h
  · exact (key j i h hi he.symm).elim

/-- Scattering `lab` through `ref`, both maps of `0 .. n-1` onto itself, gives one. -/
theorem scatterW_inj {ref lab w : Array Nat} (hsz : w.size = n) (hr : ∀ i, i < n → ref[i]! < n)
    (hrs : ∀ v, v < n → ∃ i, i < n ∧ ref[i]! = v) (hl : ∀ i, i < n → lab[i]! < n)
    (hls : ∀ v, v < n → ∃ i, i < n ∧ lab[i]! = v) :
    ∀ x y, x < n → y < n → (scatterW ref lab w n)[x]! = (scatterW ref lab w n)[y]! → x = y := by
  have ri := surj_inj (f := fun i => ref[i]!) hr hrs
  have li := surj_inj (f := fun i => lab[i]!) hl hls
  intro x y hx hy he
  obtain ⟨i, hi, rfl⟩ := hrs x hx
  obtain ⟨j, hj, rfl⟩ := hrs y hy
  rw [scatterW_at hsz hr ri n (Nat.le_refl _) i hi,
    scatterW_at hsz hr ri n (Nat.le_refl _) j hj] at he
  rw [li i j hi hj he]

/-- The best-leaf comparison of `classify`. -/
def classifyCanon (ctx : Ctx n) (level : Nat) (st : Search n) : Leaf × Search n :=
  let p : Search n × Nat :=
    if st.compCanon = 0 then
      if level < st.canonlevel then ({ st with compCanon := 1 }, 0)
      else
        let st' := { st with canong := updatecan ctx st.canong st.canonlab st.samerows, samerows := n }
        ({ st' with compCanon := (testcanlab ctx st'.canong st'.lab).1 },
          (testcanlab ctx st'.canong st'.lab).2)
    else (st, 0)
  if p.1.compCanon = 0 then (.autoCanon, scatter p.1.canonlab p.1)
  else if p.1.compCanon > 0 then (.better p.2, p.1)
  else (.bad, p.1)

theorem classify_eq (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    classify ctx level numcells st =
      if st.eqlevFirst ≠ level ∧ st.compCanon < 0 then (.bad, st)
      else if numcells ≠ n then (.internal, st)
      else if st.eqlevFirst = level then
        if st.gcaFirst ≥ st.noncheaplevel ∨ isautom ctx (scatter st.firstlab st).workperm = true then
          (.autoFirst, scatter st.firstlab st)
        else classifyCanon ctx level (scatter st.firstlab st)
      else classifyCanon ctx level st := by
  simp only [classify, classifyCanon, Id.run]
  have es : ∀ r : Array Nat, (scatter r st).compCanon = st.compCanon ∧
      (scatter r st).canonlevel = st.canonlevel ∧ (scatter r st).gcaFirst = st.gcaFirst ∧
      (scatter r st).noncheaplevel = st.noncheaplevel := fun r => by
    simp [scatter_eq]
  by_cases h1 : st.eqlevFirst ≠ level ∧ st.compCanon < 0
  · simp [h1.1, h1.2]; rfl
  · by_cases h2 : numcells = n
    · subst h2
      by_cases h3 : st.eqlevFirst = level
      · simp only [h3, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false,
          beq_self_eq_true, ite_true, ne_eq, not_true_eq_false, false_and,
          (es _).1, (es _).2.1, (es _).2.2.1, (es _).2.2.2]
        repeat' split
        all_goals first | rfl | (simp_all; done) | (exfalso; omega) | (exfalso; dsimp only at *; simp only [(es _).1] at *; omega)
      · have h4 : ¬ st.compCanon < 0 := fun h => h1 ⟨h3, h⟩
        simp only [h3, h4, decide_false, Bool.and_false, bne_self_eq_false, Bool.false_eq_true,
          ite_false, ne_eq, not_true_eq_false, false_and, not_false_eq_true, and_false]
        have h3' : (st.eqlevFirst == level) = false := by simpa using h3
        simp only [h3', Bool.false_eq_true, ite_false]
        repeat' split
        all_goals first | rfl | (simp_all; done) | (exfalso; omega) | (exfalso; dsimp only at *; simp only [(es _).1] at *; omega)
    · have h2' : (numcells != n) = true := by simpa using h2
      have h1' : (st.eqlevFirst != level && decide (st.compCanon < 0)) = false := by
        simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq, decide_eq_false_iff_not]; omega
      simp only [h1', h2', Bool.false_eq_true, ite_false, ite_true, ne_eq, h2, not_false_eq_true,
        h1]
      rfl

end NautyVerified.Spec
