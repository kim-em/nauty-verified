import HexGraphIso.Nauty.Sparse.SortSorted
import HexGraphIso.Nauty.Sparse.Cells

namespace NautyVerified.Spec.SortC

open Hex.GraphIso.Nauty.Sparse Hex.GraphIso.Nauty.Sparse.Sort

/-- The inner loop of the insertion sort, with the hole at `s + j`. -/
def shift (y : Array Nat) (s key : Nat) : Nat → Array Nat → Array Nat × Nat
  | 0, x => (x, 0)
  | j + 1, x => if y[x[s + j]!]! ≤ key then (x, j + 1)
      else shift y s key j (x.set! (s + j + 1) x[s + j]!)

/-- One pass of the outer insertion loop. -/
def insStep (y : Array Nat) (s : Nat) (x : Array Nat) (i : Nat) : Array Nat :=
  (shift y s y[x[s + i]!]! i x).1.set! (s + (shift y s y[x[s + i]!]! i x).2) x[s + i]!

theorem shift_loop (y : Array Nat) (s key : Nat) : ∀ (j k : Nat) (x : Array Nat),
    (forIn (m := Id) (List.range' k j) (x, j) fun _ st =>
      if y[st.1[s + st.2 - 1]!]! ≤ key then pure (ForInStep.done (st.1, st.2))
      else if (st.2 - 1 == 0) = true then
        pure (ForInStep.done (st.1.set! (s + st.2) st.1[s + st.2 - 1]!, st.2 - 1))
      else pure (ForInStep.yield (st.1.set! (s + st.2) st.1[s + st.2 - 1]!, st.2 - 1))) =
      shift y s key j x
  | 0, _, _ => rfl
  | j + 1, k, x => by
    have e : s + (j + 1) - 1 = s + j := by omega
    rw [List.range'_succ, List.forIn_cons, shift]
    simp only [e, Nat.add_sub_cancel]
    by_cases hk : y[x[s + j]!]! ≤ key
    · simp only [hk, ite_true]; rfl
    · simp only [hk, ite_false]
      by_cases hj : j = 0
      · subst hj; simp only [beq_self_eq_true, ite_true]; rfl
      · rw [ite_eq_right_iff.2 (fun h => absurd (by simpa using h) hj)]
        exact shift_loop y s key j (k + 1) (x.set! (s + (j + 1)) x[s + j]!)

theorem forIn_yield {α β : Type} (l : List α) (f : β → α → β) (b : β) :
    (forIn (m := Id) l b fun i b => pure (ForInStep.yield (f b i))) = l.foldl f b := by
  induction l generalizing b with
  | nil => rfl
  | cons i l ih => rw [List.forIn_cons, List.foldl_cons]; exact ih _

theorem insertion_eq (x y : Array Nat) (s len : Nat) :
    insertion x y s len = (List.range' 1 (len - 1)).foldl (insStep y s) x := by
  unfold insertion
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [← forIn_yield]
  show (forIn (m := Id) _ _ _) = _
  congr 1
  funext i x
  simp only [shift_loop]
  rfl
/-- A loop whose body ignores the index, run for at most `f` iterations. -/
def iterF {σ : Type} (body : σ → ForInStep σ) : Nat → σ → σ
  | 0, st => st
  | f + 1, st => match body st with
    | .done s' => s'
    | .yield s' => iterF body f s'

theorem forIn_iter {σ : Type} (body : σ → Id (ForInStep σ)) :
    ∀ (f k : Nat) (st : σ), (forIn (m := Id) (List.range' k f) st fun _ st => body st) =
      iterF body f st
  | 0, _, _ => rfl
  | f + 1, k, st => by
    rw [List.range'_succ, List.forIn_cons, iterF]
    show (match (body st : ForInStep σ) with
      | .done b => pure b | .yield b => forIn (m := Id) (List.range' (k + 1) f) b _) = _
    cases body st with
    | done b => rfl
    | yield b => exact forIn_iter body f (k + 1) b

/-- The left scan of the partition: state `(x, a, b)`. -/
def bodyL (y : Array Nat) (v c : Nat) (st : Array Nat × Nat × Nat) :
    ForInStep (Array Nat × Nat × Nat) :=
  if (decide (st.2.2 ≥ c) || decide (y[st.1[st.2.2]!]! > v)) = true then
    .done (st.1, st.2.1, st.2.2)
  else if (y[st.1[st.2.2]!]! == v) = true then
    .yield (st.1.swapIfInBounds st.2.1 st.2.2, st.2.1 + 1, st.2.2 + 1)
  else .yield (st.1, st.2.1, st.2.2 + 1)

/-- The right scan of the partition: state `(x, c, d)`, cursors exclusive. -/
def bodyR (y : Array Nat) (v b : Nat) (st : Array Nat × Nat × Nat) :
    ForInStep (Array Nat × Nat × Nat) :=
  if (decide (st.2.1 ≤ b) || decide (y[st.1[st.2.1 - 1]!]! < v)) = true then
    .done (st.1, st.2.1, st.2.2)
  else if (y[st.1[st.2.1 - 1]!]! == v) = true then
    .yield (st.1.swapIfInBounds (st.2.1 - 1) (st.2.2 - 1), st.2.1 - 1, st.2.2 - 1)
  else .yield (st.1, st.2.1 - 1, st.2.2)

/-- One pass of the partition's outer loop: state `(x, a, b, c, d)`. -/
def bodyP (y : Array Nat) (v len : Nat) (st : Array Nat × Nat × Nat × Nat × Nat) :
    ForInStep (Array Nat × Nat × Nat × Nat × Nat) :=
  let l := iterF (bodyL y v st.2.2.2.1) len (st.1, st.2.1, st.2.2.1)
  let r := iterF (bodyR y v l.2.2) len (l.1, st.2.2.2.1, st.2.2.2.2)
  if l.2.2 ≥ r.2.1 then .done (r.1, l.2.1, l.2.2, r.2.1, r.2.2)
  else .yield (r.1.swapIfInBounds l.2.2 (r.2.1 - 1), l.2.1, l.2.2 + 1, r.2.1 - 1, r.2.2)

/-- `k` swaps of `p + i` with `q + i`, for `i` ascending. -/
def swapRun (p q k : Nat) (x : Array Nat) : Array Nat :=
  (List.range' 0 k).foldl (fun x i => x.swapIfInBounds (p + i) (q + i)) x

/-- The partition, from the scans' final state. -/
def partFinish (s len : Nat) (r : Array Nat × Nat × Nat × Nat × Nat) : Array Nat × Nat × Nat :=
  let left := min (r.2.1 - s) (r.2.2.1 - r.2.1)
  let right := min (r.2.2.2.2 - r.2.2.2.1) (s + len - r.2.2.2.2)
  (swapRun r.2.2.1 (s + len - right) right (swapRun s (r.2.2.1 - left) left r.1),
    r.2.2.1 - r.2.1, r.2.2.2.2 - r.2.2.2.1)

theorem partition_eq (x y : Array Nat) (s len : Nat) :
    partition x y s len =
      partFinish s len (iterF (bodyP y (pivot x y s len) len) (len + 1) (x, s, s, s + len, s + len)) := by
  unfold partition
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, forIn_iter, forIn_yield]
  rfl

/-- One pass of the indirect sort's work-stack loop: state `(x, stack)`. -/
def bodyS (y : Array Nat) (st : Array Nat × List (Nat × Nat)) :
    ForInStep (Array Nat × List (Nat × Nat)) :=
  match st.2 with
  | [] => .done st
  | (start, size) :: rest =>
    if size < 11 then .yield (insertion st.1 y start size, rest)
    else .yield ((partition st.1 y start size).1,
      children start size (partition st.1 y start size).2.1 (partition st.1 y start size).2.2 rest)

theorem indirect_eq (x y : Array Nat) (s len : Nat) :
    indirect x y s len =
      (iterF (bodyS y) (2 * len + 1) (x, if len > 1 then [(s, len)] else [])).1 := by
  unfold indirect
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, forIn_iter]
  show (iterF (σ := Array Nat × List (Nat × Nat)) _ _ _).1 = _
  congr 2
  funext st
  rcases st with ⟨a, _ | ⟨⟨start, size⟩, rest⟩⟩
  · rfl
  · simp only [bodyS, children]
    split
    · rfl
    · split <;> split <;> split <;> rfl

theorem scanL_inv (y : Array Nat) (v c : Nat) :
    ∀ (f : Nat) (x : Array Nat) (aa b : Nat), aa ≤ b → b ≤ c + 1 →
      aa ≤ (iterF (bodyL y v c) f (x, aa, b)).2.1 ∧
      (iterF (bodyL y v c) f (x, aa, b)).2.1 ≤ (iterF (bodyL y v c) f (x, aa, b)).2.2 ∧
      b ≤ (iterF (bodyL y v c) f (x, aa, b)).2.2 ∧
      ((iterF (bodyL y v c) f (x, aa, b)).2.2 ≤ c ∨ (iterF (bodyL y v c) f (x, aa, b)).2.2 = b) ∧
      (iterF (bodyL y v c) f (x, aa, b)).2.2 - (iterF (bodyL y v c) f (x, aa, b)).2.1 ≥ b - aa
  | 0, _, _, _, h1, h2 => ⟨Nat.le_refl _, h1, Nat.le_refl _, .inr rfl, Nat.le_refl _⟩
  | f + 1, x, aa, b, h1, h2 => by
    simp only [iterF, bodyL]
    by_cases hb : (decide (b ≥ c) || decide (y[x[b]!]! > v)) = true
    · simp only [hb, ite_true]; exact ⟨Nat.le_refl _, h1, Nat.le_refl _, .inr trivial, Nat.le_refl _⟩
    · simp only [hb, Bool.false_eq_true, ite_false]
      have hbc : b < c := by simp at hb; omega
      by_cases he : (y[x[b]!]! == v) = true
      · simp only [he, ite_true]
        have := scanL_inv y v c f (x.swapIfInBounds aa b) (aa + 1) (b + 1) (by omega) (by omega)
        omega
      · simp only [he, Bool.false_eq_true, ite_false]
        have := scanL_inv y v c f x aa (b + 1) (by omega) (by omega)
        omega

theorem scanL_stop (y : Array Nat) (v c : Nat) (x : Array Nat) (aa b : Nat) (h : c ≤ b) :
    ∀ f, iterF (bodyL y v c) f (x, aa, b) = (x, aa, b)
  | 0 => rfl
  | f + 1 => by simp [iterF, bodyL, h]

theorem scanR_inv (y : Array Nat) (v b : Nat) :
    ∀ (f : Nat) (x : Array Nat) (c d : Nat), b ≤ c + 1 → c ≤ d →
      b ≤ (iterF (bodyR y v b) f (x, c, d)).2.1 + 1 ∧ (iterF (bodyR y v b) f (x, c, d)).2.1 ≤ c ∧
      (iterF (bodyR y v b) f (x, c, d)).2.1 ≤ (iterF (bodyR y v b) f (x, c, d)).2.2 ∧
      (iterF (bodyR y v b) f (x, c, d)).2.2 ≤ d ∧
      (iterF (bodyR y v b) f (x, c, d)).2.2 - (iterF (bodyR y v b) f (x, c, d)).2.1 ≥ d - c ∧
      (b ≤ (iterF (bodyR y v b) f (x, c, d)).2.1 ∨ (iterF (bodyR y v b) f (x, c, d)).2.1 = c)
  | 0, _, _, _, h1, h2 => ⟨h1, Nat.le_refl _, h2, Nat.le_refl _, Nat.le_refl _, .inr rfl⟩
  | f + 1, x, c, d, h1, h2 => by
    simp only [iterF, bodyR]
    by_cases hb : (decide (c ≤ b) || decide (y[x[c - 1]!]! < v)) = true
    · simp only [hb, ite_true]
      exact ⟨h1, Nat.le_refl _, h2, Nat.le_refl _, Nat.le_refl _, .inr trivial⟩
    · simp only [hb, Bool.false_eq_true, ite_false]
      have hbc : b < c := by simp at hb; omega
      by_cases he : (y[x[c - 1]!]! == v) = true
      · simp only [he, ite_true]
        have := scanR_inv y v b f (x.swapIfInBounds (c - 1) (d - 1)) (c - 1) (d - 1) (by omega)
          (by omega)
        omega
      · simp only [he, Bool.false_eq_true, ite_false]
        have := scanR_inv y v b f x (c - 1) d (by omega) (by omega)
        omega

theorem scanR_stop (y : Array Nat) (v b : Nat) (x : Array Nat) (c d : Nat) (h : c ≤ b) :
    ∀ f, iterF (bodyR y v b) f (x, c, d) = (x, c, d)
  | 0 => rfl
  | f + 1 => by simp [iterF, bodyR, h]

theorem bodyP_inv (y : Array Nat) (v len : Nat) :
    ∀ (f : Nat) (x : Array Nat) (aa b c d : Nat), 1 ≤ aa → aa ≤ b → b ≤ c + 1 → 1 ≤ c → c ≤ d →
      b ≤ d → aa ≤ c →
      let r := iterF (bodyP y v len) f (x, aa, b, c, d)
      aa ≤ r.2.1 ∧ r.2.1 ≤ r.2.2.1 ∧ r.2.2.1 ≤ r.2.2.2.1 + 1 ∧ 1 ≤ r.2.2.2.1 ∧
        r.2.2.2.1 ≤ r.2.2.2.2 ∧ r.2.2.1 ≤ r.2.2.2.2 ∧ r.2.2.2.2 ≤ d ∧ aa ≤ r.2.2.2.1
  | 0, _, _, _, _, _, h0, h1, h2, h3, h4, h5, h6 => by
    simp only [iterF]; omega
  | f + 1, x, aa, b, c, d, h0, h1, h2, h3, h4, h5, h6 => by
    have hL := scanL_inv y v c len x aa b h1 h2
    generalize hl : iterF (bodyL y v c) len (x, aa, b) = l at hL
    obtain ⟨x1, aa1, b1⟩ := l
    simp only at hL
    have hR := scanR_inv y v b1 len x1 c d (by omega) h4
    generalize hr : iterF (bodyR y v b1) len (x1, c, d) = r at hR
    obtain ⟨x2, c2, d2⟩ := r
    simp only at hR
    have hB : bodyP y v len (x, aa, b, c, d) = if b1 ≥ c2 then .done (x2, aa1, b1, c2, d2)
        else .yield (x2.swapIfInBounds b1 (c2 - 1), aa1, b1 + 1, c2 - 1, d2) := by
      simp only [bodyP, hl, hr]
    simp only [iterF, hB]
    by_cases hs : b1 ≥ c2
    · simp only [hs, ite_true]; omega
    · simp only [hs, ite_false]
      have := bodyP_inv y v len f (x2.swapIfInBounds b1 (c2 - 1)) aa1 (b1 + 1) (c2 - 1) d2
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      simp only at this
      omega

end NautyVerified.Spec.SortC
