import NautyVerified.Proofs.Harness.Graph

/-!
# The initial partition the harness builds

The harness lists the vertices colour by colour (`cellLoop`), then marks a
cell end wherever the colour changes (`endLoop`). `endsOf_iff`: in the
concatenation of classes whose keys increase strictly, a position ends its
class exactly when it is the last position or the key changes there, which
identifies the harness's `ptn` with `initialPartition`'s cell ends.
-/

namespace NautyVerified.Proofs.Harness

open Hex.GraphIso Hex.GraphIso.Nauty

/-- The ends of the nonempty classes of `cls`, placed from `off`. -/
def endsOf : List (List Nat) → Nat → List Nat
  | [], _ => []
  | cl :: rest, off => (if cl.isEmpty then [] else [off + cl.length - 1]) ++ endsOf rest (off + cl.length)

theorem foldl_ends (cls : List (List Nat)) :
    ∀ (acc : List Nat) (off : Nat),
      (cls.foldl (fun (a : List Nat × Nat) cl =>
        if cl.isEmpty then a else ((a.2 + cl.length - 1) :: a.1, a.2 + cl.length)) (acc, off)) =
      ((endsOf cls off).reverse ++ acc, off + (cls.map List.length).sum) := by
  induction cls with
  | nil => intro acc off; simp [endsOf]
  | cons cl rest ih =>
    intro acc off
    rw [List.foldl_cons]
    by_cases h : cl.isEmpty
    · rw [if_pos h, ih]
      have : cl = [] := by simpa using h
      subst this
      simp [endsOf]
    · rw [if_neg h, ih]
      simp only [endsOf, if_neg h, List.reverse_append, List.reverse_singleton, List.append_assoc,
        List.singleton_append, List.map_cons, List.sum_cons, List.reverse_nil, List.nil_append]
      refine Prod.ext (by simp) ?_
      show off + cl.length + _ = off + (cl.length + _)
      omega

theorem endsOf_bounds : ∀ (cls : List (List Nat)) (off x : Nat), x ∈ endsOf cls off →
    off ≤ x ∧ x < off + cls.flatten.length
  | [], _, _, h => by simp [endsOf] at h
  | cl :: rest, off, x, h => by
    simp only [endsOf, List.mem_append] at h
    simp only [List.flatten_cons, List.length_append]
    rcases h with h | h
    · by_cases he : cl.isEmpty
      · simp [he] at h
      · rw [if_neg he, List.mem_singleton] at h
        have : 0 < cl.length := by
          rcases cl with _ | _
          · simp at he
          · simp
        omega
    · have := endsOf_bounds rest _ x h
      omega

theorem getElem!_append (a b : List Nat) (i : Nat) :
    (a ++ b)[i]! = if i < a.length then a[i]! else b[i - a.length]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
    List.getElem!_eq_getElem?_getD]
  split
  · rename_i h
    rw [List.getElem?_append_left h]
  · rename_i h
    rw [List.getElem?_append_right (by omega)]

/-- In the concatenation of classes whose keys increase strictly along the
list, a position ends its class exactly when it is the last one or the key
changes after it. -/
theorem endsOf_iff (key : Nat → Nat) :
    ∀ (cls : List (List Nat)) (c0 : Nat),
      (∀ j (hj : j < cls.length), ∀ x ∈ cls[j], key x = c0 + j) →
      ∀ (off i : Nat), i < cls.flatten.length →
        (off + i ∈ endsOf cls off ↔
          (i + 1 = cls.flatten.length ∨ key cls.flatten[i]! ≠ key cls.flatten[i + 1]!))
  | [], _, _, _, i, hi => by simp at hi
  | cl :: rest, c0, hkey, off, i, hi => by
    have hcl : ∀ x ∈ cl, key x = c0 := fun x hx => by simpa using hkey 0 (by simp) x hx
    have hrest : ∀ j (hj : j < rest.length), ∀ x ∈ rest[j], key x = (c0 + 1) + j :=
      fun j hj x hx => by have := hkey (j + 1) (by simp; omega) x (by simpa using hx); omega
    have hrk : ∀ x ∈ rest.flatten, c0 + 1 ≤ key x := fun x hx => by
      obtain ⟨cl', hcl', hx⟩ := List.mem_flatten.1 hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcl'
      have := hrest j hj _ hx
      omega
    have ih := endsOf_iff key rest (c0 + 1) hrest
    simp only [List.flatten_cons, List.length_append] at hi ⊢
    simp only [endsOf, List.mem_append, getElem!_append]
    by_cases hi1 : i < cl.length
    · have hne : ¬ cl.isEmpty := by
        rcases cl with _ | _
        · simp at hi1
        · simp
      have hne' : cl.isEmpty = false := by simpa using hne
      simp only [hne', Bool.false_eq_true, ite_false, List.mem_singleton, hi1, ite_true]
      have hk1 : key cl[i]! = c0 := hcl _ (by rw [getElem!_pos cl i hi1]; exact List.getElem_mem _)
      have hnot : off + i ∉ endsOf rest (off + cl.length) := fun h => by
        have := endsOf_bounds rest _ _ h; omega
      by_cases hlast : i + 1 = cl.length
      · simp only [show off + i = off + cl.length - 1 by omega, true_or, true_iff]
        by_cases hr : rest.flatten.length = 0
        · left; omega
        · right
          rw [hk1, if_neg (by omega), show i + 1 - cl.length = 0 by omega]
          have := hrk rest.flatten[0]! (by rw [getElem!_pos _ 0 (by omega)]; exact List.getElem_mem _)
          omega
      · have hi2 : i + 1 < cl.length := by omega
        have hk2 : key cl[i + 1]! = c0 :=
          hcl _ (by rw [getElem!_pos cl _ hi2]; exact List.getElem_mem _)
        simp only [hi2, ite_true, hk1, hk2, ne_eq, not_true_eq_false, or_false]
        constructor
        · rintro (h | h)
          · omega
          · exact absurd h hnot
        · intro h; omega
    · simp only [hi1, if_false]
      obtain ⟨i', rfl⟩ : ∃ i', i = cl.length + i' := ⟨i - cl.length, by omega⟩
      have hi' : i' < rest.flatten.length := by omega
      have h := ih (off + cl.length) i' hi'
      rw [show off + (cl.length + i') = off + cl.length + i' by omega, h,
        show cl.length + i' - cl.length = i' by omega,
        if_neg (show ¬ cl.length + i' + 1 < cl.length by omega),
        show cl.length + i' + 1 - cl.length = i' + 1 by omega]
      constructor
      · rintro (h | h)
        · · by_cases he : cl.isEmpty
            · simp [he] at h
            · rw [if_neg he, List.mem_singleton] at h
              have : 0 < cl.length := by
                rcases cl with _ | _
                · simp at he
                · simp
              omega
        · rcases h with h | h
          · left; omega
          · right; exact h
      · rintro (h | h)
        · right; left; omega
        · right; right; exact h

/-! ## The classes the harness lists -/

/-- The vertices of colour `c`, in increasing order. -/
def clsOf (key : Nat → Nat) (n c : Nat) : List Nat := (List.range n).filter fun v => key v = c

/-- What `cellLoop` has listed after colours below `c` and vertices of colour
`c` below `j`. -/
def listed (key : Nat → Nat) (n c j : Nat) : List Nat :=
  (List.range c).flatMap (clsOf key n) ++ (List.range j).filter fun v => key v = c

theorem countP_lt_succ (key : Nat → Nat) (c : Nat) :
    ∀ l : List Nat, l.countP (fun v => key v < c + 1) =
      l.countP (fun v => key v < c) + l.countP (fun v => key v = c)
  | [] => rfl
  | x :: l => by
    simp only [List.countP_cons, countP_lt_succ key c l]
    by_cases h1 : key x < c
    · simp [h1, show key x < c + 1 by omega, show key x ≠ c by omega]; omega
    · by_cases h2 : key x = c
      · simp [h1, h2]; omega
      · simp [h1, h2, show ¬ key x < c + 1 by omega]

theorem length_flatMap_clsOf (key : Nat → Nat) (n : Nat) :
    ∀ c, ((List.range c).flatMap (clsOf key n)).length = (List.range n).countP (fun v => key v < c)
  | 0 => by simp
  | c + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_clsOf key n c,
      countP_lt_succ]
    simp [clsOf, List.countP_eq_length_filter]

theorem length_listed (key : Nat → Nat) (n c j : Nat) :
    (listed key n c j).length =
      (List.range n).countP (fun v => key v < c) + (List.range j).countP (fun v => key v = c) := by
  simp only [listed, List.length_append, length_flatMap_clsOf]
  simp [List.countP_eq_length_filter]

theorem countP_le_range (p : Nat → Bool) {j n : Nat} (hj : j ≤ n) :
    (List.range j).countP p ≤ (List.range n).countP p := by
  obtain ⟨d, rfl⟩ : ∃ d, n = j + d := ⟨n - j, by omega⟩
  rw [List.range_add, List.countP_append]
  omega

theorem countP_lt_add_eq (key : Nat → Nat) (c n : Nat) :
    (List.range n).countP (fun v => key v < c) + (List.range n).countP (fun v => key v = c) ≤ n := by
  rw [← countP_lt_succ]
  exact Nat.le_trans List.countP_le_length (by simp)

theorem length_listed_le (key : Nat → Nat) {n c j : Nat} (hj : j ≤ n) :
    (listed key n c j).length ≤ n := by
  rw [length_listed]
  have := countP_le_range (fun v => decide (key v = c)) hj
  have := countP_lt_add_eq key c n
  omega

theorem listed_full (key : Nat → Nat) {n k : Nat} (hk : ∀ v < n, key v < k) :
    (listed key n k 0).length = n := by
  rw [length_listed]
  simp only [List.range_zero, List.countP_nil, Nat.add_zero]
  have h := (List.countP_eq_length (p := fun v => decide (key v < k)) (l := List.range n)).2
    (fun v hv => by simpa using hk v (List.mem_range.1 hv))
  rw [h, List.length_range]

/-! ## `G`'s partition -/

/-- The colours the harness reads, vertex by vertex. -/
def colours {n k : Nat} (G : Colored n k) : List Nat :=
  (List.finRange n).map fun v => (G.coloring.cells.get v).val

/-- The colour of a vertex. -/
def keyOf {n k : Nat} (G : Colored n k) (v : Nat) : Nat := (colours G)[v]!

theorem colours_length {n k : Nat} (G : Colored n k) : (colours G).length = n := by
  simp [colours]

theorem keyOf_lt {n k : Nat} (G : Colored n k) {v : Nat} (hv : v < n) :
    keyOf G v = (G.coloring.cells.get ⟨v, hv⟩).val := by
  unfold keyOf colours
  rw [getElem!_pos _ v (by simp [hv])]
  simp [List.getElem_map, List.getElem_finRange]

theorem keyOf_bound {n k : Nat} (G : Colored n k) {v : Nat} (hv : v < n) : keyOf G v < k := by
  rw [keyOf_lt G hv]; exact Fin.isLt _

theorem colorClass_eq {n k : Nat} (G : Colored n k) {c : Nat} (hc : c < k) :
    colorClass G c = clsOf (keyOf G) n c := by
  simp only [colorClass, clsOf]
  apply List.filter_congr
  intro v hv
  have hv' := List.mem_range.1 hv
  rw [dite_eq_left ⟨hv', hc⟩, keyOf_lt G hv', Bool.eq_iff_iff]
  simp [Fin.ext_iff, Vector.get]

theorem initialPartition_eq {n k : Nat} (G : Colored n k) :
    initialPartition G = ((listed (keyOf G) n k 0).toArray,
      endsOf ((List.range k).map (clsOf (keyOf G) n)) 0) := by
  have hcls : (List.range k).map (colorClass G) = (List.range k).map (clsOf (keyOf G) n) :=
    List.map_congr_left fun c hc => colorClass_eq G (List.mem_range.1 hc)
  simp only [initialPartition, hcls]
  rw [foldl_ends]
  simp [listed, List.flatMap]

theorem listed_flatten (key : Nat → Nat) (n k : Nat) :
    listed key n k 0 = ((List.range k).map (clsOf key n)).flatten := by
  simp [listed, List.flatMap]

/-- The harness's cell ends are `initialPartition`'s. -/
theorem harnessPtn_get {n k : Nat} (G : Colored n k) {i : Nat} (hi : i < n) :
    (harnessPtn n (initialPartition G).2)[i]! =
      if i + 1 = n ∨ keyOf G (listed (keyOf G) n k 0)[i]! ≠ keyOf G (listed (keyOf G) n k 0)[i + 1]!
      then 0 else 1 := by
  have hlen : (listed (keyOf G) n k 0).length = n := listed_full _ fun v hv => keyOf_bound G hv
  have hkey : ∀ j (hj : j < ((List.range k).map (clsOf (keyOf G) n)).length),
      ∀ x ∈ ((List.range k).map (clsOf (keyOf G) n))[j], keyOf G x = 0 + j := by
    intro j hj x hx
    simp only [List.getElem_map, List.getElem_range, clsOf, List.mem_filter, decide_eq_true_eq] at hx
    omega
  have h := endsOf_iff (keyOf G) _ 0 hkey 0 i (by rw [← listed_flatten, hlen]; exact hi)
  rw [← listed_flatten, hlen, Nat.zero_add] at h
  simp only [harnessPtn, initialPartition_eq]
  rw [getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn]
  simp only
  by_cases hm : i ∈ endsOf ((List.range k).map (clsOf (keyOf G) n)) 0
  · rw [if_pos hm, if_pos (h.1 hm)]
  · rw [if_neg hm, if_neg (fun h' => hm (h.2 h'))]

end NautyVerified.Proofs.Harness
