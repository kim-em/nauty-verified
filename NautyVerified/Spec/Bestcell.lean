import NautyVerified.Spec.Fmptn

/-!
# HexGraphIso's `bestcell` and `targetcell`, unrolled

`startsOf` lists the starts of the nontrivial cells among a list of cells;
`starts_step` walks `cells` one cell at a time, as nauty's first `bestcell`
loop does. `bestcellRow` and `bestcellRows` are folds (`row_eq`, `rows_eq`), and
`row_bound`/`rows_bound` bound the joined-cell counts, so nauty's `int`
counters never overflow. `findStart` is the first nontrivial cell, as
`targetcell`'s scan finds it.
-/

namespace NautyVerified.Spec.Bestcell

open Hex.GraphIso.Nauty

theorem get_set (B : Array Nat) (i v x : Nat) :
    (B.set! i v)[x]! = if i = x ∧ x < B.size then v else B[x]! := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hx : x < B.size
  · rw [getElem!_pos (B.setIfInBounds i v) x (by simpa using hx), getElem!_pos B x hx,
      Array.getElem_setIfInBounds (by simpa using hx)]
    by_cases h : i = x <;> simp [h, hx]
  · rw [getElem!_neg (B.setIfInBounds i v) x (by simpa using hx), getElem!_neg B x hx]
    simp [hx]

theorem get_rep (k x : Nat) : (Array.replicate k 0)[x]! = 0 := by
  by_cases hx : x < k
  · rw [getElem!_pos _ x (by simpa using hx)]; simp
  · rw [getElem!_neg _ x (by simpa using hx)]; rfl

/-- The starts of the nontrivial cells among `L`. -/
def startsOf (L : List (Nat × Nat)) : List Nat := (L.filter fun (c1, c2) => c1 ≠ c2).map (·.1)

theorem startsOf_cons (c1 c2 : Nat) (L : List (Nat × Nat)) :
    startsOf ((c1, c2) :: L) = (if c1 ≠ c2 then [c1] else []) ++ startsOf L := by
  by_cases h : c1 = c2 <;> simp [startsOf, h]

section
variable {ptn : Array Nat} {level n : Nat}

theorem cellEnd_self (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) {c : Nat} (hc : c < n)
    (h : ptn[c]! ≤ level) : cellEnd ptn level c = c := by
  have sp := cellEnd_spec hs hc hlast
  rcases Nat.lt_or_ge c (cellEnd ptn level c) with h1 | h1
  · have := sp.2.2.2 c (Nat.le_refl _) h1; omega
  · omega

theorem cellEnd_ne (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) {c : Nat} (hc : c < n)
    (h : level < ptn[c]!) : c ≠ cellEnd ptn level c := by
  have sp := cellEnd_spec hs hc hlast
  intro he; rw [← he] at sp; omega

theorem cells_go_fuel (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) :
    ∀ F F' c, n - c ≤ F → n - c ≤ F' → cells.go ptn level n F c = cells.go ptn level n F' c
  | 0, F', c, h, _ => by
    rw [cells_go_ge _ _ _ _ _ (by omega), cells_go_ge _ _ _ _ _ (by omega)]
  | F + 1, F', c, h, h' => by
    by_cases hc : c < n
    · obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
      rw [cells_go_succ _ _ _ _ _ hc, cells_go_succ _ _ _ _ _ hc]
      have := (cellEnd_spec hs hc hlast).1
      rw [cells_go_fuel hs hlast F F'' _ (by omega) (by omega)]
    · rw [cells_go_ge _ _ _ _ _ hc, cells_go_ge _ _ _ _ _ hc]

/-- One cell of the walk. -/
theorem starts_step (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) {c : Nat} (hc : c < n) :
    startsOf (cells.go ptn level n (n - c) c) =
      (if level < ptn[c]! then [c] else []) ++
        startsOf (cells.go ptn level n (n - (cellEnd ptn level c + 1)) (cellEnd ptn level c + 1)) := by
  have he := (cellEnd_spec hs hc hlast).1
  rw [show n - c = (n - c - 1) + 1 by omega, cells_go_succ _ _ _ _ _ hc, startsOf_cons,
    cells_go_fuel hs hlast (n - c - 1) (n - (cellEnd ptn level c + 1)) _ (by omega) (by omega)]
  congr 1
  by_cases h : level < ptn[c]!
  · rw [ite_eq_left (cellEnd_ne hs hlast hc h), ite_eq_left h]
  · rw [ite_eq_right h, cellEnd_self hs hlast hc (by omega), ite_eq_right (by simp)]

theorem starts_end (F c : Nat) (hc : n ≤ c) : startsOf (cells.go ptn level n F c) = [] := by
  rw [cells_go_ge _ _ _ _ _ (by omega)]; rfl

theorem starts_eq : ((cells ptn level n).filter fun (c1, c2) => c1 ≠ c2).map (·.1) =
    startsOf (cells.go ptn level n (n - 0) 0) := by
  rw [Nat.sub_zero]; rfl

theorem mem_cells (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) :
    ∀ F c p, p ∈ cells.go ptn level n F c → c ≤ p.1 ∧ p.1 < n ∧ p.2 = cellEnd ptn level p.1
  | 0, _, _, h => by simp [cells.go] at h
  | F + 1, c, p, h => by
    by_cases hc : c < n
    · rw [cells_go_succ _ _ _ _ _ hc] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨Nat.le_refl _, hc, rfl⟩
      · have h1 := mem_cells hs hlast F _ p h
        have h2 := (cellEnd_spec hs hc hlast).1
        exact ⟨by omega, h1.2.1, h1.2.2⟩
    · rw [cells_go_ge _ _ _ _ _ hc] at h; simp at h

theorem mem_starts (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) (F c x : Nat)
    (h : x ∈ startsOf (cells.go ptn level n F c)) : c ≤ x ∧ x < n ∧ level < ptn[x]! := by
  simp only [startsOf, List.mem_map, List.mem_filter] at h
  obtain ⟨p, ⟨hp, hne⟩, rfl⟩ := h
  have := mem_cells hs hlast F c p hp
  refine ⟨this.1, this.2.1, ?_⟩
  rcases Nat.lt_or_ge level ptn[p.1]! with h1 | h1
  · exact h1
  · have := cellEnd_self hs hlast this.2.1 h1
    obtain ⟨a, b⟩ := p
    simp_all

/-- A nontrivial cell exists when some position has `ptn` above `level`. -/
theorem exists_cell (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) :
    ∀ F c x, n - c ≤ F → c ≤ x → x < n → level < ptn[x]! →
      ∃ p ∈ cells.go ptn level n F c, p.1 ≠ p.2
  | 0, c, x, h, h1, h2, _ => absurd h (by omega)
  | F + 1, c, x, h, h1, h2, h3 => by
    have hc : c < n := by omega
    rw [cells_go_succ _ _ _ _ _ hc]
    by_cases hp : level < ptn[c]!
    · exact ⟨_, List.mem_cons_self .., cellEnd_ne hs hlast hc hp⟩
    · have he := cellEnd_self hs hlast hc (by omega)
      have hx : c ≠ x := fun e => hp (e ▸ h3)
      obtain ⟨q, hq, hne⟩ := exists_cell hs hlast F (cellEnd ptn level c + 1) x (by omega)
        (by omega) h2 h3
      exact ⟨q, List.mem_cons_of_mem _ hq, hne⟩

theorem starts_ne_nil (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) {x : Nat} (hx : x < n)
    (hgt : level < ptn[x]!) : startsOf (cells.go ptn level n (n - 0) 0) ≠ [] := by
  obtain ⟨p, hp, hne⟩ := exists_cell hs hlast (n - 0) 0 x (by omega) (by omega) hx hgt
  intro h
  simp only [startsOf, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  have := h p hp
  obtain ⟨a, b⟩ := p
  simp_all

/-- `targetcell`'s scan: the first nontrivial cell starts at the first `k` with
`ptn[k] > level`. -/
theorem findStart (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) :
    ∀ F c k, n - c ≤ F → c ≤ k → k ≤ n → (∀ y, c ≤ y → y < k → ptn[y]! ≤ level) →
      (k < n → level < ptn[k]!) →
      ((cells.go ptn level n F c).find? fun (c1, c2) => c1 ≠ c2).map (·.1) =
        if k < n then some k else none
  | 0, c, k, h, h1, h2, _, _ => by
    rw [ite_eq_right (by omega)]; rfl
  | F + 1, c, k, h, h1, h2, hy, hk => by
    by_cases hc : c < n
    · rw [cells_go_succ _ _ _ _ _ hc, List.find?_cons]
      by_cases hck : c = k
      · subst hck
        have := cellEnd_ne hs hlast hc (hk hc)
        rw [ite_eq_left hc]; simp [this]
      · have hp := hy c (Nat.le_refl _) (by omega)
        have he := cellEnd_self hs hlast hc hp
        rw [he, ← findStart hs hlast F (c + 1) k (by omega) (by omega) h2
          (fun y h1 h2 => hy y (by omega) h2) hk]
        simp
    · rw [cells_go_ge _ _ _ _ _ hc, ite_eq_right (by omega)]; rfl

end

/-! ## The joined-cell counts -/

section
variable {n : Nat} (ctx : Ctx n) (lab startArr : Array Nat) (W : VSet n) (v2 : Nat)

/-- One `v1` step of `bestcellRow`. -/
def rowStep (B : Array Nat) (v1 : Nat) : Array Nat :=
  if ¬ W.interIsEmpty ctx.g[lab[startArr[v1]!]!]! ∧ ¬ W.subset ctx.g[lab[startArr[v1]!]!]! then
    (B.set! v1 (B[v1]! + 1)).set! v2 (B[v2]! + 1)
  else B

theorem row_eq : ∀ (l : List Nat) (B : Array Nat),
    bestcellRow ctx lab startArr W v2 l B = l.foldl (rowStep ctx lab startArr W v2) B
  | [], _ => rfl
  | v1 :: l, B => by
    rw [bestcellRow, List.foldl_cons, rowStep]
    split
    · exact row_eq l _
    · exact row_eq l _

theorem size_rowStep (B : Array Nat) (v1 : Nat) :
    (rowStep ctx lab startArr W v2 B v1).size = B.size := by
  unfold rowStep; split <;> simp

theorem size_row : ∀ (l : List Nat) (B : Array Nat),
    (l.foldl (rowStep ctx lab startArr W v2) B).size = B.size
  | [], _ => rfl
  | v1 :: l, B => by rw [List.foldl_cons, size_row l, size_rowStep]

/-- The bound on the counts part way through row `v2`. -/
def bnd (j x : Nat) : Nat :=
  if x < j then v2 else if x < v2 then v2 - 1 else if x = v2 then j else 0

theorem rowStep_get (C : Array Nat) (j x : Nat) :
    (rowStep ctx lab startArr W v2 C j)[x]! = C[x]! ∨
      (x = v2 ∧ (rowStep ctx lab startArr W v2 C j)[x]! = C[v2]! + 1) ∨
      (x = j ∧ (rowStep ctx lab startArr W v2 C j)[x]! = C[j]! + 1) := by
  unfold rowStep
  split
  · rw [get_set, get_set, Array.size_set!]
    by_cases h1 : v2 = x ∧ x < C.size
    · rw [ite_eq_left h1]; exact .inr (.inl ⟨h1.1.symm, rfl⟩)
    · rw [ite_eq_right h1]
      by_cases h2 : j = x ∧ x < C.size
      · rw [ite_eq_left h2]; exact .inr (.inr ⟨h2.1.symm, rfl⟩)
      · rw [ite_eq_right h2]; exact .inl rfl
  · exact .inl rfl

theorem bnd_cases (j x : Nat) :
    (x < j ∧ bnd v2 j x = v2) ∨ (j ≤ x ∧ x < v2 ∧ bnd v2 j x = v2 - 1) ∨
      (x = v2 ∧ bnd v2 j x = j) ∨ (v2 < x ∧ bnd v2 j x = 0) := by
  unfold bnd
  by_cases h1 : x < j
  · exact .inl ⟨h1, by rw [ite_eq_left h1]⟩
  · rw [ite_eq_right h1]
    by_cases h2 : x < v2
    · exact .inr (.inl ⟨by omega, h2, by rw [ite_eq_left h2]⟩)
    · rw [ite_eq_right h2]
      by_cases h3 : x = v2
      · exact .inr (.inr (.inl ⟨h3, by rw [ite_eq_left h3]⟩))
      · exact .inr (.inr (.inr ⟨by omega, by rw [ite_eq_right h3]⟩))

theorem row_bound (B : Array Nat) (hB : ∀ x, B[x]! ≤ if x < v2 then v2 - 1 else 0) :
    ∀ j ≤ v2, ∀ x, ((List.range j).foldl (rowStep ctx lab startArr W v2) B)[x]! ≤ bnd v2 j x
  | 0, _, x => by
    have := hB x
    simp only [List.range_zero, List.foldl_nil]
    rcases bnd_cases v2 0 x with ⟨h1, -⟩ | ⟨-, h2, e⟩ | ⟨h3, e⟩ | ⟨h4, e⟩
    · omega
    · rw [e]; rw [ite_eq_left h2] at this; exact this
    · rw [e]; rw [ite_eq_right (by omega)] at this; omega
    · rw [e]; rw [ite_eq_right (by omega)] at this; omega
  | j + 1, hj, x => by
    have ih := row_bound B hB j (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range j).foldl (rowStep ctx lab startArr W v2) B = C at ih
    have hx := ih x
    have hjj := ih j
    have hv := ih v2
    rcases bnd_cases v2 j j with ⟨h, -⟩ | ⟨-, -, ej⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · omega
    · rw [ej] at hjj
      rcases bnd_cases v2 j v2 with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, ev⟩ | ⟨h, -⟩
      · omega
      · omega
      · rw [ev] at hv
        rcases bnd_cases v2 (j + 1) x with ⟨h1, e1⟩ | ⟨h1, h2, e1⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
        rw [e1] <;>
        rcases rowStep_get ctx lab startArr W v2 C j x with g | ⟨g1, g⟩ | ⟨g1, g⟩ <;> rw [g] <;>
        rcases bnd_cases v2 j x with ⟨k1, f⟩ | ⟨k1, k2, f⟩ | ⟨k1, f⟩ | ⟨k1, f⟩ <;>
        rw [f] at hx <;> omega
      · omega
    · omega
    · omega
end

section
variable {n : Nat} (ctx : Ctx n) (lab ptn : Array Nat) (level : Nat) (startArr : Array Nat)

/-- One `v2` step of `bestcellRows`. -/
def rowsStep (B : Array Nat) (v2 : Nat) : Array Nat :=
  (List.range v2).foldl (rowStep ctx lab startArr
    (worksetOf n lab startArr[v2]! (cellEnd ptn level startArr[v2]!)) v2) B

theorem rows_eq : ∀ (l : List Nat) (B : Array Nat),
    bestcellRows ctx lab ptn level startArr l B = l.foldl (rowsStep ctx lab ptn level startArr) B
  | [], _ => rfl
  | v2 :: l, B => by
    rw [bestcellRows, List.foldl_cons, rowsStep, row_eq]
    exact rows_eq l _

theorem rows_bound (N : Nat) :
    ∀ k, 1 ≤ k → ∀ x, ((List.range' 1 (k - 1)).foldl (rowsStep ctx lab ptn level startArr)
      (Array.replicate N 0))[x]! ≤ if x < k then k - 1 else 0
  | 0, h, _ => absurd h (by omega)
  | 1, _, x => by simp [get_rep]
  | k + 2, _, x => by
    have ih := rows_bound N (k + 1) (by omega)
    rw [show k + 2 - 1 = k + 1 by omega, List.range'_concat, List.foldl_append, List.foldl_cons,
      List.foldl_nil, show 1 + 1 * k = k + 1 by omega]
    rw [show k + 1 - 1 = k by omega] at ih
    unfold rowsStep
    have hb := row_bound ctx lab startArr
      (worksetOf n lab startArr[k + 1]! (cellEnd ptn level startArr[k + 1]!)) (k + 1) _
      ih (k + 1) (Nat.le_refl _) x
    rcases bnd_cases (k + 1) (k + 1) x with ⟨h, e⟩ | ⟨h, h2, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ <;>
      rw [e] at hb
    · rw [ite_eq_left (by omega)]; exact hb
    · omega
    · rw [ite_eq_left (by omega)]; exact hb
    · rw [ite_eq_right (by omega)]; exact hb

theorem argmax_lt (B : Array Nat) (N : Nat) :
    ∀ (l : List Nat) (v1 v2 : Nat), (∀ i ∈ l, i < N) → v1 < N → argmaxLoop B l v1 v2 < N
  | [], _, _, _, h => h
  | i :: l, v1, v2, hl, h => by
    rw [argmaxLoop]
    split
    · exact argmax_lt B N l _ _ (fun j hj => hl j (List.mem_cons_of_mem _ hj))
        (hl i List.mem_cons_self)
    · exact argmax_lt B N l _ _ (fun j hj => hl j (List.mem_cons_of_mem _ hj)) h
end

/-- `bestcell`'s result starts a nontrivial cell, when one exists. -/
theorem bestcell_mem {n : Nat} (ctx : Ctx n) (lab ptn : Array Nat) (level : Nat) (hs : ptn.size = n)
    (hlast : ptn[n - 1]! ≤ level) {x : Nat} (hx : x < n) (hgt : level < ptn[x]!) :
    bestcell ctx lab ptn level < n ∧ level < ptn[bestcell ctx lab ptn level]! := by
  have hne := starts_ne_nil hs hlast hx hgt
  rw [bestcell]
  simp only
  rw [starts_eq]
  generalize hS : startsOf (cells.go ptn level n (n - 0) 0) = S at hne
  have hlen : S.length ≠ 0 := by intro h; exact hne (List.eq_nil_of_length_eq_zero h)
  rw [ite_eq_right (by simpa using hlen)]
  generalize hA : argmaxLoop _ _ _ _ = a
  have ha : a < S.length := by
    rw [← hA]
    exact argmax_lt _ _ _ _ _ (fun i hi => by simp [List.mem_range'] at hi; omega) (by omega)
  rw [List.getElem!_toArray, getElem!_pos S a ha]
  have := mem_starts hs hlast (n - 0) 0 S[a] (by rw [hS]; exact List.getElem_mem ha)
  exact ⟨this.2.1, this.2.2⟩

theorem bestcell_nil {n : Nat} (ctx : Ctx n) (lab ptn : Array Nat) (level : Nat)
    (h : (startsOf (cells.go ptn level n (n - 0) 0)).length = 0) :
    bestcell ctx lab ptn level = n := by
  rw [bestcell]
  simp only
  rw [starts_eq, ite_eq_left (by simpa using h)]

theorem bestcell_eq {n : Nat} (ctx : Ctx n) (lab ptn : Array Nat) (level : Nat)
    (h : (startsOf (cells.go ptn level n (n - 0) 0)).length ≠ 0) :
    let S := startsOf (cells.go ptn level n (n - 0) 0)
    let B := (List.range' 1 (S.length - 1)).foldl (rowsStep ctx lab ptn level S.toArray)
      (Array.replicate S.length 0)
    bestcell ctx lab ptn level = S[argmaxLoop B (List.range' 1 (S.length - 1)) 0 B[0]!]! := by
  intro S B
  rw [bestcell]
  simp only
  rw [starts_eq, ite_eq_right (by simpa using h), rows_eq, List.getElem!_toArray]

/-- `targetcell`'s result starts a nontrivial cell, when one exists and the hint is in range. -/
theorem targetcell_mem {n : Nat} (ctx : Ctx n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) (hh : hint < n) {x : Nat}
    (hx : x < n) (hgt : level < ptn[x]!) :
    targetcell ctx lab ptn level tcLevel hint < n ∧
      level < ptn[targetcell ctx lab ptn level tcLevel hint]! := by
  unfold targetcell
  split
  · next h => exact ⟨by omega, h.2.1⟩
  · split
    · exact bestcell_mem ctx lab ptn level hs hlast hx hgt
    · dsimp only
      split
      · next c1 c2 hf =>
        have hp := List.find?_some hf
        have hm := List.mem_of_find?_eq_some hf
        have := mem_cells hs hlast n 0 _ hm
        simp only at this hp
        refine ⟨this.2.1, ?_⟩
        rcases Nat.lt_or_ge level ptn[c1]! with h1 | h1
        · exact h1
        · have := cellEnd_self hs hlast this.2.1 h1
          simp_all
      · next hf =>
        rw [List.find?_eq_none] at hf
        obtain ⟨p, hp, hne⟩ := exists_cell hs hlast n 0 x (by omega) (by omega) hx hgt
        have := hf p hp
        obtain ⟨a, b⟩ := p
        simp_all

end NautyVerified.Spec.Bestcell
