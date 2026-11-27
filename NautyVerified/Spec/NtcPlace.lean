import HexGraphIso.Nauty.Search.Refine

/-!
# The counting-sort placement, for any starting array

A copy of the placement lemmas of HexGraphIso's
`HexGraphIso/Nauty/Search/Refine.lean` (`baseOff`, `placed`, `dest`,
`destOff`, `ntcPlace_eq_fold`, `destOff_inj`, `destOff_surj`,
`ntcPlace_eq_writeSegment`), which are private there, followed by
`place_getElem!`: on the cell's positions, `ntcPlace` started from any
array leaves the specification's segment. nauty places into `workperm`
and copies back, so the C proof needs the statement for an array other
than `lab`.
-/

namespace NautyVerified.Spec.Ntc

open Hex.GraphIso.Nauty

/-- The exclusive prefix width of the count groups below value `bmin + k`:
the number of members whose count value is strictly less than `bmin + k`,
i.e. the offset (from `cell1`) of group `k`'s base position. -/
def baseOff (counts : Array Nat) (bmin k : Nat) : Nat :=
  (List.range counts.size).countP fun o => decide (counts[o]! - bmin < k)

/-- The number of members of group `k` already placed after the
length-`o` prefix of the cell-order walk. -/
def placed (counts : Array Nat) (bmin o k : Nat) : Nat :=
  (List.range o).countP fun o' => counts[o']! - bmin == k

theorem placed_zero (counts : Array Nat) (bmin k : Nat) :
    placed counts bmin 0 k = 0 := by
  simp [placed]

/-- `placed` at the full length is the group multiplicity `baseOff (k+1)
- baseOff k`, and the group base is `baseOff k`. -/
theorem baseOff_succ (counts : Array Nat) (bmin k : Nat) :
    baseOff counts bmin (k + 1) =
      baseOff counts bmin k + placed counts bmin counts.size k := by
  rw [baseOff, baseOff, placed,
    countP_lt_succ (fun o => counts[o]! - bmin) k (List.range counts.size)]

/-- Stepping the walk past index `o` bumps `placed` for `o`'s own group,
leaving the others fixed. -/
theorem placed_succ (counts : Array Nat) (bmin o k : Nat) :
    placed counts bmin (o + 1) k =
      placed counts bmin o k + (if counts[o]! - bmin == k then 1 else 0) := by
  rw [placed, placed, List.range_succ, List.countP_append, List.countP_cons,
    List.countP_nil]
  simp only [Nat.zero_add]

theorem countP_lt_mono {c : Nat → Nat} {k k' : Nat} (h : k ≤ k')
    (l : List Nat) :
    l.countP (fun o => decide (c o < k)) ≤
      l.countP (fun o => decide (c o < k')) := by
  apply List.countP_mono_left
  intro x _ hx
  simp only [decide_eq_true_eq] at hx ⊢
  omega

/-- `baseOff` is monotone in the group index. -/
theorem baseOff_mono (counts : Array Nat) (bmin : Nat) {k k' : Nat}
    (h : k ≤ k') : baseOff counts bmin k ≤ baseOff counts bmin k' :=
  countP_lt_mono h _

/-- `placed` is monotone in the prefix length. -/
theorem placed_mono (counts : Array Nat) (bmin k : Nat) {o o' : Nat}
    (h : o ≤ o') : placed counts bmin o k ≤ placed counts bmin o' k := by
  rw [placed, placed, ← Nat.add_sub_cancel' h, List.range_add,
    List.countP_append]
  omega

/-- Room: a not-yet-placed member of group `v` leaves its group cursor
below the group multiplicity. -/
theorem placed_lt_mult (counts : Array Nat) (bmin o v : Nat)
    (ho : o < counts.size) (hv : counts[o]! - bmin == v) :
    placed counts bmin o v < placed counts bmin counts.size v := by
  have h1 : placed counts bmin (o + 1) v = placed counts bmin o v + 1 := by
    rw [placed_succ, ite_eq_left hv]
  have h2 : placed counts bmin (o + 1) v ≤ placed counts bmin counts.size v :=
    placed_mono counts bmin v (by omega)
  omega

/-- With every count in the window, `baseOff` at the window width is the
whole cell. -/
theorem baseOff_eq_size (counts : Array Nat) (bmin W : Nat)
    (hall : ∀ o, o < counts.size → counts[o]! - bmin < W) :
    baseOff counts bmin W = counts.size := by
  rw [baseOff]
  have hlen : (List.range counts.size).countP
      (fun o => decide (counts[o]! - bmin < W)) =
      (List.range counts.size).length := by
    rw [List.countP_eq_length]
    intro o ho
    rw [List.mem_range] at ho
    simp only [decide_eq_true_eq]
    exact hall o ho
  rw [hlen, List.length_range]

/-- Group intervals are disjoint: distinct groups' base-offset windows
`[baseOff k, baseOff k + mult k)` do not overlap. -/
theorem baseOff_disjoint (counts : Array Nat) (bmin : Nat) {k k' : Nat}
    (hne : k ≠ k') {r r' : Nat}
    (hr : r < placed counts bmin counts.size k)
    (hr' : r' < placed counts bmin counts.size k') :
    baseOff counts bmin k + r ≠ baseOff counts bmin k' + r' := by
  rcases Nat.lt_or_ge k k' with h | h
  · have hb : baseOff counts bmin (k + 1) ≤ baseOff counts bmin k' :=
      baseOff_mono counts bmin (by omega)
    rw [baseOff_succ] at hb
    omega
  · have hlt : k' < k := by omega
    have hb : baseOff counts bmin (k' + 1) ≤ baseOff counts bmin k :=
      baseOff_mono counts bmin (by omega)
    rw [baseOff_succ] at hb
    omega

/-- `baseOff` telescopes into the sum of the earlier group multiplicities:
the exclusive prefix sum the bucket start positions are built from. -/
theorem baseOff_eq_sum (counts : Array Nat) (bmin : Nat) :
    ∀ v : Nat,
      baseOff counts bmin v =
        ((List.range v).map
          (fun j => placed counts bmin counts.size j)).sum
  | 0 => by simp [baseOff]
  | v + 1 => by
    rw [baseOff_succ, baseOff_eq_sum counts bmin v, List.range_succ,
      List.map_append, List.sum_append]
    simp

/-! # Reusable list-indexing lemmas for the placement crux -/

/-- Reading an append below the left operand's length
reads the left operand. -/
theorem flatMap_take_length_le {α β : Type} (g : α → List β)
    (vs : List α) (m : Nat) :
    ((vs.take m).flatMap g).length ≤ (vs.flatMap g).length :=
  calc ((vs.take m).flatMap g).length
      ≤ ((vs.take m).flatMap g).length + ((vs.drop m).flatMap g).length :=
        by omega
    _ = (vs.flatMap g).length := by
        rw [← List.length_append, ← List.flatMap_append,
          List.take_append_drop]

/-- One more block extends the prefix `flatMap` length by that block. -/
theorem flatMap_take_succ_length {α β : Type} [Inhabited α]
    (g : α → List β) (vs : List α) (k : Nat) (hk : k < vs.length) :
    ((vs.take (k + 1)).flatMap g).length =
      ((vs.take k).flatMap g).length + (g (vs[k]!)).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.flatMap_append, List.length_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  congr 2
  rw [getElem!_pos vs k hk]

/-- Indexing a `flatMap` inside one block: the element at
`((vs.take k).flatMap g).length + r` is the `r`-th element of the
`k`-th block `g vs[k]`, given `k` is a real index and `r` is within
that block. -/
theorem flatMap_getElem!_block {α β : Type} [Inhabited α]
    [Inhabited β] (g : α → List β) :
    ∀ (vs : List α) (k r : Nat), k < vs.length →
      r < (g (vs[k]!)).length →
      (vs.flatMap g)[((vs.take k).flatMap g).length + r]! =
        (g (vs[k]!))[r]!
  | [], k, r, hk, _ => absurd hk (by simp)
  | x :: xs, 0, r, _, hr => by
    simp only [List.take_zero, List.flatMap_nil, List.length_nil,
      Nat.zero_add, List.getElem!_cons_zero] at hr ⊢
    rw [List.flatMap_cons, getElem!_append_left hr]
  | x :: xs, k + 1, r, hk, hr => by
    rw [List.getElem!_cons_succ] at hr
    have hk' : k < xs.length := by
      simp only [List.length_cons] at hk; omega
    have hrec := flatMap_getElem!_block g xs k r hk' hr
    have hbound : ((List.take k xs).flatMap g).length + r <
        (xs.flatMap g).length := by
      have hle := flatMap_take_succ_length g xs k hk'
      have hpref := flatMap_take_length_le g xs (k + 1)
      omega
    simp only [List.take_succ_cons, List.flatMap_cons, List.length_append,
      List.getElem!_cons_succ]
    have hge : (g x).length + ((List.take k xs).flatMap g).length + r
        ≥ (g x).length := by omega
    have hsub : (g x).length + ((List.take k xs).flatMap g).length + r
        - (g x).length = ((List.take k xs).flatMap g).length + r := by omega
    rw [getElem!_append_right hge (by rw [hsub]; exact hbound), hsub, hrec]

/-- The value-`w` group of a zipped list from start index `s`, decoded
by `dec` over the absolute positions: the segment `segmentOf` builds
for one value. -/
def grpAt {β : Type} (cs : List Nat) (w : Nat) (dec : Nat → β)
    (s : Nat) : List β :=
  ((cs.zipIdx s).filter fun p => p.1 == w).map fun p => dec p.2

/-- Counting matches through a `zipIdx` ignores the indices. -/
theorem zipIdx_countP_fst (w : Nat) :
    ∀ (cs : List Nat) (s : Nat),
      ((cs.zipIdx s).countP fun p => p.1 == w) = cs.countP (· == w)
  | [], _ => rfl
  | x :: xs, s => by
    rw [List.zipIdx_cons, List.countP_cons, List.countP_cons,
      zipIdx_countP_fst w xs (s + 1)]

/-- The length of a group is the multiplicity of its value. -/
theorem grpAt_length {β : Type} (cs : List Nat) (w : Nat)
    (dec : Nat → β) (s : Nat) :
    (grpAt cs w dec s).length = cs.countP (· == w) := by
  rw [grpAt, List.length_map, ← List.countP_eq_length_filter,
    zipIdx_countP_fst]

/-- The `r`-th element of the value-`w` group, where `r` is the number
of earlier value-`w` positions, is `dec` at the absolute position. -/
theorem grpAt_getElem! {β : Type} [Inhabited β] (w : Nat)
    (dec : Nat → β) :
    ∀ (cs : List Nat) (s o : Nat), o < cs.length → (cs[o]! == w) = true →
      (grpAt cs w dec s)[(cs.take o).countP (· == w)]! = dec (s + o)
  | [], _, o, ho, _ => absurd ho (by simp)
  | x :: xs, s, 0, _, hq => by
    simp only [List.getElem!_cons_zero] at hq
    rw [grpAt, List.zipIdx_cons, List.filter_cons_of_pos (by simpa using hq),
      List.map_cons, List.take_zero, List.countP_nil,
      List.getElem!_cons_zero, Nat.add_zero]
  | x :: xs, s, o + 1, ho, hq => by
    simp only [List.getElem!_cons_succ] at hq
    have ho' : o < xs.length := by
      simp only [List.length_cons] at ho; omega
    have hrec := grpAt_getElem! w dec xs (s + 1) o ho' hq
    rw [grpAt] at hrec
    rw [grpAt, List.zipIdx_cons, List.take_succ_cons, List.countP_cons]
    by_cases hx : (x == w) = true
    · rw [List.filter_cons_of_pos (by simpa using hx), List.map_cons,
        ite_eq_left hx, List.getElem!_cons_succ, hrec]
      congr 1; omega
    · rw [List.filter_cons_of_neg (by simpa using hx), ite_eq_right hx]
      simp only [Nat.add_zero]
      rw [hrec]; congr 1; omega

/-! # `baseOff` and `placed` as list `countP` forms -/

/-- Counting a predicate over a prefix of positions equals counting it
over the prefix list. -/
theorem countP_range_getElem! (l : List Nat) (φ : Nat → Bool) :
    ∀ o : Nat, o ≤ l.length →
      (List.range o).countP (fun i => φ (l[i]!)) = (l.take o).countP φ
  | 0, _ => by simp
  | o + 1, ho => by
    have ho' : o < l.length := by omega
    rw [List.range_succ, List.countP_append, List.countP_singleton,
      List.take_add_one, List.getElem?_eq_getElem ho', Option.toList_some,
      List.countP_append, List.countP_singleton,
      countP_range_getElem! l φ o (by omega), getElem!_pos l o ho']

/-- `placed` counts the value-`bmin + v` positions in the length-`o`
prefix (once every entry is at least `bmin`). -/
theorem placed_eq_take_countP (counts : Array Nat) (bmin o v : Nat)
    (ho : o ≤ counts.size)
    (hmin : ∀ q, q < counts.size → bmin ≤ counts[q]!) :
    placed counts bmin o v =
      (counts.toList.take o).countP (· == bmin + v) := by
  rw [placed]
  have hcongr : (List.range o).countP (fun o' => counts[o']! - bmin == v) =
      (List.range o).countP (fun i => counts.toList[i]! == bmin + v) := by
    apply List.countP_congr
    intro i hi
    rw [List.mem_range] at hi
    have hge : bmin ≤ counts[i]! := hmin i (by omega)
    rw [Array.getElem!_toList]
    simp only [beq_iff_eq]
    omega
  rw [hcongr,
    countP_range_getElem! counts.toList (· == bmin + v) o
      (by rw [Array.length_toList]; exact ho)]

/-- `baseOff` as a `countP` over the count list. -/
theorem baseOff_eq_countP (counts : Array Nat) (bmin v : Nat) :
    baseOff counts bmin v =
      counts.toList.countP (fun c => decide (c - bmin < v)) := by
  rw [baseOff]
  rw [show (fun o => decide (counts[o]! - bmin < v)) =
      (fun i => (fun c => decide (c - bmin < v)) (counts.toList[i]!)) from by
    funext o; rw [Array.getElem!_toList]]
  rw [countP_range_getElem! counts.toList (fun c => decide (c - bmin < v))
    counts.size (Nat.le_of_eq Array.length_toList.symm)]
  rw [List.take_of_length_le (Nat.le_of_eq Array.length_toList)]

/-- The prefix of value groups tiles the members of value below the
threshold: the concatenated groups for `[bmin, …, bmin + v - 1]` have
length `countP (c - bmin < v)`, once every entry is at least `bmin`. -/
theorem flatMap_grpAt_length {β : Type} (cs : List Nat)
    (dec : Nat → β) (bmin : Nat) (hmem : ∀ c ∈ cs, bmin ≤ c) :
    ∀ v : Nat,
      (((List.range v).map (bmin + ·)).flatMap
        (fun w => grpAt cs w dec 0)).length =
        cs.countP (fun c => decide (c - bmin < v))
  | 0 => by
    simp only [List.range_zero, List.map_nil, List.flatMap_nil,
      List.length_nil]
    rw [List.countP_eq_zero.mpr]
    intro c _; simp
  | v + 1 => by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.flatMap_append, List.length_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, grpAt_length,
      flatMap_grpAt_length cs dec bmin hmem v]
    have hswap : cs.countP (· == bmin + v) =
        cs.countP (fun c => c - bmin == v) := by
      apply List.countP_congr
      intro c hc
      have := hmem c hc
      simp only [beq_iff_eq]; omega
    rw [hswap]
    have := countP_lt_succ (fun c => c - bmin) v cs
    omega

/-- Indexing a value-mapped range. -/
theorem map_range_getElem! (bmin W k : Nat) (hk : k < W) :
    ((List.range W).map (bmin + ·))[k]! = bmin + k := by
  rw [getElem!_pos _ k (by rw [List.length_map, List.length_range]; exact hk),
    List.getElem_map, List.getElem_range]

/-! # The placement crux -/

/-- The scatter destination, abstractly: the flatMap of value groups,
indexed at `(members below value bmin+v) + (earlier value-bmin+v
members)`, yields `dec o`. Independent of the array bookkeeping. -/
theorem grouped_getElem! {β : Type} [Inhabited β] (cs : List Nat)
    (dec : Nat → β) (bmin W v o : Nat)
    (hmem : ∀ c ∈ cs, bmin ≤ c) (hv_lt : v < W)
    (ho : o < cs.length) (hqo : (cs[o]! == bmin + v) = true)
    (hr : (cs.take o).countP (· == bmin + v) < cs.countP (· == bmin + v)) :
    (((List.range W).map (bmin + ·)).flatMap
        (fun w => grpAt cs w dec 0))[
        cs.countP (fun c => decide (c - bmin < v)) +
        (cs.take o).countP (· == bmin + v)]! = dec o := by
  have htake : ((List.range W).map (bmin + ·)).take v =
      (List.range v).map (bmin + ·) := by
    rw [← List.map_take, List.take_range, Nat.min_eq_left (by omega)]
  have hbase : ((((List.range W).map (bmin + ·)).take v).flatMap
        (fun w => grpAt cs w dec 0)).length =
        cs.countP (fun c => decide (c - bmin < v)) := by
    rw [htake, flatMap_grpAt_length cs dec bmin hmem v]
  have hvget : ((List.range W).map (bmin + ·))[v]! = bmin + v :=
    map_range_getElem! bmin W v hv_lt
  have hglen : (grpAt cs (bmin + v) dec 0).length =
      cs.countP (· == bmin + v) := grpAt_length cs (bmin + v) dec 0
  rw [← hbase, flatMap_getElem!_block (fun w => grpAt cs w dec 0)
    ((List.range W).map (bmin + ·)) v ((cs.take o).countP (· == bmin + v))
    (by rw [List.length_map, List.length_range]; exact hv_lt)
    (by rw [hvget, hglen]; exact hr)]
  rw [hvget, grpAt_getElem! (bmin + v) dec cs 0 o ho hqo, Nat.zero_add]

/-- The placement crux: the element `segmentOf` produces at
`baseOff v + placed o v` (the counting-sort target slot for the
`o`-th member, whose count value offset is `v`) is exactly the member
`lab[cell1 + o]` the stable walk writes there. This is the first half
of `nontrivialCell = nontrivialCellFast`: it identifies the scatter
destination with the specification's grouped output. -/
theorem segmentOf_getElem!_placement (lab counts : Array Nat)
    (cell1 bmin W o : Nat)
    (hcv : countValues counts.toList = (List.range W).map (bmin + ·))
    (hmin : ∀ q, q < counts.size → bmin ≤ counts[q]!)
    (ho : o < counts.size) (hlt : counts[o]! - bmin < W) :
    (segmentOf lab cell1 counts.toList (countValues counts.toList))[
        baseOff counts bmin (counts[o]! - bmin) +
        placed counts bmin o (counts[o]! - bmin)]! = lab[cell1 + o]! := by
  have hmem : ∀ c ∈ counts.toList, bmin ≤ c := by
    intro c hc
    rw [List.mem_iff_getElem] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    have hsz : i < counts.size := by rw [Array.length_toList] at hi; exact hi
    rw [Array.getElem_toList, ← getElem!_pos counts i hsz]
    exact hmin i hsz
  have hbmin_o : bmin ≤ counts[o]! := hmin o ho
  have holen : o < counts.toList.length := by rw [Array.length_toList]; exact ho
  have hqo : (counts.toList[o]! == bmin + (counts[o]! - bmin)) = true := by
    rw [Array.getElem!_toList]; simp only [beq_iff_eq]; omega
  have hplaced_full : placed counts bmin counts.size (counts[o]! - bmin) =
      counts.toList.countP (· == bmin + (counts[o]! - bmin)) := by
    rw [placed_eq_take_countP counts bmin counts.size _ (Nat.le_refl _) hmin,
      List.take_of_length_le (Nat.le_of_eq Array.length_toList)]
  have hr : (counts.toList.take o).countP (· == bmin + (counts[o]! - bmin)) <
      counts.toList.countP (· == bmin + (counts[o]! - bmin)) := by
    rw [← placed_eq_take_countP counts bmin o _ (Nat.le_of_lt ho) hmin,
      ← hplaced_full]
    exact placed_lt_mult counts bmin o (counts[o]! - bmin) ho (by simp)
  rw [baseOff_eq_countP,
    placed_eq_take_countP counts bmin o _ (Nat.le_of_lt ho) hmin]
  have hseg : segmentOf lab cell1 counts.toList (countValues counts.toList) =
      ((List.range W).map (bmin + ·)).flatMap
        (fun w => grpAt counts.toList w (fun j => lab[cell1 + j]!) 0) := by
    rw [hcv]; rfl
  rw [hseg]
  exact grouped_getElem! counts.toList (fun j => lab[cell1 + j]!) bmin W
    (counts[o]! - bmin) o hmem hlt holen hqo hr

/-! # The placement against `writeSegment ∘ segmentOf`

`ntcPlace` walks the members in cell order, writing each at its
group's running position. It produces the same array as the
specification's `writeSegment ∘ segmentOf`, under the base-position
invariant: after a length-`o` prefix, group `v`'s cursor sits at
`base v` plus the number of already-placed value-`v` members. -/

/-- The absolute destination of the `o`-th member under the base
positions `base`: its group base plus the number of already-placed
members of its group. -/
def dest (counts : Array Nat) (bmin : Nat) (base : Nat → Nat)
    (o : Nat) : Nat :=
  base (counts[o]! - bmin) + placed counts bmin o (counts[o]! - bmin)

/-- The scatter characterization: when the cursor array holds each
group's base plus its placed count, `ntcPlace` writes member `o` at
`dest o` for each `o` in the walked window, in order. The result is a
fold of independent `set!`s. -/
theorem ntcPlace_eq_fold (counts members : Array Nat) (bmin : Nat)
    (base : Nat → Nat) :
    ∀ (fuel o0 : Nat) (lab starts : Array Nat),
      (∀ w, w < starts.size →
        starts[w]! = base w + placed counts bmin o0 w) →
      (∀ o, o0 ≤ o → o < o0 + fuel → counts[o]! - bmin < starts.size) →
      (ntcPlace counts members bmin fuel o0 lab starts).1 =
        (List.range fuel).foldl
          (fun a k => a.set! (dest counts bmin base (o0 + k)) members[o0 + k]!)
          lab
  | 0, o0, lab, starts, _, _ => by simp [ntcPlace]
  | fuel + 1, o0, lab, starts, hinv, hbound => by
    rw [ntcPlace]
    have hvsz : counts[o0]! - bmin < starts.size :=
      hbound o0 (Nat.le_refl _) (by omega)
    have hpos : starts[counts[o0]! - bmin]! =
        base (counts[o0]! - bmin) + placed counts bmin o0 (counts[o0]! - bmin) :=
      hinv _ hvsz
    have hposdest : starts[counts[o0]! - bmin]! = dest counts bmin base o0 := by
      rw [hpos, dest]
    -- the recursive cursor array still satisfies the invariant at o0 + 1
    have hinv' : ∀ w, w < (starts.set! (counts[o0]! - bmin)
          (starts[counts[o0]! - bmin]! + 1)).size →
        (starts.set! (counts[o0]! - bmin)
          (starts[counts[o0]! - bmin]! + 1))[w]! =
          base w + placed counts bmin (o0 + 1) w := by
      intro w hw
      rw [Array.size_set!] at hw
      by_cases hwv : w = counts[o0]! - bmin
      · subst hwv
        rw [Array.getElem!_set!_self _ _ _ hw, hpos, placed_succ,
          ite_eq_left (by simp)]
        omega
      · rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hwv h.symm), hinv w hw,
          placed_succ, ite_eq_right (by simpa using fun h => hwv h.symm)]
        omega
    have hbound' : ∀ o, o0 + 1 ≤ o → o < (o0 + 1) + fuel →
        counts[o]! - bmin < (starts.set! (counts[o0]! - bmin)
          (starts[counts[o0]! - bmin]! + 1)).size := by
      intro o ho1 ho2
      rw [Array.size_set!]
      exact hbound o (by omega) (by omega)
    rw [ntcPlace_eq_fold counts members bmin base fuel (o0 + 1)
      (lab.set! starts[counts[o0]! - bmin]! members[o0]!)
      (starts.set! (counts[o0]! - bmin) (starts[counts[o0]! - bmin]! + 1))
      hinv' hbound']
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    rw [hposdest]
    have hik : ∀ k, o0 + 1 + k = o0 + (k + 1) := fun k => by omega
    simp only [hik, Nat.succ_eq_add_one, Nat.add_zero]

/-- A fold of `set!`s leaves a position it never writes to unchanged. -/
theorem foldl_set!_not_mem {α : Type} [Inhabited α] (f : Nat → Nat)
    (g : Nat → α) (p : Nat) :
    ∀ (l : List Nat) (a : Array α), (∀ o ∈ l, f o ≠ p) →
      (l.foldl (fun a o => a.set! (f o) (g o)) a)[p]! = a[p]!
  | [], _, _ => rfl
  | x :: xs, a, hne => by
    rw [List.foldl_cons,
      foldl_set!_not_mem f g p xs (a.set! (f x) (g x))
        (fun o ho => hne o (List.mem_cons_of_mem _ ho)),
      Array.getElem!_set!_ne _ _ _ _ (hne x (List.mem_cons_self))]

/-- A fold of `set!`s at positions that are distinct on a duplicate-free
list reads back the value written at any given member. -/
theorem foldl_set!_mem {α : Type} [Inhabited α] (f : Nat → Nat)
    (g : Nat → α) :
    ∀ (l : List Nat) (a : Array α) (o0 : Nat), l.Nodup → o0 ∈ l →
      (∀ o ∈ l, o ≠ o0 → f o ≠ f o0) → f o0 < a.size →
      (l.foldl (fun a o => a.set! (f o) (g o)) a)[f o0]! = g o0
  | x :: xs, a, o0, hnd, ho0, hinj, hsz => by
    rw [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp ho0 with rfl | ho0'
    · rw [foldl_set!_not_mem f g (f o0) xs (a.set! (f o0) (g o0))
        (fun o ho => hinj o (List.mem_cons_of_mem _ ho)
          (fun h => hnd.1 (h ▸ ho))),
        Array.getElem!_set!_self _ _ _ hsz]
    · rw [foldl_set!_mem f g xs (a.set! (f x) (g x)) o0 hnd.2 ho0'
        (fun o ho => hinj o (List.mem_cons_of_mem _ ho))
        (by rw [Array.size_set!]; exact hsz)]

/-- `ntcPlace` preserves the labelling size (it only overwrites in
place). -/
theorem ntcPlace_size (counts members : Array Nat) (bmin : Nat) :
    ∀ (fuel o : Nat) (lab starts : Array Nat),
      (ntcPlace counts members bmin fuel o lab starts).1.size = lab.size
  | 0, _, _, _ => rfl
  | fuel + 1, o, lab, starts => by
    rw [ntcPlace, ntcPlace_size counts members bmin fuel (o + 1),
      Array.size_set!]

/-- `ntcPlace` preserves the cursor-array size. -/
theorem ntcPlace_starts_size (counts members : Array Nat) (bmin : Nat) :
    ∀ (fuel o : Nat) (lab starts : Array Nat),
      (ntcPlace counts members bmin fuel o lab starts).2.size = starts.size
  | 0, _, _, _ => rfl
  | fuel + 1, o, lab, starts => by
    rw [ntcPlace, ntcPlace_starts_size counts members bmin fuel (o + 1),
      Array.size_set!]

/-! # The initial cursor positions are the group bases -/

/-- The bucket, filled from all counts against a window-sized zero seed,
holds each group's multiplicity `placed … counts.size`. -/
theorem ntcBucket_placed (counts : Array Nat) (bmin W : Nat)
    (hbound : ∀ q, q < counts.size → counts[q]! - bmin < W)
    (v : Nat) (hv : v < W) :
    (ntcBucket counts bmin counts.size 0
        (Array.replicate W 0))[v]! =
      placed counts bmin counts.size v := by
  have hrange : ∀ q, 0 ≤ q → q < 0 + counts.size →
      counts[q]! - bmin < (Array.replicate W 0 : Array Nat).size := by
    intro q _ hq
    rw [Array.size_replicate]
    exact hbound q (by omega)
  rw [ntcBucket_spec counts bmin counts.size 0 (Array.replicate W 0)
    (by omega) hrange v (by rw [Array.size_replicate]; exact hv)]
  have hrep : (Array.replicate W 0 : Array Nat)[v]! = 0 := by
    rw [getElem!_pos _ v (by rw [Array.size_replicate]; exact hv),
      Array.getElem_replicate]
  rw [hrep, Nat.zero_add, placed, List.range_eq_range']

/-- The initial cursor array places group `w` at `cell1 + baseOff w`:
each start is the exclusive prefix sum of the earlier group
multiplicities, which is exactly `baseOff`. -/
theorem ntcStarts_baseOff (counts bucket : Array Nat) (bmin W cell1 : Nat)
    (hbucket : ∀ v, v < W → bucket[v]! = placed counts bmin counts.size v)
    (w : Nat) (hw : w < W) :
    (ntcStarts bucket W cell1 #[])[w]! = cell1 + baseOff counts bmin w := by
  have hval := ntcStarts_value bucket W cell1 #[] w (by simpa using hw)
  simp only [Array.size_empty, Nat.zero_add] at hval
  rw [hval]
  have hmap : ((List.range w).map (fun j => bucket[j]!)) =
      (List.range w).map (fun j => placed counts bmin counts.size j) := by
    apply List.map_congr_left
    intro j hj
    exact hbucket j (by rw [List.mem_range] at hj; omega)
  rw [hmap, ← baseOff_eq_sum]

/-! # The scatter is a bijection onto the cell -/

/-- The offset (from `cell1`) of the `o`-th member's scatter
destination: its group base plus its within-group cursor. -/
def destOff (counts : Array Nat) (bmin o : Nat) : Nat :=
  baseOff counts bmin (counts[o]! - bmin) +
    placed counts bmin o (counts[o]! - bmin)

/-- Every destination lands inside the cell `[0, counts.size)`. -/
theorem destOff_lt (counts : Array Nat) (bmin W : Nat)
    (hbd : ∀ q, q < counts.size → counts[q]! - bmin < W)
    (o : Nat) (ho : o < counts.size) :
    destOff counts bmin o < counts.size := by
  have hv : counts[o]! - bmin < W := hbd o ho
  have hroom : placed counts bmin o (counts[o]! - bmin) <
      placed counts bmin counts.size (counts[o]! - bmin) :=
    placed_lt_mult counts bmin o (counts[o]! - bmin) ho (by simp)
  have htile : baseOff counts bmin ((counts[o]! - bmin) + 1) ≤
      baseOff counts bmin W := baseOff_mono counts bmin (by omega)
  rw [baseOff_succ] at htile
  have hsize : baseOff counts bmin W = counts.size :=
    baseOff_eq_size counts bmin W hbd
  rw [destOff]
  omega

/-- The scatter is injective on the cell. -/
theorem destOff_inj (counts : Array Nat) (bmin : Nat)
    {o o' : Nat} (ho : o < counts.size) (ho' : o' < counts.size)
    (hne : o ≠ o') : destOff counts bmin o ≠ destOff counts bmin o' := by
  by_cases hv : counts[o]! - bmin = counts[o']! - bmin
  · -- same group: within-group cursors differ
    rw [destOff, destOff, hv]
    have hne' : placed counts bmin o (counts[o']! - bmin) ≠
        placed counts bmin o' (counts[o']! - bmin) := by
      rcases Nat.lt_or_ge o o' with h | h
      · have h1 : placed counts bmin (o + 1) (counts[o']! - bmin) =
            placed counts bmin o (counts[o']! - bmin) + 1 := by
          rw [placed_succ, ite_eq_left (by rw [← hv]; simp)]
        have h2 : placed counts bmin (o + 1) (counts[o']! - bmin) ≤
            placed counts bmin o' (counts[o']! - bmin) :=
          placed_mono counts bmin _ (by omega)
        omega
      · have hlt : o' < o := by omega
        have h1 : placed counts bmin (o' + 1) (counts[o']! - bmin) =
            placed counts bmin o' (counts[o']! - bmin) + 1 := by
          rw [placed_succ, ite_eq_left (by simp)]
        have h2 : placed counts bmin (o' + 1) (counts[o']! - bmin) ≤
            placed counts bmin o (counts[o']! - bmin) :=
          placed_mono counts bmin _ (by omega)
        omega
    omega
  · -- distinct groups: disjoint base windows
    rw [destOff, destOff]
    exact baseOff_disjoint counts bmin hv
      (placed_lt_mult counts bmin o (counts[o]! - bmin) ho (by simp))
      (placed_lt_mult counts bmin o' (counts[o']! - bmin) ho' (by simp))

/-- A `Nodup` list of naturals, all below `N`, of length `N`, contains
every `k < N`, by pigeonhole. -/
theorem nodup_range_full (N : Nat) (l : List Nat) (hnd : l.Nodup)
    (hlen : l.length = N) (hlt : ∀ x ∈ l, x < N) :
    ∀ k, k < N → k ∈ l := by
  intro k hk
  rcases Decidable.em (k ∈ l) with h | h
  · exact h
  · exfalso
    have hsub : l ⊆ (List.range N).erase k := by
      intro x hx
      rw [List.mem_erase_of_ne (by rintro rfl; exact h hx)]
      exact List.mem_range.mpr (hlt x hx)
    have hle := List.Nodup.length_le_of_subset hnd hsub
    rw [List.length_erase, List.length_range] at hle
    simp only [List.mem_range.mpr hk, ite_true] at hle
    omega

/-- Every cell offset `j < counts.size` is some member's destination. -/
theorem destOff_surj (counts : Array Nat) (bmin W : Nat)
    (hbd : ∀ q, q < counts.size → counts[q]! - bmin < W)
    (j : Nat) (hj : j < counts.size) :
    ∃ o, o < counts.size ∧ destOff counts bmin o = j := by
  have hlen : ((List.range counts.size).map
      (fun o => destOff counts bmin o)).length = counts.size := by
    rw [List.length_map, List.length_range]
  have hlt : ∀ x ∈ (List.range counts.size).map
      (fun o => destOff counts bmin o), x < counts.size := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    exact destOff_lt counts bmin W hbd o (List.mem_range.mp ho)
  have hnd : ((List.range counts.size).map
      (fun o => destOff counts bmin o)).Nodup := by
    show List.Pairwise (fun a b => a ≠ b)
      (List.map (fun o => destOff counts bmin o) (List.range counts.size))
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro a b ha hb hab heq
    exact destOff_inj counts bmin (List.mem_range.mp ha)
      (List.mem_range.mp hb) hab heq
  have hmem := nodup_range_full counts.size _ hnd hlen hlt j hj
  rw [List.mem_map] at hmem
  obtain ⟨o, ho, hoj⟩ := hmem
  exact ⟨o, List.mem_range.mp ho, hoj⟩

/-! # `ntcPlace` realises `writeSegment ∘ segmentOf` -/

/-- A fold of `set!`s preserves the array size. -/
theorem foldl_set!_size {α : Type} [Inhabited α] (f : Nat → Nat)
    (g : Nat → α) :
    ∀ (l : List Nat) (a : Array α),
      (l.foldl (fun a k => a.set! (f k) (g k)) a).size = a.size
  | [], _ => rfl
  | x :: xs, a => by
    rw [List.foldl_cons, foldl_set!_size f g xs, Array.size_set!]

/-- Reading back one written slot: `writeSegment` puts `seg[j]` at
`lo + j` whenever that slot is inside the array, whether or not the
whole segment fits (writes past the end are `set!` no-ops). -/
theorem writeSegment_getElem! :
    ∀ (seg : List Nat) (lab : Array Nat) (lo j : Nat), j < seg.length →
      lo + j < lab.size →
      (writeSegment lab lo seg)[lo + j]! = seg[j]!
  | [], _, _, j, hj, _ => absurd hj (by simp)
  | x :: seg, lab, lo, 0, _, hsz => by
    rw [writeSegment, List.getElem!_cons_zero]
    show (writeSegment (lab.set! lo x) (lo + 1) seg)[lo]! = x
    rw [writeSegment_outside seg _ (lo + 1) lo (Or.inl (by omega)),
      Array.getElem!_set!_self _ _ _ (by omega)]
  | x :: seg, lab, lo, j + 1, hj, hsz => by
    rw [writeSegment, List.getElem!_cons_succ,
      show lo + (j + 1) = (lo + 1) + j from by omega]
    exact writeSegment_getElem! seg (lab.set! lo x) (lo + 1) j
      (by simp only [List.length_cons] at hj; omega)
      (by rw [Array.size_set!]; omega)

theorem array_ext! {α : Type} [Inhabited α] {A B : Array α}
    (hsize : A.size = B.size)
    (h : ∀ p, p < A.size → A[p]! = B[p]!) : A = B := by
  apply Array.ext hsize
  intro i hi1 hi2
  have hi := h i hi1
  rwa [getElem!_pos A i hi1, getElem!_pos B i hi2] at hi

/-- The scatter placement realises the specification's stable sort:
under the group-base cursor positions, `ntcPlace` writes each member
into its group slot, producing exactly `writeSegment ∘ segmentOf`. -/
theorem ntcPlace_eq_writeSegment (lab counts members : Array Nat)
    (cell1 bmin W : Nat)
    (hmem : ∀ q, q < counts.size → bmin ≤ counts[q]!)
    (hbd : ∀ q, q < counts.size → counts[q]! - bmin < W)
    (hcv : countValues counts.toList = (List.range W).map (bmin + ·))
    (hmembers : ∀ o, o < counts.size → members[o]! = lab[cell1 + o]!)
    (starts : Array Nat) (hssize : starts.size = W)
    (hs0 : ∀ w, w < W → starts[w]! = cell1 + baseOff counts bmin w) :
    (ntcPlace counts members bmin counts.size 0 lab starts).1 =
      writeSegment lab cell1
        (segmentOf lab cell1 counts.toList (countValues counts.toList)) := by
  -- the fold's destination and value functions
  have hfeq : ∀ k, dest counts bmin (fun w => cell1 + baseOff counts bmin w) k =
      cell1 + destOff counts bmin k := by
    intro k; rw [dest, destOff]; omega
  have hfrange : ∀ k, k < counts.size →
      cell1 ≤ dest counts bmin (fun w => cell1 + baseOff counts bmin w) k ∧
      dest counts bmin (fun w => cell1 + baseOff counts bmin w) k <
        cell1 + counts.size := by
    intro k hk
    rw [hfeq k]
    exact ⟨by omega, by have := destOff_lt counts bmin W hbd k hk; omega⟩
  -- ntcPlace unfolds to a scatter fold
  have hfold := ntcPlace_eq_fold counts members bmin
    (fun w => cell1 + baseOff counts bmin w) counts.size 0 lab starts
    (by intro w hw; rw [placed_zero, Nat.add_zero]
        exact hs0 w (by rw [← hssize]; exact hw))
    (by intro o _ ho; rw [hssize]; exact hbd o (by omega))
  rw [hfold]
  simp only [Nat.zero_add]
  -- name the specification segment
  obtain ⟨seg, hseg⟩ :
      ∃ seg, seg = segmentOf lab cell1 counts.toList (countValues counts.toList) :=
    ⟨_, rfl⟩
  rw [← hseg]
  have hmem' : ∀ c ∈ counts.toList, bmin ≤ c := by
    intro c hc
    rw [List.mem_iff_getElem] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    have hsz : i < counts.size := by rw [Array.length_toList] at hi; exact hi
    rw [Array.getElem_toList, ← getElem!_pos counts i hsz]
    exact hmem i hsz
  have hseglen : seg.length = counts.size := by
    have hflat : seg = ((List.range W).map (bmin + ·)).flatMap
        (fun w => grpAt counts.toList w (fun j => lab[cell1 + j]!) 0) := by
      rw [hseg, hcv]; rfl
    rw [hflat, flatMap_grpAt_length counts.toList _ bmin hmem' W,
      ← baseOff_eq_countP, baseOff_eq_size counts bmin W hbd]
  have hsz : ((List.range counts.size).foldl
      (fun a k => a.set!
        (dest counts bmin (fun w => cell1 + baseOff counts bmin w) k)
        members[k]!) lab).size = lab.size :=
    foldl_set!_size _ _ (List.range counts.size) lab
  refine array_ext! ?_ ?_
  · rw [hsz, writeSegment_size]
  · intro p hp
    rw [hsz] at hp
    by_cases hpc : cell1 ≤ p ∧ p < cell1 + counts.size
    · -- inside the cell: p = cell1 + (p - cell1)
      obtain ⟨hp1, hp2⟩ := hpc
      have hjlt : p - cell1 < counts.size := by omega
      have hpj : p = cell1 + (p - cell1) := by omega
      obtain ⟨o, ho, hoj⟩ := destOff_surj counts bmin W hbd (p - cell1) hjlt
      have hfo : dest counts bmin (fun w => cell1 + baseOff counts bmin w) o = p := by
        rw [hfeq o, hoj]; omega
      have hinj : ∀ k ∈ List.range counts.size, k ≠ o →
          dest counts bmin (fun w => cell1 + baseOff counts bmin w) k ≠
          dest counts bmin (fun w => cell1 + baseOff counts bmin w) o := by
        intro k hk hkne
        rw [hfeq k, hfeq o]
        have := destOff_inj counts bmin (List.mem_range.mp hk) ho hkne
        omega
      have hlhs := foldl_set!_mem
        (fun k => dest counts bmin (fun w => cell1 + baseOff counts bmin w) k)
        (fun k => members[k]!) (List.range counts.size) lab o
        List.nodup_range (List.mem_range.mpr ho) hinj (by rw [hfo]; omega)
      rw [hfo] at hlhs
      rw [hlhs, hmembers o ho]
      -- RHS reads seg[p - cell1]!
      have hrhs : (writeSegment lab cell1 seg)[p]! = seg[p - cell1]! := by
        have hw := writeSegment_getElem! seg lab cell1 (p - cell1)
          (by rw [hseglen]; exact hjlt) (by omega)
        rwa [← hpj] at hw
      rw [hrhs, hseg]
      have hcrux := segmentOf_getElem!_placement lab counts cell1 bmin W o
        hcv hmem ho (hbd o ho)
      rw [show p - cell1 = baseOff counts bmin (counts[o]! - bmin) +
          placed counts bmin o (counts[o]! - bmin) by
        rw [← destOff]; exact hoj.symm]
      exact hcrux.symm
    · -- outside the cell: both give lab[p]!
      have hlhs : ((List.range counts.size).foldl
          (fun a k => a.set!
            (dest counts bmin (fun w => cell1 + baseOff counts bmin w) k)
            members[k]!) lab)[p]! = lab[p]! := by
        apply foldl_set!_not_mem
        intro k hk
        have := hfrange k (List.mem_range.mp hk)
        omega
      have hrhs : (writeSegment lab cell1 seg)[p]! = lab[p]! := by
        apply writeSegment_outside
        rw [hseglen]; omega
      rw [hlhs, hrhs]


/-- On the cell's positions, `ntcPlace` started from any array `X` writes
what `writeSegment ∘ segmentOf` puts into `lab`. -/
theorem place_getElem! (lab counts members X : Array Nat) (cell1 bmin W : Nat)
    (hmem : ∀ q, q < counts.size → bmin ≤ counts[q]!)
    (hbd : ∀ q, q < counts.size → counts[q]! - bmin < W)
    (hcv : countValues counts.toList = (List.range W).map (bmin + ·))
    (hmembers : ∀ o, o < counts.size → members[o]! = lab[cell1 + o]!)
    (starts : Array Nat) (hssize : starts.size = W)
    (hs0 : ∀ w, w < W → starts[w]! = cell1 + baseOff counts bmin w)
    (hX : cell1 + counts.size ≤ X.size) (hL : cell1 + counts.size ≤ lab.size)
    (p : Nat) (hp1 : cell1 ≤ p) (hp2 : p < cell1 + counts.size) :
    (ntcPlace counts members bmin counts.size 0 X starts).1[p]! =
      (writeSegment lab cell1
        (segmentOf lab cell1 counts.toList (countValues counts.toList)))[p]! := by
  rw [← ntcPlace_eq_writeSegment lab counts members cell1 bmin W hmem hbd hcv hmembers starts
    hssize hs0]
  have hfeq : ∀ k, dest counts bmin (fun w => cell1 + baseOff counts bmin w) k =
      cell1 + destOff counts bmin k := by
    intro k; rw [dest, destOff]; omega
  have hinv : ∀ w, w < starts.size → starts[w]! =
      (fun w => cell1 + baseOff counts bmin w) w + placed counts bmin 0 w := by
    intro w hw; rw [placed_zero, Nat.add_zero]; exact hs0 w (by rw [← hssize]; exact hw)
  have hbound : ∀ o, 0 ≤ o → o < 0 + counts.size → counts[o]! - bmin < starts.size := by
    intro o _ ho; rw [hssize]; exact hbd o (by omega)
  rw [ntcPlace_eq_fold counts members bmin _ counts.size 0 X starts hinv hbound,
    ntcPlace_eq_fold counts members bmin _ counts.size 0 lab starts hinv hbound]
  simp only [Nat.zero_add]
  obtain ⟨o, ho, hoj⟩ := destOff_surj counts bmin W hbd (p - cell1) (by omega)
  have hfo : dest counts bmin (fun w => cell1 + baseOff counts bmin w) o = p := by
    rw [hfeq o, hoj]; omega
  have hinj : ∀ k ∈ List.range counts.size, k ≠ o →
      dest counts bmin (fun w => cell1 + baseOff counts bmin w) k ≠
      dest counts bmin (fun w => cell1 + baseOff counts bmin w) o := by
    intro k hk hkne
    rw [hfeq k, hfeq o]
    have := destOff_inj counts bmin (List.mem_range.mp hk) ho hkne
    omega
  have h1 := foldl_set!_mem
    (fun k => dest counts bmin (fun w => cell1 + baseOff counts bmin w) k)
    (fun k => members[k]!) (List.range counts.size) X o
    List.nodup_range (List.mem_range.mpr ho) hinj (by rw [hfo]; omega)
  have h2 := foldl_set!_mem
    (fun k => dest counts bmin (fun w => cell1 + baseOff counts bmin w) k)
    (fun k => members[k]!) (List.range counts.size) lab o
    List.nodup_range (List.mem_range.mpr ho) hinj (by rw [hfo]; omega)
  rw [hfo] at h1 h2
  rw [h1, h2]

end NautyVerified.Spec.Ntc
