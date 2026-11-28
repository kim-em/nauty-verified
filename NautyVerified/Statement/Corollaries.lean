import NautyVerified.Statement.Harness
import HexGraphIso.Nauty.Policy.Emission
import HexGraphIso.Nauty.Invariant.OrbitComplete

/-!
# Facts behind the corollaries of the end-to-end theorem

* `rowWords_inj`, `flatMap_inj`: the setwords the harness writes for the
  canonical graph determine its rows;
* `canong_toList`: the search's canonical rows are the rows of HexGraphIso's
  canonical form `canon G`;
* `finalState_orbits`: the orbit array of the final search state is
  `Aut.orbits G`, the `orbjoin` fold over the emitted generators that
  HexGraphIso's orbit theorem is stated for. The search joins every
  automorphism it discovers, and one it does not emit leaves the orbit count,
  hence the orbit array, unchanged.
-/

namespace NautyVerified.Statement

open Hex.GraphIso Hex.GraphIso.Nauty

/-! ## Setwords determine a row -/

/-- The number whose binary digits, most significant first, are `p 0, ..., p (j - 1)`. -/
def horner (p : Nat → Prop) [DecidablePred p] : Nat → Nat
  | 0 => 0
  | j + 1 => 2 * horner p j + (if p j then 1 else 0)

theorem horner_lt (p : Nat → Prop) [DecidablePred p] : ∀ j, horner p j < 2 ^ j
  | 0 => by simp [horner]
  | j + 1 => by
    have := horner_lt p j
    simp only [horner, Nat.pow_succ]
    split <;> omega

theorem horner_inj {p q : Nat → Prop} [DecidablePred p] [DecidablePred q] :
    ∀ j, horner p j = horner q j → ∀ b, b < j → (p b ↔ q b)
  | 0, _, b, hb => absurd hb (Nat.not_lt_zero _)
  | j + 1, h, b, hb => by
    simp only [horner] at h
    have hj : (p j ↔ q j) ∧ horner p j = horner q j := by
      by_cases hp : p j <;> by_cases hq : q j <;> simp only [hp, hq, ite_true, ite_false] at h <;>
        first | omega | exact ⟨by simp [hp, hq], by omega⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
    · exact horner_inj j hj.2 b hb
    · exact hj.1

theorem foldl_bits (p : Nat → Prop) [DecidablePred p] : ∀ j, j ≤ 64 →
    (List.range j).foldl (fun acc b => if p b then acc + 2 ^ (63 - b) else acc) 0 =
      2 ^ (64 - j) * horner p j
  | 0, _ => by simp [horner]
  | j + 1, hj => by
    rw [List.range_succ, List.foldl_append, foldl_bits p j (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, horner]
    rw [show 64 - j = (63 - j) + 1 by omega, show 64 - (j + 1) = 63 - j by omega, Nat.pow_succ]
    generalize 2 ^ (63 - j) = x
    generalize horner p j = h
    split
    · rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_left_comm]
    · rw [Nat.add_zero, Nat.mul_assoc, Nat.mul_left_comm]

/-- The setwords of a row determine the row. -/
theorem rowWords_inj {n : Nat} {s t : VSet n} (h : rowWords (setwordsNeeded n) s = rowWords (setwordsNeeded n) t) :
    s = t := by
  apply VSet.ext
  intro j
  rcases Nat.lt_or_ge j n with hj | hj
  · rw [rowWords, rowWords, List.map_inj_left] at h
    have hw : j / 64 < setwordsNeeded n := by unfold setwordsNeeded; omega
    have h1 := h (j / 64) (List.mem_range.mpr hw)
    rw [BitVec.toInt_inj] at h1
    have h2 := congrArg BitVec.toNat h1
    simp only [BitVec.toNat_ofNat] at h2
    rw [foldl_bits _ 64 (Nat.le_refl _), foldl_bits _ 64 (Nat.le_refl _)] at h2
    simp only [Nat.sub_self, Nat.pow_zero, Nat.one_mul] at h2
    rw [Nat.mod_eq_of_lt (horner_lt _ 64), Nat.mod_eq_of_lt (horner_lt _ 64)] at h2
    have h3 := horner_inj 64 h2 (j % 64) (Nat.mod_lt _ (by decide))
    rw [show 64 * (j / 64) + j % 64 = j by omega] at h3
    cases hs : s.mem j <;> cases ht : t.mem j <;> simp_all
  · rw [VSet.mem_of_ge hj, VSet.mem_of_ge hj]

/-- Flattening lists of equal length through an injective map of fixed output
length is injective. -/
theorem flatMap_inj {α β : Type} {f : α → List β} {m : Nat} (hf : ∀ a b, f a = f b → a = b)
    (hm : ∀ a, (f a).length = m) :
    ∀ l₁ l₂ : List α, l₁.length = l₂.length → l₁.flatMap f = l₂.flatMap f → l₁ = l₂
  | [], [], _, _ => rfl
  | a :: l₁, b :: l₂, hl, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hm, hm])
    rw [hf a b h1, flatMap_inj hf hm l₁ l₂ (by simpa using hl) h2]

theorem length_rowWords {n : Nat} (m : Nat) (s : VSet n) : (rowWords m s).length = m := by
  simp [rowWords]

/-! ## The canonical rows -/

theorem toList_eq_map {α : Type} [Inhabited α] {a : Array α} {n : Nat} (h : a.size = n) :
    a.toList = (List.range n).map (a[·]!) := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Array.getElem_toList, List.getElem_map, List.getElem_range]
  rw [getElem!_pos a i (by simpa using h1)]

/-- The search's canonical rows are the rows of the canonical form. -/
theorem canong_toList {n k : Nat} (G : Colored n k) :
    (runColoredTraced G).result.canong.toList = (rowsOf (canon G)).toList := by
  obtain ⟨l, hl⟩ : ∃ l, Label.ofArray? n (runColored G).canonlab = some l := by
    have h := searchResult?_isSome G
    unfold searchResult? at h
    cases e : Label.ofArray? n (runColored G).canonlab with
    | none => rw [e] at h; simp at h
    | some l => exact ⟨l, rfl⟩
  have hc : canon G = G.relabel l := by
    simp only [canon, canonicalize, searchResult?, hl, Option.map_some, Option.get_some]
  rw [hc, rowsOf_relabel_eq_leafRows (canonlab_size G) (Label.ofArray?_get hl),
    runColoredTraced_result, ← canong_rows G, toList_eq_map (canongInv_size (canong_inv G))]

theorem rowsOf_eq_iff {n k : Nat} (C D : Colored n k) :
    (rowsOf C).toList = (rowsOf D).toList ↔ C.graph = D.graph := by
  constructor
  · intro h
    simp only [rowsOf, List.map_inj_left] at h
    apply Hex.Graph.ext
    intro i j
    have := congrArg (fun s => VSet.mem s j.val) (h i.val (List.mem_range.mpr i.isLt))
    simpa [mem_rowOf, i.isLt, j.isLt] using this
  · intro h
    have : rowOf C = rowOf D := by
      funext i
      unfold rowOf
      rw [h]
    rw [rowsOf, rowsOf, this]

/-- The colour of each vertex of the canonical form. -/
theorem cells_canon {n k : Nat} (G : Colored n k) (x : Fin n) :
    ((canon G).coloring.cells[x]).val = (sortedColorSeq G)[x.val]! := by
  rw [canon_eq_specCanon]
  simp only [specCanon, formOfKey, Fin.getElem_fin, Hex.Vector.getElem_ofFn']

theorem flatMap_replicate {f g : Nat → Nat} :
    ∀ l : List Nat, l.map f = l.map g →
      l.flatMap (fun c => List.replicate (f c) c) = l.flatMap (fun c => List.replicate (g c) c)
  | [], _ => rfl
  | c :: l, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.flatMap_cons, h.1, flatMap_replicate l h.2]

theorem counts_eq_iff {n k : Nat} (G H : Colored n k) :
    (List.range k).map (fun c => (colorClass G c).length) =
        (List.range k).map (fun c => (colorClass H c).length) ↔
      sortedColorSeq G = sortedColorSeq H := by
  constructor
  · intro h
    exact flatMap_replicate _ h
  · intro h
    rw [List.map_inj_left]
    intro c hc
    have hc' := List.mem_range.mp hc
    rw [← count_sortedColorSeq G hc', ← count_sortedColorSeq H hc', h]

theorem sortedColorSeq_eq {n k : Nat} {G H : Colored n k} (h : canon G = canon H) :
    sortedColorSeq G = sortedColorSeq H := by
  apply List.ext_getElem (by rw [length_sortedColorSeq, length_sortedColorSeq])
  intro i h1 h2
  have hi : i < n := by rwa [length_sortedColorSeq] at h1
  have := cells_canon G ⟨i, hi⟩
  rw [h, cells_canon H ⟨i, hi⟩, getElem!_pos (sortedColorSeq G) i h1, getElem!_pos (sortedColorSeq H) i h2] at this
  exact this.symm

theorem canon_eq_of {n k : Nat} {G H : Colored n k} (hg : (canon G).graph = (canon H).graph)
    (hs : sortedColorSeq G = sortedColorSeq H) : canon G = canon H := by
  apply Colored.ext
  · intro i j; rw [hg]
  · intro i
    apply Fin.ext
    rw [cells_canon, cells_canon, hs]

/-! ## The orbit array of the search -/

/-- Entries below `n` on the first `n` positions. -/
abbrev Bounded (n : Nat) (γ : Array Nat) : Prop := ∀ i, i < n → γ[i]! < n

theorem desc_fold {n : Nat} : ∀ (l : List (Array Nat)), (∀ γ ∈ l, Bounded n γ) → ∀ o,
    Orbit.Descending o n → Orbit.Descending (l.foldl (fun o γ => (orbjoin o γ n).1) o) n
  | [], _, _, h => h
  | γ :: l, hb, o, h =>
    desc_fold l (fun δ hδ => hb δ (List.mem_cons_of_mem _ hδ)) _
      (h.orbjoin (hb γ List.mem_cons_self))

theorem ofFn_get {n v : Nat} (hv : v < n) : (Array.ofFn (n := n) fun i => i.val)[v]! = v := by
  rw [getElem!_pos _ v (by simpa using hv)]
  simp

theorem desc_init {n : Nat} : Orbit.Descending (Array.ofFn (n := n) fun i => i.val) n :=
  ⟨by simp, fun v hv => by rw [ofFn_get hv]; exact Nat.le_refl v⟩

theorem flat_init {n : Nat} : Orbit.Flat (Array.ofFn (n := n) fun i => i.val) n :=
  fun v hv => by rw [ofFn_get hv, ofFn_get hv]

theorem count_init {n : Nat} :
    n = (List.range n).countP (fun i => (Array.ofFn (n := n) fun i => i.val)[i]! == i) := by
  rw [List.countP_eq_length.mpr (fun v hv => by rw [ofFn_get (List.mem_range.mp hv)]; simp),
    List.length_range]

/-- While the discovery trace stays within `T`: the orbit array is the
`orbjoin` fold over the emitted generators, `numorbits` counts its roots, and
the emitted generators are bounded. -/
def OrbEmit (n : Nat) (T : List (Array Nat)) (l : Emission.Log) : Prop :=
  List.Subset l.trace.toList T →
    l.orbits = Aut.orbitsOf n l.emitted.toList ∧
    l.numorbits = (List.range n).countP (fun i => l.orbits[i]! == i) ∧
    ∀ γ ∈ l.emitted.toList, Bounded n γ

/-- Each leaf keeps `OrbEmit`. A code-2 automorphism that is not emitted leaves
the orbit count unchanged, so its join leaves the orbit array unchanged
(`orbjoin_eq_of_count`). -/
theorem orbEmit_leaf {n : Nat} {T : List (Array Nat)} (hT : ∀ γ ∈ T, Bounded n γ)
    (leaf : Leaf) (level : Nat) (st : Search n) (h : OrbEmit n T (Emission.log st)) :
    OrbEmit n T (Emission.log (leafExit leaf level st).2) := by
  rw [Emission.leaf_log]
  generalize Emission.log st = l at h ⊢
  generalize st.workperm = γ
  have hjt : List.Subset l.trace.toList (l.join γ n).trace.toList := fun δ hd => by
    simp [Emission.Log.join, hd]
  have hγ : γ ∈ (l.join γ n).trace.toList := by simp [Emission.Log.join]
  have base : List.Subset (l.join γ n).trace.toList T →
      (l.orbits = Aut.orbitsOf n l.emitted.toList ∧
        l.numorbits = (List.range n).countP (fun i => l.orbits[i]! == i) ∧
        ∀ δ ∈ l.emitted.toList, Bounded n δ) ∧
      Bounded n γ ∧ Orbit.Descending l.orbits n ∧ Orbit.Flat l.orbits n := by
    intro hs
    obtain ⟨ho, hc, hb⟩ := h (fun δ hd => hs (hjt hd))
    refine ⟨⟨ho, hc, hb⟩, hT γ (hs hγ), ?_, ?_⟩
    · rw [ho]; exact desc_fold _ hb _ desc_init
    · rw [ho]; exact Orbit.flat_fold _ hb _ desc_init flat_init
  have emitCase : OrbEmit n T ((l.join γ n).emit γ) := by
    intro hs
    obtain ⟨⟨ho, -, hb⟩, hγb, hd, -⟩ := base hs
    refine ⟨?_, ?_, ?_⟩
    · show (orbjoin l.orbits γ n).1 = Aut.orbitsOf n (l.emitted.push γ).toList
      rw [Array.toList_push, Aut.orbitsOf, List.foldl_append, ← Aut.orbitsOf, ← ho]
      rfl
    · exact Orbit.count_orbjoin hd hγb
    · intro δ hδ
      have hδ' : δ ∈ l.emitted.toList ∨ δ = γ := by
        simpa [Emission.Log.emit, Emission.Log.join] using hδ
      rcases hδ' with hδ' | rfl
      · exact hb δ hδ'
      · exact hγb
  cases leaf
  all_goals try first | exact h | exact emitCase
  change OrbEmit n T
    (if (l.join γ n).numorbits == l.numorbits then l.join γ n else (l.join γ n).emit γ)
  split
  · rename_i hc
    intro hs
    obtain ⟨⟨ho, hcnt, hb⟩, hγb, hd, hf⟩ := base hs
    have hc' : (orbjoin l.orbits γ n).2 = l.numorbits := beq_iff_eq.mp hc
    have heq : (orbjoin l.orbits γ n).1 = l.orbits :=
      Orbit.orbjoin_eq_of_count hd hf hγb (hc'.trans hcnt)
    refine ⟨?_, ?_, hb⟩
    · show (orbjoin l.orbits γ n).1 = _
      rw [heq]; exact ho
    · show (orbjoin l.orbits γ n).2 = (List.range n).countP (fun i => (orbjoin l.orbits γ n).1[i]! == i)
      rw [heq]; exact hc'.trans hcnt
  · exact emitCase

theorem orbEmit_runState {n : Nat} (g : Array (VSet n)) (lab0 : Array Nat) (cellEnds : List Nat)
    {T : List (Array Nat)} (hT : ∀ γ ∈ T, Bounded n γ) :
    OrbEmit n T (Emission.log (runState n g lab0 cellEnds).2) := by
  have hinit : OrbEmit n T (Emission.log (initial n lab0 cellEnds)) :=
    fun _ => ⟨rfl, count_init, by simp [Emission.log, initial]⟩
  unfold runState
  split
  · exact hinit
  · rw [node_eq_generic]
    exact Generic.node_sound (Emission.preserve _ _ _ (OrbEmit n T)
      (fun v l s h => orbEmit_leaf hT v l s h)).sound _ _ _ _ _ hinit

/-- The orbit array of the final search state is `Aut.orbits G`. -/
theorem finalState_orbits {n k : Nat} (G : Colored n k) : (finalState G).orbits = Aut.orbits G := by
  have hT : ∀ γ ∈ Aut.trace G, Bounded n γ := fun γ hγ i hi => by
    obtain ⟨p, hp⟩ := Aut.trace_admitted G γ hγ
    rw [← autom?_val_get hp ⟨i, hi⟩]
    exact (p.get _).isLt
  have h := orbEmit_runState (rowsOf G) (initialPartition G).1 (initialPartition G).2 hT
  rw [Aut.orbits, Aut.raw_eq_emitted]
  exact (h (fun _ hγ => hγ)).1

end NautyVerified.Statement
