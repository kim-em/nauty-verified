import NautyVerified.Statement.Harness

/-!
# Facts behind the corollaries of the end-to-end theorem

* `rowWords_inj`, `flatMap_inj`: the setwords the harness writes for the
  canonical graph determine its rows;
* `canong_toList`: the search's canonical rows are the rows of HexGraphIso's
  canonical form `canon G`;
* `finalState_orbits`: the orbit array of the final search state is
  `Aut.orbits G`, the `orbjoin` fold over the recorded generators that
  HexGraphIso's orbit theorem is stated for. The search changes the orbit
  array only when it records a generator, and then joins exactly that
  generator.
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

/-- The orbit array is the `orbjoin` fold over the recorded generators. -/
def OrbFold {n : Nat} (st : Search n) : Prop :=
  st.orbits = Aut.orbitsOf n st.genTrace.toList

theorem OrbFold.congr {n : Nat} {st out : Search n} (h : OrbFold st)
    (ho : out.orbits = st.orbits) (ht : out.genTrace = st.genTrace) : OrbFold out := by
  unfold OrbFold; rw [ho, ht]; exact h

/-- A step that leaves the orbit array and the generator trace alone. -/
def Keeps {n : Nat} (f : Search n → Search n) : Prop :=
  ∀ st, (f st).orbits = st.orbits ∧ (f st).genTrace = st.genTrace

theorem Keeps.fold {n : Nat} {f : Search n → Search n} (h : Keeps f) {st : Search n}
    (hs : OrbFold st) : OrbFold (f st) :=
  hs.congr (h st).1 (h st).2

theorem keeps_visit {n : Nat} (ctx : Ctx n) (level numcells : Nat) :
    Keeps fun st => (visit ctx level numcells st).2.2 := fun _ => ⟨rfl, rfl⟩

theorem keeps_recordFirst {n : Nat} (level code : Nat) :
    Keeps (n := n) (recordFirst level code) := fun _ => ⟨rfl, rfl⟩

theorem keeps_compareCodes {n : Nat} (level code : Nat) :
    Keeps (n := n) (compareCodes level code) := by
  intro st
  unfold compareCodes
  constructor <;> simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.genTrace,
    apply_ite SearchState.orbits, ite_self]

theorem keeps_chooseTarget {n : Nat} (first : Bool) (ctx : Ctx n) (tcLevel level numcells : Nat) :
    Keeps fun st => (chooseTarget first ctx tcLevel level numcells st).2.2.2 := by
  intro st
  unfold chooseTarget
  constructor <;> simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite SearchState.genTrace, apply_ite SearchState.orbits, ite_self] <;> split <;> rfl

theorem keeps_firstterminal {n : Nat} (level : Nat) :
    Keeps (n := n) (firstterminal level) := fun _ => ⟨rfl, rfl⟩

theorem keeps_cheapCheck {n : Nat} (first : Bool) (level : Nat) :
    Keeps (n := n) (cheapCheck first level) := by
  intro st; unfold cheapCheck; split <;> exact ⟨rfl, rfl⟩

theorem keeps_child {n : Nat} (first : Bool) (level tc tv : Nat) :
    Keeps (n := n) (child first level tc tv) := by
  intro st; unfold child; cases first <;> exact ⟨rfl, rfl⟩

theorem keeps_afterChildFirst {n : Nat} (level tv1 : Nat) :
    Keeps (n := n) (afterChildFirst level tv1) := fun _ => ⟨rfl, rfl⟩

theorem keeps_afterSweep {n : Nat} (first : Bool) (level size index : Nat) :
    Keeps (n := n) (afterSweep first level size index) := by
  intro st; unfold afterSweep; split <;> exact ⟨rfl, rfl⟩

theorem keeps_recover {n : Nat} (inf level : Nat) :
    Keeps (n := n) (Nauty.recover inf level) := by
  intro st
  unfold Nauty.recover recoverLevels
  constructor <;> simp only [Id.run_pure, apply_ite Id.run,
    apply_ite SearchState.genTrace, apply_ite SearchState.orbits, ite_self] <;> rfl

theorem fold_classify {n : Nat} (ctx : Ctx n) (level numcells : Nat) {st : Search n}
    (h : OrbFold st) : OrbFold (classify ctx level numcells st).2 :=
  h.congr (classify_orbits ctx level numcells st) (classify_trace ctx level numcells st)

theorem fold_leafExit {n : Nat} (leaf : Leaf) (level : Nat) {st : Search n}
    (h : OrbFold st) : OrbFold (leafExit leaf level st).2 := by
  unfold OrbFold at h ⊢
  rw [leafExit_orbits, leafExit_trace]
  cases leaf
  all_goals first
    | exact h
    | rw [Array.toList_push, Aut.orbitsOf, List.foldl_append, ← Aut.orbitsOf, ← h]; rfl

/-- The fold invariant as a contract on every node and sweep call. -/
def foldContract (n : Nat) : Generic.Contract (Search n) n where
  nodePre _ _ _ _ st := OrbFold st
  nodePost _ _ _ _ _ result := OrbFold result.2
  sweepPre _ _ _ _ _ _ _ _ _ _ st := OrbFold st
  sweepPost _ _ _ _ _ _ _ _ _ _ _ result := OrbFold result.2.2

theorem fold_sound {n : Nat} (ctx : Ctx n) (inf tcLevel : Nat) :
    Generic.SoundPolicy ctx inf tcLevel (foldContract n) where
  node_zero := fun _ _ _ _ hin => hin
  node_step := by
    intro fuel next hnext first level numcells st hin
    change OrbFold st at hin
    change OrbFold (Generic.nodeStep ctx tcLevel next first level numcells st).2
    unfold Generic.nodeStep
    have hv : OrbFold (Generic.Policy.visit (n := n) ctx level numcells st).2.2 :=
      (keeps_visit ctx level numcells).fold hin
    generalize Generic.Policy.visit (n := n) ctx level numcells st = r at hv ⊢
    obtain ⟨nc, code, refined⟩ := r
    cases first with
    | true =>
      simp only [ite_true]
      have hc : OrbFold (Generic.Policy.recordFirst (n := n) level code refined) :=
        (keeps_recordFirst level code).fold hv
      generalize Generic.Policy.recordFirst (n := n) level code refined = compared at hc ⊢
      have ht : OrbFold (Generic.Policy.chooseTarget (n := n) true ctx tcLevel level nc compared).2.2.2 :=
        (keeps_chooseTarget true ctx tcLevel level nc).fold hc
      generalize Generic.Policy.chooseTarget (n := n) true ctx tcLevel level nc compared = t at ht ⊢
      obtain ⟨tc, cell, size, targeted⟩ := t
      dsimp only
      split
      · exact (keeps_firstterminal level).fold ht
      · have hn := hnext true level nc tc.toNat ((cell.nextElem none).getD 0)
          (cell.nextElem none) cell 0 (Generic.Policy.cheapCheck (n := n) true level targeted)
          ((keeps_cheapCheck true level).fold ht)
        change OrbFold (next true level nc tc.toNat ((cell.nextElem none).getD 0)
          (cell.nextElem none) cell 0 (Generic.Policy.cheapCheck (n := n) true level targeted)).2.2 at hn
        generalize next true level nc tc.toNat ((cell.nextElem none).getD 0)
          (cell.nextElem none) cell 0 (Generic.Policy.cheapCheck (n := n) true level targeted) = s at hn ⊢
        obtain ⟨exit, index, result⟩ := s
        cases exit <;> first | exact hn | exact (keeps_afterSweep true level size index).fold hn
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hc : OrbFold (Generic.Policy.compareCodes (n := n) level code refined) :=
        (keeps_compareCodes level code).fold hv
      generalize Generic.Policy.compareCodes (n := n) level code refined = compared at hc ⊢
      have ht : OrbFold (Generic.Policy.chooseTarget (n := n) false ctx tcLevel level nc compared).2.2.2 :=
        (keeps_chooseTarget false ctx tcLevel level nc).fold hc
      generalize Generic.Policy.chooseTarget (n := n) false ctx tcLevel level nc compared = t at ht ⊢
      obtain ⟨tc, cell, size, targeted⟩ := t
      have hcl : OrbFold (Generic.Policy.classify (n := n) ctx level nc targeted).2 :=
        fold_classify ctx level nc ht
      generalize Generic.Policy.classify (n := n) ctx level nc targeted = c at hcl ⊢
      obtain ⟨leaf, classified⟩ := c
      have hle : OrbFold (Generic.Policy.leafExit (n := n) leaf level classified).2 :=
        fold_leafExit leaf level hcl
      generalize Generic.Policy.leafExit (n := n) leaf level classified = result at hle ⊢
      obtain ⟨exit, out⟩ := result
      dsimp only
      cases exit with
      | fuel => exact hle
      | unwind => exact hle
      | done =>
        dsimp only
        have hn := hnext false level nc tc.toNat ((cell.nextElem none).getD 0)
          (cell.nextElem none) cell 0 (Generic.Policy.cheapCheck (n := n) false level out)
          ((keeps_cheapCheck false level).fold hle)
        change OrbFold (next false level nc tc.toNat ((cell.nextElem none).getD 0)
          (cell.nextElem none) cell 0 (Generic.Policy.cheapCheck (n := n) false level out)).2.2 at hn
        generalize next false level nc tc.toNat ((cell.nextElem none).getD 0)
          (cell.nextElem none) cell 0 (Generic.Policy.cheapCheck (n := n) false level out) = s at hn ⊢
        obtain ⟨exit, index, result⟩ := s
        cases exit <;> first | exact hn | exact (keeps_afterSweep false level size index).fold hn
  sweep_none := fun _ _ _ _ _ _ _ _ _ _ hin => hin
  sweep_zero := fun _ _ _ _ _ _ _ _ _ _ hin => hin
  sweep_step := by
    intro fuel cfuel descend next hdescend hnext first level numcells tc tv1 tv cell index st hin
    change OrbFold st at hin
    change OrbFold (Generic.sweepStep inf descend next first level numcells tc tv1 tv cell
      index st).2.2
    have hcontinue : ∀ cell index out, OrbFold out →
        OrbFold (Generic.resume inf next first level numcells tc tv1 tv cell index out).2.2 := by
      intro cell index out hout
      have hr : OrbFold (Generic.Policy.recover (n := n) inf level out) :=
        (keeps_recover inf level).fold hout
      unfold Generic.resume
      simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
      split <;> exact hnext _ _ _ _ _ _ _ _ _ hr
    unfold Generic.sweepStep Generic.advance
    dsimp only
    split
    · have hc : OrbFold (Generic.Policy.child (n := n) first level tc tv st) :=
        (keeps_child first level tc tv).fold hin
      have hd := hdescend (first && tv == tv1) (level + 1) (numcells + 1) _ hc
      change OrbFold (descend (first && tv == tv1) (level + 1) (numcells + 1)
        (Generic.Policy.child (n := n) first level tc tv st)).2 at hd
      generalize descend (first && tv == tv1) (level + 1) (numcells + 1)
        (Generic.Policy.child (n := n) first level tc tv st) = result at hd ⊢
      obtain ⟨exit, out⟩ := result
      have hd' : OrbFold out := hd
      have hl1 : OrbFold (Generic.Policy.leaveChild (n := n) tv
          (Generic.Policy.afterChildFirst (n := n) level tv1 out)) :=
        ((keeps_afterChildFirst level tv1).fold hd').congr rfl rfl
      have hl2 : OrbFold (Generic.Policy.leaveChild (n := n) tv out) := hd'.congr rfl rfl
      dsimp only
      split <;> cases exit <;> dsimp only <;> (try split) <;> (try split) <;>
        first | exact hl1 | exact hl2 | exact hcontinue _ _ _ hl1 | exact hcontinue _ _ _ hl2
    · exact hnext _ _ _ _ _ _ _ _ _ hin

theorem fold_runState {n : Nat} (g : Array (VSet n)) (lab0 : Array Nat) (cellEnds : List Nat) :
    OrbFold (runState n g lab0 cellEnds).2 := by
  have hinit : OrbFold (initial n lab0 cellEnds) := rfl
  unfold runState
  split
  · exact hinit
  · rw [node_eq_generic]
    exact Generic.node_sound (fold_sound _ _ _) _ _ _ _ _ hinit

/-- The orbit array of the final search state is `Aut.orbits G`. -/
theorem finalState_orbits {n k : Nat} (G : Colored n k) : (finalState G).orbits = Aut.orbits G := by
  have h := fold_runState (rowsOf G) (initialPartition G).1 (initialPartition G).2
  rw [Aut.orbits, Aut.raw_eq_trace]
  exact h

end NautyVerified.Statement
