import HexGraphIso.Nauty.Search.Refine
import HexGraphIso.Nauty.Search.VSet.Card
import HexGraphIso.Nauty.Spec.CellPermLoop

/-!
# `refineLoop`'s fuel is never exhausted

HexGraphIso's `refine` runs `refineLoop` with fuel `4 * n + 8`; nauty's C
loop has no fuel. `refineFuel st` bounds the iterations left from `st`:
while `numcells < n` it is `|active| + (n - numcells)`, otherwise `0`. Every
iteration erases the splitter from `active`, and every insertion into
`active` during a splitting pass comes with a `numcells` increment, except
the one `nontrivialFix` makes, which it pays for by erasing `maxpos`. So
`refineStep` decreases `refineFuel` (`refineFuel_step`), the initial value is
at most `2 * n` (`refineFuel_le`), and the loop is an unbounded one:

- `refineLoop_stop`: when the guard fails, `refineLoop` returns its state;
- `refineLoop_next`: when the guard holds and the fuel `F` exceeds
  `refineFuel st`, then `F = G + 1`, `refineFuel` of the next state is below
  `G`, and `refineLoop F st = refineLoop G (refineStep … st)`.

A C loop invariant "the C state represents `st` and
`refineLoop ctx level (4 * n + 8) st₀ = refineLoop ctx level F st` with
`refineFuel st < F`" is established by `refineFuel_lt_init` and carried by
these two lemmas. No invariant on `lab` or `ptn` is needed.
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty

variable {n : Nat}

/-- The iterations `refineLoop` can still make from `st`. -/
def refineFuel (st : RefineSt n) : Nat :=
  if st.numcells < n then st.active.card + (n - st.numcells) else 0

/-- From `a` to `b`, `numcells` grows and `active` grows by at most as much. -/
def Acc (a b : RefineSt n) : Prop :=
  a.numcells ≤ b.numcells ∧ b.active.card + a.numcells ≤ a.active.card + b.numcells

theorem Acc.refl (a : RefineSt n) : Acc a a := ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem Acc.trans {a b c : RefineSt n} (h₁ : Acc a b) (h₂ : Acc b c) : Acc a c :=
  ⟨Nat.le_trans h₁.1 h₂.1, by have := h₁.2; have := h₂.2; omega⟩

theorem Acc.of_eq {a b : RefineSt n} (ha : b.active = a.active) (hn : b.numcells = a.numcells) :
    Acc a b := ⟨by omega, by rw [ha, hn]; exact Nat.le_refl _⟩

theorem Acc.insert {a b : RefineSt n} {v : Nat} (ha : b.active = a.active.insert v)
    (hn : b.numcells = a.numcells + 1) : Acc a b :=
  ⟨by omega, by rw [ha, hn]; have := VSet.card_insert_le a.active v; omega⟩

/-! ## The trivial splitter -/

theorem trivialSplit_acc (level cell1 cell2 : Nat) (c1 c2 : Int) (st : RefineSt n) :
    Acc st (trivialSplit level cell1 cell2 c1 c2 st) := by
  unfold trivialSplit
  split
  · split
    · split
      · exact Acc.insert rfl rfl
      · exact Acc.insert rfl rfl
    · split
      · exact Acc.insert rfl rfl
      · exact Acc.insert rfl rfl
  · exact Acc.refl _

theorem trivialCell_acc (level : Nat) (gRow : VSet n) (cell1 cell2 : Nat) (st : RefineSt n) :
    Acc st (trivialCell level gRow cell1 cell2 st) := by
  unfold trivialCell
  split
  · exact Acc.refl _
  · exact Acc.trans (Acc.of_eq (b := { st with lab := (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
      (Int.ofNat cell1) (Int.ofNat cell2)).1 }) rfl rfl) (trivialSplit_acc _ _ _ _ _ _)

theorem refineTrivial_go_acc (level : Nat) (gRow : VSet n) :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt n), Acc st (refineTrivial.go level gRow cs st)
  | [], st => by rw [refineTrivial.go]; exact Acc.refl _
  | (c1, c2) :: cs, st => by
    rw [refineTrivial.go]
    exact (trivialCell_acc level gRow c1 c2 st).trans (refineTrivial_go_acc level gRow cs _)

theorem refineTrivial_acc (ctx : Ctx n) (level split1 : Nat) (st : RefineSt n) :
    Acc st (refineTrivial ctx level split1 st) := by
  unfold refineTrivial
  exact refineTrivial_go_acc _ _ _ _

/-! ## The nontrivial splitter -/

/-- The position `nontrivialFix` erases is `cell1` or already active. -/
def Good (cell1 : Nat) (st : RefineSt n) : Prop :=
  st.maxpos = cell1 ∨ st.active.mem st.maxpos = true

theorem windowStep_fields (level cell1 cell2 v c1 c2 : Nat) (maxcell : Int) (st : RefineSt n) :
    (windowStep level cell1 cell2 v c1 c2 maxcell st).numcells =
        (if c1 != cell1 then st.numcells + 1 else st.numcells) ∧
      (windowStep level cell1 cell2 v c1 c2 maxcell st).active =
        (if c1 != cell1 then st.active.insert c1 else st.active) ∧
      (windowStep level cell1 cell2 v c1 c2 maxcell st).maxpos =
        (if Int.ofNat (c2 - c1) > maxcell then c1 else st.maxpos) := by
  unfold windowStep
  by_cases h1 : Int.ofNat (c2 - c1) > maxcell <;> by_cases h2 : (c1 != cell1) = true <;>
    by_cases h3 : (c2 - c1 == 1) = true <;> by_cases h4 : c2 ≤ cell2 <;>
    simp only [h1, h2, h3, h4, ite_true, ite_false, Bool.false_eq_true] <;>
    simp

/-- The window scan, with a credit of one when the current `maxpos` is
neither `cell1` nor active. -/
theorem windowScan_acc (level cell1 cell2 : Nat) (counts : List Nat) (st₀ : RefineSt n) :
    ∀ (vs : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt n),
      Acc st₀ st →
      (0 ≤ maxcell → ¬ Good cell1 st →
        st.active.card + st₀.numcells + 1 ≤ st₀.active.card + st.numcells) →
      (0 ≤ maxcell ∨ ∃ v ∈ vs, 0 < multOf counts v) →
      Acc st₀ (windowScan level cell1 cell2 counts vs c1 maxcell st) ∧
        (¬ Good cell1 (windowScan level cell1 cell2 counts vs c1 maxcell st) →
          (windowScan level cell1 cell2 counts vs c1 maxcell st).active.card + st₀.numcells + 1 ≤
            st₀.active.card + (windowScan level cell1 cell2 counts vs c1 maxcell st).numcells)
  | [], c1, maxcell, st, ha, hg, hex => by
    rw [windowScan]
    rcases hex with h | ⟨_, hv, _⟩
    · exact ⟨ha, hg h⟩
    · simp at hv
  | v :: vs, c1, maxcell, st, ha, hg, hex => by
    rw [windowScan]
    split
    · next hm =>
      apply windowScan_acc level cell1 cell2 counts st₀ vs
      · obtain ⟨f1, f2, -⟩ := windowStep_fields level cell1 cell2 v c1 (c1 + multOf counts v)
          maxcell st
        refine ha.trans ?_
        by_cases hc : (c1 != cell1) = true
        · rw [ite_eq_left hc] at f1 f2; exact Acc.insert f2 f1
        · rw [ite_eq_right hc] at f1 f2; exact Acc.of_eq f2 f1
      · intro _ hng
        obtain ⟨f1, f2, f3⟩ := windowStep_fields level cell1 cell2 v c1 (c1 + multOf counts v)
          maxcell st
        rw [show c1 + multOf counts v - c1 = multOf counts v by omega] at f3
        have hci := VSet.card_insert_le st.active c1
        have h1 := ha.2
        by_cases hmax : Int.ofNat (multOf counts v) > maxcell
        · rw [ite_eq_left hmax] at f3
          by_cases hc : (c1 != cell1) = true
          · rw [ite_eq_left hc] at f1 f2
            have hge : n ≤ c1 := by
              apply Nat.le_of_not_lt; intro hlt
              exact hng (.inr (by rw [f3, f2]; exact VSet.mem_insert_self _ hlt))
            rw [f1, f2, VSet.insert_of_ge _ hge]; omega
          · exact absurd (.inl (by rw [f3]; simpa using hc)) hng
        · rw [ite_eq_right hmax] at f3
          have hng' : ¬ Good cell1 st := by
            rintro (h | h)
            · exact hng (.inl (by rw [f3, h]))
            · apply hng; right; rw [f3, f2]; split
              · exact VSet.mem_insert_mono _ _ h
              · exact h
          have := hg (by omega) hng'
          by_cases hc : (c1 != cell1) = true
          · rw [ite_eq_left hc] at f1 f2; rw [f1, f2]; omega
          · rw [ite_eq_right hc] at f1 f2; rw [f1, f2]; omega
      · left; split <;> simp only [Int.ofNat_eq_natCast] at * <;> omega
    · next hm =>
      refine windowScan_acc level cell1 cell2 counts st₀ vs c1 maxcell st ha hg ?_
      rcases hex with h | ⟨w, hw, hpos⟩
      · exact .inl h
      · rcases List.mem_cons.1 hw with rfl | hw
        · exact absurd hpos hm
        · exact .inr ⟨w, hw, hpos⟩

theorem nontrivialFix_card (cell1 : Nat) (st : RefineSt n) :
    (nontrivialFix cell1 st).numcells = st.numcells ∧
      (nontrivialFix cell1 st).active.card ≤ st.active.card + 1 ∧
      (Good cell1 st → (nontrivialFix cell1 st).active.card ≤ st.active.card) := by
  unfold nontrivialFix
  split
  · next hnm =>
    refine ⟨rfl, Nat.le_trans (VSet.card_erase_le _ _) (VSet.card_insert_le _ _), ?_⟩
    rintro (h | h)
    · show ((st.active.insert cell1).erase st.maxpos).card ≤ _
      rw [h]
      by_cases hlt : cell1 < n
      · have := VSet.card_erase_of_mem (VSet.mem_insert_self st.active hlt)
        have := VSet.card_insert_le st.active cell1
        omega
      · rw [VSet.insert_of_ge _ (by omega)]; exact VSet.card_erase_le _ _
    · show ((st.active.insert cell1).erase st.maxpos).card ≤ _
      have := VSet.card_erase_of_mem (VSet.mem_insert_mono st.active cell1 h)
      have := VSet.card_insert_le st.active cell1
      omega
  · exact ⟨rfl, by omega, fun _ => Nat.le_refl _⟩

theorem foldl_min_le : ∀ (l : List Nat) (a : Nat), l.foldl Nat.min a ≤ a
  | [], _ => Nat.le_refl _
  | _ :: l, _ => Nat.le_trans (foldl_min_le l _) (Nat.min_le_left _ _)

theorem le_foldl_max : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl Nat.max a
  | [], _ => Nat.le_refl _
  | _ :: l, _ => Nat.le_trans (Nat.le_max_left _ _) (le_foldl_max l _)

/-- The first count lies in the scanned window and occurs. -/
theorem head_mem_countValues {counts : List Nat} (h : counts ≠ []) :
    ∃ v ∈ countValues counts, 0 < multOf counts v := by
  obtain ⟨c, cs, rfl⟩ : ∃ c cs, counts = c :: cs := by
    cases counts with
    | nil => exact absurd rfl h
    | cons c cs => exact ⟨c, cs, rfl⟩
  refine ⟨c, ?_, ?_⟩
  · have h1 := foldl_min_le (c :: cs) c
    have h2 := le_foldl_max (c :: cs) c
    simp only [countValues, List.headD_cons, List.mem_map, List.mem_range]
    exact ⟨c - (c :: cs).foldl Nat.min c, by omega, by omega⟩
  · simp [multOf]

theorem nontrivialCell_acc (ctx : Ctx n) (level : Nat) (workset : VSet n) (cell1 cell2 : Nat)
    (st : RefineSt n) : Acc st (nontrivialCell ctx level workset cell1 cell2 st) := by
  unfold nontrivialCell
  split
  · exact Acc.refl _
  split
  · exact Acc.of_eq rfl rfl
  · next hne =>
    have hcs : countsOf ctx st.lab workset cell1 cell2 ≠ [] := by
      intro h; rw [h] at hne; exact hne rfl
    obtain ⟨hA, hG⟩ := windowScan_acc level cell1 cell2 (countsOf ctx st.lab workset cell1 cell2)
      st (countValues (countsOf ctx st.lab workset cell1 cell2)) cell1 (-1) st (Acc.refl _)
      (fun h => absurd h (by decide)) (.inr (head_mem_countValues hcs))
    generalize windowScan level cell1 cell2 (countsOf ctx st.lab workset cell1 cell2)
      (countValues (countsOf ctx st.lab workset cell1 cell2)) cell1 (-1) st = r at hA hG ⊢
    obtain ⟨f1, f2, f3⟩ := nontrivialFix_card cell1 { r with lab := (writeSegment r.lab cell1
      (segmentOf r.lab cell1 (countsOf ctx st.lab workset cell1 cell2)
        (countValues (countsOf ctx st.lab workset cell1 cell2)))) }
    refine ⟨by rw [f1]; exact hA.1, ?_⟩
    rw [f1]
    have hA2 := hA.2
    dsimp only at f1 f2 f3 hA2 ⊢
    by_cases hg : Good cell1 r
    · have := f3 hg; omega
    · have := hG hg; omega

theorem refineNontrivial_go_acc (ctx : Ctx n) (level : Nat) (workset : VSet n) :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt n),
      Acc st (refineNontrivial.go ctx level workset cs st)
  | [], st => by rw [refineNontrivial.go]; exact Acc.refl _
  | (c1, c2) :: cs, st => by
    rw [refineNontrivial.go]
    exact (nontrivialCell_acc ctx level workset c1 c2 st).trans
      (refineNontrivial_go_acc ctx level workset cs _)

theorem refineNontrivial_acc (ctx : Ctx n) (level split1 split2 : Nat) (st : RefineSt n) :
    Acc st (refineNontrivial ctx level split1 split2 st) := by
  unfold refineNontrivial
  exact Acc.trans (Acc.of_eq (b := { st with longcode := mash st.longcode (split2 - split1 + 1) })
    rfl rfl) (refineNontrivial_go_acc _ _ _ _ _)

/-! ## The loop -/

/-- One iteration erases the (active) splitter and then only adds as many
active positions as it adds cells. -/
theorem refineStep_acc (ctx : Ctx n) (level split1 : Nat) (st : RefineSt n)
    (hs : st.active.mem split1 = true) :
    st.numcells ≤ (refineStep ctx level split1 st).numcells ∧
      (refineStep ctx level split1 st).active.card + st.numcells + 1 ≤
        st.active.card + (refineStep ctx level split1 st).numcells := by
  have he := VSet.card_erase_of_mem hs
  have key : ∀ st' r : RefineSt n, st'.active = st.active.erase split1 →
      st'.numcells = st.numcells → Acc st' r →
      st.numcells ≤ r.numcells ∧ r.active.card + st.numcells + 1 ≤ st.active.card + r.numcells := by
    intro st' r ha hn ⟨h1, h2⟩
    rw [ha, hn] at h2; rw [hn] at h1
    exact ⟨h1, by omega⟩
  unfold refineStep
  dsimp only
  split
  · refine key _ _ ?_ ?_ (refineTrivial_acc _ _ _ _) <;> rfl
  · refine key _ _ ?_ ?_ (refineNontrivial_acc _ _ _ _ _) <;> rfl

/-- `refineStep` decreases `refineFuel` when the loop guard holds. -/
theorem refineFuel_step (ctx : Ctx n) (level : Nat) {st : RefineSt n} {split1 : Nat}
    (hn : st.numcells < n) (hp : pickSplit st.active st.hint = some split1) :
    refineFuel (refineStep ctx level split1 st) < refineFuel st := by
  have h := refineStep_acc ctx level split1 st (pickSplit_mem hp)
  unfold refineFuel
  rw [ite_eq_left hn]
  split <;> omega

/-- When the guard fails, `refineLoop` returns its state. -/
theorem refineLoop_stop (ctx : Ctx n) (level : Nat) (st : RefineSt n)
    (h : ¬ st.numcells < n ∨ pickSplit st.active st.hint = none) :
    ∀ F, refineLoop ctx level F st = st
  | 0 => rfl
  | F + 1 => by
    rw [refineLoop]
    rcases h with h | h
    · rw [ite_eq_right h]
    · split
      · rw [h]
      · rfl

/-- When the guard holds and the fuel exceeds `refineFuel`, one iteration
consumes one unit and the remaining fuel still exceeds `refineFuel`. -/
theorem refineLoop_next (ctx : Ctx n) (level : Nat) {st : RefineSt n} {split1 F : Nat}
    (hF : refineFuel st < F) (hn : st.numcells < n)
    (hp : pickSplit st.active st.hint = some split1) :
    ∃ G, F = G + 1 ∧ refineFuel (refineStep ctx level split1 st) < G ∧
      refineLoop ctx level F st = refineLoop ctx level G (refineStep ctx level split1 st) := by
  have hd := refineFuel_step ctx level hn hp
  obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
  refine ⟨G, rfl, by omega, ?_⟩
  rw [refineLoop, ite_eq_left hn]
  split
  · next s h => rw [hp] at h; cases h; rfl
  · next h => rw [hp] at h; cases h

theorem refineFuel_le (st : RefineSt n) : refineFuel st ≤ 2 * n := by
  unfold refineFuel
  have := VSet.card_le st.active
  split <;> omega

/-- `refine`'s fuel exceeds `refineFuel` of every state. -/
theorem refineFuel_lt_init (st : RefineSt n) : refineFuel st < 4 * n + 8 := by
  have := refineFuel_le st; omega

/-- With fuel above `refineFuel`, more fuel changes nothing. -/
theorem refineLoop_fuel (ctx : Ctx n) (level : Nat) :
    ∀ (F : Nat) (st : RefineSt n), refineFuel st < F →
      ∀ F', F ≤ F' → refineLoop ctx level F' st = refineLoop ctx level F st := by
  intro F
  induction F with
  | zero => intro _ h; omega
  | succ F ih =>
    intro st hF F' hF'
    by_cases hg : st.numcells < n ∧ ∃ s, pickSplit st.active st.hint = some s
    · obtain ⟨hn, s, hp⟩ := hg
      obtain ⟨G, hG, hlt, heq⟩ := refineLoop_next ctx level hF hn hp
      obtain ⟨G', hG', hlt', heq'⟩ := refineLoop_next ctx level (F := F') (by omega) hn hp
      rw [heq, heq', ih _ (by omega) G' (by omega)]
      rw [show G = F by omega]
    · have h : ¬ st.numcells < n ∨ pickSplit st.active st.hint = none := by
        rcases Decidable.em (st.numcells < n) with hn | hn
        · right
          rcases hp : pickSplit st.active st.hint with _ | s
          · rfl
          · exact absurd ⟨hn, s, hp⟩ hg
        · exact .inl hn
      rw [refineLoop_stop ctx level st h, refineLoop_stop ctx level st h]

end NautyVerified.Spec
