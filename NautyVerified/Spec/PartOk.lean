import NautyVerified.Spec.NodeOk

/-!
# The partition facts the C reads off HexGraphIso's state

`PartOk G level numcells st`: the state `st` of the run with
`inf = nautyInfinity`, with `nautyInfinity` renamed back to `n + 2` (`back`),
satisfies HexGraphIso's partition invariant `SearchOk`, and no `ptn` entry is
`n + 2`. `PartOk.facts` gives what nauty.c's callees need: `lab` is a
permutation, `ptn` entries are at most `level` or `nautyInfinity`, the last is
at most 1, and `numcells` is the number of cells, between `level` and `n`.

`NodeOk`, `PartOk` survive (`PartOk.of_nodeOk`, `PartOk.visit`,
`PartOk.recordFirst`, `PartOk.compareCodes`, `PartOk.chooseTarget`,
`PartOk.classify`, `PartOk.leafExit`, `PartOk.cheapCheck`) the steps of a node
up to its sweep, whose own states come from the sweep invariants.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {n k : Nat}

/-- `nautyInfinity` renamed back to HexGraphIso's `n + 2`. -/
def back (st : Search n) : Search n := { st with ptn := st.ptn.map (phi nautyInfinity (n + 2)) }

/-- The partition facts of a state of the `nautyInfinity` run. -/
def PartOk (G : Colored n k) (level numcells : Nat) (st : Search n) : Prop :=
  SearchOk G level numcells (back st) ∧ ∀ q : Nat, st.ptn[q]! ≠ n + 2

/-- `PartOk` depends only on `lab`, `ptn` and `canonlab` (which may become `lab`). -/
theorem PartOk.frame {G : Colored n k} {level numcells : Nat} {st out : Search n}
    (h : PartOk G level numcells st) (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (hc : out.canonlab = st.canonlab ∨ out.canonlab = st.lab) : PartOk G level numcells out :=
  ⟨frame_ok h.1 (by simp [back, hl]) (by simp [back, hp]) (by simpa [back] using hc),
    by rw [hp]; exact h.2⟩

/-- Renaming `a` to `b` and back is the identity on arrays without `b`. -/
theorem map_phi_back {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) (p : Array Nat)
    (hp : ∀ q : Nat, p[q]! ≠ b) : (p.map (phi a b)).map (phi b a) = p := by
  apply Array.ext (by simp)
  intro i h1 h2
  have hi : i < p.size := by simpa using h2
  have e := getElem!_map_phi (b := a) hb (p.map (phi a b)) i
  rw [getElem!_map_phi (b := b) ha p i] at e
  rw [getElem!_pos _ i h1, getElem!_pos p i hi] at e
  rw [e]
  have hq := hp i
  rw [getElem!_pos p i hi] at hq
  unfold phi
  by_cases hv : p[i] = a
  · simp [hv]
  · simp [hq, hv]

/-- An `(n + 2)`-run state satisfying `SearchOk`, renamed, satisfies `PartOk`. -/
theorem PartOk.of_tw {G : Colored n k} {level numcells : Nat} {X : Search n}
    (hn : n + 2 < nautyInfinity) (hX : SearchOk G level numcells X) (t : Array Int) :
    PartOk G level numcells (tw (phi (n + 2) nautyInfinity) t X) := by
  have hln := level_le_of_ok hX
  have hno : ∀ q : Nat, X.ptn[q]! ≠ nautyInfinity := by
    intro q
    rcases Nat.lt_or_ge q n with hq | hq
    · rcases hX.vals q hq with h | h <;> omega
    · rw [getElem!_neg X.ptn q (by rw [hX.ptnSize]; omega)]; decide
  refine ⟨frame_ok hX rfl ?_ (.inl rfl), fun q => ?_⟩
  · show (X.ptn.map (phi (n + 2) nautyInfinity)).map (phi nautyInfinity (n + 2)) = X.ptn
    exact map_phi_back (by omega) (by decide) X.ptn hno
  · show (X.ptn.map (phi (n + 2) nautyInfinity))[q]! ≠ n + 2
    rw [getElem!_map_phi (by omega)]
    unfold phi
    split
    · omega
    · assumption

/-- A `PartOk` state is the renamed image of its `back`. -/
theorem PartOk.eq_tw {G : Colored n k} {level numcells : Nat} {st : Search n}
    (hn : n + 2 < nautyInfinity) (h : PartOk G level numcells st) :
    st = tw (phi (n + 2) nautyInfinity) st.firsttc (back st) := by
  have e : (st.ptn.map (phi nautyInfinity (n + 2))).map (phi (n + 2) nautyInfinity) = st.ptn :=
    map_phi_back (by decide) (by omega) st.ptn h.2
  show st = tw (phi (n + 2) nautyInfinity) st.firsttc (back st)
  unfold tw back
  rw [e]

/-- What nauty.c's callees need of the partition. -/
structure PartFacts (n level numcells : Nat) (st : Search n) : Prop where
  labSize : st.lab.size = n
  labSmall : ∀ i < n, st.lab[i]! < n
  labSurj : ∀ v < n, ∃ i < n, st.lab[i]! = v
  ptnSize : st.ptn.size = n
  ptnVals : ∀ i < n, st.ptn[i]! ≤ level ∨ st.ptn[i]! = nautyInfinity
  ptnLast : st.ptn[n - 1]! ≤ 1
  count : numcells = bcount st.ptn level n
  levelLe : level ≤ numcells
  numcellsLe : numcells ≤ n

theorem PartOk.facts {G : Colored n k} {level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : PartOk G level numcells st) :
    PartFacts n level numcells st := by
  obtain ⟨hok, hne⟩ := h
  have hln := level_le_of_ok hok
  have hsz : st.ptn.size = n := by have := hok.ptnSize; simpa [back] using this
  have hback : ∀ i : Nat, (back st).ptn[i]! = phi nautyInfinity (n + 2) st.ptn[i]! := fun i =>
    getElem!_map_phi (by decide) st.ptn i
  have hsame : ∀ i : Nat, (st.ptn[i]! ≤ level ↔ (back st).ptn[i]! ≤ level) := fun i =>
    (sameAt_map (a := nautyInfinity) (b := n + 2) (by omega) (by omega) st.ptn).le i
  have hperm := isPerm_of_cellsReach hok.labSize hn0 hok.reach
  have hcount : bcount (back st).ptn level n = bcount st.ptn level n := by
    unfold bcount
    congr 1
    funext q
    exact decide_eq_decide.2 (hsame q).symm
  refine ⟨hok.labSize, fun i hi => cellsReach_lt hok.reach i hi, fun v hv => ?_, hsz, fun i hi => ?_,
    ?_, by rw [hok.count, hcount], ?_, ?_⟩
  · have hm : v ∈ (back st).lab.toList := hperm.mem_iff.2 (List.mem_range.2 hv)
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
    have hi' : i < n := by simpa [hok.labSize] using hi
    refine ⟨i, hi', ?_⟩
    have hls : st.lab.size = n := hok.labSize
    rw [getElem!_pos _ i (by rw [hls]; exact hi')]
    exact he
  · rcases hok.vals i hi with h1 | h1
    · rw [hback] at h1
      unfold phi at h1
      split at h1
      · right; assumption
      · left; exact h1
    · rw [hback] at h1
      unfold phi at h1
      split at h1
      · right; assumption
      · exact absurd h1 (hne i)
  · have hinit : (initPtn n (n + 2) (initialPartition G).2)[n - 1]! ≤ 1 := by
      have := (initial_nodeOk G hn0).ptnEnd
      rw [(initial_nodeOk G hn0).ptnSize] at this
      simpa [initial] using this
    have h1 := hok.init1 (n - 1) hinit
    rw [hback] at h1
    unfold phi at h1
    split at h1
    · omega
    · exact h1
  · rw [hok.count]; exact hok.bc
  · rw [hok.count]; exact bcount_le _ _ _

/-- A node call satisfying `NodeOk` satisfies `PartOk`. -/
theorem PartOk.of_nodeOk {G : Colored n k} {first : Bool} {level numcells : Nat} {st : Search n}
    (hn : n + 2 < nautyInfinity) (h : NodeOk G first level numcells st) :
    PartOk G level numcells st := by
  obtain ⟨t, st₂, rfl, -, hok, -⟩ := h
  exact PartOk.of_tw hn hok t

/-- Refinement keeps `PartOk`, with the new cell count. -/
theorem PartOk.visit {G : Colored n k} {level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (hlevel : 1 ≤ level) (h : PartOk G level numcells st)
    (ctx : Ctx n) :
    PartOk G level (Nauty.visit ctx level numcells st).1 (Nauty.visit ctx level numcells st).2.2 := by
  have hln := level_le_of_ok h.1
  rw [h.eq_tw hn, visit_tw _ ctx level numcells (back st) (by omega) (by omega)]
  have hv := (reachPolicy G ctx 100 hn0).visit level numcells (back st) hlevel h.1
  dsimp only [policy, Generic.Policy.visit] at hv
  exact PartOk.of_tw hn hv.1 _

theorem PartOk.recordFirst {G : Colored n k} {level numcells : Nat} {st : Search n}
    (h : PartOk G level numcells st) (code : Nat) :
    PartOk G level numcells (Nauty.recordFirst level code st) :=
  h.frame rfl rfl (.inl rfl)

theorem PartOk.compareCodes {G : Colored n k} {level numcells : Nat} {st : Search n}
    (h : PartOk G level numcells st) (code : Nat) :
    PartOk G level numcells (Nauty.compareCodes level code st) := by
  obtain ⟨hl, hp, -, hc⟩ := compareCodes_frame level code st
  exact h.frame hl hp (.inl hc)

theorem PartOk.chooseTarget {G : Colored n k} {level numcells : Nat} {st : Search n}
    (h : PartOk G level numcells st) (first : Bool) (ctx : Ctx n) (tcLevel : Nat) :
    PartOk G level numcells (Nauty.chooseTarget first ctx tcLevel level numcells st).2.2.2 := by
  obtain ⟨hl, hp, -, hc⟩ := chooseTarget_frame first ctx tcLevel level numcells st
  exact h.frame hl hp (.inl hc)

theorem PartOk.classify {G : Colored n k} {level numcells : Nat} {st : Search n}
    (h : PartOk G level numcells st) (ctx : Ctx n) :
    PartOk G level numcells (Nauty.classify ctx level numcells st).2 := by
  obtain ⟨hl, hp, -, hc⟩ := classify_frame ctx level numcells st
  exact h.frame hl hp (.inl hc)

theorem PartOk.leafExit {G : Colored n k} {level numcells : Nat} {st : Search n}
    (h : PartOk G level numcells st) (leaf : Leaf) :
    PartOk G level numcells (Nauty.leafExit leaf level st).2 := by
  obtain ⟨hl, hp, -, hc⟩ := leafExit_frame leaf level st
  exact h.frame hl hp hc

theorem PartOk.cheapCheck {G : Colored n k} {level numcells : Nat} {st : Search n}
    (h : PartOk G level numcells st) (first : Bool) :
    PartOk G level numcells (Nauty.cheapCheck first level st) := by
  unfold Nauty.cheapCheck; split
  · exact h.frame rfl rfl (.inl rfl)
  · exact h

end NautyVerified.Spec.SearchInf
