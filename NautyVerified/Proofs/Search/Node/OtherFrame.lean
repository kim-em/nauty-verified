import NautyVerified.Proofs.Search.Node.TcFrame
import NautyVerified.Proofs.Search.Step
import NautyVerified.Proofs.Search.Node.OkFirst

/-!
# A node's frame, across its own steps and its children

`NSet m S chain level`: the blocks `NodeFrame m _ S chain level` lets a node
change. A node at `level` runs steps that change blocks of `S`, blocks new
since its entry, work blocks and its own target cell, and calls children at
`level + 1`; every such change is inside `NSet m₀ S chain₀ level` for the
entry memory `m₀` and list `chain₀`:

- `nset_step`: a step's blocks, given the growth and `WorkMono` since entry;
- `nset_child`: a child's `NSet`, when the list at the call keeps the first
  `level - 1` nodes of `chain₀` and its other nodes are `chain₀`'s or new;
- `nset_own`: the node's own target cell, entry `level - 1` of the list.

`chain_inj`: in a list whose blocks are pairwise distinct, an entry's node or
cell determines its index.

`NSetG`, `nset_stepG`, `nset_childG`, `nset_ownG`: the same for any dispatch
representation (`NodeFrameG`). `sweepOkOff_breakArgs` is about HexGraphIso's
dense search and stays dense.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open NautyVerified NautyVerified.Logic NautyVerified.Program

/-- The blocks a node at `level` may change. -/
abbrev NSet (m : mem) (S : SLoc) (chain : List (block × block)) (level : Nat) (z : block) : Prop :=
  S.Chg z ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨ z = Block.tcnode0 ∨
    (∃ i p, chain[i]? = some p ∧ level ≤ i + 2 ∧ z = p.1) ∨
    (∃ i p, chain[i]? = some p ∧ level ≤ i + 1 ∧ z = p.2)

theorem NodeFrame.nset {m m' : mem} {S : SLoc} {chain : List (block × block)} {level : Nat}
    (h : NodeFrame m m' S chain level) : Unch m m' (NSet m S chain level) := h.1

theorem NodeFrame.grow {m m' : mem} {S : SLoc} {chain : List (block × block)} {level : Nat}
    (h : NodeFrame m m' S chain level) : ∀ z, Mem.valid_block m z → Mem.valid_block m' z := h.2

theorem NodeFrame.mk' {m m' : mem} {S : SLoc} {chain : List (block × block)} {level : Nat}
    (hu : Unch m m' (NSet m S chain level)) (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) :
    NodeFrame m m' S chain level := ⟨hu, hg⟩

/-- Two entries of a list of pairwise distinct blocks sharing a node or a cell are the same entry. -/
theorem chain_inj : ∀ {chain : List (block × block)},
    (chain.flatMap fun p => [p.1, p.2]).Pairwise (· ≠ ·) →
    ∀ {i j : Nat} {p q : block × block}, chain[i]? = some p → chain[j]? = some q →
      (p.1 = q.1 ∨ p.2 = q.2) → i = j
  | [], _, _, _, _, _, hp, _, _ => by simp at hp
  | a :: rest, hpw, i, j, p, q, hp, hq, he => by
    rw [List.flatMap_cons, List.pairwise_append] at hpw
    obtain ⟨hpa, hpr, hcross⟩ := hpw
    have ha : a.1 ≠ a.2 := by simpa using hpa
    have hnot : ∀ (k : Nat) (r : block × block), rest[k]? = some r → r.1 ≠ a.1 ∧ r.2 ≠ a.2 := by
      intro k r hr
      have hm : r ∈ rest := List.mem_of_getElem? hr
      refine ⟨fun e => hcross a.1 (by simp) r.1 (List.mem_flatMap.2 ⟨r, hm, by simp⟩) e.symm,
        fun e => hcross a.2 (by simp) r.2 (List.mem_flatMap.2 ⟨r, hm, by simp⟩) e.symm⟩
    rcases i with _ | i <;> rcases j with _ | j
    · rfl
    · simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hp hq
      subst hp
      have := hnot j q hq
      rcases he with e | e
      · exact absurd e.symm this.1
      · exact absurd e.symm this.2
    · simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hp hq
      subst hq
      have := hnot i p hp
      rcases he with e | e
      · exact absurd e this.1
      · exact absurd e this.2
    · simp only [List.getElem?_cons_succ] at hp hq
      rw [chain_inj hpr hp hq he]

/-- The entry an element of a list sits at. -/
theorem idx_of_mem {chain : List (block × block)} {p : block × block} (h : p ∈ chain) :
    ∃ j : Nat, chain[j]? = some p := by
  obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 h
  exact ⟨j, by rw [List.getElem?_eq_getElem hj, e]⟩

theorem getElem?_take_of {l l' : List (block × block)} {k j : Nat} (h : l.take k = l'.take k)
    (hj : j < k) : l[j]? = l'[j]? := by
  have := congrArg (·[j]?) h
  simp only [List.getElem?_take, hj, ite_true] at this
  exact this

/-- An entry at index `i ≥ level - 1` of the list at a call, if it was in the
entry list, was there at an index `≥ level - 1`. -/
theorem entry_late {chain₀ chain : List (block × block)} {level i : Nat} {p : block × block}
    (hpw : (chain.flatMap fun p => [p.1, p.2]).Pairwise (· ≠ ·))
    (ht : chain.take (level - 1) = chain₀.take (level - 1)) (hi : chain[i]? = some p)
    (hil : level - 1 ≤ i) {j : Nat} (hj : chain₀[j]? = some p) : level - 1 ≤ j := by
  apply Nat.le_of_not_lt
  intro hjl
  have e : chain[j]? = some p := by rw [getElem?_take_of ht hjl]; exact hj
  have := chain_inj hpw hi e (.inl rfl)
  omega

variable {m₀ m : mem} {S : SLoc} {chain₀ chain : List (block × block)} {level : Nat}

/-- A step's blocks are among those the node may change. -/
theorem nset_step (hg : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m z) (hw : WorkMono m₀ m)
    {z : block} (hz : S.Chg z ∨ ¬ Mem.valid_block m z ∨ IsWork m z) :
    NSet m₀ S chain₀ level z := by
  rcases hz with h | h | h
  · exact .inl h
  · exact .inr (.inl fun hv => h (hg _ hv))
  · rcases hw z h with h' | h'
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inl h')

/-- A child's blocks are among those the node may change. -/
theorem nset_child (hg : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m z) (hw : WorkMono m₀ m)
    (hpw : (chain.flatMap fun p => [p.1, p.2]).Pairwise (· ≠ ·))
    (ht : chain.take (level - 1) = chain₀.take (level - 1))
    (hmem : ∀ p ∈ chain, p ∈ chain₀ ∨ (¬ Mem.valid_block m₀ p.1 ∧ ¬ Mem.valid_block m₀ p.2))
    {z : block} (hz : NSet m S chain (level + 1) z) : NSet m₀ S chain₀ level z := by
  rcases hz with h | h | h | h | ⟨i, p, hi, hil, rfl⟩ | ⟨i, p, hi, hil, rfl⟩
  · exact .inl h
  · exact .inr (.inl fun hv => h (hg _ hv))
  · rcases hw z h with h' | h'
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inl h')
  · exact .inr (.inr (.inr (.inl h)))
  · rcases hmem p (List.mem_of_getElem? hi) with hp | ⟨hn, -⟩
    · obtain ⟨j, hj⟩ := idx_of_mem hp
      have := entry_late hpw ht hi (by omega) hj
      exact .inr (.inr (.inr (.inr (.inl ⟨j, p, hj, by omega, rfl⟩))))
    · exact .inr (.inl hn)
  · rcases hmem p (List.mem_of_getElem? hi) with hp | ⟨-, hn⟩
    · obtain ⟨j, hj⟩ := idx_of_mem hp
      have := entry_late hpw ht hi (by omega) hj
      exact .inr (.inr (.inr (.inr (.inr ⟨j, p, hj, by omega, rfl⟩))))
    · exact .inr (.inl hn)

/-- The node's own target cell is among the blocks it may change. -/
theorem nset_own (hpw : (chain.flatMap fun p => [p.1, p.2]).Pairwise (· ≠ ·))
    (ht : chain.take (level - 1) = chain₀.take (level - 1))
    (hmem : ∀ p ∈ chain, p ∈ chain₀ ∨ (¬ Mem.valid_block m₀ p.1 ∧ ¬ Mem.valid_block m₀ p.2))
    {nd bt : block} (hown : chain[level - 1]? = some (nd, bt)) : NSet m₀ S chain₀ level bt := by
  rcases hmem _ (List.mem_of_getElem? hown) with hp | ⟨-, hn⟩
  · obtain ⟨j, hj⟩ := idx_of_mem hp
    have := entry_late hpw ht hown (Nat.le_refl _) hj
    exact .inr (.inr (.inr (.inr (.inr ⟨j, _, hj, by omega, rfl⟩))))
  · exact .inr (.inl hn)


/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : Cfrontend.Clight.genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

/-- `NSet` for `D`. -/
abbrev NSetG (D : DispatchRep ge O) (m : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc)
    (chain : List (block × block)) (level : Nat) (z : block) : Prop :=
  S.ChgG D gl cl z ∨ ¬ Mem.valid_block m z ∨ IsWorkG D m z ∨ z = E.tcnode0 ∨
    (∃ i p, chain[i]? = some p ∧ level ≤ i + 2 ∧ z = p.1) ∨
    (∃ i p, chain[i]? = some p ∧ level ≤ i + 1 ∧ z = p.2)

variable {gl : D.GLoc} {cl : D.CLoc}

theorem NodeFrameG.nset {m' : mem} (h : NodeFrameG D m m' S gl cl chain level) :
    Unch m m' (NSetG D m S gl cl chain level) := h.1

theorem NodeFrameG.grow {m' : mem} (h : NodeFrameG D m m' S gl cl chain level) :
    ∀ z, Mem.valid_block m z → Mem.valid_block m' z := h.2

theorem NodeFrameG.mk' {m' : mem} (hu : Unch m m' (NSetG D m S gl cl chain level))
    (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) :
    NodeFrameG D m m' S gl cl chain level := ⟨hu, hg⟩

/-- A step's blocks are among those the node may change. -/
theorem nset_stepG (hg : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m z)
    (hw : WorkMonoG D m₀ m) {z : block}
    (hz : S.ChgG D gl cl z ∨ ¬ Mem.valid_block m z ∨ IsWorkG D m z) :
    NSetG D m₀ S gl cl chain₀ level z := by
  rcases hz with h | h | h
  · exact .inl h
  · exact .inr (.inl fun hv => h (hg _ hv))
  · rcases hw z h with h' | h'
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inl h')

/-- A child's blocks are among those the node may change. -/
theorem nset_childG (hg : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m z)
    (hw : WorkMonoG D m₀ m)
    (hpw : (chain.flatMap fun p => [p.1, p.2]).Pairwise (· ≠ ·))
    (ht : chain.take (level - 1) = chain₀.take (level - 1))
    (hmem : ∀ p ∈ chain, p ∈ chain₀ ∨ (¬ Mem.valid_block m₀ p.1 ∧ ¬ Mem.valid_block m₀ p.2))
    {z : block} (hz : NSetG D m S gl cl chain (level + 1) z) :
    NSetG D m₀ S gl cl chain₀ level z := by
  rcases hz with h | h | h | h | ⟨i, p, hi, hil, rfl⟩ | ⟨i, p, hi, hil, rfl⟩
  · exact .inl h
  · exact .inr (.inl fun hv => h (hg _ hv))
  · rcases hw z h with h' | h'
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inl h')
  · exact .inr (.inr (.inr (.inl h)))
  · rcases hmem p (List.mem_of_getElem? hi) with hp | ⟨hn, -⟩
    · obtain ⟨j, hj⟩ := idx_of_mem hp
      have := entry_late hpw ht hi (by omega) hj
      exact .inr (.inr (.inr (.inr (.inl ⟨j, p, hj, by omega, rfl⟩))))
    · exact .inr (.inl hn)
  · rcases hmem p (List.mem_of_getElem? hi) with hp | ⟨-, hn⟩
    · obtain ⟨j, hj⟩ := idx_of_mem hp
      have := entry_late hpw ht hi (by omega) hj
      exact .inr (.inr (.inr (.inr (.inr ⟨j, p, hj, by omega, rfl⟩))))
    · exact .inr (.inl hn)

/-- The node's own target cell is among the blocks it may change. -/
theorem nset_ownG (hpw : (chain.flatMap fun p => [p.1, p.2]).Pairwise (· ≠ ·))
    (ht : chain.take (level - 1) = chain₀.take (level - 1))
    (hmem : ∀ p ∈ chain, p ∈ chain₀ ∨ (¬ Mem.valid_block m₀ p.1 ∧ ¬ Mem.valid_block m₀ p.2))
    {nd bt : block} (hown : chain[level - 1]? = some (nd, bt)) :
    NSetG D m₀ S gl cl chain₀ level bt := by
  rcases hmem _ (List.mem_of_getElem? hown) with hp | ⟨-, hn⟩
  · obtain ⟨j, hj⟩ := idx_of_mem hp
    have := entry_late hpw ht hown (Nat.le_refl _) hj
    exact .inr (.inr (.inr (.inr (.inr ⟨j, _, hj, by omega, rfl⟩))))
  · exact .inr (.inl hn)

end Generic

end NautyVerified.Proofs.Search

namespace NautyVerified.Proofs.Search

open Hex.GraphIso Hex.GraphIso.Nauty NautyVerified.Spec.SearchInf

/-- The vertex an off-path sweep enters is in its target cell, which starts at
`tc`: `breakout`'s arguments. -/
theorem sweepOkOff_breakArgs {n k : Nat} {G : Colored n k} {level nc tc tv : Nat} {cell : VSet n}
    {st : Search n} (h : SweepOkOff G level nc tc cell (some tv) st) :
    tv < n ∧ tc < n ∧ ∃ j, tc ≤ j ∧ j < n ∧ st.lab[j]! = tv := by
  have hm : cell.mem tv = true := h.1.choose_spec.choose_spec.2.2.2.2.1 tv rfl
  obtain ⟨st₂, ⟨len, hc, hseg⟩, hlab⟩ := SweepOkOff.target h
  have hne : cell ≠ VSet.empty := fun he => by
    rw [he, VSet.mem_empty] at hm; cases hm
  obtain ⟨-, h2, h3⟩ := hc hne
  have hs := hseg tv hm
  rw [segN, List.mem_map] at hs
  obtain ⟨o, ho, e⟩ := hs
  rw [List.mem_range] at ho
  refine ⟨VSet.mem_lt hm, by omega, tc + o, by omega, by omega, ?_⟩
  rw [← hlab]; exact e

end NautyVerified.Proofs.Search

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Common.Values

/-- In a list of pairwise distinct blocks, no entry's node is another's cell. -/
theorem chain_cross : ∀ {chain : List (block × block)},
    (chain.flatMap fun p => [p.1, p.2]).Pairwise (· ≠ ·) →
    ∀ {p q : block × block}, p ∈ chain → q ∈ chain → p.1 ≠ q.2
  | [], _, _, _, hp, _ => by simp at hp
  | a :: rest, hpw, p, q, hp, hq => by
    rw [List.flatMap_cons, show [a.1, a.2] ++ rest.flatMap (fun p => [p.1, p.2]) =
      a.1 :: a.2 :: rest.flatMap (fun p => [p.1, p.2]) from rfl, List.pairwise_cons,
      List.pairwise_cons] at hpw
    obtain ⟨h1, h2, hr⟩ := hpw
    have m1 : ∀ r ∈ rest, r.1 ∈ rest.flatMap (fun p => [p.1, p.2]) :=
      fun r hr => List.mem_flatMap.2 ⟨r, hr, by simp⟩
    have m2 : ∀ r ∈ rest, r.2 ∈ rest.flatMap (fun p => [p.1, p.2]) :=
      fun r hr => List.mem_flatMap.2 ⟨r, hr, by simp⟩
    rcases List.mem_cons.1 hp with rfl | hp1 <;> rcases List.mem_cons.1 hq with rfl | hq1
    · exact h1 _ (.head _)
    · exact h1 _ (.tail _ (m2 q hq1))
    · exact fun e => h2 _ (m1 p hp1) e.symm
    · exact chain_cross hr hp1 hq1

end NautyVerified.Proofs.Search
