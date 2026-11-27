import NautyVerified.Proofs.Search.Node.Spec

/-!
# The target-cell list

`prevAt prev chain i`: the node whose `next` field links to entry `i` (`prev`
for `i = 0`). `TcChain.next`: that field holds entry `i`'s node, or `NULL`
at the end of the list. `tcParent_eq`: the parent a level-`level` call
receives is `prevAt tcnode0 chain (level - 1)`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program

/-- The node whose `next` field links to entry `i` of `chain`. -/
def prevAt (prev : block) : List (block × block) → Nat → block
  | _, 0 => prev
  | [], _ + 1 => prev
  | p :: rest, i + 1 => prevAt p.1 rest i

/-- What the link to entry `i` holds: its node, or `NULL` past the end. -/
def linkAt (chain : List (block × block)) (i : Nat) : val :=
  match chain[i]? with
  | some p => .Vptr p.1 Ptrofs.zero
  | none => Vnullptr

theorem TcChain.next {m : mem} {M : Nat} :
    ∀ {prev : block} {chain : List (block × block)} {i : Nat}, TcChain m M prev chain →
      i ≤ chain.length → FieldAt m .Mint64 (prevAt prev chain i) 0 (linkAt chain i)
  | _, [], 0, h, _ => h
  | _, [], _ + 1, _, hi => absurd hi (by simp)
  | _, _ :: _, 0, h, _ => h.1
  | _, _ :: rest, i + 1, h, hi => by
    simp only [prevAt, linkAt, List.getElem?_cons_succ]
    exact TcChain.next h.2.2.2 (by simpa using hi)

theorem prevAt_eq (prev : block) :
    ∀ (chain : List (block × block)) (i : Nat), i + 1 ≤ chain.length →
      prevAt prev chain (i + 1) = (chain[i]?.map Prod.fst).getD prev
  | [], _, h => absurd h (by simp)
  | p :: _, 0, _ => by simp [prevAt]
  | p :: rest, i + 1, h => by
    rw [prevAt, prevAt_eq p.1 rest i (by simpa using h)]
    obtain ⟨q, hq⟩ : ∃ q, rest[i]? = some q :=
      ⟨rest[i]'(by simp at h; omega), List.getElem?_eq_getElem _⟩
    simp [hq]

theorem tcParent_eq {chain : List (block × block)} {level : Nat} (h1 : 1 ≤ level)
    (hl : level - 1 ≤ chain.length) : tcParent chain level = prevAt Block.tcnode0 chain (level - 1) := by
  unfold tcParent
  by_cases h : level ≤ 1
  · rw [ite_eq_left h, show level - 1 = 0 by omega]; simp [prevAt]
  · rw [ite_eq_right h]
    obtain ⟨k, rfl⟩ : ∃ k, level = k + 2 := ⟨level - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 by omega, prevAt_eq _ _ _ (by omega),
      show k + 2 - 2 = k by omega]

/-- The blocks of the list, its first link included. -/
def tcBlocks (prev : block) (chain : List (block × block)) : List block :=
  prev :: chain.flatMap fun p => [p.1, p.2]

theorem FieldAt.unch' {m m' : mem} {S : block → Prop} {chunk : Common.AST.memory_chunk} {b : block}
    {off : Int} {v : val} (h : FieldAt m chunk b off v) (hu : Unch m m' S) (hb : ¬ S b) :
    FieldAt m' chunk b off v :=
  ⟨by rw [hu.load _ _ _ hb]; exact h.load, hu.access _ _ _ _ hb h.writable⟩

/-- The list survives changes to other blocks. -/
theorem TcChain.unch {m m' : mem} {M : Nat} {S : block → Prop} (hu : Unch m m' S) :
    ∀ {prev : block} {chain : List (block × block)}, TcChain m M prev chain →
      (∀ z ∈ tcBlocks prev chain, ¬ S z) → TcChain m' M prev chain
  | _, [], h, hS => h.unch' hu (hS _ (.head _))
  | _, (nd, tc) :: rest, h, hS => by
    obtain ⟨h1, h2, ⟨vals, h3⟩, h4⟩ := h
    have hnd : ¬ S nd := hS nd (by simp [tcBlocks])
    have htc : ¬ S tc := hS tc (by simp [tcBlocks])
    refine ⟨h1.unch' hu (hS _ (.head _)), h2.unch' hu hnd, ⟨vals, h3.unch hu htc⟩,
      TcChain.unch hu h4 fun z hz => hS z ?_⟩
    simp only [tcBlocks, List.mem_cons, List.flatMap_cons, List.mem_append] at hz ⊢
    rcases hz with rfl | hz
    · exact .inr (.inl (.inl rfl))
    · exact .inr (.inr hz)

theorem prevAt_mem : ∀ (prev : block) (chain : List (block × block)) (i : Nat),
    prevAt prev chain i ∈ tcBlocks prev chain
  | _, _, 0 => by simp [prevAt, tcBlocks]
  | _, [], _ + 1 => by simp [prevAt, tcBlocks]
  | prev, p :: rest, i + 1 => by
    have := prevAt_mem p.1 rest i
    simp only [prevAt, tcBlocks, List.mem_cons, List.flatMap_cons, List.mem_append] at this ⊢
    rcases this with h | h
    · exact .inr (.inl (.inl h))
    · exact .inr (.inr h)

theorem prevAt_mem_nodes : ∀ (prev : block) (chain : List (block × block)) (i : Nat),
    prevAt prev chain i = prev ∨ ∃ p ∈ chain, prevAt prev chain i = p.1
  | _, _, 0 => .inl (by simp [prevAt])
  | _, [], _ + 1 => .inl (by simp [prevAt])
  | prev, p :: rest, i + 1 => by
    rcases prevAt_mem_nodes p.1 rest i with h | ⟨q, hq, h⟩
    · exact .inr ⟨p, .head _, by simp [prevAt, h]⟩
    · exact .inr ⟨q, .tail _ hq, by simp [prevAt, h]⟩

theorem tcBlocks_cons (prev q t : block) (rest : List (block × block)) :
    tcBlocks prev ((q, t) :: rest) = prev :: q :: t :: (rest.flatMap fun p => [p.1, p.2]) := rfl

theorem mem_flat {p : block × block} {rest : List (block × block)} (hp : p ∈ rest) :
    p.1 ∈ rest.flatMap (fun p => [p.1, p.2]) ∧ p.2 ∈ rest.flatMap (fun p => [p.1, p.2]) :=
  ⟨List.mem_flatMap.2 ⟨p, hp, by simp⟩, List.mem_flatMap.2 ⟨p, hp, by simp⟩⟩

/-- Appending a node at the end of the list: the last link now points to `nd`,
whose `next` is `NULL` and whose target cell is `tc`. Every other block of the
list is unchanged, and so is the last node's `tcellptr` field. -/
theorem TcChain.snoc {m m' : mem} {M : Nat} {S : block → Prop} (hu : Unch m m' S)
    {nd tc : block} :
    ∀ {prev : block} {chain : List (block × block)}, TcChain m M prev chain →
      (tcBlocks prev chain).Pairwise (· ≠ ·) →
      (∀ z ∈ tcBlocks prev chain, z ≠ prevAt prev chain chain.length → ¬ S z) →
      (∀ v, FieldAt m .Mint64 (prevAt prev chain chain.length) 8 v →
        FieldAt m' .Mint64 (prevAt prev chain chain.length) 8 v) →
      FieldAt m' .Mint64 (prevAt prev chain chain.length) 0 (.Vptr nd Ptrofs.zero) →
      FieldAt m' .Mint64 nd 0 Vnullptr → FieldAt m' .Mint64 nd 8 (.Vptr tc Ptrofs.zero) →
      (∃ vals, ArrayAt m' .Mint64 tc 0 vals M) →
      TcChain m' M prev (chain ++ [(nd, tc)])
  | _, [], _, _, _, _, hl, h1, h2, h3 => ⟨by simpa [prevAt] using hl, h2, h3, h1⟩
  | prev, (q, t) :: rest, h, hd, hS, h8, hl, h1, h2, h3 => by
    obtain ⟨g1, g2, ⟨vals, g3⟩, g4⟩ := h
    have hlast : prevAt prev ((q, t) :: rest) ((q, t) :: rest).length =
        prevAt q rest rest.length := by simp [prevAt]
    rw [hlast] at hS hl h8
    rw [tcBlocks_cons] at hd hS
    rw [List.pairwise_cons] at hd
    obtain ⟨hprev, hd⟩ := hd
    rw [List.pairwise_cons] at hd
    obtain ⟨hqn, hd⟩ := hd
    rw [List.pairwise_cons] at hd
    obtain ⟨htn, hrest⟩ := hd
    have hmem : prevAt q rest rest.length = q ∨ ∃ p ∈ rest, prevAt q rest rest.length = p.1 := prevAt_mem_nodes q rest rest.length
    have hpl : prev ≠ prevAt q rest rest.length := by
      rcases hmem with h | ⟨p, hp, h⟩
      · rw [h]; exact hprev q (.head _)
      · rw [h]; exact hprev p.1 (.tail _ (.tail _ (mem_flat hp).1))
    have htl : t ≠ prevAt q rest rest.length := by
      rcases hmem with h | ⟨p, hp, h⟩
      · rw [h]; exact (hqn t (.head _)).symm
      · rw [h]; exact htn p.1 (mem_flat hp).1
    have hq8 : FieldAt m' .Mint64 q 8 (.Vptr t Ptrofs.zero) := by
      rcases Decidable.em (q = prevAt q rest rest.length) with hql | hql
      · exact hql ▸ h8 _ (hql ▸ g2)
      · exact g2.unch' hu (hS q (by simp) hql)
    refine ⟨g1.unch' hu (hS prev (.head _) hpl), hq8, ⟨vals, g3.unch hu (hS t (by simp) htl)⟩, ?_⟩
    refine TcChain.snoc hu g4 ?_ (fun z hz hzl => hS z ?_ hzl) h8 hl h1 h2 h3
    · rw [tcBlocks, List.pairwise_cons]
      exact ⟨fun z hz => hqn z (.tail _ hz), hrest⟩
    · rw [tcBlocks] at hz
      rcases List.mem_cons.1 hz with rfl | hz
      · simp
      · exact .tail _ (.tail _ (.tail _ hz))

/-- Entry `i`'s node points to its target cell, an array of `M` words. -/
theorem TcChain.cell {m : mem} {M : Nat} :
    ∀ {prev : block} {chain : List (block × block)} {i : Nat} {nd tc : block},
      TcChain m M prev chain → chain[i]? = some (nd, tc) →
      FieldAt m .Mint64 nd 8 (.Vptr tc Ptrofs.zero) ∧ ∃ vals, ArrayAt m .Mint64 tc 0 vals M
  | _, [], _, _, _, _, h => by simp at h
  | _, (q, t) :: _, 0, _, _, h, he => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨h.2.1, h.2.2.1⟩
  | _, _ :: _, i + 1, _, _, h, he => by
    simp only [List.getElem?_cons_succ] at he
    exact TcChain.cell h.2.2.2 he

end NautyVerified.Proofs.Search
