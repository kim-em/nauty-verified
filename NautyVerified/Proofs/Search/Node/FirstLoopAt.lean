import NautyVerified.Proofs.Search.Node.FirstShape
import NautyVerified.Proofs.Search.Node.TcFrame

/-!
# The memory of `firstpathnode0`'s child loop

`LCtx`: what stays fixed across the loop: the caller's `SLoc`, the entry
memory and target-cell list, the node's level, cell count, target cell start
and size, its five `int` locals, and its own entry of the target-cell list
(`bnd`, holding the target cell `btc`).

`LoopAt L m st pre nsp cell ch`: memory `m` holds the search state `st`, the
target cell `cell` in `btc`, the locals, and the target-cell list `ch`, which
keeps its first `level - 1` entries, has this node's at index `level - 1`, and
whose entries are old or newly allocated and never the locals. The changes
since entry are within the node's frame, and work blocks are old or new.

`LoopAt.call`: a recursive call at `level + 1` (whose specification gives
`SearchAt`, a new list, `NodeFrame` and the work-block property) keeps
`LoopAt`. `LoopAt.step`: so does one of the node's own steps that changes
only blocks of `S`, blocks not valid before, work blocks, and the target cell.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty

variable {n : Nat}

/-- The blocks of a target-cell list. -/
abbrev flat (ch : List (block × block)) : List block := ch.flatMap fun p => [p.1, p.2]

/-- A block of two entries of a list with distinct blocks is at one index. -/
theorem flat_idx : ∀ {ch : List (block × block)}, (flat ch).Pairwise (· ≠ ·) →
    ∀ {i j : Nat} {p q : block × block} {z : block}, ch[i]? = some p → ch[j]? = some q →
      (z = p.1 ∨ z = p.2) → (z = q.1 ∨ z = q.2) → i = j
  | [], _, _, _, _, _, _, hi, _, _, _ => by simp at hi
  | a :: l, hd, i, j, p, q, z, hi, hj, hp, hq => by
    simp only [flat, List.flatMap_cons] at hd
    rw [List.pairwise_append] at hd
    obtain ⟨-, hl, hx⟩ := hd
    have inl : ∀ {k : Nat} {r : block × block} {z : block}, l[k]? = some r →
        (z = r.1 ∨ z = r.2) → z ∈ flat l := by
      intro k r z hk hz
      refine List.mem_flatMap.2 ⟨r, List.mem_of_getElem? hk, ?_⟩
      rcases hz with rfl | rfl <;> simp
    rcases i with _ | i <;> rcases j with _ | j
    · rfl
    · simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
      subst hi
      exact absurd rfl (hx z (by rcases hp with rfl | rfl <;> simp) z (inl hj hq))
    · simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
      subst hj
      exact absurd rfl (hx z (by rcases hq with rfl | rfl <;> simp) z (inl hi hp))
    · simp only [List.getElem?_cons_succ] at hi hj
      exact congrArg (· + 1) (flat_idx hl hi hj hp hq)

/-- What stays fixed across `firstpathnode0`'s child loop. -/
structure LCtx (n : Nat) where
  S : SLoc
  ctx : Ctx n
  m₀ : mem
  chain₀ : List (block × block)
  level : Nat
  nc : Nat
  tc : Nat
  tcsize : Nat
  bnc : block
  bq : block
  bk : block
  bc : block
  bz : block
  bnd : block
  btc : block

/-- The node's `int` locals. -/
abbrev LCtx.locals (L : LCtx n) : List block := [L.bnc, L.bq, L.bk, L.bc, L.bz]

/-- The target-cell list during the loop. -/
structure ChainAt (L : LCtx n) (m : mem) (ch : List (block × block)) : Prop where
  chain : TcChain m L.S.M Block.tcnode0 ch
  ok : TcOk m L.S ch
  len : L.level ≤ ch.length
  own : ch[L.level - 1]? = some (L.bnd, L.btc)
  take : ch.take (L.level - 1) = L.chain₀.take (L.level - 1)
  fresh : ∀ p ∈ ch, p ∈ L.chain₀ ∨ (¬ Mem.valid_block L.m₀ p.1 ∧ ¬ Mem.valid_block L.m₀ p.2)
  apart : ∀ p ∈ ch, p.1 ∉ L.locals ∧ p.2 ∉ L.locals
  lvl : 1 ≤ L.level

/-- The memory of the loop. -/
structure LoopAt (L : LCtx n) (m : mem) (st : Search n) (pre nsp : Bool) (cell : VSet n)
    (ch : List (block × block)) : Prop where
  search : SearchAt m L.S L.ctx st pre nsp
  cell : ∃ tw, ArrayAt m .Mint64 L.btc 0 (longs tw) L.S.M ∧
    SetRep (fun w => bv64 (tw w)) L.S.M cell
  nc : ArrayAt m .Mint32 L.bnc 0 (fun _ => .Vint (ir L.nc)) 1
  tc : ArrayAt m .Mint32 L.bc 0 (fun _ => .Vint (ir L.tc)) 1
  tz : ArrayAt m .Mint32 L.bz 0 (fun _ => .Vint (ir L.tcsize)) 1
  q : ∃ v, ArrayAt m .Mint32 L.bq 0 v 1
  k : ∃ v, ArrayAt m .Mint32 L.bk 0 v 1
  chain : ChainAt L m ch
  frame : NodeFrame L.m₀ m L.S L.chain₀ L.level
  work : ∀ z, IsWork m z → IsWork L.m₀ z ∨ ¬ Mem.valid_block L.m₀ z
  locals : ∀ z ∈ L.locals, Mem.valid_block m z ∧ z ∉ L.S.blocks ∧ ¬ IsWork m z
  vU : Mem.valid_block m L.S.bUA
  pU : Mem.perm m L.S.bUA (zOfInt 0) .Cur .Nonempty

/-- An entry of the current list beyond the first `level - 1` is, if old, at an
index `≥ level - 1` of the entry list. -/
theorem ChainAt.old_idx {L : LCtx n} {m : mem} {ch : List (block × block)} (h : ChainAt L m ch)
    {i : Nat} {p : block × block} (hi : ch[i]? = some p)
    (hil : L.level - 1 ≤ i) {z : block} (hz : z = p.1 ∨ z = p.2) :
    (∃ j q, L.chain₀[j]? = some q ∧ L.level - 1 ≤ j ∧ (z = q.1 ∨ z = q.2)) ∨
      ¬ Mem.valid_block L.m₀ z := by
  rcases h.fresh p (List.mem_of_getElem? hi) with hp | ⟨h1, h2⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    refine .inl ⟨j, p, hj, ?_, hz⟩
    refine Nat.le_of_not_lt fun hlt => ?_
    have hj' : ch[j]? = some p := by
      have := congrArg (·[j]?) h.take
      simp only [List.getElem?_take] at this
      rw [ite_eq_left (by omega), ite_eq_left (by omega), hj] at this
      exact this
    have := flat_idx h.ok.pairwise hi hj' hz hz
    omega
  · exact .inr (by rcases hz with rfl | rfl <;> assumption)

/-- The blocks a node at `level` may change, from memory `m` and list `ch`. -/
abbrev frameSet (m : mem) (S : SLoc) (ch : List (block × block)) (level : Nat) (z : block) : Prop :=
  z ∈ S.blocks ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨ z = Block.tcnode0 ∨
    (∃ i p, ch[i]? = some p ∧ level ≤ i + 2 ∧ z = p.1) ∨
    (∃ i p, ch[i]? = some p ∧ level ≤ i + 1 ∧ z = p.2)

theorem NodeFrame.unch {m m' : mem} {S : SLoc} {ch : List (block × block)} {level : Nat}
    (h : NodeFrame m m' S ch level) : Unch m m' (frameSet m S ch level) := h.1

/-- A list entry at index `≥ level - 1` is within the node's frame from entry. -/
theorem ChainAt.entry_frame {L : LCtx n} {m : mem} {ch : List (block × block)} (h : ChainAt L m ch)
    {i : Nat} {p : block × block} (hi : ch[i]? = some p) (hil : L.level - 1 ≤ i) {z : block}
    (hz : z = p.1 ∨ z = p.2) : frameSet L.m₀ L.S L.chain₀ L.level z := by
  rcases h.old_idx hi hil hz with ⟨j, q, hj, hjl, hq⟩ | hnv
  · rcases hq with rfl | rfl
    · exact .inr (.inr (.inr (.inr (.inl ⟨j, q, hj, by omega, rfl⟩))))
    · exact .inr (.inr (.inr (.inr (.inr ⟨j, q, hj, by omega, rfl⟩))))
  · exact .inr (.inl hnv)

/-- A block changed by a child call is within the node's frame from entry. -/
theorem LoopAt.call_sub {L : LCtx n} {m : mem} {st : Search n} {pre nsp : Bool} {cell : VSet n}
    {ch : List (block × block)} (h : LoopAt L m st pre nsp cell ch) {z : block}
    (hz : frameSet m L.S ch (L.level + 1) z) : frameSet L.m₀ L.S L.chain₀ L.level z := by
  have hg := h.frame.2
  rcases hz with hz | hz | hz | hz | ⟨i, p, hi, hil, rfl⟩ | ⟨i, p, hi, hil, rfl⟩
  · exact .inl hz
  · exact .inr (.inl fun hv => hz (hg _ hv))
  · rcases h.work z hz with hw | hw
    · exact .inr (.inr (.inl hw))
    · exact .inr (.inl hw)
  · exact .inr (.inr (.inr (.inl hz)))
  · exact h.chain.entry_frame hi (by omega) (.inl rfl)
  · exact h.chain.entry_frame hi (by omega) (.inr rfl)

/-- A block changed by one of the node's own steps is within its frame from entry. -/
theorem LoopAt.step_sub {L : LCtx n} {m : mem} {st : Search n} {pre nsp : Bool} {cell : VSet n}
    {ch : List (block × block)} (h : LoopAt L m st pre nsp cell ch) {z : block}
    (hz : z ∈ L.S.blocks ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨ z = L.btc) :
    frameSet L.m₀ L.S L.chain₀ L.level z := by
  have hg := h.frame.2
  rcases hz with hz | hz | hz | rfl
  · exact .inl hz
  · exact .inr (.inl fun hv => hz (hg _ hv))
  · rcases h.work z hz with hw | hw
    · exact .inr (.inr (.inl hw))
    · exact .inr (.inl hw)
  · exact h.chain.entry_frame h.chain.own (Nat.le_refl _) (.inr rfl)

theorem flat_ne {ch : List (block × block)} (hd : (flat ch).Pairwise (· ≠ ·)) {p : block × block}
    (hp : p ∈ ch) : p.1 ≠ p.2 := by
  induction ch with
  | nil => cases hp
  | cons a l ih =>
    simp only [flat, List.flatMap_cons] at hd
    rw [List.pairwise_append] at hd
    obtain ⟨h1, hl, -⟩ := hd
    rcases List.mem_cons.1 hp with rfl | hp
    · simpa using h1
    · exact ih hl hp

/-- A block apart from `S`, valid, not a work block and not in the list at the
indices a child at `level + 1` may change is not changed by it. -/
theorem not_frameSet {m : mem} {S : SLoc} {ch : List (block × block)} {level : Nat} {z : block}
    (h1 : z ∉ S.blocks) (h2 : Mem.valid_block m z) (h3 : ¬ IsWork m z)
    (h4 : ∀ i p, ch[i]? = some p → level ≤ i + 2 → z ≠ p.1)
    (h5 : ∀ i p, ch[i]? = some p → level ≤ i + 1 → z ≠ p.2) : ¬ frameSet m S ch level z := by
  rintro (hz | hz | hz | rfl | ⟨i, p, hi, hil, rfl⟩ | ⟨i, p, hi, hil, rfl⟩)
  · exact h1 hz
  · exact hz h2
  · exact h3 hz
  · exact h1 (by simp [SLoc.blocks])
  · exact h4 i p hi hil rfl
  · exact h5 i p hi hil rfl

theorem ChainAt.local_safe {L : LCtx n} {m : mem} {ch : List (block × block)} (h : ChainAt L m ch)
    {z : block} (hz : z ∈ L.locals) (h1 : z ∉ L.S.blocks) (h2 : Mem.valid_block m z)
    (h3 : ¬ IsWork m z) (level : Nat) : ¬ frameSet m L.S ch level z :=
  not_frameSet h1 h2 h3 (fun _ p hi _ e => (h.apart p (List.mem_of_getElem? hi)).1 (e ▸ hz))
    (fun _ p hi _ e => (h.apart p (List.mem_of_getElem? hi)).2 (e ▸ hz))

/-- The node's own target cell is not changed by a child. -/
theorem ChainAt.cell_safe {L : LCtx n} {m : mem} {ch : List (block × block)} (h : ChainAt L m ch) :
    ¬ frameSet m L.S ch (L.level + 1) L.btc := by
  have hmem := List.mem_of_getElem? h.own
  obtain ⟨-, a2, -, a4⟩ := h.ok.apart _ hmem
  refine not_frameSet a2 (h.ok.valid _ hmem).2 a4 (fun i p hi _ e => ?_) (fun i p hi hil e => ?_)
  · have := flat_idx h.ok.pairwise hi h.own (.inl e) (.inr rfl)
    subst this
    rw [h.own] at hi; cases hi
    exact flat_ne h.ok.pairwise hmem e.symm
  · have := flat_idx h.ok.pairwise hi h.own (.inr e) (.inr rfl)
    have := h.lvl; omega

/-- A recursive call at `level + 1` keeps `LoopAt`. -/
theorem LoopAt.call {L : LCtx n} {m : mem} {st : Search n} {pre nsp : Bool} {cell : VSet n}
    {ch : List (block × block)} (h : LoopAt L m st pre nsp cell ch)
    {m' : mem} {s' : Search n} {nsp' : Bool} {ch' : List (block × block)}
    (hS : SearchAt m' L.S L.ctx s' false nsp')
    (hc1 : TcChain m' L.S.M Block.tcnode0 ch') (hc2 : TcOk m' L.S ch')
    (hc3 : L.level + 1 ≤ ch'.length) (hc4 : ch'.take L.level = ch.take L.level)
    (hc5 : ∀ p ∈ ch', p ∈ ch ∨ (¬ Mem.valid_block m p.1 ∧ ¬ Mem.valid_block m p.2))
    (hF : NodeFrame m m' L.S ch (L.level + 1))
    (hW : ∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z)
    (hvU : Mem.valid_block m' L.S.bUA) (hpU : Mem.perm m' L.S.bUA (zOfInt 0) .Cur .Nonempty)
    (hl1 : 1 ≤ L.level) :
    LoopAt L m' s' false nsp' cell ch' := by
  have hu := hF.unch
  have hg := hF.2
  have hloc : ∀ z ∈ L.locals, ¬ frameSet m L.S ch (L.level + 1) z := fun z hz =>
    have ⟨a, b, c⟩ := h.locals z hz
    h.chain.local_safe hz b a c _
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hloc
  obtain ⟨tw, hta, htr⟩ := h.cell
  obtain ⟨vq, hq⟩ := h.q
  obtain ⟨vk, hk⟩ := h.k
  have hown : ch'[L.level - 1]? = some (L.bnd, L.btc) := by
    have := congrArg (·[L.level - 1]?) hc4
    simp only [List.getElem?_take] at this
    rw [ite_eq_left (by omega), ite_eq_left (by omega)] at this
    rw [this]; exact h.chain.own
  refine
    { search := hS
      cell := ⟨tw, hta.unch hu h.chain.cell_safe, htr⟩
      nc := h.nc.unch hu (hloc _ (.inl rfl))
      tc := h.tc.unch hu (hloc _ (.inr (.inr (.inr (.inl rfl)))))
      tz := h.tz.unch hu (hloc _ (.inr (.inr (.inr (.inr rfl)))))
      q := ⟨vq, hq.unch hu (hloc _ (.inr (.inl rfl)))⟩
      k := ⟨vk, hk.unch hu (hloc _ (.inr (.inr (.inl rfl))))⟩
      chain :=
        { chain := hc1, ok := hc2, len := by omega, own := hown
          take := by
            have := congrArg (List.take (L.level - 1)) hc4
            simp only [List.take_take] at this
            rw [show min (L.level - 1) L.level = L.level - 1 by omega] at this
            rw [this]; exact h.chain.take
          fresh := fun p hp => by
            rcases hc5 p hp with hp | ⟨h1, h2⟩
            · exact h.chain.fresh p hp
            · exact .inr ⟨fun hv => h1 (h.frame.2 _ hv), fun hv => h2 (h.frame.2 _ hv)⟩
          apart := fun p hp => by
            rcases hc5 p hp with hp | ⟨h1, h2⟩
            · exact h.chain.apart p hp
            · exact ⟨fun hz => h1 (h.locals _ hz).1, fun hz => h2 (h.locals _ hz).1⟩
          lvl := hl1 }
      frame := ⟨h.frame.unch.trans (hu.mono fun z hz => h.call_sub hz), fun z hz => hg z (h.frame.2 z hz)⟩
      work := fun z hz => by
        rcases hW z hz with hw | hw
        · exact h.work z hw
        · exact .inr fun hv => hw (h.frame.2 _ hv)
      locals := fun z hz => by
        obtain ⟨a, b, c⟩ := h.locals z hz
        refine ⟨hg z a, b, fun hw => ?_⟩
        rcases hW z hw with hw | hw
        · exact c hw
        · exact hw a
      vU := hvU
      pU := hpU }

theorem TcChain.head_valid {m : mem} {M : Nat} {prev : block} {ch : List (block × block)}
    (h : TcChain m M prev ch) : Mem.valid_block m prev := by
  cases ch with
  | nil => exact h.valid
  | cons p rest => exact h.1.valid

/-- What one of the node's own steps may change: blocks of `S` other than
`userautomproc`'s and `tcnode0`, blocks not valid before, work blocks, and the
target cell. -/
abbrev stepSet (m : mem) (S : SLoc) (btc : block) (z : block) : Prop :=
  (z ∈ S.blocks ∧ z ≠ S.bUA ∧ z ≠ Block.tcnode0) ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨ z = btc

theorem perm_unch {m m' : mem} {W : block → Prop} (hu : Unch m m' W) {b : block} (hb : ¬ W b)
    (h : Mem.perm m b (zOfInt 0) .Cur .Nonempty) : Mem.perm m' b (zOfInt 0) .Cur .Nonempty := by
  have hva : Mem.valid_access m .Mint8unsigned b (zOfInt 0) .Nonempty := by
    refine ⟨fun o ho => ?_, ⟨zOfInt 0, rfl⟩⟩
    have h1 := ho.1; have h2 := ho.2
    change intOfZ _ ≤ intOfZ _ at h1
    change intOfZ _ < intOfZ _ at h2
    have h8 : intOfZ (Common.Memdata.size_chunk .Mint8unsigned) = 1 := rfl
    simp only [intOfZ_add, intOfZ_zOfInt, h8] at h1 h2
    have : o = zOfInt 0 := by apply intOfZ_injective; simp only [intOfZ_zOfInt]; omega
    rw [this]; exact h
  refine (hu.access _ _ _ _ hb hva).1 (zOfInt 0) ⟨?_, ?_⟩
  · exact Int.le_refl _
  · change intOfZ _ < intOfZ _
    have h8 : intOfZ (Common.Memdata.size_chunk .Mint8unsigned) = 1 := rfl
    simp only [intOfZ_add, intOfZ_zOfInt, h8]; omega

/-- One of the node's own steps keeps `LoopAt`. -/
theorem LoopAt.step {L : LCtx n} {m : mem} {st : Search n} {pre nsp : Bool} {cell : VSet n}
    {ch : List (block × block)} (h : LoopAt L m st pre nsp cell ch)
    {m' : mem} {st' : Search n} {pre' nsp' : Bool} {cell' : VSet n}
    (hS : SearchAt m' L.S L.ctx st' pre' nsp')
    (hu : Unch m m' (stepSet m L.S L.btc))
    (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hW : ∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z)
    (hc : ∃ tw, ArrayAt m' .Mint64 L.btc 0 (longs tw) L.S.M ∧
      SetRep (fun w => bv64 (tw w)) L.S.M cell') :
    LoopAt L m' st' pre' nsp' cell' ch := by
  have hloc : ∀ z ∈ L.locals, ¬ stepSet m L.S L.btc z := by
    intro z hz
    obtain ⟨a, b, c⟩ := h.locals z hz
    rintro (⟨hz', -⟩ | hz' | hz' | rfl)
    · exact b hz'
    · exact hz' a
    · exact c hz'
    · exact (h.chain.apart _ (List.mem_of_getElem? h.chain.own)).2 hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hloc
  obtain ⟨vq, hq⟩ := h.q
  obtain ⟨vk, hk⟩ := h.k
  have hc0 := h.chain
  have hok := hc0.ok
  -- the list's blocks other than the target cell are untouched
  have hT : ∀ z ∈ tcBlocks Block.tcnode0 ch, z ≠ L.btc → ¬ stepSet m L.S L.btc z := by
    intro z hz hne
    simp only [tcBlocks, List.mem_cons] at hz
    rintro (⟨hzS, -, h3⟩ | hz' | hz' | rfl)
    · rcases hz with rfl | hz
      · exact h3 rfl
      · obtain ⟨p, hp, hzp⟩ := List.mem_flatMap.1 hz
        obtain ⟨a1, a2, -, -⟩ := hok.apart p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzp
        rcases hzp with rfl | rfl
        · exact a1 hzS
        · exact a2 hzS
    · rcases hz with rfl | hz
      · exact hz' hc0.chain.head_valid
      · obtain ⟨p, hp, hzp⟩ := List.mem_flatMap.1 hz
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzp
        rcases hzp with rfl | rfl
        · exact hz' (hok.valid p hp).1
        · exact hz' (hok.valid p hp).2
    · rcases hz with rfl | hz
      · exact h.search.work_not hz' (by simp [SLoc.blocks])
      · obtain ⟨p, hp, hzp⟩ := List.mem_flatMap.1 hz
        obtain ⟨-, -, a3, a4⟩ := hok.apart p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hzp
        rcases hzp with rfl | rfl
        · exact a3 hz'
        · exact a4 hz'
    · exact hne rfl
  have hmem := List.mem_of_getElem? hc0.own
  refine
    { search := hS
      cell := hc
      nc := h.nc.unch hu (hloc _ (.inl rfl))
      tc := h.tc.unch hu (hloc _ (.inr (.inr (.inr (.inl rfl)))))
      tz := h.tz.unch hu (hloc _ (.inr (.inr (.inr (.inr rfl)))))
      q := ⟨vq, hq.unch hu (hloc _ (.inr (.inl rfl)))⟩
      k := ⟨vk, hk.unch hu (hloc _ (.inr (.inr (.inl rfl))))⟩
      chain :=
        { hc0 with
          chain := TcChain.setCell hu (by obtain ⟨tw, ha, -⟩ := hc; exact ⟨_, ha⟩) hc0.chain hT
            (fun e => (hok.apart _ hmem).2.1 (e ▸ by simp [SLoc.blocks]))
            (fun p hp e => by
              have ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
              have := flat_idx hok.pairwise hi hc0.own (.inl e.symm) (.inr rfl)
              subst this; rw [hc0.own] at hi; cases hi
              exact flat_ne hok.pairwise hmem e)
          ok := hok.mono hg hW }
      frame := ⟨h.frame.unch.trans (hu.mono fun z hz => h.step_sub (by
          rcases hz with ⟨h1, -⟩ | hz | hz | hz
          · exact .inl h1
          · exact .inr (.inl hz)
          · exact .inr (.inr (.inl hz))
          · exact .inr (.inr (.inr hz)))), fun z hz => hg z (h.frame.2 z hz)⟩
      work := fun z hz => by
        rcases hW z hz with hw | hw
        · exact h.work z hw
        · exact .inr fun hv => hw (h.frame.2 _ hv)
      locals := fun z hz => by
        obtain ⟨a, b, c⟩ := h.locals z hz
        refine ⟨hg z a, b, fun hw => ?_⟩
        rcases hW z hw with hw | hw
        · exact c hw
        · exact hw a
      vU := hg _ h.vU
      pU := perm_unch hu (by
          rintro (⟨-, h2, -⟩ | hz | hz | hz)
          · exact h2 rfl
          · exact hz h.vU
          · exact h.search.work_not hz (by simp [SLoc.blocks])
          · exact (hok.apart _ hmem).2.1 (hz ▸ by simp [SLoc.blocks])) h.pU }

end NautyVerified.Proofs.Search
