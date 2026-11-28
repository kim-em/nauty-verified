import NautyVerified.Proofs.Alloc.Dyn3

/-!
# A list of `DYNALLSTAT` pairs

A library's scratch arrays are `DYNALLSTAT` pairs `(bp, bs, c)`: pointer
global, capacity global, element size. `InUse m ps z`: `z` is the block of
one of the pairs `ps` with positive capacity. `SlotsOk m ps L`: every pair is
a `DynAt`, the blocks in use are none of `L`, and two pairs never share a
block in use.

`SlotsOk.unch`: the pairs survive a step that leaves their globals and blocks
alone. `SlotsOk.next`: after a step that may reallocate the pairs, each to its
old block or to one new since `m`.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word

theorem _root_.NautyVerified.Proofs.Search.lr_nat_inj {a b : Nat} (ha : a < 2147483648) (hb : b < 2147483648)
    (h : lr (a : Int) = lr (b : Int)) : a = b := by
  have := congrArg (fun x => (bv64 x).toNat) h
  simp only [bv64_repr, intOfZ_zOfInt, BitVec.toNat_ofInt] at this
  have e : ∀ x : Nat, x < 2147483648 → ((x : Int) % ((2 ^ 64 : Nat) : Int)).toNat = x := by
    intro x hx; rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp
  rw [e a ha, e b hb] at this
  exact this

/-- Two `DynAt`s of one pair agree on the block when the capacity is positive. -/
theorem _root_.NautyVerified.Proofs.Alloc.DynAt.same_cap {m : mem} {bp bs : block}
    {c c' cap cap' : Nat} {b b' : block} (h : DynAt m bp bs c cap b) (h' : DynAt m bp bs c' cap' b') :
    cap' = cap := by
  have e := h'.capLd.symm.trans h.capLd
  simp only [Option.some.injEq, val.Vlong.injEq] at e
  exact Search.lr_nat_inj h'.capLt h.capLt e

theorem _root_.NautyVerified.Proofs.Alloc.DynAt.same_block {m : mem} {bp bs : block} {c c' cap cap' : Nat} {b b' : block}
    (h : DynAt m bp bs c cap b) (h' : DynAt m bp bs c' cap' b') (hc : 0 < cap) : b' = b := by
  have hcc : cap' = cap := by
    have := h.capLd.symm.trans h'.capLd
    simp only [Option.some.injEq, val.Vlong.injEq] at this
    exact (Search.lr_nat_inj h.capLt h'.capLt this).symm
  have := (h.ptr hc).symm.trans (h'.ptr (hcc ▸ hc))
  simp only [Option.some.injEq, val.Vptr.injEq] at this
  exact this.1.symm

/-- A `DYNALLSTAT` pair: pointer global, capacity global, element size. -/
abbrev Slot := block × block × Nat

/-- The pair `p` holds `cap` elements at `b`. -/
abbrev Slot.At (m : mem) (p : Slot) (cap : Nat) (b : block) : Prop := DynAt m p.1 p.2.1 p.2.2 cap b

/-- `z` is the block of one of the pairs, in use. -/
def InUse (m : mem) (ps : List Slot) (z : block) : Prop :=
  ∃ p ∈ ps, ∃ c, 0 < c ∧ p.At m c z

/-- The pairs `ps` are `DynAt`s whose blocks in use avoid `L` and each other. -/
structure SlotsOk (m : mem) (ps : List Slot) (L : List block) : Prop where
  dyn : ∀ p ∈ ps, ∃ c b, p.At m c b
  notin : ∀ z, InUse m ps z → z ∉ L
  sep : ∀ p ∈ ps, ∀ q ∈ ps, ∀ c c' z, 0 < c → 0 < c' → p.At m c z → q.At m c' z → p = q

theorem InUse.valid {m : mem} {ps : List Slot} {z : block} (h : InUse m ps z) :
    Mem.valid_block m z := by
  obtain ⟨p, -, c, hc, d⟩ := h
  exact Malloced.valid (d.mal hc)

/-- A pair whose globals are unchanged is the same `DynAt` before. -/
theorem Slot.back_unch {m m' : mem} {W : block → Prop} {p : Slot} {c0 c : Nat} {b0 z : block}
    (d0 : p.At m c0 b0) (hu : Unch m m' W) (hp : ¬ W p.1) (hs : ¬ W p.2.1) (hc : 0 < c)
    (dz : p.At m' c z) : p.At m c z := by
  have hcc : c = c0 := by
    have := dz.capLd
    rw [hu.load _ _ _ hs, d0.capLd] at this
    simp only [Option.some.injEq, val.Vlong.injEq] at this
    exact (Search.lr_nat_inj d0.capLt dz.capLt this).symm
  subst hcc
  have := dz.ptr hc
  rw [hu.load _ _ _ hp, d0.ptr hc] at this
  simp only [Option.some.injEq, val.Vptr.injEq] at this
  exact this.1 ▸ d0

theorem SlotsOk.unch {m m' : mem} {ps : List Slot} {L : List block} (h : SlotsOk m ps L)
    {W : block → Prop} (hu : Unch m m' W) (hg : ∀ p ∈ ps, ¬ W p.1 ∧ ¬ W p.2.1)
    (hw : ∀ z, InUse m ps z → ¬ W z) :
    SlotsOk m' ps L ∧ ∀ z, InUse m' ps z → InUse m ps z := by
  have back : ∀ z, InUse m' ps z → InUse m ps z := by
    rintro z ⟨p, hp, c, hc, dz⟩
    obtain ⟨c0, b0, d0⟩ := h.dyn p hp
    exact ⟨p, hp, c, hc, Slot.back_unch d0 hu (hg p hp).1 (hg p hp).2 hc dz⟩
  refine ⟨⟨fun p hp => ?_, fun z hz => h.notin z (back z hz), ?_⟩, back⟩
  · obtain ⟨c, b, d⟩ := h.dyn p hp
    exact ⟨c, b, d.keep hu (hg p hp).1 (hg p hp).2 fun hc => Keep.unch hu (hw b ⟨p, hp, c, hc, d⟩)⟩
  · intro p hp q hq c c' z hc hc' dp dq
    obtain ⟨c0, b0, d0⟩ := h.dyn p hp
    obtain ⟨c1, b1, d1⟩ := h.dyn q hq
    exact h.sep p hp q hq c c' z hc hc' (Slot.back_unch d0 hu (hg p hp).1 (hg p hp).2 hc dp)
      (Slot.back_unch d1 hu (hg q hq).1 (hg q hq).2 hc' dq)

/-- After a step, a pair holds its old block or a block new since `m`. -/
def Slot.Next (m m' : mem) (p : Slot) : Prop :=
  ∃ c' b', p.At m' c' b' ∧ ((∀ c b, p.At m c b → c' = c ∧ (0 < c → b' = b)) ∨ ¬ Mem.valid_block m b')

theorem SlotsOk.next {m m' : mem} {ps : List Slot} {L : List block} (h : SlotsOk m ps L)
    (hL : ∀ z ∈ L, Mem.valid_block m z) (hn : ∀ p ∈ ps, Slot.Next m m' p)
    (hf : ∀ p ∈ ps, ∀ q ∈ ps, ∀ c c' z, 0 < c → 0 < c' → p.At m' c z → q.At m' c' z →
      ¬ Mem.valid_block m z → p = q) :
    SlotsOk m' ps L ∧ ∀ z, InUse m' ps z → InUse m ps z ∨ ¬ Mem.valid_block m z := by
  -- a block in use after the step: the old one of its pair, or new
  have back : ∀ p ∈ ps, ∀ c z, 0 < c → p.At m' c z → (p.At m c z) ∨ ¬ Mem.valid_block m z := by
    intro p hp c z hc dz
    obtain ⟨c', b', d', hr⟩ := hn p hp
    have hcc : c = c' := d'.same_cap dz
    subst hcc
    have hzb : z = b' := d'.same_block dz hc
    subst hzb
    rcases hr with hr | hr
    · obtain ⟨c0, b0, d0⟩ := h.dyn p hp
      obtain ⟨e1, e2⟩ := hr c0 b0 d0
      subst e1
      rw [e2 hc]
      exact .inl d0
    · exact .inr hr
  refine ⟨⟨fun p hp => ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨c', b', d', -⟩ := hn p hp
    exact ⟨c', b', d'⟩
  · rintro z ⟨p, hp, c, hc, dz⟩ hzL
    rcases back p hp c z hc dz with d | hnv
    · exact h.notin z ⟨p, hp, c, hc, d⟩ hzL
    · exact hnv (hL z hzL)
  · intro p hp q hq c c' z hc hc' dp dq
    rcases back p hp c z hc dp with d1 | hnv
    · rcases back q hq c' z hc' dq with d2 | hnv
      · exact h.sep p hp q hq c c' z hc hc' d1 d2
      · exact absurd (Malloced.valid (d1.mal hc)) hnv
    · exact hf p hp q hq c c' z hc hc' dp dq hnv
  · rintro z ⟨p, hp, c, hc, dz⟩
    rcases back p hp c z hc dz with d | hnv
    · exact .inl ⟨p, hp, c, hc, d⟩
    · exact .inr hnv

/-- An unchanged pair is a `Slot.Next`. -/
theorem Slot.next_unch {m m' : mem} {W : block → Prop} {p : Slot} {c : Nat} {b : block}
    (d : p.At m c b) (hu : Unch m m' W) (hp : ¬ W p.1) (hs : ¬ W p.2.1) (hb : 0 < c → ¬ W b) :
    Slot.Next m m' p :=
  ⟨c, b, d.keep hu hp hs fun hc => Keep.unch hu (hb hc), .inl fun _ _ d1 =>
    ⟨(d1.same_cap d), fun hc => d1.same_block d (d1.same_cap d ▸ hc)⟩⟩

/-- A pair reallocated to its old block or a new one is a `Slot.Next`. -/
theorem Slot.next_of {m m' : mem} {p : Slot} {c c' : Nat} {b b' : block} (d : p.At m c b)
    (d' : p.At m' c' b') (h : (c' = c ∧ b' = b) ∨ ¬ Mem.valid_block m b') : Slot.Next m m' p := by
  refine ⟨c', b', d', ?_⟩
  rcases h with ⟨rfl, rfl⟩ | h
  · exact .inl fun c1 b1 d1 => ⟨d1.same_cap d, fun hc => d1.same_block d (d1.same_cap d ▸ hc)⟩
  · exact .inr h

end NautyVerified.Proofs.Alloc
