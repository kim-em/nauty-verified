import NautyVerified.Proofs.Search.Node.Rebuild

/-!
# Composable frames for the search

`SFrame m m' S` lets a step change the work blocks in use in `m`. Two such
steps compose when the work blocks in use after the first were in use before
it or are new (`WorkMono`); `SStep` is `SFrame` with that condition, and
`SStep.trans` composes. `SStep.of_unch`: a step that leaves the work arrays'
globals alone.

`SlotNext`: after a step, a `DYNALLOC` pair points at its old block or at a
block new since `m`. `WorkAt.next`: `WorkAt` again from the four pairs'
`SlotNext`. `SValid m S`: the blocks of `S` are valid in `m`, so a block new
since `m` is none of them.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open NautyVerified NautyVerified.Logic NautyVerified.Program
open NautyVerified.Proofs.Alloc (DynAt Keep Malloced)
open Hex.GraphIso.Nauty

/-- The work blocks in use in `m'` were in use in `m` or are new since `m`. -/
def WorkMono (m m' : mem) : Prop := ∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z

/-- An `SFrame` after which the work blocks in use are old ones or new ones. -/
def SStep (m m' : mem) (S : SLoc) : Prop := SFrame m m' S ∧ WorkMono m m'

/-- The blocks of `S` are valid. -/
def SValid (m : mem) (S : SLoc) : Prop := ∀ z ∈ S.blocks, Mem.valid_block m z

theorem WorkMono.refl (m : mem) : WorkMono m m := fun _ h => .inl h

theorem WorkMono.trans {m m₁ m₂ : mem} (h₁ : WorkMono m m₁)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m₁ z) (h₂ : WorkMono m₁ m₂) :
    WorkMono m m₂ := fun z hz => by
  rcases h₂ z hz with h | h
  · exact h₁ z h
  · exact .inr fun hv0 => h (hv _ hv0)

theorem SStep.refl (m : mem) (S : SLoc) : SStep m m S :=
  ⟨⟨Unch.refl _ _, fun _ h => h⟩, fun _ h => .inl h⟩

theorem SStep.trans {m m₁ m₂ : mem} {S : SLoc} (h₁ : SStep m m₁ S) (h₂ : SStep m₁ m₂ S) :
    SStep m m₂ S := by
  obtain ⟨⟨u1, v1⟩, w1⟩ := h₁
  obtain ⟨⟨u2, v2⟩, w2⟩ := h₂
  refine ⟨⟨u1.trans (u2.mono fun z hz => ?_), fun z hz => v2 _ (v1 _ hz)⟩, fun z hz => ?_⟩
  · rcases hz with h | h | h
    · exact .inl h
    · exact .inr (.inl fun hv => h (v1 _ hv))
    · rcases w1 z h with h' | h'
      · exact .inr (.inr h')
      · exact .inr (.inl h')
  · rcases w2 z hz with h | h
    · exact w1 z h
    · exact .inr fun hv => h (v1 _ hv)

theorem SValid.grow {m m' : mem} {S : SLoc} (h : SValid m S)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) : SValid m' S :=
  fun z hz => hv _ (h z hz)

/-- A pair whose globals are unchanged still points at its block, if any. -/
theorem work_slot_unch {m m' : mem} {W : block → Prop} {bp bs : block} {c cap0 cap : Nat}
    {b0 z : block} (d0 : DynAt m bp bs c cap0 b0) (hu : Unch m m' W) (hp : ¬ W bp) (hs : ¬ W bs)
    (hc : 0 < cap) (dz : DynAt m' bp bs c cap z) : ∃ k, 0 < k ∧ DynAt m bp bs c k z := by
  have hcc : cap = cap0 := by
    have := dz.capLd
    rw [hu.load _ _ _ hs, d0.capLd] at this
    simp only [Option.some.injEq, val.Vlong.injEq] at this
    exact (lr_nat_inj d0.capLt dz.capLt this).symm
  subst hcc
  have := dz.ptr hc
  rw [hu.load _ _ _ hp, d0.ptr hc] at this
  simp only [Option.some.injEq, val.Vptr.injEq] at this
  exact ⟨cap, hc, this.1 ▸ d0⟩

/-- After a step, a `DYNALLOC` pair points at its old block or at one new since `m`. -/
def SlotNext (m m' : mem) (bp bs : block) (c cap0 : Nat) (b0 : block) : Prop :=
  ∃ cap' b', DynAt m' bp bs c cap' b' ∧ ((cap' = cap0 ∧ b' = b0) ∨ ¬ Mem.valid_block m b')

theorem SlotNext.unch {m m' : mem} {W : block → Prop} {bp bs : block} {c cap0 : Nat} {b0 : block}
    (d0 : DynAt m bp bs c cap0 b0) (hu : Unch m m' W) (hp : ¬ W bp) (hs : ¬ W bs)
    (hb : 0 < cap0 → ¬ W b0) : SlotNext m m' bp bs c cap0 b0 :=
  ⟨cap0, b0, d0.keep hu hp hs fun hc => Keep.unch hu (hb hc), .inl ⟨rfl, rfl⟩⟩

/-- A block in use by a pair after a step was in use by it before, or is new. -/
theorem SlotNext.back {m m' : mem} {bp bs : block} {c cap0 : Nat} {b0 : block}
    (d0 : DynAt m bp bs c cap0 b0) (h : SlotNext m m' bp bs c cap0 b0) {cap : Nat} {z : block}
    (hc : 0 < cap) (dz : DynAt m' bp bs c cap z) :
    (∃ k, 0 < k ∧ DynAt m bp bs c k z) ∨ ¬ Mem.valid_block m z := by
  obtain ⟨cap', b', d', hb⟩ := h
  have e := dz.same_block d' hc
  have hcc : cap' = cap := by
    have := d'.capLd.symm.trans dz.capLd
    simp only [Option.some.injEq, val.Vlong.injEq] at this
    exact lr_nat_inj d'.capLt dz.capLt this
  rcases hb with ⟨h1, h2⟩ | hnv
  · left; subst h1; subst h2; rw [← e]; exact ⟨cap', hcc ▸ hc, d0⟩
  · right; rw [← e]; exact hnv

/-- `WorkMono` from the four pairs. -/
theorem WorkMono.of_slots {n : Nat} {m m' : mem} {S : SLoc} {L : List block} (h : WorkAt n m S L)
    (hn : ∀ cW bW cS bS cB bB cN bN,
      DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW bW →
      DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 cS bS →
      DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 cB bB →
      DynAt m Block.nautilWorkperm Block.nautilWorkpermSz 4 cN bN →
      SlotNext m m' Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW bW ∧
      SlotNext m m' Block.naugraphWorkset Block.naugraphWorksetSz 8 cS bS ∧
      SlotNext m m' Block.naugraphBucket Block.naugraphBucketSz 4 cB bB ∧
      SlotNext m m' Block.nautilWorkperm Block.nautilWorkpermSz 4 cN bN) :
    WorkMono m m' := by
  obtain ⟨cW, bW, cS, bS, cB, bB, cN, bN, dW, dS, dB, dN, -⟩ := h.arr
  obtain ⟨sW, sS, sB, sN⟩ := hn _ _ _ _ _ _ _ _ dW dS dB dN
  rintro z (⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩)
  · rcases sW.back dW hc d with h | h
    · exact .inl (.inl h)
    · exact .inr h
  · rcases sS.back dS hc d with h | h
    · exact .inl (.inr (.inl h))
    · exact .inr h
  · rcases sB.back dB hc d with h | h
    · exact .inl (.inr (.inr (.inl h)))
    · exact .inr h
  · rcases sN.back dN hc d with h | h
    · exact .inl (.inr (.inr (.inr h)))
    · exact .inr h

/-- `WorkMono` when the four pairs were reallocated: each new block is the old one
or new since `m`. -/
theorem WorkMono.of_four {m m' : mem} {cW cS cB cN cW' cS' cB' cN' : Nat}
    {bW bS bB bN bW' bS' bB' bN' : block}
    (dW : DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW bW)
    (dS : DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 cS bS)
    (dB : DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 cB bB)
    (dN : DynAt m Block.nautilWorkperm Block.nautilWorkpermSz 4 cN bN)
    (dW' : DynAt m' Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW' bW')
    (dS' : DynAt m' Block.naugraphWorkset Block.naugraphWorksetSz 8 cS' bS')
    (dB' : DynAt m' Block.naugraphBucket Block.naugraphBucketSz 4 cB' bB')
    (dN' : DynAt m' Block.nautilWorkperm Block.nautilWorkpermSz 4 cN' bN')
    (fW : (cW' = cW ∧ bW' = bW) ∨ ¬ Mem.valid_block m bW')
    (fS : (cS' = cS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS')
    (fB : (cB' = cB ∧ bB' = bB) ∨ ¬ Mem.valid_block m bB')
    (fN : (cN' = cN ∧ bN' = bN) ∨ ¬ Mem.valid_block m bN') : WorkMono m m' := by
  rintro z (⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩)
  · rcases SlotNext.back dW ⟨_, _, dW', fW⟩ hc d with h | h
    · exact .inl (.inl h)
    · exact .inr h
  · rcases SlotNext.back dS ⟨_, _, dS', fS⟩ hc d with h | h
    · exact .inl (.inr (.inl h))
    · exact .inr h
  · rcases SlotNext.back dB ⟨_, _, dB', fB⟩ hc d with h | h
    · exact .inl (.inr (.inr (.inl h)))
    · exact .inr h
  · rcases SlotNext.back dN ⟨_, _, dN', fN⟩ hc d with h | h
    · exact .inl (.inr (.inr (.inr h)))
    · exact .inr h

/-- `WorkMono` when naugraph's three pairs were reallocated and nautil's pair's
globals are unchanged. -/
theorem WorkMono.of_three {m m' : mem} {W : block → Prop} {cW cS cB cN cW' cS' cB' : Nat}
    {bW bS bB bN bW' bS' bB' : block}
    (dW : DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW bW)
    (dS : DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 cS bS)
    (dB : DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 cB bB)
    (dN : DynAt m Block.nautilWorkperm Block.nautilWorkpermSz 4 cN bN)
    (dW' : DynAt m' Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW' bW')
    (dS' : DynAt m' Block.naugraphWorkset Block.naugraphWorksetSz 8 cS' bS')
    (dB' : DynAt m' Block.naugraphBucket Block.naugraphBucketSz 4 cB' bB')
    (fW : (cW' = cW ∧ bW' = bW) ∨ ¬ Mem.valid_block m bW')
    (fS : (cS' = cS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS')
    (fB : (cB' = cB ∧ bB' = bB) ∨ ¬ Mem.valid_block m bB')
    (hu : Unch m m' W) (hp : ¬ W Block.nautilWorkperm) (hs : ¬ W Block.nautilWorkpermSz) :
    WorkMono m m' := by
  rintro z (⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩)
  · rcases SlotNext.back dW ⟨_, _, dW', fW⟩ hc d with h | h
    · exact .inl (.inl h)
    · exact .inr h
  · rcases SlotNext.back dS ⟨_, _, dS', fS⟩ hc d with h | h
    · exact .inl (.inr (.inl h))
    · exact .inr h
  · rcases SlotNext.back dB ⟨_, _, dB', fB⟩ hc d with h | h
    · exact .inl (.inr (.inr (.inl h)))
    · exact .inr h
  · exact .inl (.inr (.inr (.inr (work_slot_unch dN hu hp hs hc d))))

/-- The work arrays' globals. -/
abbrev workG : List block :=
  [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
   Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
   Block.nautilWorkperm, Block.nautilWorkpermSz]

/-- A step leaving the work arrays' globals and the work blocks alone. -/
theorem WorkMono.of_unch {n : Nat} {m m' : mem} {S : SLoc} {L : List block} (h : WorkAt n m S L)
    {W : block → Prop} (hu : Unch m m' W) (hg : ∀ z ∈ workG, ¬ W z) (hwk : ∀ z, IsWork m z → ¬ W z) :
    WorkMono m m' := by
  simp only [List.forall_mem_cons] at hg
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, -⟩ := hg
  refine WorkMono.of_slots h fun cW bW cS bS cB bB cN bN dW dS dB dN =>
    ⟨SlotNext.unch dW hu g1 g2 fun hc => hwk _ (.inl ⟨_, hc, dW⟩),
     SlotNext.unch dS hu g3 g4 fun hc => hwk _ (.inr (.inl ⟨_, hc, dS⟩)),
     SlotNext.unch dB hu g5 g6 fun hc => hwk _ (.inr (.inr (.inl ⟨_, hc, dB⟩))),
     SlotNext.unch dN hu g7 g8 fun hc => hwk _ (.inr (.inr (.inr ⟨_, hc, dN⟩)))⟩

theorem IsWork.valid {m : mem} {z : block} (h : IsWork m z) : Mem.valid_block m z := by
  rcases h with ⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩ <;>
    exact Alloc.Malloced.valid (d.mal hc)

/-- A step confined to blocks of `S` other than the work arrays' globals, and
to blocks new since `m`. -/
theorem SStep.of_unch {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    {W : block → Prop} (hu : Unch m m' W) (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hW : ∀ z, W z → S.Chg z ∨ ¬ Mem.valid_block m z)
    (hg : ∀ z ∈ workG, ¬ W z) :
    SStep m m' S :=
  ⟨⟨hu.mono fun z hz => by
      rcases hW z hz with h | h
      · exact .inl h
      · exact .inr (.inl h), hv⟩,
   WorkMono.of_unch h.work hu hg fun z hz hWz => by
     rcases hW z hWz with h' | h'
     · exact h.work_not hz h'.1
     · exact h' hz.valid⟩

/-- How a pair's block after a step relates to its block before. -/
abbrev SlotRel (m : mem) (c' : Nat) (b' : block) (c : Nat) (b : block) : Prop :=
  (c' = c ∧ (0 < c → b' = b)) ∨ ¬ Mem.valid_block m b'

theorem slot_ne {m : mem} {bpX bsX bpY bsY : block} {kX kY cX cY cX' cY' : Nat}
    {bX bY bX' bY' : block} (dX : DynAt m bpX bsX kX cX bX) (dY : DynAt m bpY bsY kY cY bY)
    (old : 0 < cX → 0 < cY → bX ≠ bY) (eX : SlotRel m cX' bX' cX bX) (eY : SlotRel m cY' bY' cY bY)
    (hff : ¬ Mem.valid_block m bX' → ¬ Mem.valid_block m bY' → 0 < cX' → 0 < cY' → bX' ≠ bY') :
    0 < cX' → 0 < cY' → bX' ≠ bY' := by
  intro h1 h2
  rcases eX with ⟨rfl, ex⟩ | fx <;> rcases eY with ⟨rfl, ey⟩ | fy
  · rw [ex h1, ey h2]; exact old h1 h2
  · rw [ex h1]; intro e; exact fy (e ▸ Alloc.Malloced.valid (dX.mal h1))
  · rw [ey h2]; intro e; exact fx (e ▸ Alloc.Malloced.valid (dY.mal h2))
  · exact hff fx fy h1 h2

theorem slot_notin {m : mem} {L : List block} (hL : ∀ z ∈ L, Mem.valid_block m z) {c c' : Nat}
    {b b' : block} (old : 0 < c → b ∉ L) (e : SlotRel m c' b' c b) : 0 < c' → b' ∉ L := by
  intro h hm
  rcases e with ⟨rfl, e⟩ | f
  · rw [e h] at hm; exact old h hm
  · exact f (hL _ hm)

/-- `WorkAt` after a step, from each pair's new block and how it relates to the old one. -/
theorem WorkAt.next {n : Nat} {m m' : mem} {S : SLoc} {L : List block} (h : WorkAt n m S L)
    (hL : ∀ z ∈ L, Mem.valid_block m z) {cW' cS' cB' cN' : Nat} {bW' bS' bB' bN' : block}
    (dW' : DynAt m' Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW' bW')
    (dS' : DynAt m' Block.naugraphWorkset Block.naugraphWorksetSz 8 cS' bS')
    (dB' : DynAt m' Block.naugraphBucket Block.naugraphBucketSz 4 cB' bB')
    (dN' : DynAt m' Block.nautilWorkperm Block.nautilWorkpermSz 4 cN' bN')
    (eW : ∀ c b, DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 c b → SlotRel m cW' bW' c b)
    (eS : ∀ c b, DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 c b → SlotRel m cS' bS' c b)
    (eB : ∀ c b, DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 c b → SlotRel m cB' bB' c b)
    (eN : ∀ c b, DynAt m Block.nautilWorkperm Block.nautilWorkpermSz 4 c b → SlotRel m cN' bN' c b)
    (fWS : ¬ Mem.valid_block m bW' → ¬ Mem.valid_block m bS' → 0 < cW' → 0 < cS' → bW' ≠ bS')
    (fWB : ¬ Mem.valid_block m bW' → ¬ Mem.valid_block m bB' → 0 < cW' → 0 < cB' → bW' ≠ bB')
    (fSB : ¬ Mem.valid_block m bS' → ¬ Mem.valid_block m bB' → 0 < cS' → 0 < cB' → bS' ≠ bB')
    (fNW : ¬ Mem.valid_block m bN' → ¬ Mem.valid_block m bW' → 0 < cN' → 0 < cW' → bN' ≠ bW')
    (fNS : ¬ Mem.valid_block m bN' → ¬ Mem.valid_block m bS' → 0 < cN' → 0 < cS' → bN' ≠ bS')
    (fNB : ¬ Mem.valid_block m bN' → ¬ Mem.valid_block m bB' → 0 < cN' → 0 < cB' → bN' ≠ bB') :
    WorkAt n m' S L := by
  obtain ⟨cW, bW, cS, bS, cB, bB, cN, bN, dW, dS, dB, dN, nW, nS, nB, nN, pWS, pWB, pSB, pNW,
    pNS, pNB⟩ := h.arr
  have rW := eW _ _ dW
  have rS := eS _ _ dS
  have rB := eB _ _ dB
  have rN := eN _ _ dN
  exact ⟨⟨cW', bW', cS', bS', cB', bB', cN', bN', dW', dS', dB', dN',
    slot_notin hL nW rW, slot_notin hL nS rS, slot_notin hL nB rB, slot_notin hL nN rN,
    slot_ne dW dS pWS rW rS fWS, slot_ne dW dB pWB rW rB fWB, slot_ne dS dB pSB rS rB fSB,
    slot_ne dN dW pNW rN rW fNW, slot_ne dN dS pNS rN rS fNS, slot_ne dN dB pNB rN rB fNB⟩⟩

/-- An unchanged pair. -/
theorem SlotRel.unch {m m' : mem} {W : block → Prop} {bp bs : block} {k c : Nat} {b : block}
    (d : DynAt m bp bs k c b) (hu : Unch m m' W) (hp : ¬ W bp) (hs : ¬ W bs) :
    ∀ c₁ b₁, DynAt m bp bs k c₁ b₁ → SlotRel m c b c₁ b₁ := by
  intro c₁ b₁ d₁
  have hcc : c = c₁ := by
    have := d.capLd.symm.trans d₁.capLd
    simp only [Option.some.injEq, val.Vlong.injEq] at this
    exact lr_nat_inj d.capLt d₁.capLt this
  subst hcc
  exact .inl ⟨rfl, fun hc => (d₁.same_block d hc)⟩

/-- An unchanged pair's block is not new. -/
theorem fresh_old {m : mem} {bp bs : block} {k c : Nat} {b b' : block} (d : DynAt m bp bs k c b) :
    ¬ Mem.valid_block m b → ¬ Mem.valid_block m b' → 0 < c → 0 < c' → b ≠ b' :=
  fun hnv _ hc _ => absurd (Alloc.Malloced.valid (d.mal hc)) hnv

theorem fresh_old' {m : mem} {bp bs : block} {k c : Nat} {b b' : block} (d : DynAt m bp bs k c b) :
    ¬ Mem.valid_block m b' → ¬ Mem.valid_block m b → 0 < c' → 0 < c → b' ≠ b :=
  fun _ hnv _ hc => absurd (Alloc.Malloced.valid (d.mal hc)) hnv

theorem not_W {S : SLoc} {W : block → Prop} (hv : ∀ a ∈ S.vars, ∀ b ∈ globs, a ≠ b)
    (hW : ∀ z ∈ S.blocks, W z → z ∈ S.wr ∨ z ∈ workG) {l : List block}
    (h1 : ∀ z ∈ l, z ∉ wrG) (h1' : ∀ z ∈ l, z ∉ workG) (h2 : ∀ z ∈ l, z ∈ globs) :
    ∀ z ∈ l, ¬ W z := by
  intro z hz hWz
  have hb : z ∈ S.blocks := by rw [SLoc.blocks_split]; exact List.mem_append_right _ (h2 z hz)
  rcases hW z hb hWz with h | h
  · rcases List.mem_append.1 h with h | h
    · exact h1 z hz h
    · exact hv _ (SLoc.wrV_sub _ _ h) _ (h2 z hz) rfl
  · exact h1' z hz h

/-- `SearchAt` after a step that may also reallocate the work arrays. -/
theorem SearchAt.rebuildW {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st st' : Search n}
    {pre nsp pre' nsp' : Bool} (h : SearchAt m S ctx st pre nsp) {W : block → Prop}
    (hu : Unch m m' W) (hW : ∀ z ∈ S.blocks, W z → z ∈ S.wr ∨ z ∈ workG)
    (hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws], Keep m m' z)
    (hsc : Scalars m' st' nsp') (hst : Stats m' S st' pre') (har : Arrays m' S ctx st')
    (hinv : SInv st') (hwk : WorkAt n m' S S.blocks) : SearchAt m' S ctx st' pre' nsp' := by
  have hd := h.distinct
  have hv := SLoc.vars_ne hd
  have hdy : Dyns n m' S := by
    have hD := h.dyns
    have hg : ∀ z ∈ [Program.Block.nautyActive, Program.Block.nautyActiveSz,
        Program.Block.nautyFixedpts, Program.Block.nautyFixedptsSz, Program.Block.nautyWorkperm,
        Program.Block.nautyWorkpermSz, Program.Block.nautyFirstlab, Program.Block.nautyFirstlabSz,
        Program.Block.nautyCanonlab, Program.Block.nautyCanonlabSz, Program.Block.nautyFirstcode,
        Program.Block.nautyFirstcodeSz, Program.Block.nautyCanoncode,
        Program.Block.nautyCanoncodeSz, Program.Block.nautyFirsttc, Program.Block.nautyFirsttcSz,
        Block.naugraphDnwork, Block.naugraphDnworkSz],
        ¬ W z := not_W hv hW (by decide) (by decide) (by decide)
    simp only [List.forall_mem_cons] at hg hK
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, -⟩ := hg
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, -⟩ := hK
    exact { hD with
      workspace := hD.workspace.keep hu g17 g18 fun _ => k9
      active := hD.active.keep hu g1 g2 fun _ => k1
      fixedpts := hD.fixedpts.keep hu g3 g4 fun _ => k2
      workperm := hD.workperm.keep hu g5 g6 fun _ => k3
      firstlab := hD.firstlab.keep hu g7 g8 fun _ => k4
      canonlab := hD.canonlab.keep hu g9 g10 fun _ => k5
      firstcode := hD.firstcode.keep hu g11 g12 fun _ => k6
      canoncode := hD.canoncode.keep hu g13 g14 fun _ => k7
      firsttc := hD.firsttc.keep hu g15 g16 fun _ => k8 }
  exact
    { h with
      fixed := h.fixed.unch hu (not_W hv hW (by decide) (by decide) (by decide))
      scalars := hsc
      stats := hst
      arrays := har
      dyns := hdy
      work := hwk
      tables := h.tables.unch hu (not_W hv hW (by decide) (by decide) (by decide))
      inv := hinv }

/-- With capacity 0 a pair says nothing about its block. -/
theorem _root_.NautyVerified.Proofs.Alloc.DynAt.cap0 {m : mem} {bp bs : block} {c : Nat} {b : block} (h : DynAt m bp bs c 0 b)
    (b' : block) : DynAt m bp bs c 0 b' :=
  { h with ptr := fun h0 => absurd h0 (Nat.lt_irrefl 0), mal := fun h0 => absurd h0 (Nat.lt_irrefl 0),
           bne := fun h0 => absurd h0 (Nat.lt_irrefl 0) }

theorem SlotRel.next {m m' : mem} {bp bs : block} {k c' c : Nat} {b' b : block}
    (d' : DynAt m' bp bs k c' b') (r : SlotRel m c' b' c b) : SlotNext m m' bp bs k c b := by
  rcases r with ⟨rfl, hb⟩ | hf
  · by_cases hc : 0 < c'
    · exact ⟨c', b', d', .inl ⟨rfl, hb hc⟩⟩
    · have : c' = 0 := by omega
      subst this
      exact ⟨0, b, d'.cap0 b, .inl ⟨rfl, rfl⟩⟩
  · exact ⟨c', b', d', .inr hf⟩

theorem ArrayAt.valid {m : mem} {chunk : Common.AST.memory_chunk} {b : block} {base : Int}
    {vals : Nat → val} {k : Nat} (h : ArrayAt m chunk b base vals k) (hk : 0 < k) :
    Mem.valid_block m b :=
  Alloc.valid_of_access (h.writable 0 hk)

/-- A pair's new block, related to its block before by the callee, related to
any `DynAt` of the pair before. -/
theorem SlotRel.of_old {m : mem} {bp bs : block} {k c c' : Nat} {b b' : block}
    (d : DynAt m bp bs k c b) (h : (c' = c ∧ b' = b) ∨ ¬ Mem.valid_block m b') :
    ∀ c₁ b₁, DynAt m bp bs k c₁ b₁ → SlotRel m c' b' c₁ b₁ := by
  intro c₁ b₁ d₁
  have hcc : c = c₁ := by
    have := d.capLd.symm.trans d₁.capLd
    simp only [Option.some.injEq, val.Vlong.injEq] at this
    exact lr_nat_inj d.capLt d₁.capLt this
  subst hcc
  rcases h with ⟨rfl, rfl⟩ | hf
  · exact .inl ⟨rfl, fun hc => d₁.same_block d hc⟩
  · exact .inr hf

/-- After a call that reallocates only naugraph.c's `workperm`. -/
theorem SearchAt.afterWP {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) (hval : ∀ z ∈ S.blocks, Mem.valid_block m z)
    {cW : Nat} {bW : block} (dW : DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW bW)
    {W : block → Prop} (hu : Unch m m' W)
    (hW : ∀ z, W z → (z ∈ S.blocks ∧ z ∉ [Block.naugraphWorkset, Block.naugraphWorksetSz,
      Block.naugraphBucket, Block.naugraphBucketSz, Block.nautilWorkperm, Block.nautilWorkpermSz]) ∨
      (0 < cW ∧ z = bW) ∨ (z ∉ S.blocks ∧ ¬ IsWork m z))
    {cap' : Nat} {b' : block} (dW' : DynAt m' Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cap' b')
    (hrel : (cap' = cW ∧ b' = bW) ∨ ¬ Mem.valid_block m b') :
    WorkMono m m' ∧ WorkAt n m' S S.blocks := by
  obtain ⟨cW0, bW0, cS, bS, cB, bB, cN, bN, dW0, dS, dB, dN, nW, nS, nB, nN, pWS, pWB, pSB, pNW,
    pNS, pNB⟩ := h.work.arr
  have hcW : cW0 = cW := by
    have := dW0.capLd.symm.trans dW.capLd
    simp only [Option.some.injEq, val.Vlong.injEq] at this
    exact lr_nat_inj dW0.capLt dW.capLt this
  subst hcW
  have hbW : 0 < cW0 → bW0 = bW := fun hc => dW.same_block dW0 hc
  have gl : ∀ z ∈ [Block.naugraphWorkset, Block.naugraphWorksetSz, Block.naugraphBucket,
      Block.naugraphBucketSz, Block.nautilWorkperm, Block.nautilWorkpermSz], ¬ W z := by
    intro z hz hWz
    have hzb : z ∈ S.blocks := by
      rw [SLoc.blocks_split]; exact List.mem_append_right _ ((by decide : ∀ y ∈ [Block.naugraphWorkset, Block.naugraphWorksetSz, Block.naugraphBucket,
      Block.naugraphBucketSz, Block.nautilWorkperm, Block.nautilWorkpermSz], y ∈ globs) z hz)
    rcases hW z hWz with ⟨-, h1⟩ | ⟨hc, rfl⟩ | ⟨h1, -⟩
    · exact h1 hz
    · exact nW hc (hbW hc ▸ hzb)
    · exact h1 hzb
  simp only [List.forall_mem_cons] at gl
  obtain ⟨g1, g2, g3, g4, g5, g6, -⟩ := gl
  have wb : ∀ {c : Nat} {b : block}, 0 < c → b ∉ S.blocks → IsWork m b → (0 < cW0 → b ≠ bW0) →
      ¬ W b := by
    intro c b hc hb hwb hne hWb
    rcases hW b hWb with ⟨h1, -⟩ | ⟨hc', rfl⟩ | ⟨-, h1⟩
    · exact hb h1
    · exact hne hc' (hbW hc').symm
    · exact h1 hwb
  have dS' := dS.keep hu g1 g2 fun hc => Keep.unch hu (wb hc (nS hc) (.inr (.inl ⟨_, hc, dS⟩))
    fun hc' e => pWS hc' hc e.symm)
  have dB' := dB.keep hu g3 g4 fun hc => Keep.unch hu (wb hc (nB hc) (.inr (.inr (.inl ⟨_, hc, dB⟩)))
    fun hc' e => pWB hc' hc e.symm)
  have dN' := dN.keep hu g5 g6 fun hc => Keep.unch hu (wb hc (nN hc) (.inr (.inr (.inr ⟨_, hc, dN⟩)))
    fun hc' e => pNW hc hc' e)
  have rW := SlotRel.of_old dW hrel
  have rS := SlotRel.unch dS hu g1 g2
  have rB := SlotRel.unch dB hu g3 g4
  have rN := SlotRel.unch dN hu g5 g6
  refine ⟨WorkMono.of_slots h.work fun c1 b1 c2 b2 c3 b3 c4 b4 d1 d2 d3 d4 =>
      ⟨SlotRel.next dW' (rW _ _ d1), SlotRel.next dS' (rS _ _ d2), SlotRel.next dB' (rB _ _ d3),
        SlotRel.next dN' (rN _ _ d4)⟩,
    WorkAt.next h.work hval dW' dS' dB' dN' rW rS rB rN
      (fresh_old' dS) (fresh_old' dB) (fresh_old dS) (fresh_old dN) (fresh_old dN)
      (fresh_old dN)⟩

/-- After a call that reallocates naugraph.c's `workperm` and `workset`. -/
theorem SearchAt.afterWPWS {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) (hval : ∀ z ∈ S.blocks, Mem.valid_block m z)
    {cW cS : Nat} {bW bS : block}
    (dW : DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW bW)
    (dS : DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 cS bS)
    {W : block → Prop} (hu : Unch m m' W)
    (hW : ∀ z, W z → (z ∈ S.blocks ∧ z ∉ [Block.naugraphBucket, Block.naugraphBucketSz,
      Block.nautilWorkperm, Block.nautilWorkpermSz]) ∨
      (0 < cW ∧ z = bW) ∨ (0 < cS ∧ z = bS) ∨ (z ∉ S.blocks ∧ ¬ IsWork m z))
    {cW' cS' : Nat} {bW' bS' : block}
    (dW' : DynAt m' Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW' bW')
    (dS' : DynAt m' Block.naugraphWorkset Block.naugraphWorksetSz 8 cS' bS')
    (hrW : (cW' = cW ∧ bW' = bW) ∨ ¬ Mem.valid_block m bW')
    (hrS : (cS' = cS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS')
    (hne : 0 < cW' → 0 < cS' → bW' ≠ bS') :
    WorkMono m m' ∧ WorkAt n m' S S.blocks := by
  obtain ⟨cW0, bW0, cS0, bS0, cB, bB, cN, bN, dW0, dS0, dB, dN, nW, nS, nB, nN, pWS, pWB, pSB, pNW,
    pNS, pNB⟩ := h.work.arr
  have hcW : cW0 = cW := by
    have := dW0.capLd.symm.trans dW.capLd
    simp only [Option.some.injEq, val.Vlong.injEq] at this
    exact lr_nat_inj dW0.capLt dW.capLt this
  have hcS : cS0 = cS := by
    have := dS0.capLd.symm.trans dS.capLd
    simp only [Option.some.injEq, val.Vlong.injEq] at this
    exact lr_nat_inj dS0.capLt dS.capLt this
  subst hcW hcS
  have hbW : 0 < cW0 → bW0 = bW := fun hc => dW.same_block dW0 hc
  have hbS : 0 < cS0 → bS0 = bS := fun hc => dS.same_block dS0 hc
  have gl : ∀ z ∈ [Block.naugraphBucket, Block.naugraphBucketSz, Block.nautilWorkperm,
      Block.nautilWorkpermSz], ¬ W z := by
    intro z hz hWz
    have hzb : z ∈ S.blocks := by
      rw [SLoc.blocks_split]; exact List.mem_append_right _ ((by decide : ∀ y ∈ [Block.naugraphBucket,
        Block.naugraphBucketSz, Block.nautilWorkperm, Block.nautilWorkpermSz], y ∈ globs) z hz)
    rcases hW z hWz with ⟨-, h1⟩ | ⟨hc, rfl⟩ | ⟨hc, rfl⟩ | ⟨h1, -⟩
    · exact h1 hz
    · exact nW hc (hbW hc ▸ hzb)
    · exact nS hc (hbS hc ▸ hzb)
    · exact h1 hzb
  simp only [List.forall_mem_cons] at gl
  obtain ⟨g3, g4, g5, g6, -⟩ := gl
  have wb : ∀ {c : Nat} {b : block}, 0 < c → b ∉ S.blocks → IsWork m b → (0 < cW0 → b ≠ bW0) →
      (0 < cS0 → b ≠ bS0) → ¬ W b := by
    intro c b hc hb hwb hne1 hne2 hWb
    rcases hW b hWb with ⟨h1, -⟩ | ⟨hc', rfl⟩ | ⟨hc', rfl⟩ | ⟨-, h1⟩
    · exact hb h1
    · exact hne1 hc' (hbW hc').symm
    · exact hne2 hc' (hbS hc').symm
    · exact h1 hwb
  have dB' := dB.keep hu g3 g4 fun hc => Keep.unch hu (wb hc (nB hc) (.inr (.inr (.inl ⟨_, hc, dB⟩)))
    (fun hc' e => pWB hc' hc e.symm) fun hc' e => pSB hc' hc e.symm)
  have dN' := dN.keep hu g5 g6 fun hc => Keep.unch hu (wb hc (nN hc) (.inr (.inr (.inr ⟨_, hc, dN⟩)))
    (fun hc' e => pNW hc hc' e) fun hc' e => pNS hc hc' e)
  have rW := SlotRel.of_old dW hrW
  have rS := SlotRel.of_old dS hrS
  have rB := SlotRel.unch dB hu g3 g4
  have rN := SlotRel.unch dN hu g5 g6
  refine ⟨WorkMono.of_slots h.work fun c1 b1 c2 b2 c3 b3 c4 b4 d1 d2 d3 d4 =>
      ⟨SlotRel.next dW' (rW _ _ d1), SlotRel.next dS' (rS _ _ d2), SlotRel.next dB' (rB _ _ d3),
        SlotRel.next dN' (rN _ _ d4)⟩,
    WorkAt.next h.work hval dW' dS' dB' dN' rW rS rB rN
      (fun _ _ => hne) (fresh_old' dB) (fresh_old' dB) (fresh_old dN) (fresh_old dN)
      (fresh_old dN)⟩

/-- After a call that reallocates only nautil.c's `workperm`. -/
theorem SearchAt.afterN {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) (hval : ∀ z ∈ S.blocks, Mem.valid_block m z)
    {cN : Nat} {bN : block} (dN : DynAt m Block.nautilWorkperm Block.nautilWorkpermSz 4 cN bN)
    {W : block → Prop} (hu : Unch m m' W)
    (hW : ∀ z, W z → (z ∈ S.blocks ∧ z ∉ [Block.naugraphWorkperm, Block.naugraphWorkpermSz,
      Block.naugraphWorkset, Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz]) ∨
      (0 < cN ∧ z = bN) ∨ (z ∉ S.blocks ∧ ¬ IsWork m z))
    {cap' : Nat} {b' : block} (dN' : DynAt m' Block.nautilWorkperm Block.nautilWorkpermSz 4 cap' b')
    (hrel : (cap' = cN ∧ b' = bN) ∨ ¬ Mem.valid_block m b') :
    WorkMono m m' ∧ WorkAt n m' S S.blocks := by
  obtain ⟨cW, bW, cS, bS, cB, bB, cN0, bN0, dW, dS, dB, dN0, nW, nS, nB, nN, pWS, pWB, pSB, pNW,
    pNS, pNB⟩ := h.work.arr
  have hcN : cN0 = cN := by
    have := dN0.capLd.symm.trans dN.capLd
    simp only [Option.some.injEq, val.Vlong.injEq] at this
    exact lr_nat_inj dN0.capLt dN.capLt this
  subst hcN
  have hbN : 0 < cN0 → bN0 = bN := fun hc => dN.same_block dN0 hc
  have gl : ∀ z ∈ [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
      Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz], ¬ W z := by
    intro z hz hWz
    have hzb : z ∈ S.blocks := by
      rw [SLoc.blocks_split]; exact List.mem_append_right _ ((by decide : ∀ y ∈ [Block.naugraphWorkperm,
        Block.naugraphWorkpermSz, Block.naugraphWorkset, Block.naugraphWorksetSz,
        Block.naugraphBucket, Block.naugraphBucketSz], y ∈ globs) z hz)
    rcases hW z hWz with ⟨-, h1⟩ | ⟨hc, rfl⟩ | ⟨h1, -⟩
    · exact h1 hz
    · exact nN hc (hbN hc ▸ hzb)
    · exact h1 hzb
  simp only [List.forall_mem_cons] at gl
  obtain ⟨g1, g2, g3, g4, g5, g6, -⟩ := gl
  have wb : ∀ {c : Nat} {b : block}, 0 < c → b ∉ S.blocks → IsWork m b → (0 < cN0 → b ≠ bN0) →
      ¬ W b := by
    intro c b hc hb hwb hne hWb
    rcases hW b hWb with ⟨h1, -⟩ | ⟨hc', rfl⟩ | ⟨-, h1⟩
    · exact hb h1
    · exact hne hc' (hbN hc').symm
    · exact h1 hwb
  have dW' := dW.keep hu g1 g2 fun hc => Keep.unch hu (wb hc (nW hc) (.inl ⟨_, hc, dW⟩)
    fun hc' e => pNW hc' hc e.symm)
  have dS' := dS.keep hu g3 g4 fun hc => Keep.unch hu (wb hc (nS hc) (.inr (.inl ⟨_, hc, dS⟩))
    fun hc' e => pNS hc' hc e.symm)
  have dB' := dB.keep hu g5 g6 fun hc => Keep.unch hu (wb hc (nB hc) (.inr (.inr (.inl ⟨_, hc, dB⟩)))
    fun hc' e => pNB hc' hc e.symm)
  have rW := SlotRel.unch dW hu g1 g2
  have rS := SlotRel.unch dS hu g3 g4
  have rB := SlotRel.unch dB hu g5 g6
  have rN := SlotRel.of_old dN hrel
  refine ⟨WorkMono.of_slots h.work fun c1 b1 c2 b2 c3 b3 c4 b4 d1 d2 d3 d4 =>
      ⟨SlotRel.next dW' (rW _ _ d1), SlotRel.next dS' (rS _ _ d2), SlotRel.next dB' (rB _ _ d3),
        SlotRel.next dN' (rN _ _ d4)⟩,
    WorkAt.next h.work hval dW' dS' dB' dN' rW rS rB rN
      (fresh_old dW) (fresh_old dW) (fresh_old dS) (fresh_old' dW) (fresh_old' dS)
      (fresh_old' dB)⟩

/-! ### For any dispatch representation

`WorkMonoG`, `SStepG`, `SValidG`: the frames above for `SearchAtG D`.
`WorkG.step`: the scratch state after a call of one of `D`'s procedures
(`DispatchRep.Step`) whose outputs avoid nautil.c's `workperm` pair; this is
what replaces the dense `afterWP`/`afterWPWS` family for a dispatch call. -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep envAvoid)

variable {ge : Cfrontend.Clight.genv} [E : NautyEnv ge] {O : Ops} (D : DispatchRep ge O)

/-- `WorkMono` for `D`. -/
def WorkMonoG (m m' : mem) : Prop := ∀ z, IsWorkG D m' z → IsWorkG D m z ∨ ¬ Mem.valid_block m z

/-- `SStep` for `D`. -/
def SStepG (m m' : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) : Prop :=
  SFrameG D m m' S gl cl ∧ WorkMonoG D m m'

/-- `SValid` for `D`. -/
def SValidG (m : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) : Prop :=
  ∀ z ∈ S.blocksG D gl cl, Mem.valid_block m z

variable {D}

theorem WorkMonoG.refl (m : mem) : WorkMonoG D m m := fun _ h => .inl h

theorem WorkMonoG.trans {m m₁ m₂ : mem} (h₁ : WorkMonoG D m m₁)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m₁ z) (h₂ : WorkMonoG D m₁ m₂) :
    WorkMonoG D m m₂ := fun z hz => by
  rcases h₂ z hz with h | h
  · exact h₁ z h
  · exact .inr fun hv0 => h (hv _ hv0)

theorem SStepG.refl (m : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) : SStepG D m m S gl cl :=
  ⟨⟨Unch.refl _ _, fun _ h => h⟩, fun _ h => .inl h⟩

theorem SStepG.trans {m m₁ m₂ : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    (h₁ : SStepG D m m₁ S gl cl) (h₂ : SStepG D m₁ m₂ S gl cl) : SStepG D m m₂ S gl cl := by
  obtain ⟨⟨u1, v1⟩, w1⟩ := h₁
  obtain ⟨⟨u2, v2⟩, w2⟩ := h₂
  refine ⟨⟨u1.trans (u2.mono fun z hz => ?_), fun z hz => v2 _ (v1 _ hz)⟩, fun z hz => ?_⟩
  · rcases hz with h | h | h
    · exact .inl h
    · exact .inr (.inl fun hv => h (v1 _ hv))
    · rcases w1 z h with h' | h'
      · exact .inr (.inr h')
      · exact .inr (.inl h')
  · rcases w2 z hz with h | h
    · exact w1 z h
    · exact .inr fun hv => h (v1 _ hv)

theorem SValidG.grow {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    (h : SValidG D m S gl cl) (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) :
    SValidG D m' S gl cl :=
  fun z hz => hv _ (h z hz)

theorem IsWorkG.valid {m : mem} {z : block} (h : IsWorkG D m z) : Mem.valid_block m z := by
  rcases h with h | ⟨c, hc, d⟩
  · exact D.isWork_valid h
  · exact Alloc.Malloced.valid (d.mal hc)

/-- A step confined to blocks of `S` other than `D`'s written globals and
nautil.c's `workperm` pair, and to blocks new since `m`. -/
theorem SStepG.of_unch {n : Nat} {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp)
    {W : block → Prop} (hu : Unch m m' W) (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hW : ∀ z, W z → S.ChgG D gl cl z ∨ ¬ Mem.valid_block m z)
    (hg : ∀ z ∈ D.wglobs, ¬ W z) (hN : ¬ W E.nautilWorkperm ∧ ¬ W E.nautilWorkpermSz) :
    SStepG D m m' S gl cl := by
  have hwk : ∀ z, IsWorkG D m z → ¬ W z := fun z hz hWz => by
    rcases hW z hWz with h' | h'
    · exact h.work_not hz h'.1
    · exact h' hz.valid
  refine ⟨⟨hu.mono fun z hz => ?_, hv⟩, fun z hz =>
    .inl ((h.work.unch hu hg hN hwk hv).2 z hz)⟩
  rcases hW z hz with h | h
  · exact .inl h
  · exact .inr (.inl h)

/-- The scratch state after a call of one of `D`'s procedures whose outputs are
none of nautil.c's `workperm` pair and its block. -/
theorem WorkG.step {m m' : mem} {L : List block} {out : block → Prop} (h : WorkG D m L)
    (hs : D.Step m m' out) (hL : ∀ z ∈ L, Mem.valid_block m z)
    (hgL : ∀ z ∈ D.globs, z ∈ L)
    (hN : ∀ z, out z → z ≠ E.nautilWorkperm ∧ z ≠ E.nautilWorkpermSz ∧
      ∀ c b, DynAt m E.nautilWorkperm E.nautilWorkpermSz 4 c b → 0 < c → z ≠ b)
    (hNL : E.nautilWorkperm ∈ L ∧ E.nautilWorkpermSz ∈ L) :
    WorkG D m' L ∧ WorkMonoG D m m' := by
  obtain ⟨cN, bN, dN, nN, uN⟩ := h.nautil
  have eA : E.nautilWorkperm ∈ envAvoid ∧ E.nautilWorkpermSz ∈ envAvoid := by simp
  have eB : E.nautilWorkperm ∈ E.blocks ∧ E.nautilWorkpermSz ∈ E.blocks := by
    simp [NautyEnv.blocks]
  have keepG : ∀ z, z ∈ envAvoid → z ∈ E.blocks → z ∈ L → ¬ out z →
      ¬ (out z ∨ z ∈ D.wglobs ∨ D.IsWork m z ∨ ¬ Mem.valid_block m z) := by
    rintro z hA hE hzL ho (h1 | h1 | h1 | h1)
    · exact ho h1
    · exact D.globs_env _ (D.wglobs_sub _ h1) hE
    · exact (D.isWork_globs h.disp h1).2 hA
    · exact h1 (hL z hzL)
  have keepB : 0 < cN → ¬ (out bN ∨ bN ∈ D.wglobs ∨ D.IsWork m bN ∨ ¬ Mem.valid_block m bN) := by
    rintro hc (h1 | h1 | h1 | h1)
    · exact (hN _ h1).2.2 cN bN dN hc rfl
    · exact nN hc (hgL _ (D.wglobs_sub _ h1))
    · exact uN hc h1
    · exact h1 (Alloc.Malloced.valid (dN.mal hc))
  have dN' : DynAt m' E.nautilWorkperm E.nautilWorkpermSz 4 cN bN :=
    dN.keep hs.unch
      (keepG _ eA.1 eB.1 hNL.1 fun ho => (hN _ ho).1 rfl)
      (keepG _ eA.2 eB.2 hNL.2 fun ho => (hN _ ho).2.1 rfl)
      fun hc => Keep.unch hs.unch (keepB hc)
  refine ⟨⟨hs.work, ⟨cN, bN, dN', nN, fun hc hb => ?_⟩, fun z hz hzL => ?_⟩, ?_⟩
  · rcases hs.mono bN hb with h1 | h1
    · exact uN hc h1
    · exact h1 (Alloc.Malloced.valid (dN.mal hc))
  · rcases hs.mono z hz with h1 | h1
    · exact h.notin z h1 hzL
    · exact h1 (hL z hzL)
  · rintro z (hz | ⟨c, hc, d⟩)
    · exact (hs.mono z hz).imp .inl id
    · have e := d.same_block dN' hc
      have hcc := d.same_cap dN'
      subst e; subst hcc
      exact .inl (.inr ⟨_, hc, dN⟩)

end Generic

end NautyVerified.Proofs.Search
