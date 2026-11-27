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
    (hW : ∀ z, W z → z ∈ S.blocks ∨ ¬ Mem.valid_block m z) (hg : ∀ z ∈ workG, ¬ W z) :
    SStep m m' S :=
  ⟨⟨hu.mono fun z hz => by
      rcases hW z hz with h | h
      · exact .inl h
      · exact .inr (.inl h), hv⟩,
   WorkMono.of_unch h.work hu hg fun z hz hWz => by
     rcases hW z hWz with h' | h'
     · exact h.work_not hz h'
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
    (hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC], Keep m m' z)
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
        Program.Block.nautyCanoncodeSz, Program.Block.nautyFirsttc, Program.Block.nautyFirsttcSz],
        ¬ W z := not_W hv hW (by decide) (by decide) (by decide)
    simp only [List.forall_mem_cons] at hg hK
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, -⟩ := hg
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, -⟩ := hK
    exact { hD with
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

end NautyVerified.Proofs.Search
