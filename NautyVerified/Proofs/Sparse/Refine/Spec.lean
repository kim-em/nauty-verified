import NautyVerified.Proofs.Sparse.Refine.Wide

/-!
# The specification of `refine_sg`

`refineSgSpec`: called on a sparse graph `G` (`SparseGraphAt`), HexGraphIso's
partition `lab`, `ptn`, active set and cell count, a `code` cell, and its
scratch in the state `ScrAt` describes (the four `DYNALLSTAT` work arrays
and the two mark arrays, with `HITS` holding `int`-range naturals up to its
capacity), nausparse.c's `refine_sg` leaves memory holding
HexGraphIso's `Sparse.refine (ofGraph G) level lab ptn active numcells`: its
labelling, partition, cell count and active set, and its code in `*code`.
Afterwards the scratch is again in a `ScrAt` state, each array the old one or
a block new to memory, with at least `n` entries. Only the caller's written
blocks, the scratch and blocks new to memory change.

The precondition is `refineSpec`'s (Dispatch/Spec.lean) for the sparse graph,
together with what HexGraphIso's refinement needs beyond it: the active
positions are cell starts, and there are at most `numcells` of them.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Set (longs BitTable)
open NautyVerified.Proofs.Nextelement (LeftbitTable)
open Hex.GraphIso.Nauty (VSet)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

/-- `L` with new scratch arrays. -/
def Loc.withScr (L : Loc) (c1 : Nat) (b1 : block) (c2 : Nat) (b2 : block) (c3 : Nat) (b3 : block)
    (c4 : Nat) (b4 : block) (mc1 : Nat) (mb1 : block) (mc2 : Nat) (mb2 : block) : Loc :=
  { L with c1, b1, c2, b2, c3, b3, c4, b4, mc1, mb1, mc2, mb2 }

/-- `refine_sg`'s scratch at `L`: the work arrays' `DYNALLSTAT` pairs, `HITS`
holding `int`-range naturals up to its capacity, and the two mark arrays. -/
structure ScrAt (n : Nat) (m : mem) (L : Loc) : Prop where
  d1 : DynAt m Sparse.Block.work1 Sparse.Block.work1Sz 4 L.c1 L.b1
  d2 : DynAt m Block.work2 Block.work2Sz 4 L.c2 L.b2
  d3 : DynAt m Block.work3 Block.work3Sz 4 L.c3 L.b3
  d4 : DynAt m Block.work4 Block.work4Sz 4 L.c4 L.b4
  w3 : HitsOk m L.c3 L.b3
  k1 : ∃ st mk, MarksAt m L.mc1 L.mb1 st mk
  k2 : ∃ st mk, Marks2.MarksAt m L.mc2 L.mb2 st mk

/-- The scratch blocks of `L` in use. -/
def Loc.scrUsed (L : Loc) (z : block) : Prop :=
  (0 < L.c1 ∧ z = L.b1) ∨ (0 < L.c2 ∧ z = L.b2) ∨ (0 < L.c3 ∧ z = L.b3) ∨ (0 < L.c4 ∧ z = L.b4) ∨
    (0 < L.mc1 ∧ z = L.mb1) ∨ (0 < L.mc2 ∧ z = L.mb2)

/-- The scratch arrays' capacities and blocks. -/
def Loc.slots (L : Loc) : List (Nat × block) :=
  [(L.c1, L.b1), (L.c2, L.b2), (L.c3, L.b3), (L.c4, L.b4), (L.mc1, L.mb1), (L.mc2, L.mb2)]

/-- The globals `refine_sg` uses besides the scratch pairs. -/
def tblGlobals : List block :=
  [Sparse.Block.vmark1Val, Block.vmark2Val, Block.bit, (NautyEnv.leftbit : block)]

/-- The graph's blocks. -/
def Loc.gblocks (L : Loc) : List block := [L.bsg, L.bv, L.bd, L.be]

/-- The separation and size facts `refine_sg` needs of its locations. -/
structure SgSep (n : Nat) (m : mem) (L : Loc) : Prop where
  cdistinct : L.cblocks.Pairwise (· ≠ ·)
  cg : ∀ x ∈ L.cblocks, ∀ y ∈ L.gblocks, x ≠ y
  valid : ∀ z ∈ L.cblocks ++ L.gblocks, Mem.valid_block m z
  glob : ∀ z ∈ L.cblocks ++ L.gblocks, z ∉ scrGlobals ++ tblGlobals
  scrValid : ∀ z, L.scrUsed z → z ∉ L.cblocks ++ L.gblocks ∧ z ∉ scrGlobals ++ tblGlobals
  scrDistinct : ∀ i < 6, ∀ j < 6, i ≠ j → 0 < (L.slots.getD i (0, L.b1)).1 → 0 < (L.slots.getD j (0, L.b1)).1 →
    (L.slots.getD i (0, L.b1)).2 ≠ (L.slots.getD j (0, L.b1)).2
  n0 : 0 < n
  nlt : n < 1073741824
  nM : n ≤ 64 * L.M
  M1 : 0 < L.M
  Mlt : L.M < 33554432
  levlt : L.level < 2147483648

/-- A slot's array after an allocation between `m` and `m'`: the old one,
in use, or one new to `m` and valid in `m'`. -/
def Prov (m m' : mem) (c : Nat) (b b' : block) : Prop :=
  (b' = b ∧ 0 < c) ∨ (¬ Mem.valid_block m b' ∧ Mem.valid_block m' b')

/-- The blocks valid before the prologue that it may not move onto. -/
def Loc.base (L : Loc) : List block := L.cblocks ++ L.gblocks ++ scrGlobals ++ tblGlobals

/-- A slot's new array is none of the old blocks outside the old scratch. -/
theorem Prov.ne_base {m0 m m' : mem} {c : Nat} {b b' z : block} (h : Prov m m' c b b')
    (hmono : ∀ y, Mem.valid_block m0 y → Mem.valid_block m y) (hz : Mem.valid_block m0 z)
    (hu : 0 < c → z ≠ b) : b' ≠ z := by
  rcases h with ⟨rfl, hc⟩ | ⟨hnv, -⟩
  · exact (hu hc).symm
  · exact fun e => hnv (e ▸ hmono z hz)

/-- Two slots' new arrays, the first allocated no later than the second. -/
theorem Prov.ne {m1 m1' m2 m2' : mem} {c1 c2 : Nat} {b1 b1' b2 b2' : block}
    (h1 : Prov m1 m1' c1 b1 b1') (h2 : Prov m2 m2' c2 b2 b2')
    (hmono : ∀ y, Mem.valid_block m1' y → Mem.valid_block m2 y)
    (hv1 : 0 < c1 → Mem.valid_block m2 b1) (hv2 : 0 < c2 → Mem.valid_block m1 b2)
    (hold : 0 < c1 → 0 < c2 → b1 ≠ b2) : b1' ≠ b2' := by
  rcases h1 with ⟨rfl, hc1⟩ | ⟨hnv1, hv1'⟩ <;> rcases h2 with ⟨rfl, hc2⟩ | ⟨hnv2, hv2'⟩
  · exact hold hc1 hc2
  · exact fun e => hnv2 (e ▸ hv1 hc1)
  · exact fun e => hnv1 (e ▸ hv2 hc2)
  · exact fun e => hnv2 (e ▸ hmono _ hv1')

theorem SgSep.base_ne {n : Nat} {m : mem} {L : Loc} (hs : SgSep n m L) {z : block} (hz : z ∈ L.base)
    {c : Nat} {b : block} (hcb : 0 < c → L.scrUsed b) : 0 < c → z ≠ b := fun hc e => by
  have := hs.scrValid b (hcb hc)
  subst e
  simp only [Loc.base, List.mem_append] at hz this
  rcases hz with ((h | h) | h) | h
  · exact this.1 (.inl h)
  · exact this.1 (.inr h)
  · exact this.2 (.inl h)
  · exact this.2 (.inr h)

/-- The locations after the prologue satisfy `Ok`. -/
theorem Ok.withScr {n : Nat} {m0 m1 m2 m3 m4 m5 m6 : mem} {L : Loc} (hs : SgSep n m0 L)
    (hbv : ∀ z ∈ L.base, Mem.valid_block m0 z) (hov : ∀ z, L.scrUsed z → Mem.valid_block m0 z)
    (h01 : ∀ z, Mem.valid_block m0 z → Mem.valid_block m1 z)
    (h12 : ∀ z, Mem.valid_block m1 z → Mem.valid_block m2 z)
    (h23 : ∀ z, Mem.valid_block m2 z → Mem.valid_block m3 z)
    (h34 : ∀ z, Mem.valid_block m3 z → Mem.valid_block m4 z)
    (h45 : ∀ z, Mem.valid_block m4 z → Mem.valid_block m5 z)
    (h56 : ∀ z, Mem.valid_block m5 z → Mem.valid_block m6 z)
    {c1 c2 c3 c4 mc1 mc2 : Nat} {b1 b2 b3 b4 mb1 mb2 : block}
    (p1 : Prov m0 m1 L.c1 L.b1 b1) (p2 : Prov m1 m2 L.c2 L.b2 b2) (p3 : Prov m2 m3 L.c3 L.b3 b3)
    (p4 : Prov m3 m4 L.c4 L.b4 b4) (p5 : Prov m4 m5 L.mc1 L.mb1 mb1) (p6 : Prov m5 m6 L.mc2 L.mb2 mb2)
    (hc1 : n ≤ c1) (hc2 : n ≤ c2) (hc3 : n ≤ c3) (hc4 : n ≤ c4) (hc5 : n ≤ mc1) (hc6 : n ≤ mc2) :
    Ok n (L.withScr c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2) := by
  have u1 : 0 < L.c1 → L.scrUsed L.b1 := fun h => .inl ⟨h, rfl⟩
  have u2 : 0 < L.c2 → L.scrUsed L.b2 := fun h => .inr (.inl ⟨h, rfl⟩)
  have u3 : 0 < L.c3 → L.scrUsed L.b3 := fun h => .inr (.inr (.inl ⟨h, rfl⟩))
  have u4 : 0 < L.c4 → L.scrUsed L.b4 := fun h => .inr (.inr (.inr (.inl ⟨h, rfl⟩)))
  have u5 : 0 < L.mc1 → L.scrUsed L.mb1 := fun h => .inr (.inr (.inr (.inr (.inl ⟨h, rfl⟩))))
  have u6 : 0 < L.mc2 → L.scrUsed L.mb2 := fun h => .inr (.inr (.inr (.inr (.inr ⟨h, rfl⟩))))
  have bn : ∀ {c : Nat} {b : block}, (0 < c → L.scrUsed b) → ∀ z ∈ L.base, 0 < c → z ≠ b :=
    fun hcb z hz => hs.base_ne hz hcb
  have m02 := fun z h => h12 z (h01 z h)
  have m03 := fun z h => h23 z (m02 z h)
  have m04 := fun z h => h34 z (m03 z h)
  have m05 := fun z h => h45 z (m04 z h)
  have x1 : ∀ z ∈ L.base, b1 ≠ z := fun z hz => p1.ne_base (fun _ h => h) (hbv z hz) (bn u1 z hz)
  have x2 : ∀ z ∈ L.base, b2 ≠ z := fun z hz => p2.ne_base h01 (hbv z hz) (bn u2 z hz)
  have x3 : ∀ z ∈ L.base, b3 ≠ z := fun z hz => p3.ne_base m02 (hbv z hz) (bn u3 z hz)
  have x4 : ∀ z ∈ L.base, b4 ≠ z := fun z hz => p4.ne_base m03 (hbv z hz) (bn u4 z hz)
  have x5 : ∀ z ∈ L.base, mb1 ≠ z := fun z hz => p5.ne_base m04 (hbv z hz) (bn u5 z hz)
  have x6 : ∀ z ∈ L.base, mb2 ≠ z := fun z hz => p6.ne_base m05 (hbv z hz) (bn u6 z hz)
  have hd := hs.scrDistinct
  simp only [Loc.slots, List.getD_cons_zero, List.getD_cons_succ] at hd
  have o : ∀ (i j : Nat), i < 6 → j < 6 → i ≠ j → _ := fun i j hi hj hij => hd i hi j hj hij
  have y12 : b1 ≠ b2 := p1.ne p2 (fun _ h => h) (fun h => h01 _ (hov _ (u1 h))) (fun h => hov _ (u2 h))
    (o 0 1 (by decide) (by decide) (by decide))
  have y13 : b1 ≠ b3 := p1.ne p3 h12 (fun h => m02 _ (hov _ (u1 h))) (fun h => hov _ (u3 h))
    (o 0 2 (by decide) (by decide) (by decide))
  have y14 : b1 ≠ b4 := p1.ne p4 (fun z h => h23 z (h12 z h)) (fun h => m03 _ (hov _ (u1 h)))
    (fun h => hov _ (u4 h)) (o 0 3 (by decide) (by decide) (by decide))
  have y15 : b1 ≠ mb1 := p1.ne p5 (fun z h => h34 z (h23 z (h12 z h))) (fun h => m04 _ (hov _ (u1 h)))
    (fun h => hov _ (u5 h)) (o 0 4 (by decide) (by decide) (by decide))
  have y16 : b1 ≠ mb2 := p1.ne p6 (fun z h => h45 z (h34 z (h23 z (h12 z h))))
    (fun h => m05 _ (hov _ (u1 h))) (fun h => hov _ (u6 h)) (o 0 5 (by decide) (by decide) (by decide))
  have y23 : b2 ≠ b3 := p2.ne p3 (fun _ h => h) (fun h => m02 _ (hov _ (u2 h)))
    (fun h => h01 _ (hov _ (u3 h))) (o 1 2 (by decide) (by decide) (by decide))
  have y24 : b2 ≠ b4 := p2.ne p4 h23 (fun h => m03 _ (hov _ (u2 h))) (fun h => h01 _ (hov _ (u4 h)))
    (o 1 3 (by decide) (by decide) (by decide))
  have y25 : b2 ≠ mb1 := p2.ne p5 (fun z h => h34 z (h23 z h)) (fun h => m04 _ (hov _ (u2 h)))
    (fun h => h01 _ (hov _ (u5 h))) (o 1 4 (by decide) (by decide) (by decide))
  have y26 : b2 ≠ mb2 := p2.ne p6 (fun z h => h45 z (h34 z (h23 z h))) (fun h => m05 _ (hov _ (u2 h)))
    (fun h => h01 _ (hov _ (u6 h))) (o 1 5 (by decide) (by decide) (by decide))
  have y34 : b3 ≠ b4 := p3.ne p4 (fun _ h => h) (fun h => m03 _ (hov _ (u3 h)))
    (fun h => m02 _ (hov _ (u4 h))) (o 2 3 (by decide) (by decide) (by decide))
  have y35 : b3 ≠ mb1 := p3.ne p5 h34 (fun h => m04 _ (hov _ (u3 h))) (fun h => m02 _ (hov _ (u5 h)))
    (o 2 4 (by decide) (by decide) (by decide))
  have y36 : b3 ≠ mb2 := p3.ne p6 (fun z h => h45 z (h34 z h)) (fun h => m05 _ (hov _ (u3 h)))
    (fun h => m02 _ (hov _ (u6 h))) (o 2 5 (by decide) (by decide) (by decide))
  have y45 : b4 ≠ mb1 := p4.ne p5 (fun _ h => h) (fun h => m04 _ (hov _ (u4 h)))
    (fun h => m03 _ (hov _ (u5 h))) (o 3 4 (by decide) (by decide) (by decide))
  have y46 : b4 ≠ mb2 := p4.ne p6 h45 (fun h => m05 _ (hov _ (u4 h))) (fun h => m03 _ (hov _ (u6 h)))
    (o 3 5 (by decide) (by decide) (by decide))
  have y56 : mb1 ≠ mb2 := p5.ne p6 (fun _ h => h) (fun h => m05 _ (hov _ (u5 h)))
    (fun h => m04 _ (hov _ (u6 h))) (o 4 5 (by decide) (by decide) (by decide))
  have cd := hs.cdistinct
  simp only [Loc.cblocks, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at cd
  obtain ⟨⟨c12, c13, c14, c15⟩, ⟨c23, c24, c25⟩, ⟨c34, c35⟩, c45⟩ := cd
  have mb : ∀ z, z ∈ L.cblocks ∨ z ∈ L.gblocks ∨ z ∈ scrGlobals ∨ z ∈ tblGlobals → z ∈ L.base := by
    intro z hz
    simp only [Loc.base, List.mem_append]
    rcases hz with h | h | h | h
    · exact .inl (.inl (.inl h))
    · exact .inl (.inl (.inr h))
    · exact .inl (.inr h)
    · exact .inr h
  have c45' : L.ba ≠ L.bk := pw_ne hs.cdistinct 3 4 (by decide) (by simp [Loc.cblocks]; done)
  have cv : ∀ z ∈ L.cblocks, z ≠ Sparse.Block.vmark1Val ∧ z ≠ Block.vmark2Val := fun z hz =>
    ⟨fun e => hs.glob z (List.mem_append_left _ hz) (by rw [e]; simp [tblGlobals]),
      fun e => hs.glob z (List.mem_append_left _ hz) (by rw [e]; simp [tblGlobals])⟩
  refine
    { wdistinct := ?_, rw := ?_, n0 := hs.n0, nlt := hs.nlt, nM := hs.nM, M1 := hs.M1, Mlt := hs.Mlt,
      levlt := hs.levlt, c1 := hc1, c2 := hc2, c3 := hc3, c4 := hc4, mc1 := hc5, mc2 := hc6 }
  · simp only [Loc.withScr, Loc.wblocks, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    repeat' apply And.intro
    all_goals first
      | assumption
      | exact Ne.symm (by assumption)
      | decide
      | (refine Ne.symm (x1 _ (mb _ (.inl ?_))); simp [Loc.cblocks]; done)
      | (refine Ne.symm (x1 _ (mb _ (.inr (.inr (.inr ?_))))); decide)
      | (refine Ne.symm (x2 _ (mb _ (.inl ?_))); simp [Loc.cblocks]; done)
      | (refine Ne.symm (x2 _ (mb _ (.inr (.inr (.inr ?_))))); decide)
      | (refine Ne.symm (x3 _ (mb _ (.inl ?_))); simp [Loc.cblocks]; done)
      | (refine Ne.symm (x3 _ (mb _ (.inr (.inr (.inr ?_))))); decide)
      | (refine Ne.symm (x4 _ (mb _ (.inl ?_))); simp [Loc.cblocks]; done)
      | (refine Ne.symm (x4 _ (mb _ (.inr (.inr (.inr ?_))))); decide)
      | (refine Ne.symm (x5 _ (mb _ (.inl ?_))); simp [Loc.cblocks]; done)
      | (refine Ne.symm (x5 _ (mb _ (.inr (.inr (.inr ?_))))); decide)
      | (refine Ne.symm (x6 _ (mb _ (.inl ?_))); simp [Loc.cblocks]; done)
      | (refine Ne.symm (x6 _ (mb _ (.inr (.inr (.inr ?_))))); decide)
      | (refine x1 _ (mb _ (.inl ?_)); simp [Loc.cblocks]; done)
      | (refine x1 _ (mb _ (.inr (.inr (.inr ?_)))); decide)
      | (refine x2 _ (mb _ (.inl ?_)); simp [Loc.cblocks]; done)
      | (refine x2 _ (mb _ (.inr (.inr (.inr ?_)))); decide)
      | (refine x3 _ (mb _ (.inl ?_)); simp [Loc.cblocks]; done)
      | (refine x3 _ (mb _ (.inr (.inr (.inr ?_)))); decide)
      | (refine x4 _ (mb _ (.inl ?_)); simp [Loc.cblocks]; done)
      | (refine x4 _ (mb _ (.inr (.inr (.inr ?_)))); decide)
      | (refine x5 _ (mb _ (.inl ?_)); simp [Loc.cblocks]; done)
      | (refine x5 _ (mb _ (.inr (.inr (.inr ?_)))); decide)
      | (refine x6 _ (mb _ (.inl ?_)); simp [Loc.cblocks]; done)
      | (refine x6 _ (mb _ (.inr (.inr (.inr ?_)))); decide)
      | (refine (cv _ ?_).1; simp [Loc.cblocks]; done)
      | (refine (cv _ ?_).2; simp [Loc.cblocks]; done)
      | exact c45'
      | (intro _ h; exact h.elim)
  · intro z hz hw
    simp only [Loc.withScr, Loc.rblocks, List.mem_cons, List.mem_nil_iff, or_false] at hz
    have hzb : z ∈ L.base := by
      rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        (rw [h]; first
          | (refine mb _ (.inr (.inl ?_)); simp [Loc.gblocks]; done)
          | (refine mb _ (.inr (.inr (.inl ?_))); decide)
          | (refine mb _ (.inr (.inr (.inr ?_))); decide))
    have hzc : z ∉ L.cblocks ∧ z ≠ Sparse.Block.vmark1Val ∧ z ≠ Block.vmark2Val := by
      rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals first
        | (have hg : z ∈ L.gblocks := by rw [h]; simp [Loc.gblocks]
           exact ⟨fun hc => hs.cg z hc z hg rfl,
             fun e => hs.glob z (List.mem_append_right _ hg) (by rw [e]; decide),
             fun e => hs.glob z (List.mem_append_right _ hg) (by rw [e]; decide)⟩)
        | (have hg : z ∈ scrGlobals ++ tblGlobals := by rw [h]; decide
           have h1 : z ≠ Sparse.Block.vmark1Val := by rw [h]; decide
           have h2 : z ≠ Block.vmark2Val := by rw [h]; decide
           exact ⟨fun hc => hs.glob z (List.mem_append_left _ hc) hg, h1, h2⟩)
    simp only [Loc.writes, Loc.withScr, Loc.wblocks, List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals first
      | (refine hzc.1 ?_; rw [h]; simp [Loc.cblocks]; done)
      | exact x1 z hzb h.symm
      | exact x2 z hzb h.symm
      | exact x3 z hzb h.symm
      | exact x4 z hzb h.symm
      | exact x5 z hzb h.symm
      | exact x6 z hzb h.symm
      | exact hzc.2.1 h
      | exact hzc.2.2 h

end NautyVerified.Proofs.Sparse.Refine
