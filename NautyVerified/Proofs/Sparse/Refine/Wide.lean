import NautyVerified.Proofs.Sparse.Refine.Pieces

/-!
# Memory changes wider than `Frame`

`Frame L` lets only `refine_sg`'s written blocks and new blocks change. Its
prologue (the four `DYNALLOC1`s and the two `preparemarks`) and the
`distvals` call also change the work and mark pointer and size globals, and
may move a work or mark array to a new block, so the `Loc` changes.
`WFrame L m m'`: only `L`'s written blocks, the scratch globals and blocks
not valid in `m` change; the caller's blocks keep their permissions and
headers; valid blocks stay valid. `WFrame.trans` composes two such changes
across a change of `Loc` whose new blocks are old ones or new to memory.

`Mem.swap4`: after `distvals`, which writes `work3` and may move `work4`,
memory holds the same state with `work4` at its new block.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- The pointer and size globals of the work and mark arrays. -/
def scrGlobals : List block :=
  [Sparse.Block.work1, Sparse.Block.work1Sz, Block.work2, Block.work2Sz, Block.work3,
   Block.work3Sz, Block.work4, Block.work4Sz, Sparse.Block.vmark1, Sparse.Block.vmark1Sz,
   Block.vmark2, Block.vmark2Sz]

/-- The caller's blocks `refine_sg` writes. -/
def Loc.cblocks (L : Loc) : List block := [L.bl, L.bp, L.bn, L.ba, L.bk]

/-- The blocks the prologue and `distvals` may change, besides new ones. -/
def Loc.Wide (L : Loc) (z : block) : Prop := L.writes z ∨ z ∈ scrGlobals

/-- A memory change of `refine_sg` that may also move its scratch. -/
structure WFrame (L : Loc) (m m' : mem) : Prop where
  unch : Unch m m' (fun z => L.Wide z ∨ ¬ Mem.valid_block m z)
  keep : ∀ z ∈ L.cblocks, Keep m m' z
  valid : ∀ z, Mem.valid_block m z → Mem.valid_block m' z

theorem WFrame.refl (L : Loc) (m : mem) : WFrame L m m :=
  ⟨Unch.refl _ _, fun z _ => Keep.refl m z, fun _ h => h⟩

theorem Frame.wide {m m' : mem} (h : Frame L m m') (hv : ∀ z ∈ L.cblocks, Mem.valid_block m z) :
    WFrame L m m' :=
  ⟨h.unch.mono fun _ hz => hz.imp_left .inl, fun z hz => h.keep z (hv z hz), h.valid⟩

/-- Two changes, the second at a `Loc` whose blocks are `L`'s or new, with the
same caller's blocks. -/
theorem WFrame.trans {L' : Loc} {m₁ m₂ m₃ : mem} (h₁ : WFrame L m₁ m₂) (h₂ : WFrame L' m₂ m₃)
    (hL : ∀ z, L'.Wide z → L.Wide z ∨ ¬ Mem.valid_block m₁ z) (hc : L'.cblocks = L.cblocks) :
    WFrame L m₁ m₃ :=
  ⟨h₁.unch.trans (h₂.unch.mono fun z hz => by
      rcases hz with hz | hz
      · exact hL z hz
      · exact .inr fun h => hz (h₁.valid z h)),
    fun z hz => (h₁.keep z hz).trans (h₂.keep z (hc ▸ hz)),
    fun z hz => h₂.valid z (h₁.valid z hz)⟩

theorem Ok.wr {L : Loc} (hok : Ok n L) {z y : block} (hz : z ∈ L.wblocks) (hy : y ∈ L.rblocks) :
    z ≠ y := fun e => hok.rw y hy (e ▸ hz)

theorem arr_valid {m : mem} {chunk : memory_chunk} {b : block} {base : Int} {vals : Nat → val}
    {k : Nat} (h : ArrayAt m chunk b base vals k) (hk : 0 < k) : Mem.valid_block m b :=
  Alloc.valid_of_access (h.writable 0 hk)

/-- The blocks `refine_sg` writes are valid. -/
theorem Mem.wvalid {m : mem} (hok : Ok n L) (hm : Mem m L G t S) :
    ∀ z ∈ L.wblocks, Mem.valid_block m z := by
  have h0 := hok.n0
  have hM := hok.M1
  intro z hz
  simp only [Loc.wblocks, List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact arr_valid hm.lab h0
  · exact arr_valid hm.ptn h0
  · exact arr_valid hm.nc (by decide)
  · exact arr_valid hm.act hM
  · obtain ⟨_, h⟩ := hm.code; exact arr_valid h (by decide)
  · exact Alloc.Malloced.valid (hm.d1.mal (by have := hok.c1; omega))
  · exact Alloc.Malloced.valid (hm.d2.mal (by have := hok.c2; omega))
  · exact Alloc.Malloced.valid (hm.d3.mal (by have := hok.c3; omega))
  · exact Alloc.Malloced.valid (hm.d4.mal (by have := hok.c4; omega))
  · exact Alloc.Malloced.valid (hm.k1.dyn.mal (by have := hok.mc1; omega))
  · exact Alloc.Malloced.valid (hm.k2.dyn.mal (by have := hok.mc2; omega))
  · exact Alloc.valid_of_access hm.k1.valW
  · exact Alloc.valid_of_access hm.k2.valW

/-- The blocks `refine_sg` reads are valid, given that the graph's edge array is. -/
theorem Mem.rvalid {m : mem} (hok : Ok n L) (hm : Mem m L G t S) (hbe : Mem.valid_block m L.be) :
    ∀ z ∈ L.rblocks, Mem.valid_block m z := by
  have h0 := hok.n0
  intro z hz
  simp only [Loc.rblocks, List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ hm.graph.v)
  · exact arr_valid hm.graph.varr h0
  · exact arr_valid hm.graph.darr h0
  · exact hbe
  · exact Alloc.valid_of_access hm.d1.bpW
  · exact Alloc.valid_of_access hm.d1.bsW
  · exact Alloc.valid_of_access hm.d2.bpW
  · exact Alloc.valid_of_access hm.d2.bsW
  · exact Alloc.valid_of_access hm.d3.bpW
  · exact Alloc.valid_of_access hm.d3.bsW
  · exact Alloc.valid_of_access hm.d4.bpW
  · exact Alloc.valid_of_access hm.d4.bsW
  · exact Alloc.valid_of_access hm.k1.dyn.bpW
  · exact Alloc.valid_of_access hm.k1.dyn.bsW
  · exact Alloc.valid_of_access hm.k2.dyn.bpW
  · exact Alloc.valid_of_access hm.k2.dyn.bsW
  · exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ (hm.bit 0 (by decide)))
  · exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ (hm.left 0 (by decide)))

/-- The graph's blocks are none of `work4`'s globals. -/
def GSep (L : Loc) : Prop :=
  ∀ z ∈ [L.bsg, L.bv, L.bd, L.be], z ≠ Block.work4 ∧ z ≠ Block.work4Sz

/-- `L` with `work4` at block `b` of capacity `c`. -/
abbrev Loc.with4 (L : Loc) (b : block) (c : Nat) : Loc := { L with b4 := b, c4 := c }

/-- After `distvals`: `work3` written, `work4` possibly moved. -/
theorem Mem.swap4 {m m' : mem} {W : block → Prop} (hok : Ok n L) (hm : Mem m L G t S)
    (hgs : GSep L) (hbe : Mem.valid_block m L.be) (hu : Unch m m' W)
    (hW : ∀ z, W z → z = L.b3 ∨ z = L.b4 ∨ z = Block.work4 ∨ z = Block.work4Sz ∨
      ¬ Mem.valid_block m z)
    (hk3 : Keep m m' L.b3) {c4 : Nat} {b4 : block}
    (hd4 : DynAt m' Block.work4 Block.work4Sz 4 c4 b4) {w4 : Nat → val}
    (hw4 : ArrayAt m' .Mint32 b4 0 w4 c4) {w3 : Array Nat}
    (hw3 : ArrayAt m' .Mint32 L.b3 0 (ints w3) n) :
    Mem m' (L.with4 b4 c4) G t { S with w3, w4 } := by
  have hwv := hm.wvalid hok
  have hrv := hm.rvalid hok hbe
  have nw : ∀ z ∈ L.wblocks, z ≠ L.b3 → z ≠ L.b4 → ¬ W z := fun z hz h3 h4 hw => by
    rcases hW z hw with h | h | h | h | h
    · exact h3 h
    · exact h4 h
    · exact hok.wr hz (by simp [Loc.rblocks]) h
    · exact hok.wr hz (by simp [Loc.rblocks]) h
    · exact h (hwv z hz)
  have nr : ∀ z ∈ L.rblocks, z ≠ Block.work4 → z ≠ Block.work4Sz → ¬ W z := fun z hz h3 h4 hw => by
    rcases hW z hw with h | h | h | h | h
    · exact hok.wr (by simp [Loc.wblocks]) hz h.symm
    · exact hok.wr (by simp [Loc.wblocks]) hz h.symm
    · exact h3 h
    · exact h4 h
    · exact h (hrv z hz)
  have d := hok.wdistinct
  have gs := fun z hz => (hgs z hz)
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at gs
  exact
    { graph := hm.graph.unch hu (nr _ (by simp [Loc.rblocks]) gs.1.1 gs.1.2)
        (nr _ (by simp [Loc.rblocks]) gs.2.1.1 gs.2.1.2) (nr _ (by simp [Loc.rblocks]) gs.2.2.1.1 gs.2.2.1.2)
        (nr _ (by simp [Loc.rblocks]) gs.2.2.2.1 gs.2.2.2.2)
      lab := hm.lab.unch hu (nw _ (by simp [Loc.wblocks]) (pw_ne d 0 7 (by decide) (by simp [Loc.wblocks]))
        (pw_ne d 0 8 (by decide) (by simp [Loc.wblocks])))
      ptn := hm.ptn.unch hu (nw _ (by simp [Loc.wblocks]) (pw_ne d 1 7 (by decide) (by simp [Loc.wblocks]))
        (pw_ne d 1 8 (by decide) (by simp [Loc.wblocks])))
      nc := hm.nc.unch hu (nw _ (by simp [Loc.wblocks]) (pw_ne d 2 7 (by decide) (by simp [Loc.wblocks]))
        (pw_ne d 2 8 (by decide) (by simp [Loc.wblocks])))
      act := hm.act.unch hu (nw _ (by simp [Loc.wblocks]) (pw_ne d 3 7 (by decide) (by simp [Loc.wblocks]))
        (pw_ne d 3 8 (by decide) (by simp [Loc.wblocks])))
      actRep := hm.actRep
      code := let ⟨kv, hkv⟩ := hm.code
        ⟨kv, hkv.unch hu (nw _ (by simp [Loc.wblocks]) (pw_ne d 4 7 (by decide) (by simp [Loc.wblocks]))
          (pw_ne d 4 8 (by decide) (by simp [Loc.wblocks])))⟩
      d1 := hm.d1.keep hu (nr _ (by simp [Loc.rblocks]) (by decide) (by decide))
        (nr _ (by simp [Loc.rblocks]) (by decide) (by decide))
        (fun _ => Keep.unch hu (nw _ (by simp [Loc.wblocks]) (pw_ne d 5 7 (by decide) (by simp [Loc.wblocks]))
          (pw_ne d 5 8 (by decide) (by simp [Loc.wblocks]))))
      d2 := hm.d2.keep hu (nr _ (by simp [Loc.rblocks]) (by decide) (by decide))
        (nr _ (by simp [Loc.rblocks]) (by decide) (by decide))
        (fun _ => Keep.unch hu (nw _ (by simp [Loc.wblocks]) (pw_ne d 6 7 (by decide) (by simp [Loc.wblocks]))
          (pw_ne d 6 8 (by decide) (by simp [Loc.wblocks]))))
      d3 := hm.d3.keep hu (nr _ (by simp [Loc.rblocks]) (by decide) (by decide))
        (nr _ (by simp [Loc.rblocks]) (by decide) (by decide)) (fun _ => hk3)
      d4 := hd4
      w1 := hm.w1.unch hu (nw _ (by simp [Loc.wblocks]) (pw_ne d 5 7 (by decide) (by simp [Loc.wblocks]))
        (pw_ne d 5 8 (by decide) (by simp [Loc.wblocks])))
      w2 := hm.w2.unch hu (nw _ (by simp [Loc.wblocks]) (pw_ne d 6 7 (by decide) (by simp [Loc.wblocks]))
        (pw_ne d 6 8 (by decide) (by simp [Loc.wblocks])))
      w3 := hw3
      w4 := hw4
      k1 := hm.k1.unch hu (nr _ (by simp [Loc.rblocks]) (by decide) (by decide))
        (nr _ (by simp [Loc.rblocks]) (by decide) (by decide))
        (nw _ (by simp [Loc.wblocks]) (Ne.symm (pw_ne d 7 11 (by decide) (by simp [Loc.wblocks])))
          (Ne.symm (pw_ne d 8 11 (by decide) (by simp [Loc.wblocks]))))
        (fun _ => nw _ (by simp [Loc.wblocks]) (Ne.symm (pw_ne d 7 9 (by decide) (by simp [Loc.wblocks])))
          (Ne.symm (pw_ne d 8 9 (by decide) (by simp [Loc.wblocks]))))
      k2 := hm.k2.unch hu (nr _ (by simp [Loc.rblocks]) (by decide) (by decide))
        (nr _ (by simp [Loc.rblocks]) (by decide) (by decide))
        (nw _ (by simp [Loc.wblocks]) (Ne.symm (pw_ne d 7 12 (by decide) (by simp [Loc.wblocks])))
          (Ne.symm (pw_ne d 8 12 (by decide) (by simp [Loc.wblocks]))))
        (fun _ => nw _ (by simp [Loc.wblocks]) (Ne.symm (pw_ne d 7 10 (by decide) (by simp [Loc.wblocks])))
          (Ne.symm (pw_ne d 8 10 (by decide) (by simp [Loc.wblocks]))))
      bit := fun q hq => by
        rw [hu.load _ _ _ (nr _ (by simp [Loc.rblocks]) (by decide) (by decide))]; exact hm.bit q hq
      left := fun q hq => by
        erw [hu.load _ _ _ (nr (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by decide) (by decide))]
        exact hm.left q hq }

/-- `Ok` with `work4` at a block that is the old one or new to memory. -/
theorem Ok.with4 {m : mem} (hok : Ok n L) (hm : Mem m L G t S) (hbe : Mem.valid_block m L.be)
    {c4 : Nat} {b4 : block} (hc : n ≤ c4) (hb : (c4 = L.c4 ∧ b4 = L.b4) ∨ ¬ Mem.valid_block m b4) :
    Ok n (L.with4 b4 c4) := by
  rcases hb with ⟨rfl, rfl⟩ | hnv
  · exact hok
  have hwv := hm.wvalid hok
  have hrv := hm.rvalid hok hbe
  have hne : ∀ z ∈ L.wblocks, z ≠ b4 := fun z hz e => hnv (e ▸ hwv z hz)
  refine { hok with wdistinct := ?_, rw := ?_, c4 := hc }
  · have d := hok.wdistinct
    simp only [Loc.wblocks, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq] at d hne ⊢
    refine ⟨⟨d.1.1, d.1.2.1, d.1.2.2.1, d.1.2.2.2.1, d.1.2.2.2.2.1, d.1.2.2.2.2.2.1, d.1.2.2.2.2.2.2.1,
      hne.1, d.1.2.2.2.2.2.2.2.2⟩, ⟨d.2.1.1, d.2.1.2.1, d.2.1.2.2.1, d.2.1.2.2.2.1, d.2.1.2.2.2.2.1,
      d.2.1.2.2.2.2.2.1, hne.2.1, d.2.1.2.2.2.2.2.2.2⟩, ⟨d.2.2.1.1, d.2.2.1.2.1, d.2.2.1.2.2.1,
      d.2.2.1.2.2.2.1, d.2.2.1.2.2.2.2.1, hne.2.2.1, d.2.2.1.2.2.2.2.2.2⟩, ⟨d.2.2.2.1.1, d.2.2.2.1.2.1,
      d.2.2.2.1.2.2.1, d.2.2.2.1.2.2.2.1, hne.2.2.2.1, d.2.2.2.1.2.2.2.2.2⟩, ⟨d.2.2.2.2.1.1,
      d.2.2.2.2.1.2.1, d.2.2.2.2.1.2.2.1, hne.2.2.2.2.1, d.2.2.2.2.1.2.2.2.2⟩, ⟨d.2.2.2.2.2.1.1,
      d.2.2.2.2.2.1.2.1, hne.2.2.2.2.2.1, d.2.2.2.2.2.1.2.2.2⟩, ⟨d.2.2.2.2.2.2.1.1,
      hne.2.2.2.2.2.2.1, d.2.2.2.2.2.2.1.2.2⟩, ⟨hne.2.2.2.2.2.2.2.1, d.2.2.2.2.2.2.2.1.2⟩,
      (let h := hne.2.2.2.2.2.2.2.2; ⟨Ne.symm h.2.1, Ne.symm h.2.2.1, Ne.symm h.2.2.2.1, Ne.symm h.2.2.2.2⟩), d.2.2.2.2.2.2.2.2.2⟩
  · intro z hz hw
    simp only [Loc.writes, Loc.wblocks, List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals first
      | exact hnv (h ▸ hrv z hz)
      | exact hok.rw z hz (by rw [h]; simp [Loc.writes, Loc.wblocks])

theorem Loc.with4_writes {b : block} {c : Nat} {z : block} (h : (L.with4 b c).writes z) :
    L.writes z ∨ z = b := by
  simp only [Loc.writes, Loc.wblocks, Loc.with4, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

/-- `L.with4 b c`'s wide set is `L`'s, or `b` when it is new. -/
theorem Loc.with4_wide {m : mem} {b : block} {c : Nat}
    (hb : (c = L.c4 ∧ b = L.b4) ∨ ¬ Mem.valid_block m b) (z : block) (h : (L.with4 b c).Wide z) :
    L.Wide z ∨ ¬ Mem.valid_block m z := by
  rcases h with h | h
  · rcases Loc.with4_writes h with h | rfl
    · exact .inl (.inl h)
    · rcases hb with ⟨-, rfl⟩ | hnv
      · exact .inl (.inl (by simp [Loc.writes, Loc.wblocks]))
      · exact .inr hnv
  · exact .inl (.inr h)

theorem Tmp.with4 {le : temp_env} (h : Tmp le L t) (b : block) (c : Nat) : Tmp le (L.with4 b c) t :=
  ⟨h.g, h.lab, h.ptn, h.level, h.numcells, h.active, h.code, h.m, h.n, h.v, h.d, h.e, h.longcode,
    h.nactive⟩

end NautyVerified.Proofs.Sparse.Refine
