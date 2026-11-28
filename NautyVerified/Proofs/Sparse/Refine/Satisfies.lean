import NautyVerified.Proofs.Sparse.Refine.Prologue
import NautyVerified.Proofs.Sparse.Refine.DistPass
import NautyVerified.Proofs.Sparse.Refine.Starts
import NautyVerified.Proofs.Sparse.Refine.Code

/-!
# `refine_sg` meets its specification

`refineSgSpec` (see Spec.lean for the shape) and `refine_sg_satisfies_of`:
given the three splitting passes (`CountPass`, `TrivialPass`,
`NontrivialPass`), nausparse.c's `refine_sg` computes HexGraphIso's
`Sparse.refine`. The proof runs the prologue (`wp_prologue`), the initial
queue (`wp_queueLoop`), the early return, `CELLSTART` (`wp_startLoop`), the
distance pass (`wp_dist`), the main loop (`wp_mainLoop`, from `Model.entry`
with fresh scratch, which `entry_saturated` makes stop by its own test) and
the final code (`wp_finish`), and reads the result off `refineWith_entry`.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk longs BitTable)
open NautyVerified.Proofs.Nextelement (LeftbitTable)
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Spec.SortC (iterF)
open Hex.GraphIso.Nauty (VSet)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph Scratch)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat}

/-- What `refine_sg` leaves: HexGraphIso's refinement in the caller's blocks,
the scratch again in a `ScrAt` state (each array old or new), and only the
caller's written blocks, the scratch and new blocks changed. -/
def SgOut (G : Hex.SparseGraph n) (L : Loc) (lab ptn : Array Nat) (active : VSet n) (numcells : Nat)
    (m m' : mem) : Prop :=
  ArrayAt m' .Mint32 L.bl L.lb
      (ints (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).lab) n ∧
    ArrayAt m' .Mint32 L.bp L.pb
      (ints (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).ptn) n ∧
    ArrayAt m' .Mint32 L.bn L.nb (fun _ => .Vint (ir
      (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).numcells)) 1 ∧
    (∃ aw, ArrayAt m' .Mint64 L.ba L.ab (longs aw) L.M ∧ SetRep (fun w => bv64 (aw w)) L.M
      (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).active) ∧
    ArrayAt m' .Mint32 L.bk L.kb (fun _ => .Vint (ir
      (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).longcode)) 1 ∧
    (∃ c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2,
      ScrAt n m' (L.withScr c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2) ∧
      Ok n (L.withScr c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2) ∧ n ≤ c1 ∧ n ≤ c2 ∧ n ≤ c3 ∧ n ≤ c4 ∧ n ≤ mc1 ∧ n ≤ mc2 ∧
      Slot m L.c1 L.b1 c1 b1 ∧ Slot m L.c2 L.b2 c2 b2 ∧ Slot m L.c3 L.b3 c3 b3 ∧
      Slot m L.c4 L.b4 c4 b4 ∧ Slot m L.mc1 L.mb1 mc1 mb1 ∧ Slot m L.mc2 L.mb2 mc2 mb2) ∧
    Unch m m' (fun z => z ∈ L.cblocks ∨ proSet L m z) ∧ (∀ z ∈ L.cblocks, Keep m m' z) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z)

/-- The specification of `refine_sg`. -/
def refineSgSpec (G : Hex.SparseGraph n) (L : Loc) (lab ptn : Array Nat) (active : VSet n)
    (numcells : Nat) : FunSpec where
  pre args m := args = [.Vptr L.bsg L.sofs, .Vptr L.bl L.lofs, .Vptr L.bp L.pofs,
      .Vint (ir L.level), .Vptr L.bn L.nofs, .Vptr L.bc L.cofs, .Vptr L.ba L.aofs,
      .Vptr L.bk L.kofs, .Vint (ir L.M), .Vint (ir n)] ∧
    SgSep n m L ∧ SparseGraphAt m L.bsg L.sofs G L.bv L.vo L.bd L.dofs L.be L.eo ∧
    ArrayAt m .Mint32 L.bl L.lb (ints lab) n ∧ ArrayAt m .Mint32 L.bp L.pb (ints ptn) n ∧
    ArrayAt m .Mint32 L.bn L.nb (fun _ => .Vint (ir numcells)) 1 ∧
    (∃ aw, ArrayAt m .Mint64 L.ba L.ab (longs aw) L.M ∧ SetRep (fun w => bv64 (aw w)) L.M active) ∧
    (∃ kv, ArrayAt m .Mint32 L.bk L.kb kv 1) ∧ ScrAt n m L ∧ BitTable m Block.bit ∧
    LeftbitTable m ∧ lab.toList.Perm (List.range n) ∧ ptn.size = n ∧ ptn[n - 1]! ≤ L.level ∧
    (∀ i < n, ptn[i]! < 2147483648) ∧ numcells ≤ n ∧
    (∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ L.level) ∧ active.card ≤ numcells
  post _ m t _ m' := t = E0 ∧ SgOut G L lab ptn active numcells m m'

/-- The temporaries on entry. -/
def entryTemps (L : Loc) (n : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir L.M))
    (PTree.set id.code (.Vptr L.bk L.kofs) (PTree.set id.active (.Vptr L.ba L.aofs)
      (PTree.set sparse.id.count (.Vptr L.bc L.cofs) (PTree.set id.numcells (.Vptr L.bn L.nofs)
        (PTree.set id.level (.Vint (ir L.level)) (PTree.set id.ptn (.Vptr L.bp L.pofs)
          (PTree.set id.lab (.Vptr L.bl L.lofs) (PTree.set id.g (.Vptr L.bsg L.sofs)
            (create_undef_temps F.fn_temps))))))))))

theorem entry_args (L : Loc) (n : Nat) : Args (entryTemps L n) L n := by
  constructor <;> simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]

/-- The blocks the prologue may not move onto are valid. -/
theorem ScrAt.base_valid {m : mem} {L : Loc} (hs : SgSep n m L) (hscr : ScrAt n m L)
    (hbit : BitTable m Block.bit) (hleft : LeftbitTable m) : ∀ z ∈ L.base, Mem.valid_block m z := by
  obtain ⟨_, _, hk1⟩ := hscr.k1
  obtain ⟨_, _, hk2⟩ := hscr.k2
  intro z hz
  simp only [Loc.base, List.mem_append] at hz
  rcases hz with ((h | h) | h) | h
  · exact hs.valid z (List.mem_append_left _ h)
  · exact hs.valid z (List.mem_append_right _ h)
  · simp only [scrGlobals, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Alloc.valid_of_access hscr.d1.bpW
    · exact Alloc.valid_of_access hscr.d1.bsW
    · exact Alloc.valid_of_access hscr.d2.bpW
    · exact Alloc.valid_of_access hscr.d2.bsW
    · exact Alloc.valid_of_access hscr.d3.bpW
    · exact Alloc.valid_of_access hscr.d3.bsW
    · exact Alloc.valid_of_access hscr.d4.bpW
    · exact Alloc.valid_of_access hscr.d4.bsW
    · exact Alloc.valid_of_access hk1.dyn.bpW
    · exact Alloc.valid_of_access hk1.dyn.bsW
    · exact Alloc.valid_of_access hk2.dyn.bpW
    · exact Alloc.valid_of_access hk2.dyn.bsW
  · simp only [tblGlobals, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact Alloc.valid_of_access hk1.valW
    · exact Alloc.valid_of_access hk2.valW
    · exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ (hbit 0 (by decide)))
    · exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ (hleft 0 (by decide)))

/-- The old scratch blocks in use are valid. -/
theorem ScrAt.used_valid {m : mem} {L : Loc} (hscr : ScrAt n m L) :
    ∀ z, L.scrUsed z → Mem.valid_block m z := by
  obtain ⟨_, _, hk1⟩ := hscr.k1
  obtain ⟨_, _, hk2⟩ := hscr.k2
  rintro z (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩)
  · exact Alloc.Malloced.valid (hscr.d1.mal h)
  · exact Alloc.Malloced.valid (hscr.d2.mal h)
  · exact Alloc.Malloced.valid (hscr.d3.mal h)
  · exact Alloc.Malloced.valid (hscr.d4.mal h)
  · exact Alloc.Malloced.valid (hk1.dyn.mal h)
  · exact Alloc.Malloced.valid (hk2.dyn.mal h)

theorem sgOut_of {G : Hex.SparseGraph n} {L : Loc} {lab ptn : Array Nat} {active : VSet n}
    {numcells : Nat} {m m' : mem} {c1 c2 c3 c4 mc1 mc2 : Nat} {b1 b2 b3 b4 mb1 mb2 : block}
    {t : RefineSt n} {S : Scr}
    (hm : Mem m' (L.withScr c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2) G t S)
    (hok : Ok n (L.withScr c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2))
    (hwl : ∀ i < n, S.w3[i]! < 2147483648)
    (hl : t.lab = (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).lab)
    (hp : t.ptn = (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).ptn)
    (hn : t.numcells =
      (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).numcells)
    (ha : t.active = (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).active)
    (hk : ArrayAt m' .Mint32 L.bk L.kb (fun _ => .Vint (ir
      (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).longcode)) 1)
    (s1 : Slot m L.c1 L.b1 c1 b1) (s2 : Slot m L.c2 L.b2 c2 b2) (s3 : Slot m L.c3 L.b3 c3 b3)
    (s4 : Slot m L.c4 L.b4 c4 b4) (s5 : Slot m L.mc1 L.mb1 mc1 mb1) (s6 : Slot m L.mc2 L.mb2 mc2 mb2)
    (hu : Unch m m' (fun z => z ∈ L.cblocks ∨ proSet L m z)) (hkp : ∀ z ∈ L.cblocks, Keep m m' z)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) :
    SgOut G L lab ptn active numcells m m' := by
  refine ⟨hl ▸ hm.lab, hp ▸ hm.ptn, hn ▸ hm.nc, ⟨S.aw, hm.act, ha ▸ hm.actRep⟩, hk,
    ⟨c1, b1, c2, b2, c3, b3, c4, b4, mc1, mb1, mc2, mb2,
      ⟨hm.d1, hm.d2, hm.d3, hm.d4, (let ⟨_, hT, ht⟩ := hm.hi; HitsOk.join hm.w3 hwl hT ht hok.c3),
        ⟨_, _, hm.k1⟩, ⟨_, _, hm.k2⟩⟩, hok, hok.c1, hok.c2, hok.c3, hok.c4, hok.mc1, hok.mc2, s1, s2, s3, s4, s5, s6⟩, hu, hkp, hv⟩

theorem slot_pro {m : mem} {L : Loc} {c c' : Nat} {b b' : block} (s : Slot m c b c' b') (hc : 0 < c')
    (hu : 0 < c → L.scrUsed b) : proSet L m b' := by
  rcases s with ⟨rfl, rfl⟩ | hnv
  · exact .inr (.inr (.inr (.inl (hu hc))))
  · exact .inr (.inr (.inr (.inr hnv)))

theorem refine_empty (g : Graph n) (level : Nat) (lab ptn : Array Nat) (active : VSet n)
    (numcells : Nat) (hq : (Hex.GraphIso.Nauty.Sparse.Refinement.queue active).size = 0) :
    Hex.GraphIso.Nauty.Sparse.refine g level lab ptn active numcells =
      { Hex.GraphIso.Nauty.Sparse.Refinement.start lab ptn active numcells (Scratch.fresh n) with
        longcode := Hex.GraphIso.Nauty.cleanup numcells } := by
  unfold Hex.GraphIso.Nauty.Sparse.refine
  rw [Hex.GraphIso.Nauty.Sparse.refineWith_parts]
  have he : (Hex.GraphIso.Nauty.Sparse.Refinement.start lab ptn active numcells
      (Scratch.fresh n)).queue.isEmpty = true := by
    simp only [Hex.GraphIso.Nauty.Sparse.Refinement.start, Array.isEmpty_iff_size_eq_zero]; exact hq
  simp only [he, ite_true]
  rfl

theorem withScr_writes {m : mem} {L : Loc} {c1 c2 c3 c4 mc1 mc2 : Nat} {b1 b2 b3 b4 mb1 mb2 : block}
    (p1 : proSet L m b1) (p2 : proSet L m b2) (p3 : proSet L m b3) (p4 : proSet L m b4)
    (p5 : proSet L m mb1) (p6 : proSet L m mb2) {z : block}
    (h : (L.withScr c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2).Wide z) : z ∈ L.cblocks ∨ proSet L m z := by
  rcases h with h | h
  · simp only [Loc.writes, Loc.wblocks, Loc.withScr, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (refine .inl ?_; simp [Loc.cblocks]; done)
      | exact .inr ‹_›
      | exact .inr (.inr (.inl rfl))
      | exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inl h)

theorem refine_sg_satisfies_of (hC : CountPass (xi := xi)) (hT : TrivialPass (xi := xi))
    (hN : NontrivialPass (xi := xi)) (G : Hex.SparseGraph n) (L : Loc) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) :
    Satisfies xi sge (.Internal sparse.fn.refine_sg) (refineSgSpec G L lab ptn active numcells) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps L n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps L n, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  rintro args m₀ ⟨rfl, hs, hgr, hlab, hptn, hnc, ⟨aw, hact, hrep⟩, hcode, hscr, hbit, hleft, hperm, hpsz,
    hpend, hps, hncn, hcs, hcard⟩
  rw [triple_iff_wp]
  rintro e le m ⟨rfl, rfl, rfl⟩
  rw [sparse.fn.refine_sg.fn_body_eq, body_eq, body_pro]
  have hn0 := hs.n0
  have hnl := hs.nlt
  refine wp_prologue hs (hscr.base_valid hs hbit hleft) hscr.used_valid hgr hlab hptn hnc (by omega)
    hact hrep hcode hscr hbit hleft (entry_args L n) ?_
  intro c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2 le1 m1 S1 hok hm1 ht1 hHs hHl s1 s2 s3 s4 s5 s6 hun1 hg1
    ho1
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof, cop]
  refine wp_queueLoop hok hm1 (ht1.set (x := id.«i») _ (by decide)) rfl
    (by rw [temps_gss]; rfl) ?_
  intro le2 m2 S2 hm2 hw2 hw12 hw32 ht2 hu2 hg2 ho2
  have u1 : 0 < L.c1 → L.scrUsed L.b1 := fun h => .inl ⟨h, rfl⟩
  have u2 : 0 < L.c2 → L.scrUsed L.b2 := fun h => .inr (.inl ⟨h, rfl⟩)
  have u3 : 0 < L.c3 → L.scrUsed L.b3 := fun h => .inr (.inr (.inl ⟨h, rfl⟩))
  have u4 : 0 < L.c4 → L.scrUsed L.b4 := fun h => .inr (.inr (.inr (.inl ⟨h, rfl⟩)))
  have u5 : 0 < L.mc1 → L.scrUsed L.mb1 := fun h => .inr (.inr (.inr (.inr (.inl ⟨h, rfl⟩))))
  have u6 : 0 < L.mc2 → L.scrUsed L.mb2 := fun h => .inr (.inr (.inr (.inr (.inr ⟨h, rfl⟩))))
  have hcv : ∀ z ∈ L.cblocks, Mem.valid_block m z := fun z hz => hs.valid z (List.mem_append_left _ hz)
  have hcp : ∀ z ∈ L.cblocks, ¬ proSet L m z := fun z hz h => by
    have hg := hs.glob z (List.mem_append_left _ hz)
    rcases h with h | h | h | h | h
    · exact hg (List.mem_append_left _ h)
    · exact hg (List.mem_append_right _ (h ▸ by decide))
    · exact hg (List.mem_append_right _ (h ▸ by decide))
    · exact (hs.scrValid z h).1 (List.mem_append_left _ hz)
    · exact h (hcv z hz)
  have hk1 : ∀ z ∈ L.cblocks, Keep m m1 z := fun z hz => Keep.unch hun1 (hcp z hz)
  have hb2p : proSet L m b2 := slot_pro s2 (by have := hok.c2; simp only [Loc.withScr] at this; omega) u2
  have hb1p : proSet L m b1 := slot_pro s1 (by have := hok.c1; simp only [Loc.withScr] at this; omega) u1
  have hu12 : Unch m m2 (fun z => z ∈ L.cblocks ∨ proSet L m z) :=
    (hun1.mono fun z hz => .inr hz).trans (hu2.mono fun z hz => .inr (hz ▸ hb2p))
  simp only [E0_append]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, ht2.nactive, typeof, cop]
  have hqn := queue_size_le (Hex.GraphIso.Nauty.Sparse.CellQueue.of_scan
    (Hex.GraphIso.Nauty.Sparse.Refinement.queue_scan active) hcs).set
  rw [show (Hex.GraphIso.Nauty.Sparse.Refinement.start lab ptn active numcells (Scratch.fresh n)).active =
    active from rfl, show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl,
    ir_eq (a := ((Hex.GraphIso.Nauty.Sparse.Refinement.queue active).size : Int)) (b := 0)
    ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
  by_cases hq : (Hex.GraphIso.Nauty.Sparse.Refinement.queue active).size = 0
  · rw [show decide (((Hex.GraphIso.Nauty.Sparse.Refinement.queue active).size : Int) = 0) = true from
      decide_eq_true (by omega)]
    simp (config := {decide := true}) only [Val.of_bool, cop, ite_true]
    wp_step; wp_step; wp_step
    refine wp_code hok hm2 ht2.code ht2.longcode (show numcells < 2 ^ 62 by omega) ?_
    intro m3 hm3 hk3 hu3 hka3 hg3
    apply wp_return_none (Nextelement.free_empty m3)
    have hr0 := refine_empty (.ofGraph G) L.level lab ptn active numcells hq
    refine ⟨by simp, sgOut_of hm3 hok (by rw [hw32]; exact hHl)
      (by rw [hr0]) (by rw [hr0]) (by rw [hr0]) (by rw [hr0]) (by rw [hr0]; exact hk3)
      s1 s2 s3 s4 s5 s6 (hu12.trans (hu3.mono fun z hz => .inl (by rw [hz]; simp [Loc.cblocks, Loc.withScr])))
      (fun z hz => ((hk1 z hz).trans (Keep.unch hu2 fun h => hcp z hz (h ▸ hb2p))).trans (hka3 z))
      (fun z h => hg3 _ (hg2 _ (hg1 _ h)))⟩
  · rw [show decide (((Hex.GraphIso.Nauty.Sparse.Refinement.queue active).size : Int) = 0) = false from
      decide_eq_false (by omega)]
    simp (config := {decide := true}) only [Val.of_bool, cop, ite_false]
    apply wp_skip
    simp only [E0_append]
    let t2 := Hex.GraphIso.Nauty.Sparse.Refinement.indexed L.level
      (Hex.GraphIso.Nauty.Sparse.Refinement.start lab ptn active numcells (Scratch.fresh n))
    have hv2 : t2.Valid L.level := Hex.GraphIso.Nauty.Sparse.Refinement.initial_valid L.level lab ptn active
      numcells (Scratch.fresh n) hperm hpsz hpend hcs (Scratch.fresh_valid n lab ptn L.level).toBounded
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr]
    refine wp_startLoop hok (hm2.congr (t' := t2) rfl rfl rfl rfl)
      ((ht2.set (x := id.«i») _ (by decide)).congr (t' := t2) rfl rfl) hv2 hps (by rw [temps_gss]) ?_
    intro le3 m3 S3 hm3 hw13 hw23 hw33 ht3 hu3 hg3 ho3
    have hr3 : Rep (L.withScr c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2) t2 S3 :=
      ⟨hw13, fun i hi => by rw [hw23]; exact hw2 i hi, by rw [hw33, hw32]; exact hHs,
        fun i hi => by rw [hw33, hw32]; exact hHl i hi, hps⟩
    have hbc := Hex.GraphIso.Nauty.bcount_le t2.ptn L.level n
    have hb3 : Budget L.level t2 := by unfold Budget; show numcells + n ≤ _; omega
    have hgs : GSep (L.withScr c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2) := fun z hz =>
      ⟨fun e => hs.glob z (List.mem_append_right _ hz) (by rw [e]; decide),
        fun e => hs.glob z (List.mem_append_right _ hz) (by rw [e]; decide)⟩
    have hbe : Mem.valid_block m3 L.be :=
      hg3 _ (hg2 _ (hg1 _ (hs.valid _ (List.mem_append_right _ (by simp [Loc.gblocks])))))
    simp only [E0_append]
    wp_step
    refine wp_dist hC hok hm3 hr3 ht3 hv2 hb3 (show numcells < 2 ^ 62 by omega) hgs hbe ?_
    intro b4' c4' le4 m4 S4 hor4 hn4 hm4 hr4 ht4 hv4 hb4 hc4 hwf4 ho4
    have hok2 := hok.with4 hm3 hbe hn4 hor4
    have hne : (Hex.GraphIso.Nauty.Sparse.Refinement.queue active).isEmpty = false := by
      cases h : (Hex.GraphIso.Nauty.Sparse.Refinement.queue active).isEmpty
      · rfl
      · rw [Array.isEmpty_iff_size_eq_zero] at h; omega
    have hsat := entry_saturated (.ofGraph G) L.level lab ptn active numcells (Scratch.fresh n) hne hcard
    simp only [E0_append]
    wp_step
    refine wp_mainLoop hT hN hok2 hsat ⟨_, S4, hm4, hr4, ht4, hv4, hb4, hc4, Frame.refl _ _, Same.refl _,
      fun _ _ _ _ _ => rfl⟩ ?_
    intro le5 m5 t5 S5 hm5 hr5 ht5 hv5 hsame hf5 ho5
    have hfin : Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells =
        Hex.GraphIso.Nauty.Sparse.Refinement.finish (iterF (loopStep (.ofGraph G) L.level) n
          (entry (.ofGraph G) L.level lab ptn active numcells (Scratch.fresh n))) :=
      refineWith_entry _ _ _ _ _ _ _ hne
    have hcut := (Hex.GraphIso.Nauty.Sparse.refineWith_state G L.level lab ptn active numcells
      (Scratch.fresh n) hperm hpsz hpend hcs (Scratch.fresh_valid n lab ptn L.level).toBounded).2.2.1.count
    have hbr := Hex.GraphIso.Nauty.bcount_le
      (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).ptn L.level n
    have hrn : (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).numcells =
        t5.numcells := by rw [hfin]; exact hsame.numcells
    have hnc5 : t5.numcells < 2147483648 := by
      have : (Hex.GraphIso.Nauty.Sparse.refine (.ofGraph G) L.level lab ptn active numcells).numcells ≤ 2 * n := by
        unfold Hex.GraphIso.Nauty.Sparse.refine at hbr ⊢; omega
      omega
    refine wp_finish hok2 hm5 ht5 hnc5 ?_
    intro m6 hm6 hk6 hu6 hka6 hg6
    have s4' : Slot m L.c4 L.b4 c4' b4' := by
      rcases hor4 with ⟨h1, h2⟩ | hnv
      · rw [h1, h2]; exact s4
      · exact .inr fun hv => hnv (hg3 _ (hg2 _ (hg1 _ hv)))
    have cpos : ∀ {c : Nat}, n ≤ c → 0 < c := fun h => by omega
    have hok' := hok
    simp only [Loc.withScr] at hok'
    have p1 := slot_pro s1 (cpos hok'.c1) u1
    have p2 := slot_pro s2 (cpos hok'.c2) u2
    have p3 := slot_pro s3 (cpos hok'.c3) u3
    have p4 := slot_pro s4 (cpos hok'.c4) u4
    have p4' := slot_pro s4' (cpos hn4) u4
    have p5 := slot_pro s5 (cpos hok'.mc1) u5
    have p6 := slot_pro s6 (cpos hok'.mc2) u6
    have hv3 : ∀ z, Mem.valid_block m z → Mem.valid_block m3 z := fun z h => hg3 _ (hg2 _ (hg1 _ h))
    have hv4 : ∀ z, Mem.valid_block m z → Mem.valid_block m4 z := fun z h => hwf4.valid _ (hv3 _ h)
    have hu : Unch m m6 (fun z => z ∈ L.cblocks ∨ proSet L m z) := by
      refine (((hu12.trans (hu3.mono fun z hz => .inr (hz ▸ p1))).trans (hwf4.unch.mono fun z hz => ?_)).trans
        (hf5.unch.mono fun z hz => ?_)).trans (hu6.mono fun z hz => .inl (by
          rw [hz]; simp [Loc.cblocks, Loc.withScr]))
      · rcases hz with hz | hz
        · exact withScr_writes p1 p2 p3 p4 p5 p6 hz
        · exact .inr (.inr (.inr (.inr (.inr fun h => hz (hv3 _ h)))))
      · rcases hz with hz | hz
        · exact withScr_writes (c4 := c4') p1 p2 p3 p4' p5 p6 (.inl hz)
        · exact .inr (.inr (.inr (.inr (.inr fun h => hz (hv4 _ h)))))
    have hkp : ∀ z ∈ L.cblocks, Keep m m6 z := fun z hz =>
      (((((hk1 z hz).trans (Keep.unch hu2 fun h => hcp z hz (h ▸ p2))).trans
        (Keep.unch hu3 fun h => hcp z hz (h ▸ p1))).trans (hwf4.keep z hz)).trans
        (hf5.keep z (hv4 _ (hcv z hz)))).trans (hka6 z)
    have hfl : ∀ s : RefineSt n, (Hex.GraphIso.Nauty.Sparse.Refinement.finish s).lab = s.lab ∧
        (Hex.GraphIso.Nauty.Sparse.Refinement.finish s).ptn = s.ptn ∧
        (Hex.GraphIso.Nauty.Sparse.Refinement.finish s).numcells = s.numcells ∧
        (Hex.GraphIso.Nauty.Sparse.Refinement.finish s).active = s.active ∧
        (Hex.GraphIso.Nauty.Sparse.Refinement.finish s).longcode =
          Hex.GraphIso.Nauty.cleanup (Hex.GraphIso.Nauty.mash s.longcode s.numcells) :=
      fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨m6, Nextelement.free_empty m6, by simp, sgOut_of (c4 := c4') (b4 := b4') hm6 hok2
      hr5.w3small (by rw [hfin, (hfl _).1]; exact hsame.lab.symm)
      (by rw [hfin, (hfl _).2.1]; exact hsame.ptn.symm)
      (by rw [hfin, (hfl _).2.2.1]; exact hsame.numcells.symm)
      (by rw [hfin, (hfl _).2.2.2.1]; exact hsame.active.symm)
      (by rw [hfin, (hfl _).2.2.2.2, hsame.longcode, hsame.numcells]; exact hk6)
      s1 s2 s3 s4' s5 s6 hu hkp fun z h => hg6 _ (hf5.valid _ (hv4 _ h))⟩

end NautyVerified.Proofs.Sparse.Refine
