import NautyVerified.Spec.Fmptn
import NautyVerified.Proofs.Refine.Guard
import NautyVerified.Proofs.Refine.Mash
import NautyVerified.Proofs.Refine.Scan
import NautyVerified.Proofs.Set.Bit

/-!
# One iteration of `refine`'s loop

`wp_step`: `DELELEMENT(active, split1)`, `split2` the end of `split1`'s cell,
`longcode = MASH(longcode, split1 + split2)`, then the trivial or nontrivial
pass, computes HexGraphIso's `refineStep`. The passes enter as hypotheses
(`TrivialPass`, `NontrivialPass`), proved in `Refine/Trivial.lean` and
`Refine/Nontrivial.lean`.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (longs BitTable)
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

theorem LeftbitTable.unch {m m' : mem} {S : block → Prop} (h : Nextelement.LeftbitTable m)
    (hu : Unch m m' S) (hb : ¬ S Block.leftbit) : Nextelement.LeftbitTable m' := fun i hi => by
  rw [hu.load _ _ _ hb]; exact h i hi

theorem BytecountTable.unch {m m' : mem} {S : block → Prop} (h : Init.BytecountTable m)
    (hu : Unch m m' S) (hb : ¬ S Block.naugraphBytecount) : Init.BytecountTable m' := fun i hi => by
  rw [hu.load _ _ _ hb]; exact h i hi

/-- Only `active`'s block changed: `Mem` holds with its new words and set. -/
theorem Mem.setAct {n : Nat} {m m' : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw aw' : Nat → Lib.Integers.int64} {s : VSet n} (hok : Ok n L) (hm : Mem m L ctx st aw)
    (hu : Unch m m' (· = L.ba)) (harr : ArrayAt m' .Mint64 L.ba L.ab (longs aw') L.M)
    (hrep : SetRep (fun w => bv64 (aw' w)) L.M s) :
    Mem m' L ctx { st with active := s } aw' := by
  have d := hok.distinct
  have h0 : L.bg ≠ L.ba := pw_ne d 0 5 (by decide) (by simp [Loc.blocks])
  have h1 : L.bl ≠ L.ba := pw_ne d 1 5 (by decide) (by simp [Loc.blocks])
  have h2 : L.bp ≠ L.ba := pw_ne d 2 5 (by decide) (by simp [Loc.blocks])
  have h3 : L.bn ≠ L.ba := pw_ne d 3 5 (by decide) (by simp [Loc.blocks])
  have h4 : L.bc ≠ L.ba := pw_ne d 4 5 (by decide) (by simp [Loc.blocks])
  have h7 : L.ba ≠ L.bW := pw_ne d 5 7 (by decide) (by simp [Loc.blocks])
  have h8 : L.ba ≠ L.bS := pw_ne d 5 8 (by decide) (by simp [Loc.blocks])
  have h9 : L.ba ≠ L.bB := pw_ne d 5 9 (by decide) (by simp [Loc.blocks])
  have g10 : L.ba ≠ Block.naugraphWorkperm := pw_ne d 5 10 (by decide) (by simp [Loc.blocks])
  have g11 : L.ba ≠ Block.naugraphWorkpermSz := pw_ne d 5 11 (by decide) (by simp [Loc.blocks])
  have g12 : L.ba ≠ Block.naugraphWorkset := pw_ne d 5 12 (by decide) (by simp [Loc.blocks])
  have g13 : L.ba ≠ Block.naugraphWorksetSz := pw_ne d 5 13 (by decide) (by simp [Loc.blocks])
  have g14 : L.ba ≠ Block.naugraphBucket := pw_ne d 5 14 (by decide) (by simp [Loc.blocks])
  have g15 : L.ba ≠ Block.naugraphBucketSz := pw_ne d 5 15 (by decide) (by simp [Loc.blocks])
  have g16 : L.ba ≠ Block.naugraphBit := pw_ne d 5 16 (by decide) (by simp [Loc.blocks])
  have g17 : L.ba ≠ Block.naugraphBytecount := pw_ne d 5 17 (by decide) (by simp [Loc.blocks])
  have g18 : L.ba ≠ Block.leftbit := pw_ne d 5 18 (by decide) (by simp [Loc.blocks])
  obtain ⟨cv, hcv⟩ := hm.cnt
  exact
    { graph := ⟨hm.graph.arr.unch hu h0, hm.graph.rep⟩
      lab := hm.lab.unch hu h1
      ptn := hm.ptn.unch hu h2
      nc := hm.nc.unch hu h3
      act := harr
      actRep := hrep
      cnt := ⟨cv, hcv.unch hu h4⟩
      dW := hm.dW.keep hu (Ne.symm g10) (Ne.symm g11) fun _ => Keep.unch hu (Ne.symm h7)
      dS := hm.dS.keep hu (Ne.symm g12) (Ne.symm g13) fun _ => Keep.unch hu (Ne.symm h8)
      dB := hm.dB.keep hu (Ne.symm g14) (Ne.symm g15) fun _ => Keep.unch hu (Ne.symm h9)
      bit := hm.bit.unch hu (Ne.symm g16)
      bytes := BytecountTable.unch hm.bytes hu (Ne.symm g17)
      left := LeftbitTable.unch hm.left hu (Ne.symm g18) }

/-- The trivial-splitter pass, as `Refine/Trivial.lean` proves it. -/
def TrivialPass (xi : ExternalCalls) : Prop :=
  ∀ {n : Nat} {Q : Post} {le : temp_env} {m : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} {split1 : Nat},
    Ok n L → Mem m L ctx st aw → Tmp le L st → StInv n L st → st.numcells < n →
    PTree.get dense.id.split1 le = some (.Vint (ir split1)) → split1 < n →
    (∀ le' m', Done le' m' L ctx (refineTrivial ctx L.level split1 st) → Unch m m' L.writes →
      Q.normal E0 empty_env le' m') →
    Wp xi ge dense.fn.refine trivial Q empty_env le m

/-- The nontrivial-splitter pass, as `Refine/Nontrivial.lean` proves it. -/
def NontrivialPass (xi : ExternalCalls) : Prop :=
  ∀ {n : Nat} {Q : Post} {le : temp_env} {m : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} {split1 split2 : Nat},
    Ok n L → L.M ≤ L.capS → Mem m L ctx st aw → Tmp le L st → StInv n L st → st.numcells < n →
    PTree.get dense.id.split1 le = some (.Vint (ir split1)) →
    PTree.get dense.id.split2 le = some (.Vint (ir split2)) →
    split1 < split2 → split2 = cellEnd st.ptn L.level split1 → split2 < n →
    (∀ le' m', Done le' m' L ctx (refineNontrivial ctx L.level split1 split2 st) →
      Unch m m' L.writes → Q.normal E0 empty_env le' m') →
    Wp xi ge dense.fn.refine nontrivial Q empty_env le m

theorem pickSplit_mem {n : Nat} {active : VSet n} {hint s : Nat}
    (h : pickSplit active hint = some s) : active.mem s = true := by
  unfold pickSplit at h
  split at h
  · cases h; assumption
  · split at h
    · cases h; exact (VSet.nextElem_eq_some_iff.1 (by assumption)).1
    · exact (VSet.nextElem_eq_some_iff.1 h).1

/-- `longcode = c`. -/
theorem Tmp.setCode {n : Nat} {le : temp_env} {L : Loc} {st : RefineSt n} (h : Tmp le L st)
    (c : Nat) : Tmp (PTree.set dense.id.longcode (.Vlong (lr c)) le) L { st with longcode := c } where
  g := by rw [temps_gso _ _ (by decide)]; exact h.g
  lab := by rw [temps_gso _ _ (by decide)]; exact h.lab
  ptn := by rw [temps_gso _ _ (by decide)]; exact h.ptn
  level := by rw [temps_gso _ _ (by decide)]; exact h.level
  numcells := by rw [temps_gso _ _ (by decide)]; exact h.numcells
  count := by rw [temps_gso _ _ (by decide)]; exact h.count
  active := by rw [temps_gso _ _ (by decide)]; exact h.active
  code := by rw [temps_gso _ _ (by decide)]; exact h.code
  m := by rw [temps_gso _ _ (by decide)]; exact h.m
  n := by rw [temps_gso _ _ (by decide)]; exact h.n
  longcode := temps_gss _ _ _
  hint := by rw [temps_gso _ _ (by decide)]; exact h.hint
  maxpos := by rw [temps_gso _ _ (by decide)]; exact h.maxpos

section Generic
open NautyVerified.Proofs.Set (sk)

/-- One iteration in dialect `D`, with the passes `tr` and `ntr`. -/
abbrev stepG (D : Dialect) (tr ntr : statement) : statement :=
  .Ssequence (D.delE dense.id.active (tv dense.id.split1))
    (.Ssequence (scanEnd dense.id.split2 dense.id.split1)
      (.Ssequence (sk (mash (.Ebinop .Oadd (tv dense.id.split1) (tv dense.id.split2) tint)))
        (sk (.Sifthenelse (.Ebinop .Oeq (tv dense.id.split1) (tv dense.id.split2) tint) tr ntr))))

/-- The main loop in dialect `D`. -/
abbrev mainLoopG (D : Dialect) (u0 u1 u2 u3 u4 u5 : ident) (tr ntr : statement) : statement :=
  .Sloop (.Ssequence (guardG D u0 u1 u2 u3 u4 u5) (stepG D tr ntr)) .Sskip

end Generic

theorem mainLoop_D0 : mainLoop = mainLoopG D0 (idOf 709) (idOf 710) (idOf 711) (idOf 712)
    (idOf 713) (idOf 714) trivial nontrivial := rfl

theorem mainLoop_D1 : Refine1.mainLoop = mainLoopG D1 (idOf 707) (idOf 708) (idOf 709)
    (idOf 710) (idOf 711) (idOf 712) Refine1.trivial Refine1.nontrivial := rfl

/-- The trivial-splitter pass `tr` of `f`, on the locations `L` and graph `ctx`. -/
def TrivialPassAt (xi : ExternalCalls) (f : function) (tr : statement) {n : Nat} (L : Loc)
    (ctx : Ctx n) : Prop :=
  ∀ {Q : Post} {le : temp_env} {m : mem} {st : RefineSt n} {aw : Nat → Lib.Integers.int64}
    {split1 : Nat},
    Mem m L ctx st aw → Tmp le L st → StInv n L st → st.numcells < n →
    PTree.get dense.id.split1 le = some (.Vint (ir split1)) → split1 < n →
    (∀ le' m', Done le' m' L ctx (refineTrivial ctx L.level split1 st) → Unch m m' L.writes →
      Q.normal E0 empty_env le' m') →
    Wp xi ge f tr Q empty_env le m

/-- The nontrivial-splitter pass `ntr` of `f`, on the locations `L` and graph `ctx`. -/
def NontrivialPassAt (xi : ExternalCalls) (f : function) (ntr : statement) {n : Nat} (L : Loc)
    (ctx : Ctx n) : Prop :=
  ∀ {Q : Post} {le : temp_env} {m : mem} {st : RefineSt n} {aw : Nat → Lib.Integers.int64}
    {split1 split2 : Nat},
    Mem m L ctx st aw → Tmp le L st → StInv n L st → st.numcells < n →
    PTree.get dense.id.split1 le = some (.Vint (ir split1)) →
    PTree.get dense.id.split2 le = some (.Vint (ir split2)) →
    split1 < split2 → split2 = cellEnd st.ptn L.level split1 → split2 < n →
    (∀ le' m', Done le' m' L ctx (refineNontrivial ctx L.level split1 split2 st) →
      Unch m m' L.writes → Q.normal E0 empty_env le' m') →
    Wp xi ge f ntr Q empty_env le m

/-- One iteration in dialect `D`: HexGraphIso's `refineStep` for the chosen `split1`. -/
theorem wp_iterG {D : Dialect} (hD : D.Sem) {f : function} {tr ntr : statement} {n : Nat}
    {Q : Post} {le : temp_env} {m : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} {s : Nat} (hMok : D.okM L.M) (hok : Ok n L)
    (hT : TrivialPassAt xi f tr L ctx) (hN : NontrivialPassAt xi f ntr L ctx)
    (hm : Mem m L ctx st aw)
    (ht : Tmp le L st) (hi : StInv n L st) (hnc : st.numcells < n)
    (hps : pickSplit st.active st.hint = some s)
    (hs1 : PTree.get dense.id.split1 le = some (.Vint (ir s)))
    (hQ : ∀ le' m', Done le' m' L ctx (refineStep ctx L.level s st) → Unch m m' L.writes →
      Q.normal E0 empty_env le' m') :
    Wp xi ge f (stepG D tr ntr) Q empty_env le m := by
  have hsn : s < n := VSet.mem_lt (pickSplit_mem hps)
  have hnl := hok.nlt
  have hnM := hok.nM
  have hMl := hok.Mlt
  simp only [stepG]
  wp_step
  refine hD.delE hMok hMl hm.act ht.active (c := s) (show Exec.evalExpr ge empty_env le m
    (tv dense.id.split1) = _ from hs1) rfl (by omega) hm.bit rfl ?_
  intro m1 harr1 hu1
  have hm1 := hm.setAct hok hu1 harr1 (Set.setRep_del hm.actRep (by omega))
  have hps' := hi.ok.ptnSize
  have hlast : st.ptn[n - 1]! ≤ L.level := by have := hi.ok.ptnEnd; rwa [hps'] at this
  obtain ⟨hce1, hce2, hce3, hce4⟩ := Spec.cellEnd_spec hps' hsn hlast
  show Wp _ _ _ (.Ssequence _ _) _ _ _ _
  wp_step
  refine wp_scanEnd (by decide) (by decide) hm1.ptn (by omega) ht.ptn ht.level hok.levlt
    hi.ptnSmall hs1 hce1 hce2 hce3 hce4 ?_
  intro le2 hs2 ho2
  have ht2 : Tmp le2 L st := ht.temps fun x hx => ho2 x (by
    rintro rfl; rcases hx with hx | hx | hx | hx <;> revert hx <;> decide)
  have hs1' : PTree.get dense.id.split1 le2 = some (.Vint (ir s)) := by
    rw [ho2 _ (by decide)]; exact hs1
  have hadd : Exec.evalExpr ge empty_env le2 m1
      (.Ebinop .Oadd (tv dense.id.split1) (tv dense.id.split2) tint) =
      some (.Vint (ir ((s + cellEnd st.ptn L.level s : Nat) : Int))) := by
    simp only [Exec.evalExpr, hs1', hs2, typeof, cop, ir_add]
    push_cast; rfl
  dsimp only
  wp_step; wp_step; wp_step
  refine wp_mash ht2.longcode hi.code hadd rfl (by omega) ?_
  let en := cellEnd st.ptn L.level s
  let st2 : RefineSt n :=
    { st with
      active := st.active.erase s
      longcode := Hex.GraphIso.Nauty.mash st.longcode (s + en) }
  have hm2 : Mem m1 L ctx st2 (Set.delW aw s) := hm1.congr rfl rfl rfl rfl
  have ht3 : Tmp (PTree.set dense.id.longcode (.Vlong (lr (Hex.GraphIso.Nauty.mash st.longcode (s + en)))) le2) L st2 :=
    (ht2.setCode _).congr rfl rfl rfl
  have hi2 : StInv n L st2 :=
    { ok := ⟨hi.ok.labSize, hi.ok.labOk, hi.ok.ptnSize, hi.ok.ptnEnd⟩
      ptnSmall := hi.ptnSmall, ncSmall := hi.ncSmall, hint := hi.hint, maxpos := hi.maxpos
      code := Nat.lt_trans (mash_lt _ _) (by decide) }
  have hs1'' : PTree.get dense.id.split1 (PTree.set dense.id.longcode
      (.Vlong (lr (Hex.GraphIso.Nauty.mash st.longcode (s + en)))) le2) = some (.Vint (ir s)) := by
    rw [temps_gso _ _ (by decide)]; exact hs1'
  have hs2'' : PTree.get dense.id.split2 (PTree.set dense.id.longcode
      (.Vlong (lr (Hex.GraphIso.Nauty.mash st.longcode (s + en)))) le2) = some (.Vint (ir en)) := by
    rw [temps_gso _ _ (by decide)]; exact hs2
  have hQ' : ∀ le' m', Done le' m' L ctx (refineStep ctx L.level s st) → Unch m1 m' L.writes →
      Q.normal E0 empty_env le' m' := fun le' m' hd hu =>
    hQ le' m' hd ((hu1.mono fun z hz => .inr (.inr (.inr (.inr (.inl hz))))).trans hu)
  dsimp only
  wp_step; wp_step
  apply wp_if_eval
  simp (config := {zetaDelta := true}) only [] at hs1'' hs2''
  simp only [Exec.evalExpr, hs1'', hs2'', typeof, cop]
  rw [ir_eq (a := (s : Int)) (b := (en : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hse : s = en
  · rw [ite_eq_left (by simp [hse])]
    refine hT hm2 ht3 hi2 hnc hs1'' hsn fun le' m' hd hu => hQ' le' m' ?_ hu
    have : refineStep ctx L.level s st = refineTrivial ctx L.level s st2 := by
      simp only [refineStep]; rw [ite_eq_left (by simp [en, ← hse])]
    rw [this]; exact hd
  · rw [ite_eq_right (by simp; omega)]
    refine hN hm2 ht3 hi2 hnc hs1'' hs2'' (by omega) rfl hce2 fun le' m' hd hu => hQ' le' m' ?_ hu
    have : refineStep ctx L.level s st = refineNontrivial ctx L.level s en st2 := by
      simp only [refineStep]; rw [ite_eq_right (by simpa [en] using hse)]
    rw [this]; exact hd

/-- One iteration: HexGraphIso's `refineStep` for the chosen `split1`. -/
theorem wp_iter (hT : TrivialPass xi) (hN : NontrivialPass xi) {n : Nat} {Q : Post}
    {le : temp_env} {m : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} {s : Nat} (hok : Ok n L) (hcS : L.M ≤ L.capS)
    (hm : Mem m L ctx st aw)
    (ht : Tmp le L st) (hi : StInv n L st) (hnc : st.numcells < n)
    (hps : pickSplit st.active st.hint = some s)
    (hs1 : PTree.get dense.id.split1 le = some (.Vint (ir s)))
    (hQ : ∀ le' m', Done le' m' L ctx (refineStep ctx L.level s st) → Unch m m' L.writes →
      Q.normal E0 empty_env le' m') :
    Wp xi ge dense.fn.refine step Q empty_env le m :=
  wp_iterG D0_sem True.intro hok (fun hm ht hi hnc hs hsp hQ => hT hok hm ht hi hnc hs hsp hQ)
    (fun hm ht hi hnc hs1 hs2 h12 he h2n hQ => hN hok hcS hm ht hi hnc hs1 hs2 h12 he h2n hQ)
    hm ht hi hnc hps hs1 hQ

/-- The loop state with fuel `F`: memory and temporaries describe `st`, and the
rest of HexGraphIso's loop from `st` with fuel `F` gives the final result. -/
def LoopAt {n : Nat} (L : Loc) (ctx : Ctx n) (st₀ : RefineSt n) (m₀ : mem) (F : Nat)
    (le : temp_env) (m : mem) : Prop :=
  ∃ st, Done le m L ctx st ∧ refineFuel st < F ∧
    refineLoop ctx L.level (4 * n + 8) st₀ = refineLoop ctx L.level F st ∧ Unch m₀ m L.writes

/-- The main loop in dialect `D` is HexGraphIso's `refineLoop` with fuel `4n + 8`. -/
theorem wp_mainLoopG {D : Dialect} (hD : D.Sem) {u0 u1 u2 u3 u4 u5 : ident}
    (hU : GuardOk [u0, u1, u2, u3, u4, u5]) {f : function} {tr ntr : statement} {n : Nat}
    {Q : Post} {le : temp_env} {m : mem} {L : Loc} {ctx : Ctx n} {st₀ : RefineSt n}
    (hMok : D.okM L.M) (hok : Ok n L) (hT : TrivialPassAt xi f tr L ctx)
    (hN : NontrivialPassAt xi f ntr L ctx) (hd : Done le m L ctx st₀)
    (hQ : ∀ le' m', Done le' m' L ctx (refineLoop ctx L.level (4 * n + 8) st₀) →
      Unch m m' L.writes → Q.normal E0 empty_env le' m') :
    Wp xi ge f (mainLoopG D u0 u1 u2 u3 u4 u5 tr ntr) Q empty_env le m := by
  simp only [mainLoopG]
  refine wp_loop (I := fun F t e le' m' => t = E0 ∧ e = empty_env ∧ LoopAt L ctx st₀ m F le' m')
    (J := fun F t e le' m' => t = E0 ∧ e = empty_env ∧ ∃ G, G < F ∧ LoopAt L ctx st₀ m G le' m')
    ?_ ?_ (n := 4 * n + 8)
    ⟨rfl, rfl, st₀, hd, refineFuel_lt_init st₀, rfl, Unch.refl _ _⟩
  · rintro F t e le' m' ⟨rfl, rfl, st, ⟨aw, hm, ht, hi⟩, hF, hloop, hu⟩
    wp_step
    refine wp_guardG hD hU hMok hok hm ht hi ?_ ?_
    · intro le'' hstop ht''
      simp only [E0_append]
      refine hQ le'' m' ?_ hu
      rw [hloop, refineLoop_stop ctx L.level st hstop]
      exact ⟨aw, hm, ht'', hi⟩
    · intro le'' s hnc hps ht'' hs1
      simp only [E0_append]
      obtain ⟨G, rfl, hG, hloop'⟩ := refineLoop_next ctx L.level hF hnc hps
      refine wp_iterG hD hMok hok hT hN hm ht'' hi hnc hps hs1 fun le3 m3 hd3 hu3 => ?_
      simp only [E0_append]
      exact ⟨True.intro, True.intro, G, by omega, _, hd3, hG, hloop.trans hloop', hu.trans hu3⟩
  · rintro F t e le' m' ⟨rfl, rfl, G, hG, hl⟩
    apply wp_skip
    exact ⟨G, hG, by simp, rfl, hl⟩

/-- `refine`'s main loop is HexGraphIso's `refineLoop` with fuel `4n + 8`. -/
theorem wp_mainLoop (hT : TrivialPass xi) (hN : NontrivialPass xi) {n : Nat} {Q : Post}
    {le : temp_env} {m : mem} {L : Loc} {ctx : Ctx n} {st₀ : RefineSt n} (hok : Ok n L)
    (hcS : L.M ≤ L.capS) (hd : Done le m L ctx st₀)
    (hQ : ∀ le' m', Done le' m' L ctx (refineLoop ctx L.level (4 * n + 8) st₀) →
      Unch m m' L.writes → Q.normal E0 empty_env le' m') :
    Wp xi ge dense.fn.refine mainLoop Q empty_env le m :=
  wp_mainLoopG D0_sem (by decide) True.intro hok
    (fun hm ht hi hnc hs hsp hQ => hT hok hm ht hi hnc hs hsp hQ)
    (fun hm ht hi hnc hs1 hs2 h12 he h2n hQ => hN hok hcS hm ht hi hnc hs1 hs2 h12 he h2n hQ) hd hQ

end NautyVerified.Proofs.Refine
