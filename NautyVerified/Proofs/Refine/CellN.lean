import NautyVerified.Proofs.Refine.PlaceN

/-!
# One cell of the nontrivial pass

`wp_fixN`: `if (!ISELEMENT(active, cell1)) { ADDELEMENT(active, cell1);
DELELEMENT(active, maxpos); }` is HexGraphIso's `nontrivialFix`.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Spec.Ntc
open NautyVerified.Source NautyVerified.Proofs NautyVerified.Proofs.Alloc
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

theorem wp_fixN {Q : Post} {le : temp_env} {m : mem} {n : Nat} {L : Loc} {ctx : Ctx n}
    {st : RefineSt n} {aw : Nat → Lib.Integers.int64} {cell1 : Nat}
    (hok : Ok n L) (hm : Mem m L ctx st aw) (ht : Tmp le L st)
    (hcl1 : PTree.get dense.id.cell1 le = some (.Vint (ir cell1))) (hc : cell1 < n)
    (hmp : st.maxpos < n)
    (hQ : ∀ m' aw', Mem m' L ctx (nontrivialFix cell1 st) aw' → Unch m m' (· = L.ba) →
      Q.normal E0 empty_env le m') :
    Wp xi ge Source.dense.fn.refine fixN Q empty_env le m := by
  have hnM := hok.nM
  have hnl := hok.nlt
  have hMl := hok.Mlt
  have hel := Set.eval_isElement (e := empty_env) (le := le) (m := m) (a := tv dense.id.cell1)
    hm.act (by omega) ht.active hcl1 rfl (by omega) (by omega) hm.bit rfl find_naugraphBit
  rw [hm.actRep.2 cell1 (by omega)] at hel
  apply wp_if_eval
  rw [Exec.evalExpr, hel]
  simp only [typeof, cop]
  cases hmem : st.active.mem cell1
  · -- not active: add `cell1`, drop `maxpos`
    simp only [Val.of_bool, Bool.false_eq_true, ite_false]
    rw [show Cfrontend.Cop.sem_unary_operation .Onotbool Vfalse tint m = some Vtrue from rfl]
    dsimp only
    rw [show Cfrontend.Cop.bool_val Vtrue tint m = some true from rfl]
    simp only [ite_true]
    wp_step
    refine Set.wp_addElementB hm.act (by omega) ht.active hcl1 rfl (by omega) (by omega)
      find_naugraphBit hm.bit rfl ?_
    intro m1 hact1 hu1 _
    have hrep1 := Set.setRep_add hm.actRep hc
    have hm1 := hm.setAct hok hu1 hact1 hrep1
    refine Set.wp_delElementB hact1 (by omega) ht.active ht.maxpos rfl (by omega) (by omega)
      find_naugraphBit (hm1.bit) rfl ?_
    intro m2 hact2 hu2 _
    have hm2 := hm1.setAct hok hu2 hact2 (Set.setRep_del hrep1 (by omega))
    simp only [E0_append]
    refine hQ m2 _ (hm2.congr (by simp [nontrivialFix, hmem]) (by simp [nontrivialFix, hmem])
      (by simp [nontrivialFix, hmem]) (by simp [nontrivialFix, hmem])) (hu1.trans hu2)
  · simp only [Val.of_bool, ite_true]
    rw [show Cfrontend.Cop.sem_unary_operation .Onotbool Vtrue tint m = some Vfalse from rfl]
    dsimp only
    rw [show Cfrontend.Cop.bool_val Vfalse tint m = some false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    apply wp_skip
    refine hQ m aw (hm.congr (by simp [nontrivialFix, hmem]) (by simp [nontrivialFix, hmem])
      (by simp [nontrivialFix, hmem]) (by simp [nontrivialFix, hmem])) (Unch.refl _ _)

theorem le_cmax {cs : List Nat} {c : Nat} (h : c ∈ cs) : c ≤ cmax cs := by
  obtain ⟨o, ho, rfl⟩ := List.mem_iff_getElem.1 h
  have hk : cs.length - 1 + 1 = cs.length := by omega
  rw [cmax, ← pmax_last hk, ← getElem!_pos cs o ho]
  exact le_pmax (by omega) (by omega)

theorem nontrivialCell_eqc {n : Nat} (ctx : Ctx n) (level : Nat) (ws : VSet n) {cell1 cell2 : Nat}
    (st : RefineSt n) (h12 : cell1 < cell2)
    (he : cmin (countsOf ctx st.lab ws cell1 cell2) = cmax (countsOf ctx st.lab ws cell1 cell2)) :
    nontrivialCell ctx level ws cell1 cell2 st =
      { st with longcode := (Hex.GraphIso.Nauty.mash st.longcode
          (cmin (countsOf ctx st.lab ws cell1 cell2) + cell1)) } := by
  rw [nontrivialCell, ite_eq_right (by simp; omega), ite_eq_left (by simp only [beq_iff_eq]; exact he)]

theorem nontrivialCell_nec {n : Nat} (ctx : Ctx n) (level : Nat) (ws : VSet n) {cell1 cell2 : Nat}
    (st : RefineSt n) (h12 : cell1 < cell2)
    (he : cmin (countsOf ctx st.lab ws cell1 cell2) ≠ cmax (countsOf ctx st.lab ws cell1 cell2)) :
    nontrivialCell ctx level ws cell1 cell2 st =
      nontrivialFix cell1
        { windowScan level cell1 cell2 (countsOf ctx st.lab ws cell1 cell2)
            (countValues (countsOf ctx st.lab ws cell1 cell2)) cell1 (-1) st with
          lab := writeSegment st.lab cell1 (segmentOf st.lab cell1 (countsOf ctx st.lab ws cell1 cell2)
            (countValues (countsOf ctx st.lab ws cell1 cell2))) } := by
  rw [nontrivialCell, ite_eq_right (by simp; omega), ite_eq_right (by simp only [beq_iff_eq]; exact he)]
  simp only [windowScan_lab]

/-- What a processed cell leaves, besides `Mem` and `Tmp`. -/
structure CellOut (n level : Nat) (st0 st : RefineSt n) (cell1 cell2 : Nat) : Prop where
  ok : StOk n level st
  psmall : ∀ i < n, st.ptn[i]! < 2147483648
  code : st.longcode < 2 ^ 62
  hint : st.hint < n
  maxpos : st.maxpos < n
  nc : st.numcells ≤ st0.numcells + (cell2 + 1 - cell1)

theorem startVals_curVals (cs : List Nat) (cell1 : Nat) (bv0 : Nat → val) (v : Nat) :
    startVals cs cell1 bv0 v = curVals cs (cmin cs) (cmax cs) cell1 0 bv0 v := by
  unfold startVals curVals
  by_cases hv : cmin cs ≤ v ∧ v ≤ cmax cs
  · rw [ite_eq_left hv, ite_eq_left hv, placed_zero, Nat.add_zero,
      baseOff_below (fun c hc => cmin_le hc) hv.1]
  · rw [ite_eq_right hv, ite_eq_right hv]

/-- What the placement leaves in `workperm`, on the cell. -/
theorem place_target {n : Nat} {cs : List Nat} {lab : Array Nat} {cell1 cell2 : Nat}
    (hlen : cs.length = cell2 + 1 - cell1) (h12 : cell1 < cell2) (h2n : cell2 < n)
    (hls : lab.size = n) (q : Nat) (hq1 : cell1 ≤ q) (hq2 : q ≤ cell2) :
    (placed' cs (cmin cs) cell1 (members lab cell1 cs.length) n cs.length)[q]! =
      (writeSegment lab cell1 (segmentOf lab cell1 cs (countValues cs)))[q]! := by
  have hsz : cs.toArray.size = cs.length := List.size_toArray
  have hco := toArray_get! cs
  have hmem : ∀ q, q < cs.toArray.size → cmin cs ≤ cs.toArray[q]! := fun q hq => by
    rw [hco, getElem!_pos cs q (by omega)]; exact cmin_le (List.getElem_mem _)
  have hbd : ∀ q, q < cs.toArray.size → cs.toArray[q]! - cmin cs < cmax cs + 1 - cmin cs :=
    fun q hq => by
      have h1 := hmem q hq
      rw [hco, getElem!_pos cs q (by omega)] at h1 ⊢
      have := le_cmax (List.getElem_mem (l := cs) (by omega : q < cs.length))
      omega
  have hcv : countValues cs.toArray.toList = (List.range (cmax cs + 1 - cmin cs)).map (cmin cs + ·) := by
    rw [List.toList_toArray]; rfl
  have h := fold_getElem! lab cs.toArray (members lab cell1 cs.length)
    (Array.replicate n n) cell1 (cmin cs) (cmax cs + 1 - cmin cs) hmem hbd hcv
    (fun o ho => members_get lab cell1 _ o (by omega)) (by simp; omega) (by omega) q hq1 (by omega)
  rw [List.toList_toArray] at h
  rw [placed', ← hsz]
  exact h

/-- The temporaries `splitN` assigns. -/
def splitTemps : List Common.AST.ident :=
  [dense.id.i, dense.id.c1, dense.id.c2, dense.id.maxcell, dense.id.maxpos, dense.id.hint,
   dense.id.longcode, idOf 731]

theorem wp_splitN {Q : Post} {le : temp_env} {m : mem} {n : Nat} {L : Loc} {ctx : Ctx n}
    {st : RefineSt n} {aw : Nat → Lib.Integers.int64} {ws : VSet n}
    {wsw : Nat → Lib.Integers.int64} {cell1 cell2 : Nat} {cv0 bv0 wv0 : Nat → val}
    (hf : CFrame m L ctx st.lab ws wsw) (hm : Mem m L ctx st aw) (ht : Tmp le L st)
    (hso : StOk n L.level st) (hb0 : SBound n st st cell1 cell1) (h12 : cell1 < cell2)
    (h2n : cell2 < n)
    (hbmin : PTree.get dense.id.bmin le =
      some (.Vint (ir (cmin (countsOf ctx st.lab ws cell1 cell2) : Nat))))
    (hbmax : PTree.get dense.id.bmax le =
      some (.Vint (ir (cmax (countsOf ctx st.lab ws cell1 cell2) : Nat))))
    (hcl1 : PTree.get dense.id.cell1 le = some (.Vint (ir cell1)))
    (hcl2 : PTree.get dense.id.cell2 le = some (.Vint (ir cell2)))
    (hcnt : ArrayAt m .Mint32 L.bc L.cb
      (cntVals (countsOf ctx st.lab ws cell1 cell2) cell1 (cell2 - cell1) cv0) n)
    (hbkt : ArrayAt m .Mint32 L.bB 0 (fun v =>
      if cmin (countsOf ctx st.lab ws cell1 cell2) ≤ v ∧ v ≤ cmax (countsOf ctx st.lab ws cell1 cell2)
      then .Vint (ir (multOf (countsOf ctx st.lab ws cell1 cell2) v : Nat)) else bv0 v) L.capB)
    (hwp : ArrayAt m .Mint32 L.bW 0 wv0 L.capW)
    (hQ : ∀ le' m' aw', Mem m' L ctx (nontrivialCell ctx L.level ws cell1 cell2 st) aw' →
      Tmp le' L (nontrivialCell ctx L.level ws cell1 cell2 st) →
      CellOut n L.level st (nontrivialCell ctx L.level ws cell1 cell2 st) cell1 cell2 →
      (∃ bv, ArrayAt m' .Mint32 L.bB 0 bv L.capB) → (∃ wv, ArrayAt m' .Mint32 L.bW 0 wv L.capW) →
      Unch m m' L.writes → Keep m m' L.bB → Keep m m' L.bW →
      (∀ z, z ∉ splitTemps → PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m' ∧ Q.cont E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.refine splitN Q empty_env le m := by
  have hok := hf.ok
  have d := hok.wd
  have hnl := hok.nlt
  have hcapB := hf.capB
  have hcapW := hf.capW
  have hcB := hok.capB
  have hcW := hok.capW
  generalize hcs : countsOf ctx st.lab ws cell1 cell2 = cs at *
  have hlen : cs.length = cell2 + 1 - cell1 := by rw [← hcs, countsOf_length]
  have hcle : ∀ o, cs[o]! ≤ n := fun o => by rw [← hcs]; exact countsOf_le ctx st.lab ws cell1 cell2 o
  have hBn : cmax cs ≤ n := by
    rw [cmax, ← pmax_last (k := cell2 - cell1) (by omega)]; exact pmax_le hcle (by omega)
  have hAB : cmin cs ≤ cmax cs := by
    rw [cmin, cmax, ← pmin_last (k := cell2 - cell1) (by omega),
      ← pmax_last (k := cell2 - cell1) (by omega)]
    exact pmin_le_pmax (by omega)
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hbmin, hbmax, typeof, cop]
  rw [ir_eq (a := ((cmin cs : Nat) : Int)) (b := ((cmax cs : Nat) : Int)) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩]
  by_cases hE : cmin cs = cmax cs
  · rw [ite_eq_left (by simp [hE])]
    have heq := nontrivialCell_eqc ctx L.level ws st h12 (hcs ▸ hE)
    rw [hcs] at heq
    wp_step; wp_step; wp_step
    refine wp_mash ht.longcode hb0.code (i := cmin cs + cell1)
      (by rw [eval_add_ii (x := ((cmin cs : Nat) : Int)) (y := (cell1 : Int)) (e := empty_env)
            (le := le) (m := m) (a := tv dense.id.bmin) (b := tv dense.id.cell1) hbmin rfl hcl1 rfl]
          push_cast; rfl) rfl (by omega) ?_
    apply wp_continue
    simp only [E0_append]
    refine (hQ _ m aw ?_ ?_ ?_ ⟨_, hbkt⟩ ⟨_, hwp⟩ (Unch.refl _ _) (Keep.refl _ _) (Keep.refl _ _)
      ?_).2
    · rw [heq]; exact hm.congr rfl rfl rfl rfl
    · rw [heq]; exact ht.setCode _
    · have hok2 := nontrivialCell_stOk (ctx := ctx) (workset := ws) (cell1 := cell1) hso h2n
      rw [heq] at hok2 ⊢
      have := mash_lt st.longcode (cmin cs + cell1)
      exact ⟨hok2, hb0.psmall, by simp only; omega, hb0.hint, hb0.maxpos, by simp only; omega⟩
    · intro z hz
      have : z ≠ dense.id.longcode := fun h => hz (h ▸ by simp [splitTemps])
      rw [temps_gso _ _ this]
  · rw [ite_eq_right (by simp; omega)]
    apply wp_skip
    have hne := nontrivialCell_nec ctx L.level ws st h12 (hcs ▸ hE)
    rw [hcs] at hne
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hcl1]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop, ir_neg]
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr]
    rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), hbmin]
    let le1 := PTree.set dense.id.i (.Vint (ir (cmin cs : Nat))) (PTree.set dense.id.maxcell
      (.Vint (ir (-1))) (PTree.set dense.id.c1 (.Vint (ir cell1)) le))
    have g1 : ∀ z, z ≠ dense.id.i → z ≠ dense.id.maxcell → z ≠ dense.id.c1 →
        PTree.get z le1 = PTree.get z le := fun z h1 h2 h3 => by
      simp only [le1]; rw [temps_gso _ _ h1, temps_gso _ _ h2, temps_gso _ _ h3]
    have ht1 : Tmp le1 L st := ((ht.set _ (by decide)).set _ (by decide)).set _ (by decide)
    refine wp_scanLoop (ws := ws) (bv0 := bv0) hf hm ht1 hb0 h12 h2n (by rw [hcs]; exact temps_gss _ _ _)
      (by rw [g1 _ (by decide) (by decide) (by decide), hcs]; exact hbmax)
      (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gss])
      (by rw [temps_gso _ _ (by decide), temps_gss])
      (by rw [g1 _ (by decide) (by decide) (by decide)]; exact hcl1)
      (by rw [g1 _ (by decide) (by decide) (by decide)]; exact hcl2) (by rw [hcs]; exact hbkt) ?_
    intro le2 m2 aw2 hm2 ht2 hsb2 hbk2 hu2 hk2 g2
    rw [hcs] at hm2 ht2 hsb2 hbk2
    generalize hW : windowScan L.level cell1 cell2 cs (countValues cs) cell1 (-1) st = W at *
    have nS : ∀ {z}, L.bp ≠ z → L.ba ≠ z → L.bn ≠ z → L.bB ≠ z →
        ¬ (z = L.bp ∨ z = L.ba ∨ z = L.bn ∨ z = L.bB) := fun h1 h2 h3 h4 h => by
      rcases h with h | h | h | h
      · exact h1 h.symm
      · exact h2 h.symm
      · exact h3 h.symm
      · exact h4 h.symm
    have hf2 := hf.unch (hu2.mono fun z hz => by rcases hz with h | h | h | h <;> simp [h])
    have hcnt2 := hcnt.unch hu2 (nS d.bp_bc (Ne.symm d.bc_ba) d.bn_bc (Ne.symm d.bc_bB))
    have hwp2 := hwp.unch hu2 (nS d.bp_bW d.ba_bW d.bn_bW (Ne.symm d.bW_bB))
    have hlab2 : ArrayAt m2 .Mint32 L.bl L.lb (ints st.lab) n := by rw [← hsb2.lab]; exact hm2.lab
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr]
    rw [g2 _ (by decide), g1 _ (by decide) (by decide) (by decide), hcl1]
    let le3 := PTree.set dense.id.i (.Vint (ir cell1)) le2
    have g3 : ∀ z, z ≠ dense.id.i → PTree.get z le3 = PTree.get z le2 := fun z h => temps_gso _ _ h
    have ht3 : Tmp le3 L W := ht2.set _ (by decide)
    have hcl23 : PTree.get dense.id.cell2 le3 = some (.Vint (ir cell2)) := by
      rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide) (by decide) (by decide)]; exact hcl2
    refine wp_placeLoop (cs := cs) (A := cmin cs) (B := cmax cs) hok hcapW hcapB hlen h12 h2n
      (fun c hc => ⟨cmin_le hc, le_cmax hc⟩) hBn (temps_gss _ _ _) hcl23 ht3.count ht3.lab hlab2
      hf2.labs hcnt2 (hbk2.congr fun v _ => startVals_curVals cs cell1 bv0 v) hf2.bkp hwp2 hf2.wpp ?_
    intro le4 m4 hwk4 hbk4 hu4 hkB4 hkW4 g4
    generalize hT : writeSegment st.lab cell1 (segmentOf st.lab cell1 cs (countValues cs)) = T at *
    have hso2 := nontrivialCell_stOk (ctx := ctx) (workset := ws) (cell1 := cell1) hso h2n
    rw [hne] at hso2
    have hTlab : (nontrivialFix cell1 { W with lab := T }).lab = T := by
      simp only [nontrivialFix]; split <;> rfl
    have hTs : T.size = n := by rw [← hTlab]; exact hso2.labSize
    have hTv : ∀ q, q < n → T[q]! < n := fun q hq => by
      rw [← hTlab]; exact hso2.labOk q (by rw [hTlab, hTs]; exact hq)
    have hls : st.lab.size = n := hso.labSize
    have hcne : cs ≠ [] := fun h => by rw [h] at hlen; simp at hlen; omega
    have hsegl : (segmentOf st.lab cell1 cs (countValues cs)).length = cs.length := by
      have h := seg_length st.lab cs.toArray cell1 (cmin cs) (cmax cs + 1 - cmin cs)
        (fun q hq => by
          rw [toArray_get!, getElem!_pos cs q (by simpa using hq)]; exact cmin_le (List.getElem_mem _))
        (fun q hq => by
          have hq' : q < cs.length := by simpa using hq
          rw [toArray_get!, getElem!_pos cs q hq']
          have := cmin_le (List.getElem_mem hq')
          have := le_cmax (List.getElem_mem hq')
          omega)
        (by rw [List.toList_toArray]; rfl)
      rw [List.toList_toArray] at h
      simpa using h
    have hlab4 := hlab2.unch hu4 (by
      rintro (h | h)
      · exact d.bl_bB h
      · exact d.bl_bW h)
    have hwpp4 : Mem.load .Mint64 m4 Block.naugraphWorkperm (zOfInt 0) =
        some (.Vptr L.bW Ptrofs.zero) := by
      rw [hu4.load _ _ _ (by rintro (h | h); exact d.bB_g0 h.symm; exact d.bW_g0 h.symm)]
      exact hf2.wpp
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr]
    rw [g4 _ (by decide) (by decide), g3 _ (by decide), g2 _ (by decide),
      g1 _ (by decide) (by decide) (by decide), hcl1]
    let le5 := PTree.set dense.id.i (.Vint (ir cell1)) le4
    have ht4 : Tmp le4 L W := ht3.temps fun x hx => g4 x (by
      rcases hx with hx | hx | hx | hx
      · simp [args] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide
      · subst hx; decide
      · subst hx; decide
      · subst hx; decide) (by
      rcases hx with hx | hx | hx | hx
      · simp [args] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide
      · subst hx; decide
      · subst hx; decide
      · subst hx; decide)
    have ht5 : Tmp le5 L W := ht4.set _ (by decide)
    have hcl25 : PTree.get dense.id.cell2 le5 = some (.Vint (ir cell2)) := by
      rw [temps_gso _ _ (by decide), g4 _ (by decide) (by decide)]; exact hcl23
    refine wp_copyLoop (lab0 := st.lab) (T := T) hok hcapW h12 h2n (temps_gss _ _ _) hcl25 ht5.lab
      hlab4 hwk4 hwpp4 (fun q hq1 hq2 => ?_) (fun q hq hq' => ?_) ?_
    · unfold wpVals
      rw [place_target hlen h12 h2n hls q hq1 hq2, hT, ite_eq_left ⟨by omega, hTv q (by omega)⟩]
    · rw [← hT]
      exact writeSegment_outside _ _ _ _ (by rw [hsegl, hlen]; omega)
    intro le6 m6 hla6 hu6 g6
    have hcnt4 := hcnt2.unch hu4 (by
      rintro (h | h)
      · exact d.bc_bB h
      · exact d.bc_bW h)
    have hm4 : Mem m4 L ctx W aw2 := hm2.away hok (hu4.mono fun z hz => by
      rcases hz with h | h
      · exact .inr (.inl h)
      · exact .inr (.inr h)) hkB4 hkW4 ⟨_, hcnt4⟩
    have hm6 := hm4.setLab hok hu6 hla6
    have ht6 : Tmp le6 L { W with lab := T } :=
      (ht5.temps fun x hx => g6 x (by
        rcases hx with hx | hx | hx | hx
        · simp [args] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        · subst hx; decide
        · subst hx; decide
        · subst hx; decide)).congr rfl rfl rfl
    have hcl16 : PTree.get dense.id.cell1 le6 = some (.Vint (ir cell1)) := by
      rw [g6 _ (by decide), temps_gso _ _ (by decide), g4 _ (by decide) (by decide), g3 _ (by decide),
        g2 _ (by decide), g1 _ (by decide) (by decide) (by decide)]
      exact hcl1
    wp_step; wp_step
    refine wp_fixN hok hm6 ht6 hcl16 (by omega) hsb2.maxpos ?_
    intro m7 aw7 hm7 hu7
    have hfix : nontrivialFix cell1 { W with lab := T } = nontrivialCell ctx L.level ws cell1 cell2 st :=
      hne.symm
    have hfx : ∀ s : RefineSt n, (nontrivialFix cell1 s).ptn = s.ptn ∧
        (nontrivialFix cell1 s).numcells = s.numcells ∧ (nontrivialFix cell1 s).hint = s.hint ∧
        (nontrivialFix cell1 s).maxpos = s.maxpos ∧ (nontrivialFix cell1 s).longcode = s.longcode :=
      fun s => by simp only [nontrivialFix]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨f1, f2, f3, f4, f5⟩ := hfx { W with lab := T }
    refine (hQ le6 m7 aw7 (hfix ▸ hm7) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).1
    · rw [← hfix]; exact ht6.congr f5 f3 f4
    · rw [← hfix]
      refine ⟨hfix ▸ hso2, ?_, ?_, ?_, ?_, ?_⟩
      · rw [f1]; exact hsb2.psmall
      · rw [f5]; exact hsb2.code
      · rw [f3]; exact hsb2.hint
      · rw [f4]; exact hsb2.maxpos
      · rw [f2]; exact hsb2.nc
    · obtain ⟨bv, hbv⟩ := hbk4
      exact ⟨bv, (hbv.unch hu6 d.bl_bB.symm).unch hu7 (Ne.symm d.ba_bB)⟩
    · exact ⟨_, (hwk4.unch hu6 d.bl_bW.symm).unch hu7 (Ne.symm d.ba_bW)⟩
    · refine ((hu2.mono fun z hz => ?_).trans (hu4.mono fun z hz => ?_)).trans
        ((hu6.mono fun z hz => .inl hz).trans (hu7.mono fun z hz => .inr (.inr (.inr (.inr (.inl hz))))))
      · rcases hz with h | h | h | h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inr (.inr (.inl h))))
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))
      · rcases hz with h | h
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))
        · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
    · exact ((hk2.trans hkB4).trans (Keep.unch hu6 d.bl_bB.symm)).trans
        (Keep.unch hu7 (Ne.symm d.ba_bB))
    · exact (((Keep.unch hu2 (nS d.bp_bW d.ba_bW d.bn_bW (Ne.symm d.bW_bB))).trans hkW4).trans
        (Keep.unch hu6 d.bl_bW.symm)).trans (Keep.unch hu7 (Ne.symm d.ba_bW))
    · intro z hz
      simp only [splitTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hz
      have hz2 : z ∉ [dense.id.i, dense.id.c1, dense.id.c2, dense.id.maxcell, dense.id.maxpos,
          dense.id.hint, dense.id.longcode] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h0, h1, h2, h3, h4, h5, h6⟩
      rw [g6 z h0, temps_gso _ _ h0, g4 z h0 h7, g3 z h0, g2 z hz2, g1 z h0 h3 h1]

end NautyVerified.Proofs.Refine
