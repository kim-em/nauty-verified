import NautyVerified.Proofs.Refine.CellN

/-!
# The nontrivial-splitter pass

`wp_cellLoopN`: the loop over all cells, one `wp_cellN` per nonsingleton cell,
is HexGraphIso's `refineNontrivialFast.go` over the snapshot of `ptn` taken
before the pass. `wp_nontrivial`: the whole pass (the splitter's set, its
code, the cell loop) is `refineNontrivial`.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs NautyVerified.Proofs.Alloc
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

/-- `CFrame` from `Mem`, `StOk` and the splitter's words. -/
theorem CFrame.of {n : Nat} {m : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} {ws : VSet n} {wsw : Nat → Lib.Integers.int64}
    (hok : Ok n L) (hcS : L.M ≤ L.capS) (hm : Mem m L ctx st aw) (hso : StOk n L.level st)
    (hwsA : ArrayAt m .Mint64 L.bS 0 (longs wsw) L.M)
    (hwsR : SetRep (fun w => bv64 (wsw w)) L.M ws) : CFrame m L ctx st.lab ws wsw where
  ok := hok
  graph := hm.graph
  larr := hm.lab
  labs := fun i hi => hso.labOk i (by rw [hso.labSize]; exact hi)
  wsA := hwsA
  wsR := hwsR
  wsp := hm.dS.ptr (by have := hok.M1; omega)
  bkp := hm.dB.ptr (by have := hok.capB; omega)
  wpp := hm.dW.ptr (by have := hok.capW; have := hok.n0; omega)
  bytes := hm.bytes
  bit := hm.bit
  capB := hm.dB.capLt
  capW := hm.dW.capLt

theorem goN_succ {n : Nat} (ctx : Ctx n) (level : Nat) (ws : VSet n) (ptn0 : Array Nat) (F c : Nat)
    (st : RefineSt n) (hc : c < n) :
    refineNontrivialFast.go ctx level ws ptn0 (F + 1) c st =
      refineNontrivialFast.go ctx level ws ptn0 F (cellEnd ptn0 level c + 1)
        (nontrivialCell ctx level ws c (cellEnd ptn0 level c) st) := by
  rw [refineNontrivialFast.go, ite_eq_left hc]

theorem goN_ge {n : Nat} (ctx : Ctx n) (level : Nat) (ws : VSet n) (ptn0 : Array Nat) (F c : Nat)
    (st : RefineSt n) (hc : ¬ c < n) :
    refineNontrivialFast.go ctx level ws ptn0 F c st = st := by
  cases F <;> simp [refineNontrivialFast.go, hc]

theorem nontrivialCell_self {n : Nat} (ctx : Ctx n) (level : Nat) (ws : VSet n) (c : Nat)
    (st : RefineSt n) : nontrivialCell ctx level ws c c st = st := by
  simp [nontrivialCell]

theorem windowScan_ptn_out {n : Nat} (level cell1 cell2 : Nat) (counts : List Nat) {j : Nat}
    (hj : cell2 < j) :
    ∀ (vs : List Nat) (c1 : Nat) (mc : Int) (s : RefineSt n),
      (windowScan level cell1 cell2 counts vs c1 mc s).ptn[j]! = s.ptn[j]!
  | [], _, _, _ => rfl
  | v :: vs, c1, mc, s => by
    rw [windowScan]
    split
    · rw [windowScan_ptn_out level cell1 cell2 counts hj vs]
      obtain ⟨-, -, -, -, -, -, e7⟩ := windowStep_eq level cell1 cell2 v c1 (multOf counts v) mc s
      rw [e7]; split
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      · rfl
    · exact windowScan_ptn_out level cell1 cell2 counts hj vs c1 mc s

theorem nontrivialCell_ptn_out {n : Nat} (ctx : Ctx n) (level : Nat) (ws : VSet n) {c e j : Nat}
    (st : RefineSt n) (hce : c < e) (hj : e < j) :
    (nontrivialCell ctx level ws c e st).ptn[j]! = st.ptn[j]! := by
  by_cases hE : cmin (countsOf ctx st.lab ws c e) = cmax (countsOf ctx st.lab ws c e)
  · rw [nontrivialCell_eqc ctx level ws st hce hE]
  · rw [nontrivialCell_nec ctx level ws st hce hE]
    have : ∀ s : RefineSt n, (nontrivialFix c s).ptn = s.ptn := fun s => by
      simp only [nontrivialFix]; split <;> rfl
    rw [this]
    exact windowScan_ptn_out level c e _ hj _ _ _ _

structure PassInvN {n : Nat} (le : temp_env) (m0 m : mem) (L : Loc) (ctx : Ctx n)
    (st0 : RefineSt n) (ws : VSet n) (wsw : Nat → Lib.Integers.int64) (R : RefineSt n) (p : Nat)
    (stc : RefineSt n) : Prop where
  mem : ∃ aw, Mem m L ctx stc aw
  unch : Unch m0 m (cellW L)
  tmp : Tmp le L stc
  wsA : ArrayAt m .Mint64 L.bS 0 (longs wsw) L.M
  wsR : SetRep (fun w => bv64 (wsw w)) L.M ws
  pn : p ≤ n
  fuel : ∃ F, n - p ≤ F ∧ R = refineNontrivialFast.go ctx L.level ws st0.ptn F p stc
  agree : ∀ j, p ≤ j → j < n → stc.ptn[j]! = st0.ptn[j]!
  ok : StOk n L.level stc
  small : ∀ i < n, stc.ptn[i]! < 2147483648
  nc : stc.numcells ≤ st0.numcells + p
  hint : stc.hint < n
  maxpos : stc.maxpos < n
  code : stc.longcode < 2 ^ 62

theorem notCellW_bS {L : Loc} (d : WDist L) : ¬ cellW L L.bS := by
  rintro (h | h | h | h | h | h | h)
  · exact d.bl_bS h.symm
  · exact d.bp_bS h.symm
  · exact d.bn_bS h.symm
  · exact d.bc_bS h.symm
  · exact d.ba_bS h.symm
  · exact d.bW_bS h.symm
  · exact d.bS_bB h

theorem wp_cellLoopN {Q : Post} {le : temp_env} {m0 m : mem} {n : Nat} {L : Loc} {ctx : Ctx n}
    {st0 : RefineSt n} {ws : VSet n} {wsw : Nat → Lib.Integers.int64} {R stc : RefineSt n}
    (hok : Ok n L) (hcS : L.M ≤ L.capS) (hok0 : StOk n L.level st0)
    (hI : PassInvN le m0 m L ctx st0 ws wsw R 0 stc)
    (hc : PTree.get dense.id.cell1 le = some (.Vint (ir (0 : Nat))))
    (hQ : ∀ le' m', PassInvN le' m0 m' L ctx st0 ws wsw R n R → Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.refine cellLoopN Q empty_env le m := by
  have hn := hok.nlt
  have d := hok.wd
  have hsz0 : st0.ptn.size = n := hok0.ptnSize
  have hend0 : st0.ptn[n - 1]! ≤ L.level := by have := hok0.ptnEnd; rwa [hsz0] at this
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ c stc, v = n - c ∧ PTree.get dense.id.cell1 le' = some (.Vint (ir c)) ∧
      PassInvN le' m0 m' L ctx st0 ws wsw R c stc
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ c en stc, c ≤ en ∧ en < n ∧ v = n - c ∧
      PTree.get dense.id.cell2 le' = some (.Vint (ir en)) ∧
      PassInvN le' m0 m' L ctx st0 ws wsw R (en + 1) stc
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0) ⟨rfl, rfl, 0, stc, rfl, hc, hI⟩
  · rintro v t e' le' m' ⟨rfl, rfl, c, stc, rfl, hc, hP⟩
    have ht := hP.tmp
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hc, ht.n, typeof, cop]
    have := hP.pn
    rw [ir_lt (a := (c : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hcn : c < n
    · rw [ite_eq_left (by simpa using hcn)]
      apply wp_skip
      obtain ⟨aw, hm⟩ := hP.mem
      have hspec := Spec.cellEnd_spec hsz0 hcn hend0
      obtain ⟨F, hF, hR⟩ := hP.fuel
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [goN_succ _ _ _ _ _ _ _ hcn] at hR
      generalize hen : cellEnd st0.ptn L.level c = en at hspec hR
      obtain ⟨hce, hen', hstop, hgo⟩ := hspec
      wp_step
      refine wp_scanEnd (x := dense.id.cell2) (y := dense.id.cell1) (by decide) (by decide) hm.ptn
        (by omega) ht.ptn ht.level hok.levlt hP.small hc hce hen'
        (by rw [hP.agree en hce hen']; exact hstop)
        (fun i h1 h2 => by rw [hP.agree i h1 (by omega)]; exact hgo i h1 h2) ?_
      intro le1 hcell2 ho1
      have hc1 : PTree.get dense.id.cell1 le1 = some (.Vint (ir c)) := by
        rw [ho1 _ (by decide)]; exact hc
      have ht1 : Tmp le1 L stc := ht.temps fun x hx => ho1 x (by
        rcases hx with hx | rfl | rfl | rfl
        · intro h; subst h; revert hx; decide
        all_goals decide)
      wp_step; wp_step; wp_step
      apply wp_if_eval
      simp only [Exec.evalExpr, hc1, hcell2, typeof, cop]
      rw [ir_eq (a := (c : Int)) (b := (en : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      by_cases hce' : c = en
      · rw [ite_eq_left (by simp; omega)]
        apply wp_continue
        subst hce'
        rw [nontrivialCell_self] at hR
        refine ⟨rfl, rfl, c, c, stc, Nat.le_refl _, hen', rfl, hcell2,
          { hP with
            mem := ⟨aw, hm⟩
            tmp := ht1
            pn := hen'
            fuel := ⟨F', by omega, hR⟩
            agree := fun j h1 h2 => hP.agree j (by omega) h2
            nc := by have := hP.nc; omega }⟩
      · rw [ite_eq_right (by simp; omega)]
        apply wp_skip
        have hlt : c < en := by omega
        have hf := CFrame.of hok hcS hm hP.ok hP.wsA hP.wsR
        obtain ⟨bv0, hbv0⟩ := malloced_array (hm.dB.mal (by have := hok.capB; omega)) .Mint32 4
          rfl rfl L.capB (Nat.le_refl _)
        obtain ⟨wv0, hwv0⟩ := malloced_array (hm.dW.mal (by have := hok.capW; have := hok.n0; omega))
          .Mint32 4 rfl rfl L.capW (Nat.le_refl _)
        have hb0 : SBound n stc stc c c := ⟨rfl, hP.ok.ptnSize, hP.small, hP.code, hP.hint, hP.maxpos,
          by omega⟩
        refine wp_cellN hf hm ht1 hP.ok hb0 hlt hen' hc1 hcell2 hbv0 hwv0 ?_
        intro le2 m2 aw2 hm2 ht2 hco2 _ _ hu2 _ _ g2
        have hJ : J (n - c) E0 empty_env le2 m2 := by
          refine ⟨rfl, rfl, c, en, _, Nat.le_of_lt hlt, hen', rfl, ?_,
            { mem := ⟨aw2, hm2⟩
              unch := hP.unch.trans hu2
              tmp := ht2
              wsA := hP.wsA.unch hu2 (notCellW_bS d)
              wsR := hP.wsR
              pn := hen'
              fuel := ⟨F', by omega, hR⟩
              agree := fun j h1 h2 => by
                rw [nontrivialCell_ptn_out _ _ _ _ hlt (by omega)]
                exact hP.agree j (by omega) h2
              ok := hco2.ok
              small := hco2.psmall
              nc := by have := hco2.nc; have := hP.nc; omega
              hint := hco2.hint
              maxpos := hco2.maxpos
              code := hco2.code }⟩
          rw [g2 _ (by decide)]; exact hcell2
        exact ⟨hJ, hJ⟩
    · rw [ite_eq_right (by simpa using hcn)]
      apply wp_break
      have hcn' : c = n := by omega
      subst hcn'
      obtain ⟨F, -, hR⟩ := hP.fuel
      rw [goN_ge _ _ _ _ _ _ _ hcn] at hR
      subst hR
      exact hQ le' m' hP
  · rintro v t e' le' m' ⟨rfl, rfl, c, en, stc, hce, hen, rfl, hc2, hP⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hc2, typeof, cop, ir_add]
    refine ⟨n - (en + 1), by omega, by simp, rfl, en + 1, stc, rfl, ?_, ?_⟩
    · rw [temps_gss]; push_cast; rfl
    · exact { hP with tmp := hP.tmp.set _ (by decide) }

end NautyVerified.Proofs.Refine
