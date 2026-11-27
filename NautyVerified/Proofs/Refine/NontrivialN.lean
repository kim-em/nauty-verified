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

/-- `CFrame` from `Mem` and `StOk`. -/
theorem CFrame.of {n : Nat} {m : mem} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64}
    (hok : Ok n L) (hm : Mem m L ctx st aw) (hso : StOk n L.level st) : CFrame m L ctx st.lab where
  ok := hok
  graph := hm.graph
  larr := hm.lab
  labs := fun i hi => hso.labOk i (by rw [hso.labSize]; exact hi)
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
    (st0 : RefineSt n) (ws : VSet n) (Sp : temp_env → mem → Prop) (R : RefineSt n) (p : Nat)
    (stc : RefineSt n) : Prop where
  mem : ∃ aw, Mem m L ctx stc aw
  unch : Unch m0 m (cellW L)
  tmp : Tmp le L stc
  sp : Sp le m
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

/-- What a function's one-cell statement `cn` does, as `wp_cellN` states it, with the
temporaries `T` it assigns and the splitter facts `Sp`. -/
def CellPass (xi : ExternalCalls) (f : function) (cn : statement) (T : List Common.AST.ident)
    {n : Nat} (L : Loc) (ctx : Ctx n) (ws : VSet n) (Sp : temp_env → mem → Prop) : Prop :=
  ∀ {Q : Post} {le : temp_env} {m : mem} {st : RefineSt n} {aw : Nat → Lib.Integers.int64}
    {cell1 cell2 : Nat} {bv0 wv0 : Nat → val},
    Sp le m → CFrame m L ctx st.lab → Mem m L ctx st aw → Tmp le L st →
    StOk n L.level st → SBound n st st cell1 cell1 → cell1 < cell2 → cell2 < n →
    PTree.get dense.id.cell1 le = some (.Vint (ir cell1)) →
    PTree.get dense.id.cell2 le = some (.Vint (ir cell2)) →
    ArrayAt m .Mint32 L.bB 0 bv0 L.capB → ArrayAt m .Mint32 L.bW 0 wv0 L.capW →
    (∀ le' m' aw', Mem m' L ctx (nontrivialCell ctx L.level ws cell1 cell2 st) aw' →
      Tmp le' L (nontrivialCell ctx L.level ws cell1 cell2 st) →
      CellOut n L.level st (nontrivialCell ctx L.level ws cell1 cell2 st) cell1 cell2 →
      (∃ bv, ArrayAt m' .Mint32 L.bB 0 bv L.capB) → (∃ wv, ArrayAt m' .Mint32 L.bW 0 wv L.capW) →
      Unch m m' (cellW L) → Keep m m' L.bB → Keep m m' L.bW →
      (∀ z, z ∉ T → PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m' ∧ Q.cont E0 empty_env le' m') →
    Wp xi ge f cn Q empty_env le m

/-- The loop over the cells, with the one-cell statement `cn`. -/
abbrev cellLoopNG (cn : statement) : statement :=
  .Sloop
    (.Ssequence
      (Set.sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.cell1) (tv dense.id.n) tint) .Sskip .Sbreak))
      (.Ssequence (scanEnd dense.id.cell2 dense.id.cell1)
        (.Ssequence
          (Set.sk (.Sifthenelse (.Ebinop .Oeq (tv dense.id.cell1) (tv dense.id.cell2) tint)
            .Scontinue .Sskip))
          cn)))
    (Set.sk (.Sset dense.id.cell1 (.Ebinop .Oadd (tv dense.id.cell2) (ci 1 tint) tint)))

theorem cellLoopN_D0 : cellLoopN = cellLoopNG cellN := rfl

theorem cellLoopN_D1 : Refine1.cellLoopN = cellLoopNG Refine1.cellN := rfl

theorem wp_cellLoopN {cn : statement} {T : List Common.AST.ident}
    (hcT : dense.id.cell2 ∉ T ∧ dense.id.cell1 ∉ T) {f : function} {Q : Post} {le : temp_env}
    {m0 m : mem} {n : Nat} {L : Loc} {ctx : Ctx n}
    {st0 : RefineSt n} {ws : VSet n} {Sp : temp_env → mem → Prop} {R stc : RefineSt n}
    (hCP : CellPass xi f cn T L ctx ws Sp) (hSo : SpOk Sp L (dense.id.cell1 :: dense.id.cell2 :: T))
    (hok : Ok n L) (hok0 : StOk n L.level st0)
    (hI : PassInvN le m0 m L ctx st0 ws Sp R 0 stc)
    (hc : PTree.get dense.id.cell1 le = some (.Vint (ir (0 : Nat))))
    (hQ : ∀ le' m', PassInvN le' m0 m' L ctx st0 ws Sp R n R → Q.normal E0 empty_env le' m') :
    Wp xi ge f (cellLoopNG cn) Q empty_env le m := by
  have hn := hok.nlt
  have d := hok.wd
  have hsz0 : st0.ptn.size = n := hok0.ptnSize
  have hend0 : st0.ptn[n - 1]! ≤ L.level := by have := hok0.ptnEnd; rwa [hsz0] at this
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ c stc, v = n - c ∧ PTree.get dense.id.cell1 le' = some (.Vint (ir c)) ∧
      PassInvN le' m0 m' L ctx st0 ws Sp R c stc
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ c en stc, c ≤ en ∧ en < n ∧ v = n - c ∧
      PTree.get dense.id.cell2 le' = some (.Vint (ir en)) ∧
      PassInvN le' m0 m' L ctx st0 ws Sp R (en + 1) stc
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
            sp := hSo.temps hP.sp fun z hz => ho1 z fun h => hz (h ▸ by simp)
            pn := hen'
            fuel := ⟨F', by omega, hR⟩
            agree := fun j h1 h2 => hP.agree j (by omega) h2
            nc := by have := hP.nc; omega }⟩
      · rw [ite_eq_right (by simp; omega)]
        apply wp_skip
        have hlt : c < en := by omega
        have hf := CFrame.of hok hm hP.ok
        have hSp1 : Sp le1 m' := hSo.temps hP.sp fun z hz => ho1 z fun h => hz (h ▸ by simp)
        obtain ⟨bv0, hbv0⟩ := malloced_array (hm.dB.mal (by have := hok.capB; omega)) .Mint32 4
          rfl rfl L.capB (Nat.le_refl _)
        obtain ⟨wv0, hwv0⟩ := malloced_array (hm.dW.mal (by have := hok.capW; have := hok.n0; omega))
          .Mint32 4 rfl rfl L.capW (Nat.le_refl _)
        have hb0 : SBound n stc stc c c := ⟨rfl, hP.ok.ptnSize, hP.small, hP.code, hP.hint, hP.maxpos,
          by omega⟩
        refine hCP hSp1 hf hm ht1 hP.ok hb0 hlt hen' hc1 hcell2 hbv0 hwv0 ?_
        intro le2 m2 aw2 hm2 ht2 hco2 _ _ hu2 _ _ g2
        have hJ : J (n - c) E0 empty_env le2 m2 := by
          refine ⟨rfl, rfl, c, en, _, Nat.le_of_lt hlt, hen', rfl, ?_,
            { mem := ⟨aw2, hm2⟩
              unch := hP.unch.trans hu2
              tmp := ht2
              sp := hSo.temps (hSo.unch hSp1 hu2 fun z hz => hz) fun z hz =>
                g2 z fun h => hz (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
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
          rw [g2 _ hcT.1]; exact hcell2
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
    · exact { hP with
        tmp := hP.tmp.set _ (by decide)
        sp := hSo.temps hP.sp fun z hz => temps_gso _ _ fun h => hz (h ▸ by simp) }

/-- The splitter's set after its first `k` members. -/
def wsPre {n : Nat} (lab : Array Nat) (split1 k : Nat) : VSet n :=
  (List.range k).foldl (fun w o => w.insert lab[split1 + o]!) .empty

theorem wsPre_succ {n : Nat} (lab : Array Nat) (split1 k : Nat) :
    (wsPre lab split1 (k + 1) : VSet n) = (wsPre lab split1 k : VSet n).insert lab[split1 + k]! := by
  simp [wsPre, List.range_succ]

theorem wp_fillWS {f : function} {Q : Post} {le : temp_env} {m : mem} {n : Nat} {L : Loc} {lab : Array Nat}
    {split1 split2 : Nat} {w0 : Nat → Lib.Integers.int64}
    (hok : Ok n L) (hs1 : PTree.get dense.id.split1 le = some (.Vint (ir split1)))
    (hs2 : PTree.get dense.id.split2 le = some (.Vint (ir split2)))
    (hlabp : PTree.get dense.id.lab le = some (.Vptr L.bl L.lofs))
    (hlarr : ArrayAt m .Mint32 L.bl L.lb (ints lab) n) (hlabs : ∀ i < n, lab[i]! < n)
    (h12 : split1 ≤ split2) (h2n : split2 < n)
    (hwsA : ArrayAt m .Mint64 L.bS 0 (longs w0) L.M)
    (hwsR : SetRep (fun w => bv64 (w0 w)) L.M (VSet.empty : VSet n))
    (hwsp : Mem.load .Mint64 m Block.naugraphWorkset (zOfInt 0) = some (.Vptr L.bS Ptrofs.zero))
    (hbit : Set.BitTable m Block.naugraphBit)
    (hQ : ∀ le' m' w', ArrayAt m' .Mint64 L.bS 0 (longs w') L.M →
      SetRep (fun w => bv64 (w' w)) L.M (worksetOf n lab split1 split2) →
      Unch m m' (· = L.bS) → Keep m m' L.bS →
      (∀ z, z ≠ dense.id.i → PTree.get z le' = PTree.get z le) → Q.normal E0 empty_env le' m') :
    Wp xi ge f fillWS Q empty_env le m := by
  have hn := hok.nlt
  have hnM := hok.nM
  have hMl := hok.Mlt
  have d := hok.wd
  let len := split2 + 1 - split1
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ k w, k ≤ len ∧ v = len - k ∧
      PTree.get dense.id.i le' = some (.Vint (ir (split1 + k : Nat))) ∧
      ArrayAt m' .Mint64 L.bS 0 (longs w) L.M ∧
      SetRep (fun x => bv64 (w x)) L.M (wsPre lab split1 k : VSet n) ∧
      Unch m m' (· = L.bS) ∧ Keep m m' L.bS ∧
      (∀ z, z ≠ dense.id.i → PTree.get z le' = PTree.get z le)
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ k w, k < len ∧ v = len - k ∧
      PTree.get dense.id.i le' = some (.Vint (ir (split1 + k : Nat))) ∧
      ArrayAt m' .Mint64 L.bS 0 (longs w) L.M ∧
      SetRep (fun x => bv64 (w x)) L.M (wsPre lab split1 (k + 1) : VSet n) ∧
      Unch m m' (· = L.bS) ∧ Keep m m' L.bS ∧
      (∀ z, z ≠ dense.id.i → PTree.get z le' = PTree.get z le)
  simp only [fillWS, Set.sk]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hs1, E0_append]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := len) ⟨rfl, rfl, 0, w0, Nat.zero_le _, rfl,
    by simp, hwsA, by simpa [wsPre] using hwsR, Unch.refl _ _, Keep.refl _ _,
    fun z hz => temps_gso _ _ hz⟩
  · rintro v t e' le' m' ⟨rfl, rfl, k, w, hk, rfl, hik, hwk, hrk, hu, hkp, ho⟩
    have hs2' : PTree.get dense.id.split2 le' = some (.Vint (ir split2)) := by
      rw [ho _ (by decide)]; exact hs2
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hik, hs2', typeof, cop]
    rw [ir_lt (a := (split2 : Int)) (b := ((split1 + k : Nat) : Int)) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    by_cases hkl : k = len
    · rw [ite_eq_right (by simp; omega)]
      apply wp_break
      subst hkl
      refine hQ le' m' w hwk ?_ hu hkp ho
      have : (wsPre lab split1 (split2 + 1 - split1) : VSet n) = worksetOf n lab split1 split2 := rfl
      rw [← this]; exact hrk
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      have hlarr' := hlarr.unch hu d.bl_bS
      have hlabp' : PTree.get dense.id.lab le' = some (.Vptr L.bl L.lofs) := by
        rw [ho _ (by decide)]; exact hlabp
      have hle := eval_at (ge := ge) (e := empty_env) hlarr' (by omega) dense.id.lab hlabp'
        (tv dense.id.i) (split1 + k) (by omega) hik rfl
      have hlk := hlabs (split1 + k) (by omega)
      have hwsp' : Mem.load .Mint64 m' Block.naugraphWorkset (zOfInt 0) =
          some (.Vptr L.bS Ptrofs.zero) := by rw [hu.load _ _ _ (Ne.symm d.bS_g2)]; exact hwsp
      refine Set.wp_addElementG rfl find_naugraphWorkset hwsp' (by exact hwk) (by omega) hle rfl
        (by omega) (by omega) rfl find_naugraphBit (hbit.unch hu (Ne.symm d.bS_g6)) ?_
      intro m1 hw1 hu1 _ hk1
      refine ⟨by simp, rfl, k, Set.addW w lab[split1 + k]!, by omega, rfl, hik, hw1, ?_,
        hu.trans hu1, hkp.trans hk1, ho⟩
      rw [wsPre_succ]
      exact Set.setRep_add hrk hlk
  · rintro v t e' le' m' ⟨rfl, rfl, k, w, hk, rfl, hik, hwk, hrk, hu, hkp, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hik, typeof, cop, ir_add]
    refine ⟨len - (k + 1), by omega, by simp, rfl, k + 1, w, by omega, rfl, ?_, hwk, hrk, hu, hkp,
      fun z hz => by rw [temps_gso _ _ hz, ho z hz]⟩
    rw [temps_gss]; push_cast; rw [Int.add_assoc]

/-- `refine`'s pass for a nontrivial splitting cell is HexGraphIso's `refineNontrivial`. -/
theorem wp_nontrivial : NontrivialPass xi := by
  intro n Q le m L ctx st aw split1 split2 hok hcS hm ht hi hnc hs1 hs2 h12 hse h2n hQ
  have d := hok.wd
  have hn := hok.nlt
  have hnM := hok.nM
  have hMl := hok.Mlt
  have hM1 := hok.M1
  have hso := hi.ok
  have hlabs : ∀ i < n, st.lab[i]! < n := fun i hi' => hso.labOk i (by rw [hso.labSize]; exact hi')
  -- EMPTYSET(workset, m)
  obtain ⟨v0, hv0⟩ := malloced_array (hm.dS.mal (by omega)) .Mint64 8 rfl rfl L.M
    (Nat.mul_le_mul_left 8 hcS)
  have hwsp := hm.dS.ptr (by omega)
  simp only [nontrivial]
  wp_step
  refine Set.wp_emptySetG (g := dense.id.«naugraph:workset») (mv := dense.id.m) (es := dense.id.es_)
    (tmp := idOf 717) (by decide) rfl find_naugraphWorkset hwsp (Ne.symm d.bS_g2) hv0 hM1 (by omega)
    ht.m ?_
  intro le1 m1 hw1 hu1 _ hk1 g1
  have hm1 : Mem m1 L ctx st aw := by
    obtain ⟨cv, hcv⟩ := hm.cnt
    have nS : ∀ {z}, L.bS ≠ z → ¬ (z = L.bS) := fun h1 h => h1 h.symm
    exact hm.frame hok (hu1.mono fun z hz => .inr (.inr (.inr (.inr (.inr (.inr (.inl hz)))))))
      (Keep.unch hu1 d.bW_bS) hk1 (Keep.unch hu1 (Ne.symm d.bS_bB)) (hm.lab.unch hu1 d.bl_bS)
      (hm.ptn.unch hu1 d.bp_bS) (hm.nc.unch hu1 d.bn_bS) (hm.act.unch hu1 d.ba_bS) hm.actRep
      ⟨cv, hcv.unch hu1 d.bc_bS⟩
  have ht1 : Tmp le1 L st := ht.away [dense.id.es_, idOf 717] (by decide) fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    exact g1 z hz.1 hz.2
  have hwsp1 : Mem.load .Mint64 m1 Block.naugraphWorkset (zOfInt 0) =
      some (.Vptr L.bS Ptrofs.zero) := by rw [hu1.load _ _ _ (Ne.symm d.bS_g2)]; exact hwsp
  wp_step
  refine wp_fillWS (lab := st.lab) hok (by rw [g1 _ (by decide) (by decide)]; exact hs1)
    (by rw [g1 _ (by decide) (by decide)]; exact hs2) ht1.lab hm1.lab hlabs (by omega) h2n hw1
    (Set.setRep_zero hnM) hwsp1 hm1.bit ?_
  intro le2 m2 w2 hw2 hr2 hu2 hk2 g2
  have hm2 : Mem m2 L ctx st aw := by
    obtain ⟨cv, hcv⟩ := hm1.cnt
    exact hm1.frame hok (hu2.mono fun z hz => .inr (.inr (.inr (.inr (.inr (.inr (.inl hz)))))))
      (Keep.unch hu2 d.bW_bS) hk2 (Keep.unch hu2 (Ne.symm d.bS_bB)) (hm1.lab.unch hu2 d.bl_bS)
      (hm1.ptn.unch hu2 d.bp_bS) (hm1.nc.unch hu2 d.bn_bS) (hm1.act.unch hu2 d.ba_bS) hm1.actRep
      ⟨cv, hcv.unch hu2 d.bc_bS⟩
  have ht2 : Tmp le2 L st := ht1.temps fun x hx => g2 x (by
    rcases hx with hx | rfl | rfl | rfl
    · intro h; subst h; revert hx; decide
    all_goals decide)
  have gs : ∀ z, z ≠ dense.id.i → z ≠ dense.id.es_ → z ≠ idOf 717 →
      PTree.get z le2 = PTree.get z le := fun z h1 h2 h3 => by rw [g2 z h1, g1 z h2 h3]
  -- MASH(longcode, split2 - split1 + 1)
  wp_step; wp_step; wp_step
  refine wp_mash ht2.longcode hi.code (i := split2 - split1 + 1) ?_ rfl (by omega) ?_
  · simp only [Exec.evalExpr, typeof, cop]
    rw [gs _ (by decide) (by decide) (by decide), gs _ (by decide) (by decide) (by decide), hs1, hs2]
    simp only [cop, ir_sub, ir_add]
    congr 3; omega
  let st1 : RefineSt n := { st with longcode := Hex.GraphIso.Nauty.mash st.longcode (split2 - split1 + 1) }
  have ht3 := ht2.setCode (Hex.GraphIso.Nauty.mash st.longcode (split2 - split1 + 1))
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr]
  have hR : refineNontrivial ctx L.level split1 split2 st =
      refineNontrivialFast.go ctx L.level (worksetOf n st.lab split1 split2) st1.ptn n 0 st1 := by
    rw [refineNontrivial_eq_fast]; rfl
  have hwsp2 : Mem.load .Mint64 m2 Block.naugraphWorkset (zOfInt 0) =
      some (.Vptr L.bS Ptrofs.zero) := by rw [hu2.load _ _ _ (Ne.symm d.bS_g2)]; exact hwsp1
  have hCP : CellPass xi Source.dense.fn.refine cellN cellTemps L ctx
      (worksetOf n st.lab split1 split2) (SpWords L (worksetOf n st.lab split1 split2) w2) :=
    fun hSp hf hm ht hso hb0 h12 h2n hcl1 hcl2 hbkt hwp hQ =>
      wp_cellN (by decide) D0_sem (cntHead_ok (by decide)) (cntHead_ok (by decide)) hSp
        (SpWords.ok d _) True.intro hf hm ht hso hb0 h12 h2n hcl1 hcl2 hbkt hwp hQ
  refine wp_cellLoopN (by decide) hCP (SpWords.ok d _) (st0 := st1) (stc := st1)
    (R := refineNontrivial ctx L.level split1 split2 st)
    hok ⟨hso.labSize, hso.labOk, hso.ptnSize, hso.ptnEnd⟩
    { mem := ⟨aw, hm2.congr rfl rfl rfl rfl⟩
      unch := Unch.refl _ _
      tmp := ht3.set _ (by decide)
      sp := ⟨hw2, hr2, hwsp2⟩
      pn := Nat.zero_le _
      fuel := ⟨n, by omega, hR⟩
      agree := fun _ _ _ => rfl
      ok := ⟨hso.labSize, hso.labOk, hso.ptnSize, hso.ptnEnd⟩
      small := hi.ptnSmall
      nc := Nat.le_add_right _ _
      hint := hi.hint
      maxpos := hi.maxpos
      code := by have := mash_lt st.longcode (split2 - split1 + 1); exact Nat.lt_trans this (by decide) }
    (by rw [temps_gss]; rfl) ?_
  intro le' m' hP
  obtain ⟨aw', hm'⟩ := hP.mem
  refine hQ le' m' ⟨aw', hm', hP.tmp,
    { ok := hP.ok, ptnSmall := hP.small,
      ncSmall := by have := hP.nc; have h2 : st1.numcells = st.numcells := rfl; omega,
      hint := hP.hint, maxpos := hP.maxpos, code := hP.code }⟩ ?_
  refine ((hu1.trans hu2).mono fun z hz => .inr (.inr (.inr (.inr (.inr (.inr (.inl hz))))))).trans
    (hP.unch.mono fun z hz => ?_)
  rcases hz with h | h | h | h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))

end NautyVerified.Proofs.Refine
