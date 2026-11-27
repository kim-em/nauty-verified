import NautyVerified.Proofs.Refine.CellCount
import NautyVerified.Proofs.Refine.Upd
import NautyVerified.Proofs.Refine.Mash
import NautyVerified.Proofs.Set.Bit
import NautyVerified.Proofs.Refine.Trivial

/-!
# The window scan of the nontrivial pass

`wp_scanLoop`: for a cell `[cell1, cell2]` with counts `cs`, the loop
`for (i = bmin; i <= bmax; ++i) if (bucket[i]) { … }` performs HexGraphIso's
`windowScan` over the values `bmin .. bmax` (the code, `maxpos`, the new
active cells, `hint`, `*numcells` and the new cell ends in `ptn`), and turns
each nonempty `bucket[v]` into the start position of its group,
`cell1 + #{counts < v}`.
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

/-- The least and greatest count, as HexGraphIso's `nontrivialCell` writes them. -/
abbrev cmin (cs : List Nat) : Nat := cs.foldl Nat.min (cs.headD 0)
abbrev cmax (cs : List Nat) : Nat := cs.foldl Nat.max (cs.headD 0)

/-- The number of counts below `v`. -/
abbrev below (cs : List Nat) (v : Nat) : Nat := cs.countP fun c => decide (c < v)

theorem below_succ (cs : List Nat) (v : Nat) : below cs (v + 1) = below cs v + multOf cs v := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [below, multOf, List.countP_cons] at ih ⊢
    rw [ih]
    by_cases h : c < v
    · have h1 : c < v + 1 := by omega
      have h3 : ¬ c = v := by omega
      simp [h, h1, h3]; omega
    · by_cases h2 : c = v
      · subst h2; simp; omega
      · have h1 : ¬ c < v + 1 := by omega
        simp [h, h1, h2]

theorem below_le (cs : List Nat) (v : Nat) : below cs v ≤ cs.length := List.countP_le_length

/-- Every count is at least the least one. -/
theorem cmin_le {cs : List Nat} {c : Nat} (h : c ∈ cs) : cmin cs ≤ c := by
  obtain ⟨o, ho, rfl⟩ := List.mem_iff_getElem.1 h
  have hk : cs.length - 1 + 1 = cs.length := by omega
  rw [cmin, ← pmin_last hk, ← getElem!_pos cs o ho]
  exact pmin_le (by omega) (by omega)

theorem below_cmin (cs : List Nat) : below cs (cmin cs) = 0 :=
  List.countP_eq_zero.2 fun c hc h => by simp at h; have := cmin_le hc; omega

/-- The bucket after the scan: each nonempty group's start. -/
def startVals (cs : List Nat) (cell1 : Nat) (bv0 : Nat → val) (v : Nat) : val :=
  if cmin cs ≤ v ∧ v ≤ cmax cs then
    (if multOf cs v = 0 then .Vint (ir 0) else .Vint (ir (cell1 + below cs v : Nat)))
  else bv0 v

/-- `windowStep`, field by field. -/
theorem windowStep_eq {n : Nat} (level cell1 cell2 v c1 k : Nat) (mc : Int) (s : RefineSt n) :
    let w := windowStep level cell1 cell2 v c1 (c1 + k) mc s
    w.lab = s.lab ∧
    w.longcode = Hex.GraphIso.Nauty.mash s.longcode (v + c1) ∧
    w.maxpos = (if Int.ofNat k > mc then c1 else s.maxpos) ∧
    w.active = (if (c1 != cell1) = true then s.active.insert c1 else s.active) ∧
    w.numcells = (if (c1 != cell1) = true then s.numcells + 1 else s.numcells) ∧
    w.hint = (if (c1 != cell1) = true ∧ (k == 1) = true then c1 else s.hint) ∧
    w.ptn = (if c1 + k ≤ cell2 then s.ptn.set! (c1 + k - 1) level else s.ptn) := by
  intro w
  have hk : c1 + k - c1 = k := by omega
  simp only [w, windowStep, hk]
  by_cases h1 : Int.ofNat k > mc <;> by_cases h2 : (c1 != cell1) = true <;>
    by_cases h3 : (k == 1) = true <;> by_cases h4 : c1 + k ≤ cell2 <;>
    simp only [h1, h2, h3, h4, ite_true, ite_false, Bool.false_eq_true, and_self, and_true,
      and_false] <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The bounds the scan keeps. -/
structure SBound (n : Nat) (st0 st : RefineSt n) (cell1 c1 : Nat) : Prop where
  lab : st.lab = st0.lab
  psize : st.ptn.size = n
  psmall : ∀ i < n, st.ptn[i]! < 2147483648
  code : st.longcode < 2 ^ 62
  hint : st.hint < n
  maxpos : st.maxpos < n
  nc : st.numcells ≤ st0.numcells + (c1 - cell1)

/-- `if (c2 - c1 > maxcell) { maxcell = c2 - c1; maxpos = c1; }` -/
abbrev grpMax : statement :=
  .Sifthenelse
    (.Ebinop .Ogt (.Ebinop .Osub (tv dense.id.c2) (tv dense.id.c1) tint) (tv dense.id.maxcell) tint)
    (.Ssequence
      (Set.sk (.Sset dense.id.maxcell (.Ebinop .Osub (tv dense.id.c2) (tv dense.id.c1) tint)))
      (Set.sk (.Sset dense.id.maxpos (tv dense.id.c1))))
    .Sskip

/-- `if (c1 != cell1) { ADDELEMENT(active, c1); if (c2 - c1 == 1) hint = c1; ++*numcells; }` -/
abbrev grpAct (D : Dialect) : statement :=
  .Sifthenelse (.Ebinop .One (tv dense.id.c1) (tv dense.id.cell1) tint)
    (.Ssequence
      (D.addE dense.id.active (tv dense.id.c1))
      (.Ssequence
        (Set.sk (.Sifthenelse
          (.Ebinop .Oeq (.Ebinop .Osub (tv dense.id.c2) (tv dense.id.c1) tint) (ci 1 tint) tint)
          (Set.sk (.Sset dense.id.hint (tv dense.id.c1))) .Sskip))
        (Set.sk (.Sassign (.Ederef (pi dense.id.numcells) tint)
          (.Ebinop .Oadd (.Ederef (pi dense.id.numcells) tint) (ci 1 tint) tint)))))
    .Sskip

/-- `if (c2 <= cell2) ptn[c2 - 1] = level;` -/
abbrev grpPtn : statement :=
  .Sifthenelse (.Ebinop .Ole (tv dense.id.c2) (tv dense.id.cell2) tint)
    (Set.sk (.Sassign (ix dense.id.ptn (.Ebinop .Osub (tv dense.id.c2) (ci 1 tint) tint))
      (tv dense.id.level)))
    .Sskip

/-- One nonempty count group of the window scan. -/
abbrev group (D : Dialect) : statement :=
  .Ssequence
    (Set.sk (.Sset dense.id.c2
      (.Ebinop .Oadd (tv dense.id.c1) (gix dense.id.«naugraph:bucket» (tv dense.id.i)) tint)))
    (.Ssequence
      (Set.sk (.Sassign (gix dense.id.«naugraph:bucket» (tv dense.id.i)) (tv dense.id.c1)))
      (.Ssequence
        (Set.sk (mash (.Ebinop .Oadd (tv dense.id.i) (tv dense.id.c1) tint)))
        (.Ssequence (Set.sk grpMax)
          (.Ssequence (Set.sk (grpAct D))
            (.Ssequence (Set.sk grpPtn) (Set.sk (.Sset dense.id.c1 (tv dense.id.c2))))))))

/-- The window scan in dialect `D`. -/
abbrev scanLoopG (D : Dialect) : statement :=
  .Sloop
    (.Ssequence
      (Set.sk (.Sifthenelse (.Ebinop .Ole (tv dense.id.i) (tv dense.id.bmax) tint) .Sskip .Sbreak))
      (Set.sk (.Sifthenelse (gix dense.id.«naugraph:bucket» (tv dense.id.i)) (group D) .Sskip)))
    (Set.sk (.Sset dense.id.i (.Ebinop .Oadd (tv dense.id.i) (ci 1 tint) tint)))

theorem scanLoop_D0 : scanLoop = scanLoopG D0 := rfl

theorem scanLoop_D1 : Refine1.scanLoop = scanLoopG D1 := rfl

theorem SBound.step {n : Nat} {st0 s : RefineSt n} {level cell1 cell2 v c1 k : Nat} {mc : Int}
    (h : SBound n st0 s cell1 c1) (hk : 0 < k) (hck : c1 + k ≤ cell2 + 1) (h2n : cell2 < n)
    (hlv : level < 2147483648) (h1c : cell1 ≤ c1) :
    SBound n st0 (windowStep level cell1 cell2 v c1 (c1 + k) mc s) cell1 (c1 + k) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := windowStep_eq level cell1 cell2 v c1 k mc s
  have hcn : c1 < n := by omega
  refine ⟨by rw [e1, h.lab], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e7]; split
    · rw [Array.size_set!]; exact h.psize
    · exact h.psize
  · intro i hi
    rw [e7]; split
    · by_cases hij : i = c1 + k - 1
      · subst hij; rw [Array.getElem!_set!_self _ _ _ (by rw [h.psize]; omega)]; exact hlv
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hij)]; exact h.psmall i hi
    · exact h.psmall i hi
  · rw [e2]; have := mash_lt s.longcode (v + c1); omega
  · rw [e6]; split
    · exact hcn
    · exact h.hint
  · rw [e3]; split
    · exact hcn
    · exact h.maxpos
  · rw [e5]; have := h.nc; split <;> omega

theorem wp_grpMax {f : function} {Q : Post} {le : temp_env} {n : Nat} {L : Loc} {st : RefineSt n} {m : mem}
    {c1 k : Nat} {mc : Int} (ht : Tmp le L st)
    (hc1 : PTree.get dense.id.c1 le = some (.Vint (ir c1)))
    (hc2 : PTree.get dense.id.c2 le = some (.Vint (ir (c1 + k : Nat))))
    (hmc : PTree.get dense.id.maxcell le = some (.Vint (ir mc)))
    (hb : c1 + k < 2147483648) (hmc1 : -1 ≤ mc) (hmc2 : mc < 2147483648)
    (hQ : ∀ le', Tmp le' L { st with maxpos := if Int.ofNat k > mc then c1 else st.maxpos } →
      PTree.get dense.id.maxcell le' = some (.Vint (ir (if Int.ofNat k > mc then (k : Int) else mc))) →
      (∀ z, z ≠ dense.id.maxcell → z ≠ dense.id.maxpos → PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m) :
    Wp xi ge f grpMax Q empty_env le m := by
  apply wp_if_eval
  simp only [Exec.evalExpr, hc1, hc2, hmc, typeof, cop, ir_sub]
  have hk : ((c1 + k : Nat) : Int) - c1 = k := by omega
  rw [hk, ir_lt (a := mc) (b := (k : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases h : (k : Int) > mc
  · rw [ite_eq_left (by simpa using h)]
    have h' : Int.ofNat k > mc := h
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hc1, hc2, typeof, cop, ir_sub, hk]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gso _ _ (show dense.id.c1 ≠ dense.id.maxcell by decide), hc1]
    refine hQ _ ?_ ?_ ?_
    · rw [ite_eq_left h']
      exact (ht.set _ (by decide)).setMaxpos c1
    · rw [temps_gso _ _ (by decide), temps_gss, ite_eq_left h']
    · intro z h1 h2; rw [temps_gso _ _ h2, temps_gso _ _ h1]
  · rw [ite_eq_right (by simpa using h)]
    apply wp_skip
    have h' : ¬ Int.ofNat k > mc := h
    refine hQ _ ?_ ?_ fun _ _ _ => rfl
    · rw [ite_eq_right h']; exact ht
    · rw [ite_eq_right h']; exact hmc

theorem wp_grpAct {D : Dialect} (hD : D.Sem) {f : function} {Q : Post} {le : temp_env} {n : Nat}
    {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} {m : mem} {cell1 c1 k : Nat} (hMok : D.okM L.M) (hok : Ok n L)
    (hm : Mem m L ctx st aw) (ht : Tmp le L st)
    (hc1 : PTree.get dense.id.c1 le = some (.Vint (ir c1)))
    (hc2 : PTree.get dense.id.c2 le = some (.Vint (ir (c1 + k : Nat))))
    (hcl1 : PTree.get dense.id.cell1 le = some (.Vint (ir cell1)))
    (hcn : c1 < n) (hcl : cell1 < n) (hk : k < 2147483648)
    (hQ : ∀ le' m' aw', Mem m' L ctx { st with
        active := if (c1 != cell1) = true then st.active.insert c1 else st.active
        numcells := if (c1 != cell1) = true then st.numcells + 1 else st.numcells
        hint := if (c1 != cell1) = true ∧ (k == 1) = true then c1 else st.hint } aw' →
      Tmp le' L { st with
        active := if (c1 != cell1) = true then st.active.insert c1 else st.active
        numcells := if (c1 != cell1) = true then st.numcells + 1 else st.numcells
        hint := if (c1 != cell1) = true ∧ (k == 1) = true then c1 else st.hint } →
      Unch m m' (fun z => z = L.ba ∨ z = L.bn) →
      (∀ z, z ≠ dense.id.hint → PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge f (grpAct D) Q empty_env le m := by
  have hnM := hok.nM
  have hnl := hok.nlt
  have hMl := hok.Mlt
  have d := hok.wd
  apply wp_if_eval
  simp only [Exec.evalExpr, hc1, hcl1, typeof, cop]
  rw [ir_eq (a := (c1 : Int)) (b := (cell1 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hce : c1 = cell1
  · subst hce
    rw [ite_eq_right (by simp)]
    apply wp_skip
    have hb : (c1 != c1) = false := by simp
    simp only [hb, Bool.false_eq_true, ite_false, false_and] at hQ
    exact hQ le m aw hm ht (Unch.refl _ _) fun _ _ => rfl
  · rw [ite_eq_left (by simp; omega)]
    have hb : (c1 != cell1) = true := by simpa using hce
    simp only [hb, ite_true, true_and] at hQ
    wp_step
    refine hD.addE hMok hMl hm.act ht.active (tv dense.id.c1 |> fun _ => hc1) rfl
      (by omega) hm.bit rfl ?_
    intro m1 hact1 hu1
    have hm1 := hm.setAct hok hu1 hact1 (Set.setRep_add hm.actRep hcn)
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hc1, hc2, typeof, cop, ir_sub]
    have hkk : ((c1 + k : Nat) : Int) - c1 = k := by omega
    rw [hkk, ir_eq (a := (k : Int)) (b := 1) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
    have hrest : ∀ le1 (h : Nat), Tmp le1 L { st with active := st.active.insert c1, hint := h } →
        (∀ z, z ≠ dense.id.hint → PTree.get z le1 = PTree.get z le) →
        ((k == 1) = true → h = c1) → (¬ (k == 1) = true → h = st.hint) →
        Wp xi ge f
          (Set.sk (.Sassign (.Ederef (pi dense.id.numcells) tint)
            (.Ebinop .Oadd (.Ederef (pi dense.id.numcells) tint) (ci 1 tint) tint)))
          { normal := fun t => Q.normal (E0 ++ E0 ++ t), brk := fun t => Q.brk (E0 ++ E0 ++ t),
            cont := fun t => Q.cont (E0 ++ E0 ++ t), ret := fun t => Q.ret (E0 ++ E0 ++ t) }
          empty_env le1 m1 := by
      intro le1 h ht1 ho1 hh1 hh2
      have hm1' : Mem m1 L ctx { st with active := st.active.insert c1, hint := h } (Set.addW aw c1) :=
        hm1.congr rfl rfl rfl rfl
      wp_step; wp_step
      refine wp_cellStore hm1'.nc ht1.numcells (x := ((st.numcells + 1 : Nat) : Int)) ?_ rfl ?_
      · rw [eval_add_ii (eval_cell hm1'.nc ht1.numcells) rfl (y := 1) rfl rfl]
        push_cast; rfl
      · intro m2 hnc2 hu2
        have hm2 := hm1'.setNc hok hu2 hnc2
        refine hQ le1 m2 (Set.addW aw c1) ?_ ?_ ?_ ho1
        · by_cases hk1 : (k == 1) = true
          · rw [ite_eq_left hk1]; have := hh1 hk1; subst this; exact hm2.congr rfl rfl rfl rfl
          · rw [ite_eq_right hk1]; have := hh2 hk1; subst this; exact hm2.congr rfl rfl rfl rfl
        · by_cases hk1 : (k == 1) = true
          · rw [ite_eq_left hk1]; have := hh1 hk1; subst this; exact ht1.congr rfl rfl rfl
          · rw [ite_eq_right hk1]; have := hh2 hk1; subst this; exact ht1.congr rfl rfl rfl
        · exact (hu1.mono fun z hz => .inl hz).trans (hu2.mono fun z hz => .inr hz)
    by_cases hk1 : k = 1
    · rw [ite_eq_left (by simp [hk1])]
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hc1]
      simp only [E0_append]
      exact hrest _ c1 (ht.congr rfl rfl rfl |>.setHint c1 |>.congr rfl rfl rfl)
        (fun z hz => temps_gso _ _ hz) (fun _ => rfl) (fun h => absurd (by simpa using hk1) h)
    · rw [ite_eq_right (by simp; omega)]
      apply wp_skip
      simp only [E0_append]
      exact hrest le st.hint (ht.congr rfl rfl rfl) (fun _ _ => rfl)
        (fun h => absurd (by simpa using h) hk1) (fun _ => rfl)

theorem wp_grpPtn {f : function} {Q : Post} {le : temp_env} {n : Nat} {L : Loc} {ctx : Ctx n} {st : RefineSt n}
    {aw : Nat → Lib.Integers.int64} {m : mem} {cell2 c1 k : Nat} (hok : Ok n L)
    (hm : Mem m L ctx st aw) (ht : Tmp le L st) (hsz : st.ptn.size = n)
    (hc2 : PTree.get dense.id.c2 le = some (.Vint (ir (c1 + k : Nat))))
    (hcl2 : PTree.get dense.id.cell2 le = some (.Vint (ir cell2)))
    (hk : 0 < k) (hck : c1 + k ≤ cell2 + 1) (h2n : cell2 < n)
    (hQ : ∀ m', Mem m' L ctx { st with
        ptn := if c1 + k ≤ cell2 then st.ptn.set! (c1 + k - 1) L.level else st.ptn } aw →
      Unch m m' (· = L.bp) → Q.normal E0 empty_env le m') :
    Wp xi ge f grpPtn Q empty_env le m := by
  have hnl := hok.nlt
  have hlv := hok.levlt
  apply wp_if_eval
  simp only [Exec.evalExpr, hc2, hcl2, typeof, cop]
  rw [ir_lt (a := (cell2 : Int)) (b := ((c1 + k : Nat) : Int)) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩]
  by_cases h : c1 + k ≤ cell2
  · rw [ite_eq_left (by simp; omega)]
    wp_step; wp_step
    have hidx : Exec.evalExpr ge empty_env le m
        (.Ebinop .Osub (tv dense.id.c2) (ci 1 tint) tint) = some (.Vint (ir (c1 + k - 1 : Nat))) := by
      simp only [Exec.evalExpr, hc2, typeof, cop, ir_sub]; congr 3; omega
    refine wp_store hm.ptn (by omega) dense.id.ptn ht.ptn _ (c1 + k - 1) (by omega) hidx rfl
      (tv dense.id.level) L.level ht.level rfl ?_
    intro m' harr hu
    refine hQ m' ?_ hu
    rw [ite_eq_left h]
    exact hm.setPtn hok hu (by rw [ints_set (by omega)]; exact harr)
  · rw [ite_eq_right (by simp; omega)]
    apply wp_skip
    refine hQ m ?_ (Unch.refl _ _)
    rw [ite_eq_right h]
    exact hm

theorem wp_group {D : Dialect} (hD : D.Sem) {f : function} {Q : Post} {le : temp_env} {n : Nat}
    {L : Loc} {ctx : Ctx n} {st : RefineSt n} (hMok : D.okM L.M)
    {aw : Nat → Lib.Integers.int64} {m : mem} {cell1 cell2 v c1 k : Nat} {mc : Int}
    {bv : Nat → val} (hok : Ok n L) (hm : Mem m L ctx st aw) (ht : Tmp le L st)
    (hsz : st.ptn.size = n) (hcode : st.longcode < 2 ^ 62)
    (hi : PTree.get dense.id.i le = some (.Vint (ir v)))
    (hc1 : PTree.get dense.id.c1 le = some (.Vint (ir c1)))
    (hmc : PTree.get dense.id.maxcell le = some (.Vint (ir mc)))
    (hcl1 : PTree.get dense.id.cell1 le = some (.Vint (ir cell1)))
    (hcl2 : PTree.get dense.id.cell2 le = some (.Vint (ir cell2)))
    (hbkt : ArrayAt m .Mint32 L.bB 0 bv L.capB) (hbv : bv v = .Vint (ir k))
    (hbkp : Mem.load .Mint64 m Block.naugraphBucket (zOfInt 0) = some (.Vptr L.bB Ptrofs.zero))
    (hcapB : L.capB < 2147483648) (hv : v < L.capB) (hvn : v ≤ n) (hk : 0 < k) (hck : c1 + k ≤ cell2 + 1)
    (h1c : cell1 ≤ c1) (h2n : cell2 < n) (hmc1 : -1 ≤ mc) (hmc2 : mc < 2147483648)
    (hQ : ∀ le' m' aw', Mem m' L ctx (windowStep L.level cell1 cell2 v c1 (c1 + k) mc st) aw' →
      Tmp le' L (windowStep L.level cell1 cell2 v c1 (c1 + k) mc st) →
      ArrayAt m' .Mint32 L.bB 0 (upd bv v (.Vint (ir c1))) L.capB →
      Unch m m' (fun z => z = L.bp ∨ z = L.ba ∨ z = L.bn ∨ z = L.bB) → Keep m m' L.bB →
      PTree.get dense.id.c1 le' = some (.Vint (ir (c1 + k : Nat))) →
      PTree.get dense.id.maxcell le' =
        some (.Vint (ir (if Int.ofNat k > mc then (k : Int) else mc))) →
      (∀ z, z ∉ [dense.id.c1, dense.id.c2, dense.id.maxcell, dense.id.maxpos, dense.id.hint,
        dense.id.longcode] → PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge f (group D) Q empty_env le m := by
  have hnl := hok.nlt
  have d := hok.wd
  have hread := eval_gat (e := empty_env) (le := le) rfl find_naugraphBucket hbkp hbkt
    hcapB (tv dense.id.i) v hv hi rfl
  rw [hbv] at hread
  simp only [group, Set.sk]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_add_ii (x := (c1 : Int)) (y := (k : Int)) (e := empty_env) (le := le) (m := m)
    (a := tv dense.id.c1) hc1 rfl hread rfl]
  let le1 := PTree.set dense.id.c2 (.Vint (ir ((c1 : Int) + k))) le
  have hc2 : PTree.get dense.id.c2 le1 = some (.Vint (ir (c1 + k : Nat))) := by
    simp only [le1, temps_gss]; push_cast; rfl
  have ht1 : Tmp le1 L st := ht.set _ (by decide)
  wp_step; wp_step; wp_step
  refine wp_gstore rfl find_naugraphBucket hbkp hbkt hcapB (tv dense.id.i) v hv
    (by show PTree.get _ _ = _; rw [temps_gso _ _ (by decide)]; exact hi) rfl (tv dense.id.c1) c1
    (by show PTree.get _ _ = _; rw [temps_gso _ _ (by decide)]; exact hc1) rfl ?_
  intro m1 hbkt1 hu1 hk1
  obtain ⟨cv, hcv⟩ := hm.cnt
  have hm1 : Mem m1 L ctx st aw := hm.away hok (hu1.mono fun z hz => .inr (.inl hz)) hk1
    (Keep.unch hu1 d.bW_bB) ⟨cv, hcv.unch hu1 d.bc_bB⟩
  wp_step; wp_step; wp_step
  refine wp_mash ht1.longcode hcode (i := v + c1)
    (by rw [eval_add_ii (x := (v : Int)) (y := (c1 : Int))
          (by show PTree.get _ _ = _; rw [temps_gso _ _ (by decide)]; exact hi) rfl
          (by show PTree.get _ _ = _; rw [temps_gso _ _ (by decide)]; exact hc1) rfl]
        push_cast; rfl) rfl (by omega) ?_
  let le2 := PTree.set dense.id.longcode (.Vlong (lr (Hex.GraphIso.Nauty.mash st.longcode (v + c1) : Nat))) le1
  have ht2 := ht1.setCode (Hex.GraphIso.Nauty.mash st.longcode (v + c1))
  have g2 : ∀ z, z ≠ dense.id.longcode → z ≠ dense.id.c2 → PTree.get z le2 = PTree.get z le :=
    fun z h1 h2 => by simp only [le2, le1]; rw [temps_gso _ _ h1, temps_gso _ _ h2]
  dsimp only
  wp_step; wp_step; wp_step
  refine wp_grpMax (k := k) ht2 (by rw [g2 _ (by decide) (by decide)]; exact hc1)
    (by rw [temps_gso _ _ (by decide)]; exact hc2)
    (by rw [g2 _ (by decide) (by decide)]; exact hmc) (by omega) hmc1 hmc2 ?_
  intro le3 ht3 hmc3 g3
  let s3 : RefineSt n := { st with
    longcode := Hex.GraphIso.Nauty.mash st.longcode (v + c1)
    maxpos := if Int.ofNat k > mc then c1 else st.maxpos }
  have hm3 : Mem m1 L ctx s3 aw := hm1.congr rfl rfl rfl rfl
  have ht3' : Tmp le3 L s3 := ht3
  have g3' : ∀ z, z ≠ dense.id.maxcell → z ≠ dense.id.maxpos → z ≠ dense.id.longcode →
      z ≠ dense.id.c2 → PTree.get z le3 = PTree.get z le :=
    fun z h1 h2 h3 h4 => by rw [g3 z h1 h2, g2 z h3 h4]
  dsimp only
  wp_step; wp_step; wp_step
  refine wp_grpAct hD (k := k) hMok hok hm3 ht3'
    (by rw [g3' _ (by decide) (by decide) (by decide) (by decide)]; exact hc1)
    (by rw [g3 _ (by decide) (by decide)]; rw [temps_gso _ _ (by decide)]; exact hc2)
    (by rw [g3' _ (by decide) (by decide) (by decide) (by decide)]; exact hcl1)
    (by omega) (by omega) (by omega) ?_
  intro le4 m4 aw4 hm4 ht4 hu4 g4
  dsimp only
  wp_step; wp_step; wp_step
  have hsz4 : ({ s3 with
        active := if (c1 != cell1) = true then s3.active.insert c1 else s3.active
        numcells := if (c1 != cell1) = true then s3.numcells + 1 else s3.numcells
        hint := if (c1 != cell1) = true ∧ (k == 1) = true then c1 else s3.hint } : RefineSt n).ptn.size
      = n := hsz
  refine wp_grpPtn (c1 := c1) (k := k) hok hm4 ht4 hsz4
    (by rw [g4 _ (by decide), g3 _ (by decide) (by decide), temps_gso _ _ (by decide)]; exact hc2)
    (by rw [g4 _ (by decide), g3' _ (by decide) (by decide) (by decide) (by decide)]; exact hcl2)
    hk hck h2n ?_
  intro m5 hm5 hu5
  wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr]
  rw [g4 _ (by decide), g3 _ (by decide) (by decide), temps_gso _ _ (by decide), hc2]
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := windowStep_eq L.level cell1 cell2 v c1 k mc st
  refine hQ _ m5 aw4 ?_ ?_ ?_ ?_ ?_ (temps_gss _ _ _) ?_ ?_
  · refine hm5.congr ?_ ?_ ?_ ?_
    · exact e1
    · exact e7
    · exact e5
    · exact e4
  · refine (ht4.set _ (by decide)).congr ?_ ?_ ?_
    · exact e2
    · exact e6
    · exact e3
  · have hu45 : Unch m1 m5 (fun z => z = L.ba ∨ z = L.bn ∨ z = L.bp) :=
      (hu4.mono fun z hz => by rcases hz with h | h <;> simp [h]).trans
        (hu5.mono fun z hz => by simp [hz])
    exact hbkt1.unch hu45 (by
      rintro (h | h | h)
      · exact d.ba_bB h.symm
      · exact d.bn_bB h.symm
      · exact d.bp_bB h.symm)
  · refine (hu1.mono fun z hz => ?_).trans ((hu4.mono fun z hz => ?_).trans (hu5.mono fun z hz => ?_))
    · exact .inr (.inr (.inr hz))
    · rcases hz with h | h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
    · exact .inl hz
  · refine hk1.trans ((Keep.unch hu4 ?_).trans (Keep.unch hu5 (Ne.symm d.bp_bB)))
    rintro (h | h)
    · exact d.ba_bB h.symm
    · exact d.bn_bB h.symm
  · rw [temps_gso _ _ (by decide), g4 _ (by decide)]; exact hmc3
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hz
    rw [temps_gso _ _ h0, g4 z h4, g3' z h2 h3 h5 h1]

theorem wp_scanLoop {D : Dialect} (hD : D.Sem) {f : function} {Q : Post} {le : temp_env} {m : mem} {n : Nat} {L : Loc} {ctx : Ctx n}
    {st : RefineSt n} {aw : Nat → Lib.Integers.int64} {ws : VSet n}
    {cell1 cell2 : Nat} {bv0 : Nat → val}
    (hMok : D.okM L.M)
    (hf : CFrame m L ctx st.lab) (hm : Mem m L ctx st aw) (ht : Tmp le L st)
    (hb0 : SBound n st st cell1 cell1) (h12 : cell1 < cell2) (h2n : cell2 < n)
    (hi : PTree.get dense.id.i le =
      some (.Vint (ir (cmin (countsOf ctx st.lab ws cell1 cell2) : Nat))))
    (hbmax : PTree.get dense.id.bmax le =
      some (.Vint (ir (cmax (countsOf ctx st.lab ws cell1 cell2) : Nat))))
    (hc1 : PTree.get dense.id.c1 le = some (.Vint (ir cell1)))
    (hmc : PTree.get dense.id.maxcell le = some (.Vint (ir (-1))))
    (hcl1 : PTree.get dense.id.cell1 le = some (.Vint (ir cell1)))
    (hcl2 : PTree.get dense.id.cell2 le = some (.Vint (ir cell2)))
    (hbkt : ArrayAt m .Mint32 L.bB 0 (fun v =>
      if cmin (countsOf ctx st.lab ws cell1 cell2) ≤ v ∧ v ≤ cmax (countsOf ctx st.lab ws cell1 cell2)
      then .Vint (ir (multOf (countsOf ctx st.lab ws cell1 cell2) v : Nat)) else bv0 v) L.capB)
    (hQ : ∀ le' m' aw',
      Mem m' L ctx (windowScan L.level cell1 cell2 (countsOf ctx st.lab ws cell1 cell2)
        (countValues (countsOf ctx st.lab ws cell1 cell2)) cell1 (-1) st) aw' →
      Tmp le' L (windowScan L.level cell1 cell2 (countsOf ctx st.lab ws cell1 cell2)
        (countValues (countsOf ctx st.lab ws cell1 cell2)) cell1 (-1) st) →
      SBound n st (windowScan L.level cell1 cell2 (countsOf ctx st.lab ws cell1 cell2)
        (countValues (countsOf ctx st.lab ws cell1 cell2)) cell1 (-1) st) cell1 (cell2 + 1) →
      ArrayAt m' .Mint32 L.bB 0 (startVals (countsOf ctx st.lab ws cell1 cell2) cell1 bv0) L.capB →
      Unch m m' (fun z => z = L.bp ∨ z = L.ba ∨ z = L.bn ∨ z = L.bB) → Keep m m' L.bB →
      (∀ z, z ∉ [dense.id.i, dense.id.c1, dense.id.c2, dense.id.maxcell, dense.id.maxpos,
        dense.id.hint, dense.id.longcode] → PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge f (scanLoopG D) Q empty_env le m := by
  have hok := hf.ok
  have hnl := hok.nlt
  have hcapB := hf.capB
  have hcapB2 := hok.capB
  have hlv := hok.levlt
  generalize hcs : countsOf ctx st.lab ws cell1 cell2 = cs at *
  have hlen : cs.length = cell2 - cell1 + 1 := by rw [← hcs, countsOf_length]; omega
  have hcle : ∀ o, cs[o]! ≤ n := fun o => by rw [← hcs]; exact countsOf_le ctx st.lab ws cell1 cell2 o
  have hab : cmin cs ≤ cmax cs := by
    rw [cmin, cmax, ← pmin_last (k := cell2 - cell1) (by omega),
      ← pmax_last (k := cell2 - cell1) (by omega)]
    exact pmin_le_pmax (by omega)
  have hbn : cmax cs ≤ n := by
    rw [cmax, ← pmax_last (k := cell2 - cell1) (by omega)]; exact pmax_le hcle (by omega)
  have hmlt : ∀ v, multOf cs v ≤ cs.length := fun v => List.countP_le_length
  have hbl : ∀ v, below cs v ≤ cs.length := fun v => below_le cs v
  generalize hA : cmin cs = A at *
  generalize hB : cmax cs = B at *
  have hcv : countValues cs = List.range' A (B + 1 - A) := by
    rw [countValues, List.range'_eq_map_range]
    simp only [← hA, ← hB, cmin, cmax]
  rw [hcv] at hQ
  -- the bucket values below and above the scan position `j`
  let bk := fun (j : Nat) (v : Nat) => if A ≤ v ∧ v ≤ B then
    (if v < j then (if multOf cs v = 0 then Vint (ir 0) else Vint (ir (cell1 + below cs v : Nat)))
      else Vint (ir (multOf cs v : Nat))) else bv0 v
  let S := windowScan L.level cell1 cell2 cs (List.range' A (B + 1 - A)) cell1 (-1) st
  let Oth := fun le' : temp_env => ∀ z, z ∉ [dense.id.i, dense.id.c1, dense.id.c2, dense.id.maxcell,
    dense.id.maxpos, dense.id.hint, dense.id.longcode] → PTree.get z le' = PTree.get z le
  let P := fun (j : Nat) (le' : temp_env) (m' : mem) => ∃ (c1 : Nat) (mc : Int) (s : RefineSt n)
      (aw' : Nat → Lib.Integers.int64),
    A ≤ j ∧ j ≤ B + 1 ∧ c1 = cell1 + below cs j ∧
    PTree.get dense.id.c1 le' = some (.Vint (ir c1)) ∧
    PTree.get dense.id.maxcell le' = some (.Vint (ir mc)) ∧ -1 ≤ mc ∧ mc ≤ n ∧
    windowScan L.level cell1 cell2 cs (List.range' j (B + 1 - j)) c1 mc s = S ∧
    Mem m' L ctx s aw' ∧ Tmp le' L s ∧ SBound n st s cell1 c1 ∧
    ArrayAt m' .Mint32 L.bB 0 (bk j) L.capB ∧
    Unch m m' (fun z => z = L.bp ∨ z = L.ba ∨ z = L.bn ∨ z = L.bB) ∧ Keep m m' L.bB ∧ Oth le'
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ j, v = B + 1 - j ∧ PTree.get dense.id.i le' = some (.Vint (ir j)) ∧ P j le' m'
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ j, j ≤ B ∧ v = B + 1 - j ∧ PTree.get dense.id.i le' = some (.Vint (ir j)) ∧
      P (j + 1) le' m'
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := B + 1 - A) ⟨rfl, rfl, A, rfl, hi, cell1, -1, st, aw,
    Nat.le_refl _, by omega, ?_, hc1, hmc, by decide, by omega, rfl, hm, ht, hb0,
    hbkt.congr fun v _ => ?_, Unch.refl _ _, Keep.refl _ _, fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, j, rfl, hij, c1, mc, s, aw', hj1, hj2, hc1e, hc1', hmc',
      hmc1, hmc2, hS, hms, hts, hsb, hbk, hu, hk, ho⟩
    have hbmax' : PTree.get dense.id.bmax le' = some (.Vint (ir (B : Nat))) := by
      rw [ho _ (by decide)]; exact hbmax
    have hcl1' : PTree.get dense.id.cell1 le' = some (.Vint (ir cell1)) := by
      rw [ho _ (by decide)]; exact hcl1
    have hcl2' : PTree.get dense.id.cell2 le' = some (.Vint (ir cell2)) := by
      rw [ho _ (by decide)]; exact hcl2
    have hfu := hf.unch (hu.mono fun z hz => by
      rcases hz with h | h | h | h <;> simp [h])
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hij, hbmax', typeof, cop]
    rw [ir_lt (a := (B : Int)) (b := (j : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hjB : j ≤ B
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      wp_step; wp_step
      apply wp_if_eval
      have hread := eval_gat (e := empty_env) (le := le') rfl find_naugraphBucket hfu.bkp hbk
        hcapB (tv dense.id.i) j (by omega) hij rfl
      have hread2 : Exec.evalExpr ge empty_env le' m' (gix dense.id.«naugraph:bucket» (tv dense.id.i)) =
          some (.Vint (ir (multOf cs j : Nat))) := by
        rw [hread]; simp only [bk]; rw [ite_eq_left ⟨hj1, hjB⟩, ite_eq_right (Nat.lt_irrefl j)]
      rw [hread2]
      simp only [typeof, cop]
      have hml := hmlt j
      rw [show Lib.Integers.Int.zero = ir 0 from rfl,
        ir_eq (a := ((multOf cs j : Nat) : Int)) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
      have hrng : List.range' j (B + 1 - j) = j :: List.range' (j + 1) (B + 1 - (j + 1)) := by
        rw [show B + 1 - j = (B + 1 - (j + 1)) + 1 by omega, List.range'_succ]
      by_cases hm0 : multOf cs j = 0
      · rw [ite_eq_right (by simp [hm0])]
        apply wp_skip
        refine ⟨rfl, rfl, j, hjB, rfl, hij, c1, mc, s, aw', by omega, by omega, ?_, hc1', hmc', hmc1,
          hmc2, ?_, hms, hts, hsb, hbk.congr fun v _ => ?_, hu, hk, ho⟩
        · rw [below_succ, hm0, Nat.add_zero]; exact hc1e
        · rw [← hS, hrng, windowScan, ite_eq_right (show ¬ multOf cs j > 0 by omega)]
        · simp only [bk]
          by_cases hv : A ≤ v ∧ v ≤ B
          · rw [ite_eq_left hv, ite_eq_left hv]
            by_cases hvj : v = j
            · subst hvj; simp [hm0]
            · by_cases hvj2 : v < j
              · rw [ite_eq_left hvj2, ite_eq_left (show v < j + 1 by omega)]
              · rw [ite_eq_right hvj2, ite_eq_right (show ¬ v < j + 1 by omega)]
          · rw [ite_eq_right hv, ite_eq_right hv]
      · rw [ite_eq_left (by simp; omega)]
        have hbl1 : below cs (j + 1) ≤ cs.length := hbl (j + 1)
        rw [below_succ] at hbl1
        refine wp_group hD (k := multOf cs j) hMok hok hms hts hsb.psize hsb.code hij hc1' hmc' hcl1' hcl2'
          hbk ?_ hfu.bkp hcapB (by omega) (by omega) (by omega) (by omega) (by omega) h2n hmc1
          (by omega) ?_
        · simp only [bk]; rw [ite_eq_left ⟨hj1, hjB⟩, ite_eq_right (Nat.lt_irrefl j)]
        intro le2 m2 aw2 hm2 ht2 hbk2 hu2 hk2 hc12 hmc22 ho2
        refine ⟨rfl, rfl, j, hjB, rfl, ?_, c1 + multOf cs j,
          (if Int.ofNat (multOf cs j) > mc then (multOf cs j : Int) else mc), _, aw2, by omega,
          by omega, ?_, hc12, hmc22, ?_, ?_, ?_, hm2, ht2, ?_, hbk2.congr fun v _ => ?_,
          hu.trans (hu2.mono fun z hz => hz), hk.trans hk2, fun z hz => ?_⟩
        · rw [ho2 _ (by decide)]; exact hij
        · rw [below_succ, hc1e, Nat.add_assoc]
        · split <;> omega
        · split <;> omega
        · rw [← hS, hrng, windowScan, ite_eq_left (show multOf cs j > 0 by omega)]
          rfl
        · exact hsb.step (by omega) (by omega) h2n hlv (by omega)
        · simp only [bk, upd]
          by_cases hv : A ≤ v ∧ v ≤ B
          · rw [ite_eq_left hv, ite_eq_left hv]
            by_cases hvj : v = j
            · subst hvj
              rw [ite_eq_left rfl, ite_eq_left (show v < v + 1 by omega), ite_eq_right hm0, hc1e]
            · rw [ite_eq_right hvj]
              by_cases hvj2 : v < j
              · rw [ite_eq_left hvj2, ite_eq_left (show v < j + 1 by omega)]
              · rw [ite_eq_right hvj2, ite_eq_right (show ¬ v < j + 1 by omega)]
          · have hvj : ¬ v = j := fun h => hv (h ▸ ⟨hj1, hjB⟩)
            rw [ite_eq_right hvj, ite_eq_right hv, ite_eq_right hv]
        · have hz' : z ∉ [dense.id.c1, dense.id.c2, dense.id.maxcell, dense.id.maxpos, dense.id.hint,
              dense.id.longcode] := fun h => hz (List.mem_cons_of_mem _ h)
          rw [ho2 z hz', ho z hz]
    · rw [ite_eq_right (by simp; omega)]
      apply wp_break
      have hjB1 : j = B + 1 := by omega
      subst hjB1
      obtain rfl : s = windowScan L.level cell1 cell2 cs (List.range' A (B + 1 - A)) cell1 (-1) st := by
        have h := hS
        simp only [Nat.sub_self, List.range'_zero, windowScan] at h
        exact h
      refine hQ le' m' aw' hms hts ?_ (hbk.congr fun v _ => ?_) hu hk ho
      · exact { hsb with nc := by have := hsb.nc; have := hbl (B + 1); omega }
      · simp only [bk, startVals, hA, hB]
        by_cases hv : A ≤ v ∧ v ≤ B
        · rw [ite_eq_left hv, ite_eq_left hv, ite_eq_left (by omega)]
        · rw [ite_eq_right hv, ite_eq_right hv]
  · rintro v tr e' le' m' ⟨rfl, rfl, j, hjB, rfl, hij, c1, mc, s, aw', hj1, hj2, hc1e, hc1', hmc',
      hmc1, hmc2, hS, hms, hts, hsb, hbk, hu, hk, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hij, typeof, cop, ir_add]
    refine ⟨B + 1 - (j + 1), by omega, by simp, rfl, j + 1, rfl, by rw [temps_gss]; push_cast; rfl, c1, mc, s, aw',
      hj1, hj2, hc1e, by rw [temps_gso _ _ (by decide)]; exact hc1',
      by rw [temps_gso _ _ (by decide)]; exact hmc', hmc1, hmc2, hS, hms, hts.set _ (by decide),
      hsb, hbk, hu, hk, fun z hz => ?_⟩
    have : z ≠ dense.id.i := fun h => hz (h ▸ by simp)
    rw [temps_gso _ _ this, ho z hz]
  · rw [← hA, below_cmin, Nat.add_zero]
  · simp only [bk]
    by_cases hv : A ≤ v ∧ v ≤ B
    · rw [ite_eq_left hv, ite_eq_left hv, ite_eq_right (by omega)]
    · rw [ite_eq_right hv, ite_eq_right hv]

end NautyVerified.Proofs.Refine
