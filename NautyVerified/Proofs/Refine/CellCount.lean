import NautyVerified.Proofs.Refine.CountN
import NautyVerified.Proofs.Refine.WindowN
import NautyVerified.Spec.CountWin

/-!
# Counting one cell

`wp_countRest`: after the first member of the cell `[cell1, cell2]`, the loop
`while (++i <= cell2) { cnt = …; widen the window; ++bucket[cnt]; count[i] = cnt; }`
leaves `count[cell1 + o]` holding the count `cs[o]` of every member
(`cs = countsOf …`), `bmin`/`bmax` the least and greatest counts, and
`bucket[v]` the multiplicity of each `v` in `[bmin, bmax]`.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs NautyVerified.Proofs.Alloc
open NautyVerified.Proofs.Init (BytecountTable)
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Graph (GraphAt)
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

theorem countsOf_length {n : Nat} (ctx : Ctx n) (lab : Array Nat) (ws : VSet n) (cell1 cell2 : Nat) :
    (countsOf ctx lab ws cell1 cell2).length = cell2 + 1 - cell1 := by
  simp [countsOf]

theorem countsOf_get {n : Nat} (ctx : Ctx n) (lab : Array Nat) (ws : VSet n) {cell1 cell2 o : Nat}
    (ho : o < cell2 + 1 - cell1) :
    (countsOf ctx lab ws cell1 cell2)[o]! = ws.cardInter ctx.g[lab[cell1 + o]!]! := by
  rw [getElem!_pos _ o (by rw [countsOf_length]; exact ho)]
  simp [countsOf]

/-- The `count` array after the first `k + 1` members. -/
def cntVals (cs : List Nat) (cell1 k : Nat) (cv0 : Nat → val) (p : Nat) : val :=
  if cell1 ≤ p ∧ p ≤ cell1 + k then .Vint (ir (cs[p - cell1]! : Nat)) else cv0 p

/-- The `bucket` array after the first `k + 1` members. -/
def bktVals (cs : List Nat) (k : Nat) (bv0 : Nat → val) (v : Nat) : val :=
  if pmin cs k ≤ v ∧ v ≤ pmax cs k then .Vint (ir (pmult cs k v : Nat)) else bv0 v

/-- The bucket after both widenings for the next count `c`. -/
theorem bkt_widen (cs : List Nat) (k c : Nat) (hk : k < cs.length) (bv0 : Nat → val) (v : Nat) :
    (if pmax cs k < v ∧ v ≤ max (pmax cs k) c then .Vint (ir 0) else
      (if min (pmin cs k) c ≤ v ∧ v < pmin cs k then .Vint (ir 0) else bktVals cs k bv0 v)) =
    (if min (pmin cs k) c ≤ v ∧ v ≤ max (pmax cs k) c then .Vint (ir (pmult cs k v : Nat))
      else bv0 v) := by
  have hle := pmin_le_pmax hk
  have hout := pmult_out hk v
  unfold bktVals
  by_cases h1 : pmax cs k < v ∧ v ≤ max (pmax cs k) c
  · rw [ite_eq_left h1, ite_eq_left (by omega), hout (.inr h1.1)]; rfl
  · rw [ite_eq_right h1]
    by_cases h2 : min (pmin cs k) c ≤ v ∧ v < pmin cs k
    · rw [ite_eq_left h2, ite_eq_left (by omega), hout (.inl h2.2)]; rfl
    · rw [ite_eq_right h2]
      by_cases h3 : pmin cs k ≤ v ∧ v ≤ pmax cs k
      · rw [ite_eq_left h3, ite_eq_left (by omega)]
      · rw [ite_eq_right h3, ite_eq_right (by omega)]

theorem bkt_inc (cs : List Nat) (k : Nat) (hk : k + 1 < cs.length) (bv0 : Nat → val) (v : Nat) :
    upd (fun v => if min (pmin cs k) cs[k + 1]! ≤ v ∧ v ≤ max (pmax cs k) cs[k + 1]! then
        Vint (ir (pmult cs k v : Nat)) else bv0 v) cs[k + 1]!
      (.Vint (ir ((pmult cs k cs[k + 1]! : Nat) + 1))) v = bktVals cs (k + 1) bv0 v := by
  unfold bktVals
  rw [pmin_succ hk, pmax_succ hk, pmult_succ hk]
  simp only [upd]
  by_cases hv : v = cs[k + 1]!
  · subst hv
    rw [ite_eq_left rfl, ite_eq_left (by omega), ite_eq_left rfl]
    push_cast; rfl
  · rw [ite_eq_right hv]
    by_cases h3 : min (pmin cs k) cs[k + 1]! ≤ v ∧ v ≤ max (pmax cs k) cs[k + 1]!
    · rw [ite_eq_left h3, ite_eq_left h3, ite_eq_right (Ne.symm hv), Nat.add_zero]
    · rw [ite_eq_right h3, ite_eq_right h3]

theorem cnt_inc (cs : List Nat) (cell1 k : Nat) (cv0 : Nat → val) (p : Nat) :
    upd (cntVals cs cell1 k cv0) (cell1 + (k + 1)) (.Vint (ir (cs[k + 1]! : Nat))) p =
      cntVals cs cell1 (k + 1) cv0 p := by
  unfold cntVals
  simp only [upd]
  by_cases hp : p = cell1 + (k + 1)
  · subst hp; rw [ite_eq_left rfl, ite_eq_left (by omega), show cell1 + (k + 1) - cell1 = k + 1 by omega]
  · rw [ite_eq_right hp]
    by_cases h : cell1 ≤ p ∧ p ≤ cell1 + k
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- What the nontrivial pass reads while it counts and splits one cell: the
graph, `lab`, the splitter's words, the pointer globals and the tables. -/
structure CFrame {n : Nat} (m : mem) (L : Loc) (ctx : Ctx n) (lab : Array Nat) (ws : VSet n)
    (wsw : Nat → Lib.Integers.int64) : Prop where
  ok : Ok n L
  graph : GraphAt m L.bg L.gofs L.gw ctx.g L.M
  larr : ArrayAt m .Mint32 L.bl L.lb (ints lab) n
  labs : ∀ i < n, lab[i]! < n
  wsA : ArrayAt m .Mint64 L.bS 0 (longs wsw) L.M
  wsR : SetRep (fun w => bv64 (wsw w)) L.M ws
  wsp : Mem.load .Mint64 m Block.naugraphWorkset (zOfInt 0) = some (.Vptr L.bS Ptrofs.zero)
  bkp : Mem.load .Mint64 m Block.naugraphBucket (zOfInt 0) = some (.Vptr L.bB Ptrofs.zero)
  wpp : Mem.load .Mint64 m Block.naugraphWorkperm (zOfInt 0) = some (.Vptr L.bW Ptrofs.zero)
  bytes : BytecountTable m
  bit : Set.BitTable m Block.naugraphBit
  capB : L.capB < 2147483648
  capW : L.capW < 2147483648

/-- `CFrame` survives writes to `count`, `bucket`, `workperm`, `ptn`, `active`
and `*numcells`. -/
theorem CFrame.unch {n : Nat} {m m' : mem} {L : Loc} {ctx : Ctx n} {lab : Array Nat} {ws : VSet n}
    {wsw : Nat → Lib.Integers.int64} (h : CFrame m L ctx lab ws wsw)
    (hu : Unch m m' (fun z => z = L.bc ∨ z = L.bB ∨ z = L.bW ∨ z = L.bp ∨ z = L.ba ∨ z = L.bn)) :
    CFrame m' L ctx lab ws wsw :=
  have d := h.ok.wd
  have nW : ∀ {g : block}, L.bc ≠ g → L.bB ≠ g → L.bW ≠ g → L.bp ≠ g → L.ba ≠ g → L.bn ≠ g →
      ¬ (g = L.bc ∨ g = L.bB ∨ g = L.bW ∨ g = L.bp ∨ g = L.ba ∨ g = L.bn) :=
    fun h1 h2 h3 h4 h5 h6 h => by
      rcases h with h | h | h | h | h | h
      · exact h1 h.symm
      · exact h2 h.symm
      · exact h3 h.symm
      · exact h4 h.symm
      · exact h5 h.symm
      · exact h6 h.symm
  { h with
    graph := ⟨h.graph.arr.unch hu (nW (Ne.symm d.bg_bc) (Ne.symm d.bg_bB) (Ne.symm d.bg_bW)
      (Ne.symm d.bg_bp) (Ne.symm d.bg_ba) (Ne.symm d.bg_bn)), h.graph.rep⟩
    larr := h.larr.unch hu (nW (Ne.symm d.bl_bc) (Ne.symm d.bl_bB) (Ne.symm d.bl_bW)
      (Ne.symm d.bl_bp) (Ne.symm d.bl_ba) (Ne.symm d.bl_bn))
    wsA := h.wsA.unch hu (nW d.bc_bS (Ne.symm d.bS_bB) (d.bW_bS) (d.bp_bS) (d.ba_bS) (d.bn_bS))
    wsp := by rw [hu.load _ _ _ (nW d.bc_g2 d.bB_g2 d.bW_g2 d.bp_g2 d.ba_g2 d.bn_g2)]; exact h.wsp
    bkp := by rw [hu.load _ _ _ (nW d.bc_g4 d.bB_g4 d.bW_g4 d.bp_g4 d.ba_g4 d.bn_g4)]; exact h.bkp
    wpp := by rw [hu.load _ _ _ (nW d.bc_g0 d.bB_g0 d.bW_g0 d.bp_g0 d.ba_g0 d.bn_g0)]; exact h.wpp
    bytes := BytecountTable.unch h.bytes hu (nW d.bc_g7 d.bB_g7 d.bW_g7 d.bp_g7 d.ba_g7 d.bn_g7)
    bit := h.bit.unch hu (nW d.bc_g6 d.bB_g6 d.bW_g6 d.bp_g6 d.ba_g6 d.bn_g6) }

theorem cardInter_le {n : Nat} (s t : VSet n) : s.cardInter t ≤ n := by
  rw [VSet.cardInter_eq]; exact VSet.card_le _

theorem countsOf_le {n : Nat} (ctx : Ctx n) (lab : Array Nat) (ws : VSet n) (cell1 cell2 : Nat)
    (o : Nat) : (countsOf ctx lab ws cell1 cell2)[o]! ≤ n := by
  by_cases ho : o < cell2 + 1 - cell1
  · rw [countsOf_get ctx lab ws ho]; exact cardInter_le _ _
  · rw [getElem!_neg _ _ (by rw [countsOf_length]; omega)]; exact Nat.zero_le _

/-- The temporaries the counting loop assigns. -/
def cntTemps : List Common.AST.ident :=
  [dense.id.i, idOf 724, dense.id.set1, dense.id.set2, dense.id.cnt, dense.id.c1, idOf 725,
   idOf 726, idOf 727, idOf 728, dense.id.x, dense.id.bmin, dense.id.bmax, idOf 729, idOf 730]

/-- `Tmp` survives assignments to temporaries outside `args` and the three scalars. -/
theorem Tmp.away {n : Nat} {le le' : temp_env} {L : Loc} {st : RefineSt n} (h : Tmp le L st)
    (T : List Common.AST.ident)
    (hT : ∀ x ∈ args ++ [dense.id.longcode, dense.id.hint, dense.id.maxpos], x ∉ T)
    (hle : ∀ z, z ∉ T → PTree.get z le' = PTree.get z le) : Tmp le' L st :=
  h.temps fun x hx => hle x (hT x (by
    rcases hx with hx | hx | hx | hx
    · exact List.mem_append_left _ hx
    · subst hx; simp
    · subst hx; simp
    · subst hx; simp))

theorem wp_countRest {Q : Post} {le : temp_env} {m : mem} {n : Nat} {L : Loc} {ctx : Ctx n}
    {st : RefineSt n} {ws : VSet n} {wsw : Nat → Lib.Integers.int64} {cell1 cell2 : Nat}
    {cv0 bv0 : Nat → val}
    (hf : CFrame m L ctx st.lab ws wsw) (ht : Tmp le L st)
    (h12 : cell1 < cell2) (h2n : cell2 < n)
    (hi : PTree.get dense.id.i le = some (.Vint (ir cell1)))
    (hc2 : PTree.get dense.id.cell2 le = some (.Vint (ir cell2)))
    (hbmin : PTree.get dense.id.bmin le =
      some (.Vint (ir (pmin (countsOf ctx st.lab ws cell1 cell2) 0 : Nat))))
    (hbmax : PTree.get dense.id.bmax le =
      some (.Vint (ir (pmax (countsOf ctx st.lab ws cell1 cell2) 0 : Nat))))
    (hcnt : ArrayAt m .Mint32 L.bc L.cb (cntVals (countsOf ctx st.lab ws cell1 cell2) cell1 0 cv0) n)
    (hbkt : ArrayAt m .Mint32 L.bB 0 (bktVals (countsOf ctx st.lab ws cell1 cell2) 0 bv0) L.capB)
    (hQ : ∀ le' m',
      PTree.get dense.id.bmin le' =
        some (.Vint (ir (pmin (countsOf ctx st.lab ws cell1 cell2) (cell2 - cell1) : Nat))) →
      PTree.get dense.id.bmax le' =
        some (.Vint (ir (pmax (countsOf ctx st.lab ws cell1 cell2) (cell2 - cell1) : Nat))) →
      ArrayAt m' .Mint32 L.bc L.cb
        (cntVals (countsOf ctx st.lab ws cell1 cell2) cell1 (cell2 - cell1) cv0) n →
      ArrayAt m' .Mint32 L.bB 0
        (bktVals (countsOf ctx st.lab ws cell1 cell2) (cell2 - cell1) bv0) L.capB →
      Unch m m' (fun z => z = L.bc ∨ z = L.bB) → Keep m m' L.bB →
      (∀ z, z ∉ cntTemps → PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.refine countRest Q empty_env le m := by
  have hok := hf.ok
  have d := hok.wd
  have hcap := hok.capB
  have hnlt := hok.nlt
  generalize hcs : countsOf ctx st.lab ws cell1 cell2 = cs at *
  have hlen : cs.length = cell2 - cell1 + 1 := by rw [← hcs, countsOf_length]; omega
  have hcle : ∀ o, cs[o]! ≤ n := fun o => by rw [← hcs]; exact countsOf_le ctx st.lab ws cell1 cell2 o
  let F := cell2 - cell1
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ k, k ≤ F ∧ v = F - k ∧
      PTree.get dense.id.i le' = some (.Vint (ir (cell1 + k : Nat))) ∧
      PTree.get dense.id.bmin le' = some (.Vint (ir (pmin cs k : Nat))) ∧
      PTree.get dense.id.bmax le' = some (.Vint (ir (pmax cs k : Nat))) ∧
      ArrayAt m' .Mint32 L.bc L.cb (cntVals cs cell1 k cv0) n ∧
      ArrayAt m' .Mint32 L.bB 0 (bktVals cs k bv0) L.capB ∧
      Unch m m' (fun z => z = L.bc ∨ z = L.bB) ∧ Keep m m' L.bB ∧
      (∀ z, z ∉ cntTemps → PTree.get z le' = PTree.get z le)
  refine wp_loop (I := I) (J := fun v tr e' le' m' => ∃ v', v' < v ∧ I v' tr e' le' m') ?_ ?_
    (n := F) ⟨rfl, rfl, 0, Nat.zero_le _, rfl, by simpa using hi, hbmin, hbmax, hcnt, hbkt,
      Unch.refl _ _, Keep.refl _ _, fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, k, hk, rfl, hik, hmin, hmax, hca, hba, hu, hkp, ho⟩
    have hc2' : PTree.get dense.id.cell2 le' = some (.Vint (ir cell2)) := by
      rw [ho _ (by decide)]; exact hc2
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hik, typeof, cop, ir_add]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, temps_gso _ _ (show (idOf 724) ≠ dense.id.i by decide),
      typeof, cop]
    rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), hc2']
    simp only [cop]
    rw [ir_lt (a := (cell2 : Int)) (b := ((cell1 + k : Nat) : Int) + 1) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    by_cases hkF : k = F
    · rw [ite_eq_right (by simp; omega)]
      apply wp_break
      subst hkF
      simp only [E0_append]
      refine hQ _ _ ?_ ?_ hca hba hu hkp ?_
      · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hmin
      · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hmax
      · intro z hz
        have h1 : z ≠ dense.id.i := fun h => hz (h ▸ by simp [cntTemps])
        have h2 : z ≠ idOf 724 := fun h => hz (h ▸ by simp [cntTemps])
        rw [temps_gso _ _ h1, temps_gso _ _ h2, ho z hz]
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      dsimp only
      have hk1 : k + 1 < cs.length := by omega
      have hcu := hf.unch (hu.mono fun z hz => by rcases hz with h | h <;> simp [h])
      let le2 := PTree.set dense.id.i (.Vint (ir (((cell1 + k : Nat) : Int) + 1)))
        (PTree.set (idOf 724) (.Vint (ir (((cell1 + k : Nat) : Int) + 1))) le')
      have ho2 : ∀ z, z ∉ cntTemps → PTree.get z le2 = PTree.get z le := fun z hz => by
        have h1 : z ≠ dense.id.i := fun h => hz (h ▸ by simp [cntTemps])
        have h2 : z ≠ idOf 724 := fun h => hz (h ▸ by simp [cntTemps])
        simp only [le2]; rw [temps_gso _ _ h1, temps_gso _ _ h2, ho z hz]
      have ht2 : Tmp le2 L st := ht.away cntTemps (by decide) ho2
      have hi2 : PTree.get dense.id.i le2 = some (.Vint (ir (cell1 + (k + 1) : Nat))) := by
        simp only [le2, temps_gss]; push_cast; rw [Int.add_assoc]
      have hlk := hf.labs (cell1 + (k + 1)) (by omega)
      refine wp_cntHead (by decide) hok ht2 hcu.graph hcu.larr hcu.wsA hcu.wsR hcu.wsp hi2
        (by omega) hlk hcu.bytes ?_
      intro le3 hcnt3 ho3
      have hcs1 : ws.cardInter ctx.g[st.lab[cell1 + (k + 1)]!]! = cs[k + 1]! := by
        rw [← hcs, countsOf_get ctx st.lab ws (by omega)]
      rw [hcs1] at hcnt3
      have hg3 : ∀ z, z ≠ dense.id.c1 → z ≠ idOf 725 → z ≠ idOf 726 → z ≠ idOf 727 → z ≠ idOf 728 →
          z ≠ dense.id.x → z ≠ dense.id.set1 → z ≠ dense.id.set2 → z ≠ dense.id.cnt →
          z ≠ dense.id.i → z ≠ idOf 724 → PTree.get z le3 = PTree.get z le' :=
        fun z h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
          rw [ho3 z h0 h1 h2 h3 h4 h5 h6 h7 h8, temps_gso _ _ h9, temps_gso _ _ h10]
      have hmin3 : PTree.get dense.id.bmin le3 = some (.Vint (ir (pmin cs k : Nat))) := by
        rw [hg3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact hmin
      have hmax3 : PTree.get dense.id.bmax le3 = some (.Vint (ir (pmax cs k : Nat))) := by
        rw [hg3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact hmax
      have hpk := pmin_le (cs := cs) (k := k) (o := 0) (by omega) (Nat.zero_le _)
      have hxk := le_pmax (cs := cs) (k := k) (o := 0) (by omega) (Nat.zero_le _)
      have hc0 := hcle 0
      have hck := hcle (k + 1)
      have hpmax := le_pmax (cs := cs) (k := k) (o := k) (by omega) (Nat.le_refl _)
      have hck2 := hcle k
      have hmaxle : pmax cs k ≤ n := pmax_le hcle (by omega)
      have hcapB := hf.capB
      wp_step
      refine wp_widenLo (by decide) (by decide) hmin3 hcnt3 hba (hcu.bkp) (Ne.symm d.bB_g4)
        (by omega) (by omega) (by omega) ?_
      intro le4 m4 hmin4 hba4 hu4 hk4 ho4
      have hcnt4 : PTree.get dense.id.cnt le4 = some (.Vint (ir (cs[k + 1]! : Nat))) := by
        rw [ho4 _ (by decide) (by decide)]; exact hcnt3
      have hmax4 : PTree.get dense.id.bmax le4 = some (.Vint (ir (pmax cs k : Nat))) := by
        rw [ho4 _ (by decide) (by decide)]; exact hmax3
      have hbkp4 : Mem.load .Mint64 m4 Block.naugraphBucket (zOfInt 0) =
          some (.Vptr L.bB Ptrofs.zero) := by rw [hu4.load _ _ _ (Ne.symm d.bB_g4)]; exact hcu.bkp
      wp_step
      refine wp_widenHi (by decide) (by decide) hmax4 hcnt4 hba4 hbkp4 (Ne.symm d.bB_g4)
        (by omega) (by omega) (by omega) ?_
      intro le5 m5 hmax5 hba5 hu5 hk5 ho5
      have hcnt5 : PTree.get dense.id.cnt le5 = some (.Vint (ir (cs[k + 1]! : Nat))) := by
        rw [ho5 _ (by decide) (by decide)]; exact hcnt4
      have hbkp5 : Mem.load .Mint64 m5 Block.naugraphBucket (zOfInt 0) =
          some (.Vptr L.bB Ptrofs.zero) := by rw [hu5.load _ _ _ (Ne.symm d.bB_g4)]; exact hbkp4
      have hW : ∀ v, (if pmax cs k < v ∧ v ≤ max (pmax cs k) cs[k + 1]! then Vint (ir 0) else
          (if min (pmin cs k) cs[k + 1]! ≤ v ∧ v < pmin cs k then Vint (ir 0) else
            bktVals cs k bv0 v)) =
          (if min (pmin cs k) cs[k + 1]! ≤ v ∧ v ≤ max (pmax cs k) cs[k + 1]! then
            Vint (ir (pmult cs k v : Nat)) else bv0 v) :=
        bkt_widen cs k cs[k + 1]! (by omega) bv0
      have hba5' := hba5.congr fun v _ => hW v
      have hread := eval_gat (e := empty_env) (le := le5) rfl find_naugraphBucket hbkp5 hba5'
        (by omega) (tv dense.id.cnt) cs[k + 1]! (by omega) hcnt5 rfl
      simp only [and_self, Nat.min_le_right, Nat.le_max_right, ite_true] at hread
      wp_step; wp_step; wp_step
      refine wp_gstore rfl find_naugraphBucket hbkp5 hba5' (by omega) (tv dense.id.cnt) cs[k + 1]!
        (by omega) hcnt5 rfl _ ((pmult cs k cs[k + 1]! : Nat) + 1)
        (by rw [eval_add_ii hread rfl (x := ((pmult cs k cs[k + 1]! : Nat) : Int)) (y := 1)
          (show Exec.evalExpr ge empty_env le5 m5 (ci 1 tint) = some (.Vint (ir 1)) from rfl) rfl])
        rfl ?_
      intro m6 hba6 hu6 hk6
      dsimp only
      have hu46 : Unch m' m6 (· = L.bB) := (hu4.trans hu5).trans hu6
      have hca6 := hca.unch hu46 d.bc_bB
      have hi5 : PTree.get dense.id.i le5 = some (.Vint (ir (cell1 + (k + 1) : Nat))) := by
        rw [ho5 _ (by decide) (by decide), ho4 _ (by decide) (by decide),
          ho3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]
        exact hi2
      have ht5 : Tmp le5 L st := by
        refine ht2.away [dense.id.c1, idOf 725, idOf 726, idOf 727, idOf 728, dense.id.x,
          dense.id.set1, dense.id.set2, dense.id.cnt, dense.id.bmin, idOf 729, dense.id.bmax,
          idOf 730] (by decide) fun z hz => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hz
        rw [ho5 z h11 h12, ho4 z h9 h10, ho3 z h0 h1 h2 h3 h4 h5 h6 h7 h8]
      wp_step; wp_step
      refine wp_storeV hca6 (by omega) dense.id.count ht5.count (tv dense.id.i) (cell1 + (k + 1))
        (by omega) hi5 rfl (tv dense.id.cnt) (cs[k + 1]! : Nat) hcnt5 rfl ?_
      intro m7 hca7 hu7
      have hba7 := hba6.unch hu7 (Ne.symm d.bc_bB)
      refine ⟨F - (k + 1), by omega, by simp, rfl, k + 1, by omega, rfl, hi5, ?_, ?_,
        hca7.congr fun p _ => cnt_inc cs cell1 k cv0 p, hba7.congr fun v _ => bkt_inc cs k hk1 bv0 v,
        ?_, ?_, ?_⟩
      · rw [ho5 _ (by decide) (by decide), pmin_succ hk1]; exact hmin4
      · rw [pmax_succ hk1]; exact hmax5
      · refine ((hu.trans (hu46.mono fun z hz => .inr hz)).trans (hu7.mono fun z hz => .inl hz))
      · exact ((hkp.trans ((hk4.trans hk5).trans hk6))).trans (Keep.unch hu7 (Ne.symm d.bc_bB))
      · intro z hz
        have hs : ∀ y ∈ cntTemps, z ≠ y := fun y hy h => hz (h ▸ hy)
        simp only [cntTemps, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] at hs
        obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hs
        rw [ho5 z h12 h14, ho4 z h11 h13, ho3 z h5 h6 h7 h8 h9 h10 h2 h3 h4]
        exact ho2 z hz
  · rintro v tr e' le' m' hJ
    apply wp_skip
    simpa using hJ

end NautyVerified.Proofs.Refine
