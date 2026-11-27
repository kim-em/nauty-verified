import NautyVerified.Proofs.Alloc.KeepV
import NautyVerified.Proofs.Refine.CountN
import NautyVerified.Proofs.Refine.WindowN
import NautyVerified.Spec.CountWin
import NautyVerified.Proofs.Refine.Temps
import NautyVerified.Proofs.Refine1.Count

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

/-- `while (++i <= cell2) { <count lab[i]>; widen the window; ++bucket[cnt]; count[i] = cnt; }`
with the per-member count `hd` and SimplExpr's temporaries `t1 t2 t3`. -/
abbrev countRestG (hd : statement → statement) (t1 t2 t3 : Common.AST.ident) : statement :=
  .Sloop
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (Set.sk (.Sset t1 (.Ecast (.Ebinop .Oadd (tv dense.id.i) (ci 1 tint) tint) tint)))
          (.Sset dense.id.i (tv t1)))
        (.Sifthenelse (.Ebinop .Ole (tv t1) (tv dense.id.cell2) tint) .Sskip .Sbreak))
      (hd (.Ssequence (widenLo t2) (.Ssequence (widenHi t3)
        (.Ssequence
          (Set.sk (.Sassign (gix dense.id.«naugraph:bucket» (tv dense.id.cnt))
            (.Ebinop .Oadd (gix dense.id.«naugraph:bucket» (tv dense.id.cnt)) (ci 1 tint) tint)))
          (Set.sk (.Sassign (ix dense.id.count (tv dense.id.i)) (tv dense.id.cnt))))))))
    .Sskip

theorem countRest_D0 : countRest =
    countRestG (cntHead (idOf 725) (idOf 726) (idOf 727) (idOf 728)) (idOf 724) (idOf 729)
      (idOf 730) := rfl

theorem countRest_D1 : Refine1.countRest =
    countRestG (fun rest => .Ssequence (Refine1.cnt1 (idOf 719)) rest) (idOf 718) (idOf 720)
      (idOf 721) := rfl

/-- What the nontrivial pass reads while it counts and splits one cell: the
graph, `lab`, the pointer globals and the tables. What it reads about the
splitter set depends on the function (`CountHead`). -/
structure CFrame {n : Nat} (m : mem) (L : Loc) (ctx : Ctx n) (lab : Array Nat) : Prop where
  ok : Ok n L
  graph : GraphAt m L.bg L.gofs L.gw ctx.g L.M
  larr : ArrayAt m .Mint32 L.bl L.lb (ints lab) n
  labs : ∀ i < n, lab[i]! < n
  bkp : Mem.load .Mint64 m Block.naugraphBucket (zOfInt 0) = some (.Vptr L.bB Ptrofs.zero)
  wpp : Mem.load .Mint64 m Block.naugraphWorkperm (zOfInt 0) = some (.Vptr L.bW Ptrofs.zero)
  bytes : BytecountTable m
  bit : Set.BitTable m Block.naugraphBit
  capB : L.capB < 2147483648
  capW : L.capW < 2147483648

/-- `CFrame` survives writes to `count`, `bucket`, `workperm`, `ptn`, `active`
and `*numcells`. -/
theorem CFrame.unch {n : Nat} {m m' : mem} {L : Loc} {ctx : Ctx n} {lab : Array Nat}
    (h : CFrame m L ctx lab)
    (hu : Unch m m' (fun z => z = L.bc ∨ z = L.bB ∨ z = L.bW ∨ z = L.bp ∨ z = L.ba ∨ z = L.bn)) :
    CFrame m' L ctx lab :=
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

/-- `hd rest` sets `cnt` to the neighbour count of `lab[i]` in the splitter set `ws`,
assigning only `hdTemps ht`, then runs `rest`; `Sp` is what it reads about the splitter. -/
def CountHead (xi : ExternalCalls) (f : function) (hd : statement → statement)
    (ht : List Common.AST.ident) {n : Nat} (L : Loc) (ctx : Ctx n) (ws : VSet n)
    (Sp : temp_env → mem → Prop) : Prop :=
  ∀ {Q : Post} {le : temp_env} {m : mem} {rest : statement} {st : RefineSt n} {i : Nat},
    Sp le m → CFrame m L ctx st.lab → Tmp le L st →
    PTree.get dense.id.i le = some (.Vint (ir i)) → i < n →
    (∀ le', PTree.get dense.id.cnt le' = some (.Vint (ir (ws.cardInter ctx.g[st.lab[i]!]! : Nat))) →
      (∀ z, z ∉ hdTemps ht → PTree.get z le' = PTree.get z le) → Wp xi ge f rest Q empty_env le' m) →
    Wp xi ge f (hd rest) Q empty_env le m

/-- `Sp` survives the nontrivial pass's writes to memory, and changes of the
temporaries outside `T`. -/
structure SpOk (Sp : temp_env → mem → Prop) (L : Loc) (T : List Common.AST.ident) : Prop where
  unch : ∀ {le m m'} {S : block → Prop}, Sp le m → Unch m m' S →
    (∀ z, S z → z = L.bl ∨ z = L.bp ∨ z = L.bn ∨ z = L.bc ∨ z = L.ba ∨ z = L.bW ∨ z = L.bB) →
    Sp le m'
  temps : ∀ {le le' m}, Sp le m → (∀ z, z ∉ T → PTree.get z le' = PTree.get z le) → Sp le' m

theorem SpOk.mono {Sp : temp_env → mem → Prop} {L : Loc} {T T' : List Common.AST.ident}
    (h : SpOk Sp L T') (hT : ∀ z ∈ T, z ∈ T') : SpOk Sp L T :=
  ⟨h.unch, fun hs ho => h.temps hs fun z hz => ho z fun h' => hz (hT z h')⟩

/-- `refine`'s. -/
abbrev cntTemps : List Common.AST.ident :=
  cntTempsG (idOf 724) (idOf 729) (idOf 730) [idOf 725, idOf 726, idOf 727, idOf 728]

theorem cntTemps_away {t1 t2 t3 : Common.AST.ident} {hts : List Common.AST.ident}
    (hT : NTemps ([t1, t2, t3] ++ hts)) :
    ∀ x ∈ args ++ [dense.id.longcode, dense.id.hint, dense.id.maxpos], x ∉ cntTempsG t1 t2 t3 hts := by
  intro x hx hm
  have hc : ∀ y ∈ args ++ [dense.id.longcode, dense.id.hint, dense.id.maxpos],
      y ∉ [dense.id.i, dense.id.set1, dense.id.set2, dense.id.cnt, dense.id.c1, dense.id.x,
        dense.id.bmin, dense.id.bmax] := by decide
  have hA := hT.notMem (l := [t1, t2, t3] ++ hts) (fun y hy => hy) (args_names x hx)
  have hB := hc x hx
  simp only [cntTempsG, hdTemps, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
    not_or] at hm hA hB
  simp_all

/-- `refine`'s splitter set: `M` words in the `workset` block. -/
def SpWords {n : Nat} (L : Loc) (ws : VSet n) (wsw : Nat → Lib.Integers.int64) (_le : temp_env)
    (m : mem) : Prop :=
  ArrayAt m .Mint64 L.bS 0 (longs wsw) L.M ∧ SetRep (fun w => bv64 (wsw w)) L.M ws ∧
    Mem.load .Mint64 m Block.naugraphWorkset (zOfInt 0) = some (.Vptr L.bS Ptrofs.zero)

theorem SpWords.ok {n : Nat} {L : Loc} {ws : VSet n} {wsw : Nat → Lib.Integers.int64}
    (d : WDist L) (T : List Common.AST.ident) : SpOk (SpWords L ws wsw) L T where
  unch := fun ⟨hA, hR, hp⟩ hu hS => by
    have nS : ∀ g, g ≠ L.bl → g ≠ L.bp → g ≠ L.bn → g ≠ L.bc → g ≠ L.ba → g ≠ L.bW → g ≠ L.bB →
        ∀ S : block → Prop, (∀ z, S z → z = L.bl ∨ z = L.bp ∨ z = L.bn ∨ z = L.bc ∨ z = L.ba ∨
          z = L.bW ∨ z = L.bB) → ¬ S g := by
      intro g h1 h2 h3 h4 h5 h6 h7 S hS hg
      rcases hS g hg with h | h | h | h | h | h | h <;> contradiction
    refine ⟨hA.unch hu (nS _ (Ne.symm d.bl_bS) (Ne.symm d.bp_bS) (Ne.symm d.bn_bS) (Ne.symm d.bc_bS)
      (Ne.symm d.ba_bS) (Ne.symm d.bW_bS) d.bS_bB _ hS), hR, ?_⟩
    rw [hu.load _ _ _ (nS _ (Ne.symm d.bl_g2) (Ne.symm d.bp_g2) (Ne.symm d.bn_g2) (Ne.symm d.bc_g2)
      (Ne.symm d.ba_g2) (Ne.symm d.bW_g2) (Ne.symm d.bB_g2) _ hS)]
    exact hp
  temps := fun hs _ => hs

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

/-- `refine`'s per-member count: the word loop over the `workset` block. -/
theorem cntHead_ok {f : function} {a b c d : Common.AST.ident}
    (hd : [dense.id.c1, a, b, c, d, dense.id.x, dense.id.set1, dense.id.set2, dense.id.cnt,
      dense.id.m].Pairwise (· ≠ ·)) {n : Nat} {L : Loc} {ctx : Ctx n} {ws : VSet n}
    {wsw : Nat → Lib.Integers.int64} :
    CountHead xi f (cntHead a b c d) [a, b, c, d] L ctx ws (SpWords L ws wsw) := by
  intro Q le m rest st i ⟨hA, hR, hp⟩ hf ht hi hin hQ
  refine wp_cntHead hd hf.ok ht hf.graph hf.larr hA hR hp hi hin (hf.labs i hin) hf.bytes ?_
  intro le' hc ho
  refine hQ le' hc fun z hz => ?_
  have e : ∀ y ∈ hdTemps [a, b, c, d], z ≠ y := fun y hy h => hz (h ▸ hy)
  exact ho z (e _ (by simp)) (e _ (by simp)) (e _ (by simp)) (e _ (by simp)) (e _ (by simp))
    (e _ (by simp)) (e _ (by simp)) (e _ (by simp)) (e _ (by simp))

theorem wp_countRest {hd : statement → statement} {t1 t2 t3 : Common.AST.ident}
    {hts : List Common.AST.ident} (hT : NTemps ([t1, t2, t3] ++ hts))
    {f : function} {Q : Post} {le : temp_env} {m : mem} {n : Nat} {L : Loc} {ctx : Ctx n}
    {st : RefineSt n} {ws : VSet n} {Sp : temp_env → mem → Prop} {cell1 cell2 : Nat}
    {cv0 bv0 : Nat → val} (hH : CountHead xi f hd hts L ctx ws Sp)
    (hSp : Sp le m) (hSo : SpOk Sp L (cntTempsG t1 t2 t3 hts))
    (hf : CFrame m L ctx st.lab) (ht : Tmp le L st)
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
      Unch m m' (fun z => z = L.bc ∨ z = L.bB) → Alloc.KeepA m m' →
      (∀ z, z ∉ cntTempsG t1 t2 t3 hts → PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge f (countRestG hd t1 t2 t3) Q empty_env le m := by
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
      Unch m m' (fun z => z = L.bc ∨ z = L.bB) ∧ Alloc.KeepA m m' ∧
      (∀ z, z ∉ cntTempsG t1 t2 t3 hts → PTree.get z le' = PTree.get z le)
  refine wp_loop (I := I) (J := fun v tr e' le' m' => ∃ v', v' < v ∧ I v' tr e' le' m') ?_ ?_
    (n := F) ⟨rfl, rfl, 0, Nat.zero_le _, rfl, by simpa using hi, hbmin, hbmax, hcnt, hbkt,
      Unch.refl _ _, Alloc.KeepA.refl _, fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, k, hk, rfl, hik, hmin, hmax, hca, hba, hu, hkp, ho⟩
    have hc2' : PTree.get dense.id.cell2 le' = some (.Vint (ir cell2)) := by
      rw [ho _ (by nscr)]; exact hc2
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hik, typeof, cop, ir_add]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, temps_gso _ _ (show t1 ≠ dense.id.i by nscr),
      typeof, cop]
    rw [temps_gso _ _ (by nscr), temps_gso _ _ (by nscr), hc2']
    simp only [cop]
    rw [ir_lt (a := (cell2 : Int)) (b := ((cell1 + k : Nat) : Int) + 1) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    by_cases hkF : k = F
    · rw [ite_eq_right (by simp; omega)]
      apply wp_break
      subst hkF
      simp only [E0_append]
      refine hQ _ _ ?_ ?_ hca hba hu hkp ?_
      · rw [temps_gso _ _ (by nscr), temps_gso _ _ (by nscr)]; exact hmin
      · rw [temps_gso _ _ (by nscr), temps_gso _ _ (by nscr)]; exact hmax
      · intro z hz
        have h1 : z ≠ dense.id.i := fun h => hz (h ▸ by simp [cntTempsG])
        have h2 : z ≠ t1 := fun h => hz (h ▸ by simp [cntTempsG])
        rw [temps_gso _ _ h1, temps_gso _ _ h2, ho z hz]
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      dsimp only
      have hk1 : k + 1 < cs.length := by omega
      have hcu := hf.unch (hu.mono fun z hz => by rcases hz with h | h <;> simp [h])
      let le2 := PTree.set dense.id.i (.Vint (ir (((cell1 + k : Nat) : Int) + 1)))
        (PTree.set t1 (.Vint (ir (((cell1 + k : Nat) : Int) + 1))) le')
      have ho2 : ∀ z, z ∉ cntTempsG t1 t2 t3 hts → PTree.get z le2 = PTree.get z le := fun z hz => by
        have h1 : z ≠ dense.id.i := fun h => hz (h ▸ by simp [cntTempsG])
        have h2 : z ≠ t1 := fun h => hz (h ▸ by simp [cntTempsG])
        simp only [le2]; rw [temps_gso _ _ h1, temps_gso _ _ h2, ho z hz]
      have ht2 : Tmp le2 L st := ht.away (cntTempsG t1 t2 t3 hts) (cntTemps_away hT) ho2
      have hi2 : PTree.get dense.id.i le2 = some (.Vint (ir (cell1 + (k + 1) : Nat))) := by
        simp only [le2, temps_gss]; push_cast; rw [Int.add_assoc]
      have hlk := hf.labs (cell1 + (k + 1)) (by omega)
      have hSp2 : Sp le2 m' := hSo.temps (hSo.unch hSp hu fun z hz => by
        rcases hz with h | h
        · exact .inr (.inr (.inr (.inl h)))
        · exact .inr (.inr (.inr (.inr (.inr (.inr h)))))) ho2
      refine hH hSp2 hcu ht2 hi2 (by omega) ?_
      intro le3 hcnt3 ho3
      have hcs1 : ws.cardInter ctx.g[st.lab[cell1 + (k + 1)]!]! = cs[k + 1]! := by
        rw [← hcs, countsOf_get ctx st.lab ws (by omega)]
      rw [hcs1] at hcnt3
      have hg3 : ∀ z, z ∉ hdTemps hts → z ≠ dense.id.i → z ≠ t1 → PTree.get z le3 = PTree.get z le' :=
        fun z h0 h9 h10 => by rw [ho3 z h0, temps_gso _ _ h9, temps_gso _ _ h10]
      have hmin3 : PTree.get dense.id.bmin le3 = some (.Vint (ir (pmin cs k : Nat))) := by
        rw [hg3 _ (by nscr) (by nscr) (by nscr)]; exact hmin
      have hmax3 : PTree.get dense.id.bmax le3 = some (.Vint (ir (pmax cs k : Nat))) := by
        rw [hg3 _ (by nscr) (by nscr) (by nscr)]; exact hmax
      have hpk := pmin_le (cs := cs) (k := k) (o := 0) (by omega) (Nat.zero_le _)
      have hxk := le_pmax (cs := cs) (k := k) (o := 0) (by omega) (Nat.zero_le _)
      have hc0 := hcle 0
      have hck := hcle (k + 1)
      have hpmax := le_pmax (cs := cs) (k := k) (o := k) (by omega) (Nat.le_refl _)
      have hck2 := hcle k
      have hmaxle : pmax cs k ≤ n := pmax_le hcle (by omega)
      have hcapB := hf.capB
      wp_step
      refine wp_widenLo (by nscr) (by nscr) hmin3 hcnt3 hba (hcu.bkp) (Ne.symm d.bB_g4)
        (by omega) (by omega) (by omega) ?_
      intro le4 m4 hmin4 hba4 hu4 hk4 ho4
      have hcnt4 : PTree.get dense.id.cnt le4 = some (.Vint (ir (cs[k + 1]! : Nat))) := by
        rw [ho4 _ (by nscr) (by nscr)]; exact hcnt3
      have hmax4 : PTree.get dense.id.bmax le4 = some (.Vint (ir (pmax cs k : Nat))) := by
        rw [ho4 _ (by nscr) (by nscr)]; exact hmax3
      have hbkp4 : Mem.load .Mint64 m4 Block.naugraphBucket (zOfInt 0) =
          some (.Vptr L.bB Ptrofs.zero) := by rw [hu4.load _ _ _ (Ne.symm d.bB_g4)]; exact hcu.bkp
      wp_step
      refine wp_widenHi (by nscr) (by nscr) hmax4 hcnt4 hba4 hbkp4 (Ne.symm d.bB_g4)
        (by omega) (by omega) (by omega) ?_
      intro le5 m5 hmax5 hba5 hu5 hk5 ho5
      have hcnt5 : PTree.get dense.id.cnt le5 = some (.Vint (ir (cs[k + 1]! : Nat))) := by
        rw [ho5 _ (by nscr) (by nscr)]; exact hcnt4
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
      intro m6 hba6 hu6 hk6'
      have hk6 := Alloc.KeepA.of_keep hu6 hk6'
      dsimp only
      have hu46 : Unch m' m6 (· = L.bB) := (hu4.trans hu5).trans hu6
      have hca6 := hca.unch hu46 d.bc_bB
      have hi5 : PTree.get dense.id.i le5 = some (.Vint (ir (cell1 + (k + 1) : Nat))) := by
        rw [ho5 _ (by nscr) (by nscr), ho4 _ (by nscr) (by nscr),
          ho3 _ (by nscr)]
        exact hi2
      have ht5 : Tmp le5 L st := by
        refine ht2.away (cntTempsG t1 t2 t3 hts) (cntTemps_away hT) fun z hz => ?_
        have hs : ∀ y ∈ cntTempsG t1 t2 t3 hts, z ≠ y := fun y hy h => hz (h ▸ hy)
        rw [ho5 z (hs _ (by simp)) (hs _ (by simp)), ho4 z (hs _ (by simp)) (hs _ (by simp)),
          ho3 z fun h => hz (List.mem_append_left _ (List.mem_append_right _ h))]
      wp_step; wp_step
      refine wp_storeV hca6 (by omega) dense.id.count ht5.count (tv dense.id.i) (cell1 + (k + 1))
        (by omega) hi5 rfl (tv dense.id.cnt) (cs[k + 1]! : Nat) hcnt5 rfl ?_
      intro m7 hca7 hu7 hk7
      have hba7 := hba6.unch hu7 (Ne.symm d.bc_bB)
      refine ⟨F - (k + 1), by omega, by simp, rfl, k + 1, by omega, rfl, hi5, ?_, ?_,
        hca7.congr fun p _ => cnt_inc cs cell1 k cv0 p, hba7.congr fun v _ => bkt_inc cs k hk1 bv0 v,
        ?_, ?_, ?_⟩
      · rw [ho5 _ (by nscr) (by nscr), pmin_succ hk1]; exact hmin4
      · rw [pmax_succ hk1]; exact hmax5
      · refine ((hu.trans (hu46.mono fun z hz => .inr hz)).trans (hu7.mono fun z hz => .inl hz))
      · exact ((hkp.trans ((hk4.trans hk5).trans hk6))).trans hk7
      · intro z hz
        have hs : ∀ y ∈ cntTempsG t1 t2 t3 hts, z ≠ y := fun y hy h => hz (h ▸ hy)
        rw [ho5 z (hs _ (by simp)) (hs _ (by simp)), ho4 z (hs _ (by simp)) (hs _ (by simp)),
          ho3 z fun h => hz (List.mem_append_left _ (List.mem_append_right _ h))]
        exact ho2 z hz
  · rintro v tr e' le' m' hJ
    apply wp_skip
    simpa using hJ

end NautyVerified.Proofs.Refine
