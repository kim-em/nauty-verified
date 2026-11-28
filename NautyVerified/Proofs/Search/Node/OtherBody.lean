import NautyVerified.Proofs.Search.Node.OtherTail
import NautyVerified.Proofs.Search.Node.ProcFacts
import NautyVerified.Proofs.Search.Processnode.Satisfies

/-!
# `othernode0` meets its specification

`othernode_bodyG`: nauty.c's `othernode0` satisfies the off-path node
specification `nodeSpecG` at `level` for any `DispatchC`, `Classifier` and
search policy with its `PolicyLink` and `NodeLaws`, given the specification at
`level + 1` for its children and the emission law `EmLawOffG`.

The body: the locals are allocated on entry (`oEntry_existsG`, `alloc_ints`),
the prologue finds this level's target-cell entry (`wp_nodePrologueG`), then
the kill check, the node count, the refinement (`wp_nodeVisitG`, the policy's
`visit` by `PolicyLink.visit_same`), the code comparisons, the target cell
(`wp_chooseOffG`, `PolicyLink.target_eq`/`target_same`), `processnode`
(`wp_nodeProcessG`) and, when the node continues, `wp_otherTailG`;
HexGraphIso's side is `node_false_succG`. `oPostG`: freeing the locals at a
return gives the specification's postcondition.

The dense `othernode_body` is the instance at `Dispatch.dense`,
`denseClassifier`, `denseLink` and `denseLaws` (`nodeSpec_ofG`,
`nodeSpec_toG`, `EmLawOff.toG`).
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (Keep)
open NautyVerified.Proofs.Set (sk longs)
open Hex.GraphIso Hex.GraphIso.Nauty
open NautyVerified.Spec.SearchInf (SweepOkOff)

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

theorem vars_notWork {S : SLoc} (hd : S.blocks.Pairwise (· ≠ ·)) {z : block} (hz : z ∈ S.vars) :
    z ∉ workG := fun h => SLoc.vars_ne hd z hz z (workG_globs z h) rfl

theorem vars_chg {S : SLoc} (hd : S.blocks.Pairwise (· ≠ ·)) {z : block} (hz : z ∈ S.vars)
    (hu : z ≠ S.bUA) : S.Chg z :=
  ⟨SLoc.vars_blocks hz, hu, fun e => SLoc.vars_ne hd z hz _ tcnode0_globs e⟩

/-- `othernode0`'s temporaries on entry. -/
abbrev oTemps (a b c d e : val) : temp_env :=
  PTree.set dense.id.tcnode_parent e (PTree.set dense.id.numcells d (PTree.set dense.id.level c
    (PTree.set dense.id.ptn b (PTree.set dense.id.lab a
      (create_undef_temps dense.fn.«nauty:othernode0».fn_temps)))))

/-- What holds just after `othernode0`'s entry. -/
def OEntry (m₀ : mem) (e : env) (m : mem) (L : OLocs) : Prop :=
  e = oEnv L ∧ (∀ z ∈ L.list, ¬ Mem.valid_block m₀ z ∧ Mem.valid_access m .Mint32 z (zOfInt 0) .Freeable) ∧
    L.list.Pairwise (· ≠ ·) ∧ Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z) ∧
    (∀ z, Mem.valid_block m₀ z → Mem.valid_block m z)

/-! ### For any dispatch and search policy -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}

theorem compareCodes_ptnG {κ : Type} (level code : Nat) (st : SearchState n κ) :
    (compareCodes level code st).ptn = st.ptn := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.ptn, ite_self]

theorem compareCodes_labG {κ : Type} (level code : Nat) (st : SearchState n κ) :
    (compareCodes level code st).lab = st.lab := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.lab, ite_self]

theorem compareCodes_canongG {κ : Type} (level code : Nat) (st : SearchState n κ) :
    (compareCodes level code st).canong = st.canong := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.canong, ite_self]

theorem oEntry_existsG (m₀ : mem) (args : List val) (a b c d e : val)
    (ha : args = [a, b, c, d, e]) :
    ∃ en le m, function_entry2 ge dense.fn.«nauty:othernode0» args m₀ en le m ∧
      le = oTemps a b c d e ∧ ∃ L, OEntry m₀ en m L := by
  subst ha
  have hids : [dense.id.numcells, dense.id.refcode, dense.id.tcellsize, dense.id.tc,
      dense.id.qinvar].Nodup := by decide
  obtain ⟨en, m, hav, hout, hin, hdist, hu, hg⟩ := alloc_ints (ge := ge) _ empty_env m₀ hids
  obtain ⟨b1, e1, f1, -, a1⟩ := hin dense.id.numcells (by simp)
  obtain ⟨b2, e2, f2, -, a2⟩ := hin dense.id.refcode (by simp)
  obtain ⟨b3, e3, f3, -, a3⟩ := hin dense.id.tcellsize (by simp)
  obtain ⟨b4, e4, f4, -, a4⟩ := hin dense.id.tc (by simp)
  obtain ⟨b5, e5, f5, -, a5⟩ := hin dense.id.qinvar (by simp)
  let L : OLocs := ⟨b1, b2, b3, b4, b5⟩
  have hd : ∀ x y, x ∈ [dense.id.numcells, dense.id.refcode, dense.id.tcellsize, dense.id.tc,
      dense.id.qinvar] → y ∈ [dense.id.numcells, dense.id.refcode, dense.id.tcellsize, dense.id.tc,
      dense.id.qinvar] → x ≠ y → ∀ bx by_, Bound en x bx → Bound en y by_ → bx ≠ by_ :=
    fun x y hx hy => hdist x hx y hy
  have he : en = oEnv L := by
    apply PTree.extensionality
    intro i
    by_cases h1 : i = dense.id.qinvar
    · subst h1; rw [e5]; exact (PTree.gss _ _ _).symm
    by_cases h2 : i = dense.id.tc
    · subst h2; rw [e4, PTree.gso _ _ (by decide)]; exact (PTree.gss _ _ _).symm
    by_cases h3 : i = dense.id.tcellsize
    · subst h3; rw [e3, PTree.gso _ _ (by decide), PTree.gso _ _ (by decide)]
      exact (PTree.gss _ _ _).symm
    by_cases h4 : i = dense.id.refcode
    · subst h4; rw [e2, PTree.gso _ _ (by decide), PTree.gso _ _ (by decide),
        PTree.gso _ _ (by decide)]; exact (PTree.gss _ _ _).symm
    by_cases h5 : i = dense.id.numcells
    · subst h5; rw [e1, PTree.gso _ _ (by decide), PTree.gso _ _ (by decide),
        PTree.gso _ _ (by decide), PTree.gso _ _ (by decide)]; exact (PTree.gss _ _ _).symm
    rw [hout i (by simp [h1, h2, h3, h4, h5]), PTree.gso _ _ h1, PTree.gso _ _ h2,
      PTree.gso _ _ h3, PTree.gso _ _ h4, PTree.gso _ _ h5]
  refine ⟨en, _, m, ⟨?_, ?_, ?_, hav, rfl⟩, rfl, L, he, ?_, ?_, hu, hg⟩
  · exact Nextelement.norepet_of_nodup (by decide)
  · exact Nextelement.norepet_of_nodup (by decide)
  · exact Nextelement.disjoint_of (by decide)
  · intro z hz
    simp only [OLocs.list, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact ⟨f1, a1⟩
    · exact ⟨f2, a2⟩
    · exact ⟨f3, a3⟩
    · exact ⟨f4, a4⟩
    · exact ⟨f5, a5⟩
  · simp only [OLocs.list, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    all_goals first
      | exact hd _ _ (by simp) (by simp) (by decide) _ _ e1 e2
      | exact hd _ _ (by simp) (by simp) (by decide) _ _ e1 e3
      | exact hd _ _ (by simp) (by simp) (by decide) _ _ e1 e4
      | exact hd _ _ (by simp) (by simp) (by decide) _ _ e1 e5
      | exact hd _ _ (by simp) (by simp) (by decide) _ _ e2 e3
      | exact hd _ _ (by simp) (by simp) (by decide) _ _ e2 e4
      | exact hd _ _ (by simp) (by simp) (by decide) _ _ e2 e5
      | exact hd _ _ (by simp) (by simp) (by decide) _ _ e3 e4
      | exact hd _ _ (by simp) (by simp) (by decide) _ _ e3 e5
      | exact hd _ _ (by simp) (by simp) (by decide) _ _ e4 e5

variable [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]

/-- The specification's postcondition at a return, once the locals are freed. -/
theorem oPostG {D : DispatchRep ge O} {K : PolicyLink O n} {G : O.Gr n} (Lw : NodeLaws K G)
    {Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {st : SearchState n (O.Canon n)} {level nc : Nat}
    {chain : List (block × block)} {args : List val}
    {m₀ m : mem} {chain' : List (block × block)} {ncw tcw : val} {nd bt : block} {L : OLocs}
    {s : SearchState n (O.Canon n)} {ns : Bool} {v : Int} {t : trace}
    (hLS : ∀ z ∈ L.list, z ∉ S.blocksG D gl cl) (hLF : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z)
    (hLd : L.list.Pairwise (· ≠ ·)) (hS : SearchAtG D m S gl cl G s false ns)
    (c : CarryG D m₀ m S gl cl chain chain' level ncw tcw nd bt L)
    (hok : Lw.NodeOk false level nc st)
    (hr2 : (hexNodeG false G level nc st).2 = s)
    (hrv : exitValue level (hexNodeG false G level nc st).1 = (v, ns))
    (hEm : Emits t (Em false level nc st)) :
    match Mem.free_list m (blocks_of_env ge (oEnv L)) with
    | some m'' =>
      (nodeSpecG D xi Lw.NodeOk Em false S gl cl G st level nc chain).post args m₀ t (.Vint (ir v)) m''
    | none => False := by
  obtain ⟨m', hfree, hS', hTc', hTo', hF', hW'⟩ := c.finish hLS hLF hLd hS
  rw [hfree]
  have hlt : level - 1 < chain'.length := by
    have := c.own; rw [List.getElem?_eq_some_iff] at this; obtain ⟨h1, -⟩ := this; exact h1
  have hl1 := c.l1
  refine ⟨by rw [hrv], by rw [hr2, hrv]; exact hS', hEm,
    ⟨chain', hTc', hTo', by omega, c.take, c.old⟩, hF', hW', ?_⟩
  exact fun tg sh h => Lw.unwind_lt hok _ tg sh h

set_option maxHeartbeats 16000000 in
/-- `othernode0` meets the generic off-path node specification at `level`, for
the dispatch `D`, the classifier `C` and the policy `P` with link `L` and laws
`Lw`, given its specification at `level + 1` and the emission law. -/
theorem othernode_bodyG (D : DispatchC ge O) (C : Classifier O) (L : PolicyLink O n)
    {G : O.Gr n} (Lw : NodeLaws L G) (Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int)
    (hLaw : EmLawOffG Em G) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc)
    (st : SearchState n (O.Canon n)) (level nc : Nat) (chain : List (block × block))
    (hRec : ∀ s nc' ch, Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (nodeSpecG D.toDispatchRep xi Lw.NodeOk Em false S gl cl G s (level + 1) nc' ch)) :
    Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (nodeSpecG D.toDispatchRep xi Lw.NodeOk Em false S gl cl G st level nc chain) := by
  refine satisfies_internal (Entry := fun args m₀ e le m =>
      le = oTemps (.Vptr S.bl S.lofs) (.Vptr S.bp S.pofs) (.Vint (ir level)) (.Vint (ir nc))
        (.Vptr (tcParent chain level) Ptrofs.zero) ∧ ∃ L, OEntry m₀ e m L) ?_ ?_
  · rintro args m ⟨hargs, -⟩
    obtain ⟨en, le, m', hfe, hle, Lo, hL⟩ := oEntry_existsG m args _ _ _ _ _ hargs
    exact ⟨en, le, m', hfe, hle, Lo, hL⟩
  rintro args m₀ ⟨hargs, h0, hTc0, hTo0, hlen, hcb, hl1, hln, hncn, hok, huaV, huaP⟩
  rw [triple_iff_wp]
  rintro e le mA ⟨rfl, Lo, rfl, hLA, hLd, huA, hgA⟩
  have hLF : ∀ z ∈ Lo.list, ¬ Mem.valid_block m₀ z := fun z hz => (hLA z hz).1
  have haccA : ∀ z ∈ Lo.list, Mem.valid_access mA .Mint32 z (zOfInt 0) .Freeable :=
    fun z hz => (hLA z hz).2
  have hnl := h0.nlt
  have hInv := Lw.inv hok
  obtain ⟨hSA, hTcA, hToA, hbackA, hwmA, hLS, hwkA, hcA⟩ :=
    oAllocG (L := Lo) h0 huaV hTc0 hTo0 huA hgA hLF
  have hE : OEnvG D.toDispatchRep (oEnv Lo) S gl cl m₀ Lo := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hLF, hLd, hLS⟩
    · (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
    · (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
    · (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
    · (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
    · (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
    · intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
      obtain ⟨h1, h2, h3, h4, h5⟩ := hx
      rw [PTree.gso _ _ h5, PTree.gso _ _ h4, PTree.gso _ _ h3, PTree.gso _ _ h2, PTree.gso _ _ h1]
      rfl
  have hfr : dense.fn.«nauty:othernode0».fn_return = tint := rfl
  rw [dense.fn.«nauty:othernode0».fn_body_eq, Othernode.body_eq, Othernode.body_rest]
  have hgl := hE.glob
  have hl := h0.lit
  obtain ⟨_, -, bncA⟩ := arrayAt_of_access (haccA Lo.bnc (by simp))
  refine wp_nodePrologueG (nc := nc) hSA (hgA _ huaV) hTcA hToA hlen hl1 hE.enc bncA
    (hLS _ (by simp)) (hwkA _ (by simp)) (hcA _ (by simp)) (hE.gl _)
    (by simp (config := {decide := true}) only [oTemps, temps_gso, temps_gss])
    (by simp (config := {decide := true}) only [oTemps, temps_gso, temps_gss]) ?_
  intro le1 m1 chain' nd bt hS1 hA1 hTc1 hTo1 hown htake hold hcellE hU1 hg1 hwm1 hK1 hthis1 htcl1 hle1
  obtain ⟨tcw, c1⟩ := CarryG.init h0 hTo0 hl1 hlen huaV huaP hLF hLS hLd huA hgA hwmA haccA hwkA
    hcA hA1 hTc1 hTo1 hown htake hold hU1 hg1 hwm1 hK1
  have hlab1 : PTree.get dense.id.lab le1 = some (.Vptr S.bl S.lofs) := by
    rw [hle1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [oTemps, temps_gso, temps_gss]
  have hptn1 : PTree.get dense.id.ptn le1 = some (.Vptr S.bp S.pofs) := by
    rw [hle1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [oTemps, temps_gso, temps_gss]
  have hlev1 : PTree.get dense.id.level le1 = some (.Vint (ir level)) := by
    rw [hle1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [oTemps, temps_gso, temps_gss]
  have hLd' := hLd
  simp only [OLocs.list, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true] at hLd'
  obtain ⟨⟨d12, d13, d14, d15⟩, ⟨d23, d24, d25⟩, ⟨d34, d35⟩, d45⟩ := hLd'
  -- the kill check
  wp_step
  refine wp_otherKillG (hgl _ (by decide)) ?_
  simp only [seqPost, Post.after]
  have k708 : ∀ x, x ≠ idOf 708 → PTree.get x (PTree.set (idOf 708) (.Vint Int.zero) le1) =
      PTree.get x le1 := fun x h => temps_gso _ _ h
  -- the node count
  wp_step; wp_step; wp_step
  refine wp_numnodesG hS1 (hgl _ (by decide)) ?_
  intro m2 h2 hu2 hg2
  have wrB : ∀ z ∈ [S.bst], z ∈ wrEnv ∨ z ∈ S.wrVG ∨
      z ∈ D.toDispatchRep.canonBlocks cl S.bc :=
    fun z hz => .inr (.inl (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; simp [hz]))
  have hu2' : Unch m1 m2 (· ∈ [S.bst]) := hu2.mono fun z hz => by simp [hz]
  obtain ⟨c2, nbt2⟩ := c1.chg hLS hLF hS1 hu2' hg2 (hS1.wmono hu2' wrB hg2)
    (fun z hz => .inl (hS1.chgL wrB hz)) hcellE
  have hbncS : Lo.bnc ∉ S.blocksG D.toDispatchRep gl cl := hLS _ (by simp)
  have hA2 := hA1.unch hu2' (fun hz => hbncS (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    exact hz ▸ (hS1.chgL wrB (by simp)).1))
  obtain ⟨cv2, hcv2⟩ := hcellE
  have hcell2 : ∃ vals, ArrayAt m2 .Mint64 bt 0 vals S.M := ⟨cv2, hcv2.unch hu2' nbt2⟩
  simp only [seqPost, Post.after, E0_append]
  -- the refinement
  have hlocS : ∀ z ∈ Lo.list, z ∉ S.blocksG D.toDispatchRep gl cl ∧ Mem.valid_block m2 z ∧
      ¬ IsWorkG D.toDispatchRep m2 z := fun z hz =>
    ⟨hLS z hz, Alloc.valid_of_access (c2.locs z hz).1, (c2.locs z hz).2.1⟩
  obtain ⟨_, -, hqA⟩ := arrayAt_of_access (c2.locs Lo.bq (by simp)).1
  obtain ⟨_, -, hkA⟩ := arrayAt_of_access (c2.locs Lo.bk (by simp)).1
  wp_step; wp_step; wp_step
  refine wp_nodeVisitG (st := { st with numnodes := st.numnodes + 1 }) h2 c2.uaV
    (TcChain.headValid c2.tcc) (bnc := Lo.bnc) (bq := Lo.bq) (bk := Lo.bk)
    (by
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_singleton _ _⟩⟩
      · intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl
        · exact d15
        · exact d12
      · intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        subst hz; exact fun e => d25 e.symm)
    (fun z hz => hlocS z (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> simp))
    hE.enc hE.eq hE.ek (hE.gl _) hA2 hqA hkA
    (by rw [k708 _ (by decide)]; exact hlab1) (by rw [k708 _ (by decide)]; exact hptn1)
    (by rw [k708 _ (by decide)]; exact hlev1) hl1 hln hncn (Lw.visit_active (st := st) hok)
    { Lw.visit_inv hok h0.inv with } ?_
  intro m3 h3 hnc3 hk3 hq3 hU3 hg3 hwm3 hK3
  -- the policy's visit
  have hvs := L.visit_same G level nc st hInv (Lw.visitOk hok)
  dsimp only at hnc3 hk3
  rw [← L.visit_numcells G level nc st hInv (Lw.visitOk hok)] at hnc3
  rw [← L.visit_code G level nc st hInv (Lw.visitOk hok)] at hk3
  have h3' := h3.same hvs
  have hvInv := L.visit_inv G level nc st hInv (Lw.visitOk hok)
  have hpf := Lw.visit_part hok
  have hcl := Lw.code_lt hok
  generalize hvv : P.visit G level nc st = v at hnc3 hk3 h3' hvInv hpf hcl
  have ld : ∀ {mm : mem} {b : block} {w : val}, ArrayAt mm .Mint32 b 0 (fun _ => w) 1 →
      Mem.load .Mint32 mm b (zOfInt 0) = some w := fun hA => by
    simpa [elemOfs] using hA.load 0 (by decide)
  obtain ⟨btS, -, btV, -, -⟩ := c2.ntc
  have hnot3 : ∀ z, z ∉ S.blocksG D.toDispatchRep gl cl → Mem.valid_block m2 z →
      ¬ IsWorkG D.toDispatchRep m2 z → z ≠ Lo.bnc → z ≠ Lo.bq → z ≠ Lo.bk →
      ¬ (S.ChgG D.toDispatchRep gl cl z ∨ ¬ Mem.valid_block m2 z ∨ IsWorkG D.toDispatchRep m2 z ∨
        z = Lo.bnc ∨ z = Lo.bq ∨ z = Lo.bk) := by
    intro z h1 h2 h3 h4 h5 h6
    rintro (h | h | h | h | h | h)
    · exact h1 h.1
    · exact h h2
    · exact h3 h
    · exact h4 h
    · exact h5 h
    · exact h6 h
  have nbt3 := hnot3 bt btS btV c2.ntc.2.1
    (fun e => ((c2.locs _ (by simp)).2.2 _ (List.mem_of_getElem? c2.own)).2 e)
    (fun e => ((c2.locs _ (by simp)).2.2 _ (List.mem_of_getElem? c2.own)).2 e)
    (fun e => ((c2.locs _ (by simp)).2.2 _ (List.mem_of_getElem? c2.own)).2 e)
  have nbz3 := hnot3 Lo.bz (hlocS _ (by simp)).1 (hlocS _ (by simp)).2.1 (hlocS _ (by simp)).2.2
    (fun e => d13 e.symm) (fun e => d35 e) (fun e => d23 e.symm)
  have nbc3 := hnot3 Lo.bc (hlocS _ (by simp)).1 (hlocS _ (by simp)).2.1 (hlocS _ (by simp)).2.2
    (fun e => d14 e.symm) (fun e => d45 e) (fun e => d24 e.symm)
  obtain ⟨cv, hcv⟩ := hcell2
  have c3 := c2.step (ncw' := .Vint (ir v.1)) (tcw' := tcw) hLS hLF h2 hU3 hg3 hwm3
    (fun z hz => by
      rcases hz with h | h | h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      all_goals (subst h; exact .inr (.inr (.inr (.inl (by simp))))))
    (fun z hz => by
      simp only [OLocs.list, List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      · exact hK3 _ (by simp)
      · exact hK3 _ (by simp)
      · exact Keep.unch hU3 nbz3
      · exact Keep.unch hU3 nbc3
      · exact hK3 _ (by simp))
    ⟨cv, hcv.unch hU3 nbt3⟩ (Keep.unch hU3 nbt3) (ld hnc3)
    (by rw [hU3.load _ _ _ nbc3]; exact c2.tcv)
  have hcell3 : ∃ vals, ArrayAt m3 .Mint64 bt 0 vals S.M := ⟨cv, hcv.unch hU3 nbt3⟩
  simp only [seqPost, Post.after, E0_append]
  -- `code = (short)refcode`, the statistics
  wp_step
  refine wp_codeSetG hE.ek (ld hk3) hcl ?_
  simp only [seqPost, Post.after, E0_append]
  wp_step
  refine wp_invstat0G hE.eq (ld hq3) ?_
  simp only [seqPost, Post.after, E0_append]
  -- the code comparisons
  have kc : ∀ x, x ≠ dense.id.code → x ≠ idOf 708 →
      PTree.get x (PTree.set dense.id.code (.Vint (ir v.2.1))
        (PTree.set (idOf 708) (.Vint Int.zero) le1)) = PTree.get x le1 :=
    fun x h1 h2 => by rw [temps_gso _ _ h1, temps_gso _ _ h2]
  wp_step
  refine wp_codeFirstG h3' (hgl _ (by decide)) (hgl _ (by decide))
    (by rw [kc _ (by decide) (by decide)]; exact hlev1) (temps_gss _ _ _) hcl hl1 hln ?_
  intro le4 m4 h4 hu4 hg4 hle4
  have wrF : ∀ z ∈ [E.eqlevFirst], z ∈ wrEnv ∨ z ∈ S.wrVG ∨
      z ∈ D.toDispatchRep.canonBlocks cl S.bc :=
    fun z hz => .inl (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; simp [hz])
  obtain ⟨c4, nbt4⟩ := c3.chg hLS hLF h3' hu4 hg4 (h3'.wmono hu4 wrF hg4)
    (fun z hz => .inl (h3'.chgL wrF hz)) hcell3
  obtain ⟨cv3, hcv3⟩ := hcell3
  have hcell4 : ∃ vals, ArrayAt m4 .Mint64 bt 0 vals S.M := ⟨cv3, hcv3.unch hu4 nbt4⟩
  have k4 : ∀ x, x ≠ idOf 709 → x ≠ dense.id.code → x ≠ idOf 708 →
      PTree.get x le4 = PTree.get x le1 :=
    fun x h0 h1 h2 => (hle4 x h0).trans (kc x h1 h2)
  have hcode4 : PTree.get dense.id.code le4 = some (.Vint (ir v.2.1)) := by
    rw [hle4 _ (by decide)]; exact temps_gss _ _ _
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_codeCanonG h4 (hgl _ (by decide)) (hgl _ (by decide)) (hgl _ (by decide))
    (hgl _ (by decide)) (by rw [k4 _ (by decide) (by decide) (by decide)]; exact hlev1) hcode4
    hcl hl1 hln ?_
  intro m5 h5 hu5 hg5
  have wrC : ∀ z ∈ [E.compCanon, E.eqlevCanon, S.bCC], z ∈ wrEnv ∨ z ∈ S.wrVG ∨
      z ∈ D.toDispatchRep.canonBlocks cl S.bc := fun z hz => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact .inl (by simp)
    · exact .inl (by simp)
    · exact .inr (.inl (by simp))
  obtain ⟨c5, nbt5⟩ := c4.chg hLS hLF h4 hu5 hg5 (h4.wmono hu5 wrC hg5)
    (fun z hz => .inl (h4.chgL wrC hz)) hcell4
  obtain ⟨cv4, hcv4⟩ := hcell4
  have hcell5 : ∃ vals, ArrayAt m5 .Mint64 bt 0 vals S.M := ⟨cv4, hcv4.unch hu5 nbt5⟩
  rw [← compareCodes_eq, ← L.compareCodes_eq] at h5
  simp only [seqPost, Post.after, E0_append]
  -- `tc = -1`
  obtain ⟨_, -, hbcA⟩ := arrayAt_of_access (c5.locs Lo.bc (by simp)).1
  wp_step; wp_step; wp_step
  refine wp_localStoreG hE.ec hbcA (rhs := .Eunop .Oneg (ci 1 tint) tint) (w := -1)
    (by simp [Exec.evalExpr, typeof, cop]) rfl ?_
  intro m6 hA6 hu6 hK6 hg6
  obtain ⟨btS5, btW5, -, -, -⟩ := c5.ntc
  have bc6 : ¬ bt = Lo.bc := fun e =>
    ((c5.locs _ (by simp)).2.2 _ (List.mem_of_getElem? c5.own)).2 e
  have hbcS : Lo.bc ∉ S.blocksG D.toDispatchRep gl cl := hLS _ (by simp)
  have hbcW : ¬ IsWorkG D.toDispatchRep m5 Lo.bc := (c5.locs _ (by simp)).2.1
  obtain ⟨cv5, hcv5⟩ := hcell5
  have hwm6 : WorkMonoG D.toDispatchRep m5 m6 := fun z hz => .inl ((h5.work.unch hu6
    (fun z hz e => hbcS (e ▸ SLoc.mem_blocksG_of _
      (.inr (.inr (.inr (.inr (.inr (D.toDispatchRep.wglobs_sub _ hz))))))))
    ⟨fun e => hbcS (e ▸ SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp))))))),
      fun e => hbcS (e ▸ SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp)))))))⟩
    (fun z hz e => hbcW (e ▸ hz)) hg6).2 z hz)
  have c6 := c5.step (ncw' := .Vint (ir v.1)) (tcw' := .Vint (ir (-1))) hLS hLF h5 hu6 hg6 hwm6
    (fun z hz => .inr (.inr (.inr (.inl (hz ▸ by simp)))))
    (fun z _ => hK6 z) ⟨cv5, hcv5.unch hu6 bc6⟩ (hK6 bt)
    (by rw [hu6.load _ _ _ (fun e => d14 e)]; exact c5.ncv) (ld hA6)
  have h6 := h5.unch hu6 (fun z hz e => hbcS (e ▸ hz)) (fun z hz e => hbcW (e ▸ hz)) hg6
  simp only [seqPost, Post.after, E0_append]
  -- the target cell
  obtain ⟨btS6, btW6, btV6, -, -⟩ := c6.ntc
  have nbt : ∀ z ∈ Lo.list, bt ≠ z := fun z hz e =>
    ((c6.locs _ hz).2.2 _ (List.mem_of_getElem? c6.own)).2 e
  obtain ⟨_, -, hbzA⟩ := arrayAt_of_access (c6.locs Lo.bz (by simp)).1
  have hst1 : (P.compareCodes level v.2.1 v.2.2).lab = v.2.2.lab ∧
      (P.compareCodes level v.2.1 v.2.2).ptn = v.2.2.ptn ∧
      (P.compareCodes level v.2.1 v.2.2).canong = v.2.2.canong := by
    rw [L.compareCodes_eq]
    exact ⟨compareCodes_labG _ _ _, compareCodes_ptnG _ _ _, compareCodes_canongG _ _ _⟩
  have hTok : L.TargetOk G level v.1 (P.compareCodes level v.2.1 v.2.2) := by
    have := Lw.targetOk hok; rw [hvv] at this; exact this
  have hTinv : L.Inv G (P.compareCodes level v.2.1 v.2.2).canong := by
    rw [hst1.2.2]; exact hvInv
  wp_step
  refine wp_chooseOffG (nc := v.1) h6 c6.uaV (TcChain.headValid c6.tcc) (bnc := Lo.bnc)
    (by
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_singleton _ _⟩⟩
      · intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl
        · exact nbt _ (by simp)
        · exact nbt _ (by simp)
      · intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        subst hz; exact d34)
    (fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨btS6, btV6, btW6⟩
      · exact ⟨hLS _ (by simp), Alloc.valid_of_access (c6.locs _ (by simp)).1,
          (c6.locs _ (by simp)).2.1⟩
      · exact ⟨hLS _ (by simp), Alloc.valid_of_access (c6.locs _ (by simp)).1,
          (c6.locs _ (by simp)).2.1⟩)
    (by rw [k4 _ (by decide) (by decide) (by decide)]; exact htcl1) hE.enc hE.ez hE.ec (hE.gl _)
    c6.ncv hpf.numcellsLe ⟨cv5, hcv5.unch hu6 bc6⟩ hbzA hA6
    (by rw [k4 _ (by decide) (by decide) (by decide)]; exact hlab1)
    (by rw [k4 _ (by decide) (by decide) (by decide)]; exact hptn1)
    (by rw [k4 _ (by decide) (by decide) (by decide)]; exact hlev1) hl1 hln
    (fun hch => by
      rw [hst1.1, hst1.2.1]
      have hlt := Lw.target_lt hok
      rw [hvv] at hlt
      refine hlt hch.1 _ ?_
      have hfr' := h6.inv.firsttcRange level (by omega)
      unfold offHint
      split
      · exact hfr'.2
      · omega) ?_
  intro le7 m7 h7 hc7 hch7 ht7 hz7 hU7 hg7 hwm7 hK7 hle7
  have hte := L.target_eq false G 100 level v.1 _ hTinv hTok
  have hts := L.target_same false G 100 level v.1 _ hTinv hTok
  have h7' := h7.same hts
  generalize hctg : P.chooseTarget false G 100 level v.1 (P.compareCodes level v.2.1 v.2.2) = ct
    at hte hts h7'
  rw [← hte.1] at hc7
  rw [← hte.2.1, ← hte.2.2] at hch7
  have nbnc7 : ¬ (S.ChgG D.toDispatchRep gl cl Lo.bnc ∨ ¬ Mem.valid_block m6 Lo.bnc ∨
      IsWorkG D.toDispatchRep m6 Lo.bnc ∨ Lo.bnc = bt ∨ Lo.bnc = Lo.bz ∨ Lo.bnc = Lo.bc) := by
    rintro (h | h | h | h | h | h)
    · exact hbncS h.1
    · exact h (Alloc.valid_of_access (c6.locs _ (by simp)).1)
    · exact (c6.locs _ (by simp)).2.1 h
    · exact nbt _ (by simp) h.symm
    · exact d13 h
    · exact d14 h
  have nloc7 : ∀ z ∈ [Lo.bk, Lo.bq], ¬ (S.ChgG D.toDispatchRep gl cl z ∨ ¬ Mem.valid_block m6 z ∨
      IsWorkG D.toDispatchRep m6 z ∨ z = bt ∨ z = Lo.bz ∨ z = Lo.bc) := by
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl <;> rintro (h | h | h | h | h | h)
    all_goals first
      | exact hLS _ (by simp) h.1
      | exact h (Alloc.valid_of_access (c6.locs _ (by simp)).1)
      | exact (c6.locs _ (by simp)).2.1 h
      | exact nbt _ (by simp) h.symm
      | exact d23 h | exact d24 h | exact d35 h.symm | exact d45 h.symm
  have c7 := c6.step (ncw' := .Vint (ir v.1)) (tcw' := .Vint (ir ct.1)) hLS hLF h6 hU7 hg7 hwm7
    (fun z hz => by
      rcases hz with h | h | h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inr h)))
      all_goals (subst h; exact .inr (.inr (.inr (.inl (by simp))))))
    (fun z hz => by
      simp only [OLocs.list, List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      · exact Keep.unch hU7 nbnc7
      · exact Keep.unch hU7 (nloc7 _ (by simp))
      · exact hK7 _ (by simp)
      · exact hK7 _ (by simp)
      · exact Keep.unch hU7 (nloc7 _ (by simp)))
    ht7 (hK7 _ (by simp)) (by rw [hU7.load _ _ _ nbnc7]; exact c6.ncv) (ld hc7)
  have k7 : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.tcnode_this,
      dense.id.tcell], PTree.get x le7 = PTree.get x le1 := fun x hx => by
    rw [hle7 x (by revert x; decide) (by revert x; decide) (by revert x; decide),
      k4 x (by revert x; decide) (by revert x; decide) (by revert x; decide)]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at k7
  obtain ⟨k7a, k7b, k7c, k7d, k7e⟩ := k7
  simp only [seqPost, Post.after, E0_append]
  -- the node callback
  wp_step
  refine wp_userNodeG h7' (hgl _ (by decide)) ?_
  simp only [seqPost, Post.after, E0_append]
  -- HexGraphIso's node, unfolded
  have hN : hexNodeG false G level nc st =
      Generic.node false G nautyInf 100 (n + 2 - level + 1) level nc st := by
    show Generic.node _ _ _ _ (n + 3 - level) _ _ _ = _
    rw [show n + 3 - level = n + 2 - level + 1 by omega]
  rw [node_false_succG] at hN
  simp only [hvv, hctg, L.classify_eq, L.leafExit_eq, L.cheapCheck_eq] at hN
  have hL := hLaw level nc st hl1 hln
  simp only [hvv, hctg, procExitG, procWordsG, L.classify_eq, L.leafExit_eq,
    L.cheapCheck_eq] at hL
  have hlok := Lw.leafOk hok
  simp only [hvv, hctg] at hlok
  have hfit := Lw.leafFits hok
  simp only [hvv, hctg] at hfit
  have hlt := Lw.leaf_lt hok
  simp only [hvv, hctg, procExitG, L.classify_eq, L.leafExit_eq] at hlt
  -- processnode
  refine wp_nodeProcessG h7' (Processnode.processnode_satisfiesG D C S gl cl G ct.2.2.2 level v.1)
    hcb hl1 hln hpf.numcellsLe hlok (h7'.valid_all c7.uaV (TcChain.headValid c7.tcc)) c7.uaP hfit
    hE.enc c7.ncv
    (hgl _ (by decide)) (by rw [k7a]; exact hlab1) (by rw [k7b]; exact hptn1)
    (by rw [k7c]; exact hlev1) hfr hlt (leafExit_noFuel _ _ _) ?_ ?_
  · intro t m' hnd hS' hw hF hW
    obtain ⟨-, -, btV7, -, -⟩ := c7.ntc
    have hout : ∀ z, z ∉ S.blocksG D.toDispatchRep gl cl → Mem.valid_block m7 z →
        ¬ IsWorkG D.toDispatchRep m7 z →
        ¬ (S.ChgG D.toDispatchRep gl cl z ∨ ¬ Mem.valid_block m7 z ∨
          IsWorkG D.toDispatchRep m7 z) := by
      rintro z h1 h2 h3 (h | h | h)
      · exact h1 h.1
      · exact h h2
      · exact h3 h
    have hloc : ∀ z ∈ Lo.list, ¬ (S.ChgG D.toDispatchRep gl cl z ∨ ¬ Mem.valid_block m7 z ∨
        IsWorkG D.toDispatchRep m7 z) := fun z hz =>
      hout z (hLS z hz) (Alloc.valid_of_access (c7.locs z hz).1) (c7.locs z hz).2.1
    have hbt7 := hout bt btS6 btV7 c7.ntc.2.1
    obtain ⟨cw7, hcw7⟩ := ht7
    have c' := c7.step (ncw' := .Vint (ir v.1)) (tcw' := .Vint (ir ct.1)) hLS hLF h7 hF.1 hF.2 hW
      (fun z hz => by
        rcases hz with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h)))
      (fun z hz => Keep.unch hF.1 (hloc z hz)) ⟨cw7, hcw7.unch hF.1 hbt7⟩ (Keep.unch hF.1 hbt7)
      (by rw [hF.1.load _ _ _ (hloc _ (by simp))]; exact c7.ncv)
      (by rw [hF.1.load _ _ _ (hloc _ (by simp))]; exact c7.tcv)
    have hnf := leafExit_noFuel (O.classify G level v.1 ct.2.2.2).1 level
      (O.classify G level v.1 ct.2.2.2).2
    simp only [procExitO, procWordsO] at hS' hw hnd hL hN ⊢
    generalize leafExit (O.classify G level v.1 ct.2.2.2).1 level
      (O.classify G level v.1 ct.2.2.2).2 = lx at hS' hw hnd hnf hL hN ⊢
    obtain ⟨ex, s1⟩ := lx
    cases ex with
    | done => exact absurd rfl hnd
    | fuel => exact absurd rfl hnf
    | unwind tg sh =>
      have hr : hexNodeG false G level nc st = (.unwind tg sh, s1) := hN
      exact oPostG Lw hLS hLF hLd hS' c' hok (by rw [hr]) (by rw [hr]) (by
        rw [hL]; simpa using emits_killEv.append hw.emits)
  · intro t le' m' hd' hS' hw hF hW hle'
    obtain ⟨-, -, btV7, -, -⟩ := c7.ntc
    have hout : ∀ z, z ∉ S.blocksG D.toDispatchRep gl cl → Mem.valid_block m7 z →
        ¬ IsWorkG D.toDispatchRep m7 z →
        ¬ (S.ChgG D.toDispatchRep gl cl z ∨ ¬ Mem.valid_block m7 z ∨
          IsWorkG D.toDispatchRep m7 z) := by
      rintro z h1 h2 h3 (h | h | h)
      · exact h1 h.1
      · exact h h2
      · exact h3 h
    have hloc : ∀ z ∈ Lo.list, ¬ (S.ChgG D.toDispatchRep gl cl z ∨ ¬ Mem.valid_block m7 z ∨
        IsWorkG D.toDispatchRep m7 z) := fun z hz =>
      hout z (hLS z hz) (Alloc.valid_of_access (c7.locs z hz).1) (c7.locs z hz).2.1
    have hbt7 := hout bt btS6 btV7 c7.ntc.2.1
    -- the node chose its target cell
    have hdn := Lw.leaf_done hok
    simp only [hvv, hctg, procExitG, L.classify_eq, L.leafExit_eq] at hdn
    obtain ⟨hnc', hcho⟩ := hdn hd'
    obtain ⟨⟨cw7, hcw7, hrep7⟩, -⟩ := hch7 ⟨hnc', hcho⟩
    have hct0 : 0 ≤ ct.1 := by
      rw [hte.1, chooseTargetG_false_eq, ite_eq_left ⟨hnc', hcho⟩]; exact Int.natCast_nonneg _
    have hctv : ((ct.1.toNat : Nat) : Int) = ct.1 := Int.toNat_of_nonneg hct0
    have c' := c7.step (ncw' := .Vint (ir v.1)) (tcw' := .Vint (ir ((ct.1.toNat : Nat) : Int)))
      hLS hLF h7 hF.1 hF.2 hW
      (fun z hz => by
        rcases hz with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h)))
      (fun z hz => Keep.unch hF.1 (hloc z hz)) ⟨_, hcw7.unch hF.1 hbt7⟩ (Keep.unch hF.1 hbt7)
      (by rw [hF.1.load _ _ _ (hloc _ (by simp))]; exact c7.ncv)
      (by rw [hF.1.load _ _ _ (hloc _ (by simp)), hctv]; exact c7.tcv)
    have hsw := Lw.off_start hok
    simp only [hvv, hctg, procExitG, L.classify_eq, L.leafExit_eq, L.cheapCheck_eq] at hsw
    have hsw' := hsw hd'
    have hnf0 := Lw.noFuel hok hln
    have hk' : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.tcnode_this,
        dense.id.tcell], PTree.get x le' = PTree.get x le1 := fun x hx => by
      rw [hle' x (by revert x; decide) (by revert x; decide)]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact k7a
      · exact k7b
      · exact k7c
      · exact k7d
      · exact k7e
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hk'
    obtain ⟨ka, kb, kc', kd, ke⟩ := hk'
    simp only [procExitO, procWordsO] at hS' hw hd' hsw' hL hN
    generalize leafExit (O.classify G level v.1 ct.2.2.2).1 level
      (O.classify G level v.1 ct.2.2.2).2 = lx at hS' hw hd' hsw' hL hN
    obtain ⟨ex, s1⟩ := lx
    simp only at hd'
    subst hd'
    simp only [ite_true] at hL hN
    rw [show n + 2 - level = nodeFuel n (level + 1) by simp only [nodeFuel]; omega] at hN
    refine wp_otherTailG (Em := Em) (tc := ct.1.toNat) D L Lw hE hfr hS' c'
      ⟨cw7, hcw7.unch hF.1 hbt7, hrep7⟩
      (ka.trans hlab1) (kb.trans hptn1) (kc'.trans hlev1) (kd.trans hthis1) (ke.trans htcl1) hln
      hnc' hcb (fun s ch => hRec s (v.1 + 1) ch) hsw' ?_ ?_ ?_
    · intro hf
      apply hnf0
      show (hexNodeG false G level nc st).1 = .fuel
      rw [hN]
      have hf' : (Generic.sweep false G nautyInf 100 (nodeFuel n (level + 1)) (n + 1) level v.1
          ct.1.toNat ((ct.2.1.nextElem none).getD 0) (ct.2.1.nextElem none) ct.2.1 0
          (cheapCheck false level s1)).1 = .fuel := hf
      rw [hf']
    · intro t2 m2 ch2 hd2 hEm2 hS2 hc2
      have hd2' : (Generic.sweep false G nautyInf 100 (nodeFuel n (level + 1)) (n + 1) level v.1
          ct.1.toNat ((ct.2.1.nextElem none).getD 0) (ct.2.1.nextElem none) ct.2.1 0
          (cheapCheck false level s1)).1 = .done := hd2
      have hr : hexNodeG false G level nc st = (.unwind (level - 1) false,
          P.afterSweep false level ct.2.2.1
            (oSweepG G level v.1 ct.1.toNat ((ct.2.1.nextElem none).getD 0) (n + 1)
              (ct.2.1.nextElem none) ct.2.1 (cheapCheck false level s1)).2.1
            (oSweepG G level v.1 ct.1.toNat ((ct.2.1.nextElem none).getD 0) (n + 1)
              (ct.2.1.nextElem none) ct.2.1 (cheapCheck false level s1)).2.2) := by
        rw [hN, hd2']
      have hsa := L.afterSweep_same false level ct.2.2.1
        (oSweepG G level v.1 ct.1.toNat ((ct.2.1.nextElem none).getD 0) (n + 1)
          (ct.2.1.nextElem none) ct.2.1 (cheapCheck false level s1)).2.1
        (oSweepG G level v.1 ct.1.toNat ((ct.2.1.nextElem none).getD 0) (n + 1)
          (ct.2.1.nextElem none) ct.2.1 (cheapCheck false level s1)).2.2
      simp only [afterSweep, Bool.false_eq_true, ite_false] at hsa
      have := oPostG (Em := Em) (xi := xi) (v := ((level - 1 : Nat) : Int)) (args := args)
        (chain := chain) Lw hLS hLF hLd (hS2.same hsa) hc2 hok (by rw [hr]) (by rw [hr]; rfl) (by
          rw [hL]; simpa using emits_killEv.append (hw.emits.append hEm2))
      rw [show ((level - 1 : Nat) : Int) = (level : Int) - 1 by omega] at this
      revert this
      cases Mem.free_list m2 (blocks_of_env ge (oEnv Lo)) <;> simp [Post.after]
    · intro t2 m2 tg sh ch2 hu2 htg hS2 hau hEm2 hc2
      have hu2' : (Generic.sweep false G nautyInf 100 (nodeFuel n (level + 1)) (n + 1) level v.1
          ct.1.toNat ((ct.2.1.nextElem none).getD 0) (ct.2.1.nextElem none) ct.2.1 0
          (cheapCheck false level s1)).1 = .unwind tg sh := hu2
      have hr : hexNodeG false G level nc st = (.unwind tg sh,
          (oSweepG G level v.1 ct.1.toNat ((ct.2.1.nextElem none).getD 0) (n + 1)
            (ct.2.1.nextElem none) ct.2.1 (cheapCheck false level s1)).2.2) := by
        rw [hN, hu2']
      have := oPostG (Em := Em) (xi := xi) (v := (tg : Int)) (args := args)
        (chain := chain) Lw hLS hLF hLd hS2 hc2 hok (by rw [hr]) (by rw [hr]; rfl) (by
          rw [hL]; simpa using emits_killEv.append (hw.emits.append hEm2))
      revert this
      cases Mem.free_list m2 (blocks_of_env ge (oEnv Lo)) <;> simp [Post.after]

end Generic

/-- The dense instance of `othernode_bodyG`. -/
theorem othernode_body {k : Nat} (G : Colored n k) (Em : Bool → Nat → Nat → Search n → List Int)
    (hLaw : EmLawOff Em ⟨rowsOf G⟩) (S : SLoc) (st : Search n) (level nc : Nat)
    (chain : List (block × block))
    (_hRef : Refine.RefineFn xi S.M (.Vptr S.refineBlock Ptrofs.zero))
    (hRec : ∀ s nc' ch, Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (othernodeSpecG xi G Em S s (level + 1) nc' ch)) :
    Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (othernodeSpecG xi G Em S st level nc chain) := by
  intro args m hpre
  have hS := hpre.2.1
  have hn0 := hS.n0
  have hnI : n + 2 < SearchInf.nautyInfinity := by have := hS.nlt; show n + 2 < 2000000002; omega
  exact nodeSpec_ofG (othernode_bodyG Dispatch.dense denseClassifier denseLink
    (denseLaws G ⟨rowsOf G⟩ hn0 hnI) Em hLaw.toG S () () st level nc chain
    fun s nc' ch => nodeSpec_toG hS.gw (hRec s nc' ch)) args m hpre

end NautyVerified.Proofs.Search
