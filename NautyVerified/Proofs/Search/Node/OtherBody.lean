import NautyVerified.Proofs.Search.Node.OtherTail
import NautyVerified.Proofs.Search.Node.ProcFacts
import NautyVerified.Proofs.Search.Processnode.Satisfies

/-!
# `othernode0` meets its specification

`othernode_body`: nauty.c's `othernode0` satisfies `othernodeSpecG` at
`level`, given `othernode0`'s specification at `level + 1` for its children,
the emission law `EmLawOff`, and `refine`'s specification.

The body: the locals are allocated on entry (`alloc_ints`), the prologue finds
this level's target-cell entry (`wp_nodePrologue`), then the kill check, the
node count, the refinement (`wp_nodeVisit`), the code comparisons, the target
cell (`wp_chooseOff`), `processnode` (`wp_nodeProcess`) and, when the node
continues, `wp_otherTail`; HexGraphIso's side is `node_false_succ`.
`oPost`: freeing the locals at a return gives the specification's
postcondition.
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

/-- The specification's postcondition at a return, once the locals are freed. -/
theorem oPost {k : Nat} {G : Colored n k} {Em : Bool → Nat → Nat → Search n → List Int}
    {S : SLoc} {st : Search n} {level nc : Nat} {chain : List (block × block)} {args : List val}
    {m₀ m : mem} {chain' : List (block × block)} {ncw tcw : val} {nd bt : block} {L : OLocs}
    {s : Search n} {ns : Bool} {v : Int} {t : trace}
    (hLS : ∀ z ∈ L.list, z ∉ S.blocks) (hLF : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z)
    (hLd : L.list.Pairwise (· ≠ ·)) (hS : SearchAt m S ⟨rowsOf G⟩ s false ns)
    (c : Carry m₀ m S chain chain' level ncw tcw nd bt L)
    (hok : SearchInf.NodeOk G false level nc st)
    (hr2 : (hexNode false ⟨rowsOf G⟩ level nc st).2 = s)
    (hrv : exitValue level (hexNode false ⟨rowsOf G⟩ level nc st).1 = (v, ns))
    (hEm : Emits t (Em false level nc st)) :
    match Mem.free_list m (blocks_of_env ge (oEnv L)) with
    | some m'' => (othernodeSpecG xi G Em S st level nc chain).post args m₀ t (.Vint (ir v)) m''
    | none => False := by
  obtain ⟨m', hfree, hS', hTc', hTo', hF', hW'⟩ := c.finish hLS hLF hLd hS
  rw [hfree]
  have hlt : level - 1 < chain'.length := by
    have := c.own; rw [List.getElem?_eq_some_iff] at this; obtain ⟨h1, -⟩ := this; exact h1
  have hl1 := c.l1
  refine ⟨by rw [hrv], by rw [hr2, hrv]; exact hS', hEm,
    ⟨chain', hTc', hTo', by omega, c.take, c.old⟩, hF', hW', ?_⟩
  exact SearchInf.nodeOk_unwind_lt hok _ _ _ _

theorem vars_notWork {S : SLoc} (hd : S.blocks.Pairwise (· ≠ ·)) {z : block} (hz : z ∈ S.vars) :
    z ∉ workG := fun h => SLoc.vars_ne hd z hz z (workG_globs z h) rfl

theorem vars_chg {S : SLoc} (hd : S.blocks.Pairwise (· ≠ ·)) {z : block} (hz : z ∈ S.vars)
    (hu : z ≠ S.bUA) : S.Chg z :=
  ⟨SLoc.vars_blocks hz, hu, fun e => SLoc.vars_ne hd z hz _ tcnode0_globs e⟩

theorem compareCodes_ptn' (level code : Nat) (st : Search n) :
    (compareCodes level code st).ptn = st.ptn := by
  rw [compareCodes]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.ptn, ite_self]

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

theorem oEntry_exists (m₀ : mem) (args : List val) (a b c d e : val)
    (ha : args = [a, b, c, d, e]) :
    ∃ en le m, function_entry2 ge dense.fn.«nauty:othernode0» args m₀ en le m ∧
      le = oTemps a b c d e ∧ ∃ L, OEntry m₀ en m L := by
  subst ha
  have hids : [dense.id.numcells, dense.id.refcode, dense.id.tcellsize, dense.id.tc,
      dense.id.qinvar].Nodup := by decide
  obtain ⟨en, m, hav, hout, hin, hdist, hu, hg⟩ := alloc_ints _ empty_env m₀ hids
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

set_option maxHeartbeats 16000000 in
theorem othernode_body {k : Nat} (G : Colored n k) (Em : Bool → Nat → Nat → Search n → List Int)
    (hLaw : EmLawOff Em ⟨rowsOf G⟩) (S : SLoc) (st : Search n) (level nc : Nat)
    (chain : List (block × block))
    (hRef : Refine.RefineFn xi S.M (.Vptr S.refineBlock Ptrofs.zero))
    (hRec : ∀ s nc' ch, Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (othernodeSpecG xi G Em S s (level + 1) nc' ch)) :
    Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (othernodeSpecG xi G Em S st level nc chain) := by
  refine satisfies_internal (Entry := fun args m₀ e le m =>
      le = oTemps (.Vptr S.bl S.lofs) (.Vptr S.bp S.pofs) (.Vint (ir level)) (.Vint (ir nc))
        (.Vptr (tcParent chain level) Ptrofs.zero) ∧ ∃ L, OEntry m₀ e m L) ?_ ?_
  · rintro args m ⟨hargs, -⟩
    obtain ⟨en, le, m', hfe, hle, L, hL⟩ := oEntry_exists m args _ _ _ _ _ hargs
    exact ⟨en, le, m', hfe, hle, L, hL⟩
  rintro args m₀ ⟨hargs, h0, hTc0, hTo0, hlen, hcb, hl1, hln, hncn, hok, huaV, huaP⟩
  rw [triple_iff_wp]
  rintro e le mA ⟨rfl, L, rfl, hLA, hLd, huA, hgA⟩
  have hLF : ∀ z ∈ L.list, ¬ Mem.valid_block m₀ z := fun z hz => (hLA z hz).1
  have haccA : ∀ z ∈ L.list, Mem.valid_access mA .Mint32 z (zOfInt 0) .Freeable :=
    fun z hz => (hLA z hz).2
  have hn0 := h0.n0
  have hnl := h0.nlt
  have hnI : n + 2 < SearchInf.nautyInfinity := by show n + 2 < 2000000002; omega
  obtain ⟨hSA, hTcA, hToA, hbackA, hwmA, hLS, hwkA, hcA⟩ :=
    oAlloc (L := L) h0 huaV hTc0 hTo0 huA hgA hLF
  have hE : OEnv (oEnv L) S m₀ L := by
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
  have hd := h0.distinct
  have T0 : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level], x ≠ dense.id.tcnode_this ∧
      x ≠ dense.id.tcell ∧ x ≠ idOf 703 ∧ x ≠ idOf 704 ∧ x ≠ idOf 705 ∧ x ≠ idOf 706 ∧
      x ≠ idOf 707 := by decide
  obtain ⟨_, -, bncA⟩ := arrayAt_of_access (haccA L.bnc (by simp))
  refine wp_nodePrologue (nc := nc) hSA (hgA _ huaV) hTcA hToA hlen hl1 hE.enc bncA (hLS _ (by simp))
    (hwkA _ (by simp)) (hcA _ (by simp)) (hE.gl _)
    (by simp (config := {decide := true}) only [oTemps, temps_gso, temps_gss])
    (by simp (config := {decide := true}) only [oTemps, temps_gso, temps_gss]) ?_
  intro le1 m1 chain' nd bt hS1 hA1 hTc1 hTo1 hown htake hold hcellE hU1 hg1 hwm1 hK1 hthis1 htcl1 hle1
  obtain ⟨tcw, c1⟩ := Carry.init h0 hTo0 hl1 hlen huaV huaP hLF hLS hLd huA hgA hwmA haccA hwkA hcA
    hA1 hTc1 hTo1 hown htake hold hU1 hg1 hwm1 hK1
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
  refine wp_otherKill (hgl _ (by decide)) ?_
  simp only [seqPost, Post.after]
  have k708 : ∀ x, x ≠ idOf 708 → PTree.get x (PTree.set (idOf 708) (.Vint Int.zero) le1) =
      PTree.get x le1 := fun x h => temps_gso _ _ h
  -- the node count
  wp_step; wp_step; wp_step
  refine wp_numnodes hS1 (hgl _ (by decide)) ?_
  intro m2 h2 hu2 hg2
  have hbst : S.bst ∈ S.vars := by simp [SLoc.vars]
  obtain ⟨c2, -, hcell2, -⟩ := c1.chg hLS hS1 hu2 hg2
    (fun z hz => by subst hz; exact ⟨vars_chg hd hbst (by sep_ne hd), vars_notWork hd hbst⟩) hcellE
  have hbncS : L.bnc ∉ S.blocks := hLS _ (by simp)
  have hA2 := hA1.unch hu2 (fun e => hbncS (e ▸ SLoc.vars_blocks hbst))
  simp only [seqPost, Post.after, E0_append]
  -- the refinement
  have hlocS : ∀ z ∈ L.list, z ∉ S.blocks ∧ Mem.valid_block m2 z ∧ ¬ IsWork m2 z := fun z hz =>
    ⟨hLS z hz, Alloc.valid_of_access (c2.locs z hz).1, (c2.locs z hz).2.1⟩
  obtain ⟨_, -, hqA⟩ := arrayAt_of_access (c2.locs L.bq (by simp)).1
  obtain ⟨_, -, hkA⟩ := arrayAt_of_access (c2.locs L.bk (by simp)).1
  wp_step; wp_step; wp_step
  refine wp_nodeVisit (st := { st with numnodes := st.numnodes + 1 }) h2 c2.uaV
    (TcChain.headValid c2.tcc) hRef (bnc := L.bnc) (bq := L.bq) (bk := L.bk)
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
    (by rw [k708 _ (by decide)]; exact hlev1) hl1 hln hncn
    { SInv.visitSt hn0 hnI hS1.inv hok ⟨rowsOf G⟩ with } ?_
  intro m3 h3 hnc3 hk3 hq3 hU3 hg3 hwm3 hK3
  have hv := visit_eq ⟨rowsOf G⟩ level nc st
  generalize hvv : visit ⟨rowsOf G⟩ level nc st = v at hv
  obtain ⟨hv1, hv2, hv3⟩ := hv
  rw [← hv1] at h3
  rw [← hv2] at hnc3
  rw [← hv3] at hk3
  have ld : ∀ {mm : mem} {b : block} {w : val}, ArrayAt mm .Mint32 b 0 (fun _ => w) 1 →
      Mem.load .Mint32 mm b (zOfInt 0) = some w := fun hA => by
    simpa [elemOfs] using hA.load 0 (by decide)
  obtain ⟨btS, -, btV, -, -⟩ := c2.ntc
  have hnot3 : ∀ z, z ∉ S.blocks → Mem.valid_block m2 z → ¬ IsWork m2 z → z ≠ L.bnc → z ≠ L.bq →
      z ≠ L.bk → ¬ (S.Chg z ∨ ¬ Mem.valid_block m2 z ∨ IsWork m2 z ∨ z = L.bnc ∨ z = L.bq ∨
        z = L.bk) := by
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
  have nbz3 := hnot3 L.bz (hlocS _ (by simp)).1 (hlocS _ (by simp)).2.1 (hlocS _ (by simp)).2.2
    (fun e => d13 e.symm) (fun e => d35 e) (fun e => d23 e.symm)
  have nbc3 := hnot3 L.bc (hlocS _ (by simp)).1 (hlocS _ (by simp)).2.1 (hlocS _ (by simp)).2.2
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
  have hc := visit_code_lt ⟨rowsOf G⟩ level nc st
  rw [hvv] at hc
  simp only [seqPost, Post.after, E0_append]
  -- `code = (short)refcode`, the statistics
  wp_step
  refine wp_codeSet hE.ek (ld hk3) (by omega) ?_
  simp only [seqPost, Post.after, E0_append]
  wp_step
  refine wp_invstat0 hE.eq (ld hq3) ?_
  simp only [seqPost, Post.after, E0_append]
  -- the code comparisons
  have kc : ∀ x, x ≠ dense.id.code → x ≠ idOf 708 →
      PTree.get x (PTree.set dense.id.code (.Vint (ir v.2.1)) (PTree.set (idOf 708) (.Vint Int.zero) le1)) =
      PTree.get x le1 := fun x h1 h2 => by rw [temps_gso _ _ h1, temps_gso _ _ h2]
  wp_step
  refine wp_codeFirst h3 (hgl _ (by decide)) (hgl _ (by decide))
    (by rw [kc _ (by decide) (by decide)]; exact hlev1) (temps_gss _ _ _) (by omega) hl1 hln ?_
  intro le4 m4 h4 hu4 hg4 hle4
  obtain ⟨c4, -, hcell4, -⟩ := c3.chg hLS h3 hu4 hg4
    (fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      subst hz; exact ⟨⟨by simp [SLoc.blocks], by sep_ne hd, by decide⟩, by decide⟩) hcell3
  have k4 : ∀ x, x ≠ idOf 709 → x ≠ dense.id.code → x ≠ idOf 708 → PTree.get x le4 = PTree.get x le1 :=
    fun x h0 h1 h2 => (hle4 x h0).trans (kc x h1 h2)
  have hcode4 : PTree.get dense.id.code le4 = some (.Vint (ir v.2.1)) := by
    rw [hle4 _ (by decide)]; exact temps_gss _ _ _
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_codeCanon h4 (hgl _ (by decide)) (hgl _ (by decide)) (hgl _ (by decide))
    (hgl _ (by decide)) (by rw [k4 _ (by decide) (by decide) (by decide)]; exact hlev1) hcode4
    (by omega) hl1 hln ?_
  intro m5 h5 hu5 hg5
  have hbCC : S.bCC ∈ S.vars := by simp [SLoc.vars]
  obtain ⟨c5, -, hcell5, -⟩ := c4.chg hLS h4 hu5 hg5
    (fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨⟨by simp [SLoc.blocks], by sep_ne hd, by decide⟩, by decide⟩
      · exact ⟨⟨by simp [SLoc.blocks], by sep_ne hd, by decide⟩, by decide⟩
      · exact ⟨vars_chg hd hbCC (by sep_ne hd), vars_notWork hd hbCC⟩) hcell4
  rw [← compareCodes_eq] at h5
  simp only [seqPost, Post.after, E0_append]
  -- `tc = -1`
  obtain ⟨_, -, hbcA⟩ := arrayAt_of_access (c5.locs L.bc (by simp)).1
  wp_step; wp_step; wp_step
  refine wp_localStore hE.ec hbcA (rhs := .Eunop .Oneg (ci 1 tint) tint) (w := -1)
    (by simp [Exec.evalExpr, typeof, cop]) rfl ?_
  intro m6 hA6 hu6 hK6 hg6
  obtain ⟨btS5, btW5, -, -, -⟩ := c5.ntc
  have bc6 : ¬ bt = L.bc := fun e =>
    ((c5.locs _ (by simp)).2.2 _ (List.mem_of_getElem? c5.own)).2 e
  have hbcS : L.bc ∉ S.blocks := hLS _ (by simp)
  obtain ⟨cv5, hcv5⟩ := hcell5
  have c6 := c5.step (ncw' := .Vint (ir v.1)) (tcw' := .Vint (ir (-1))) hLS hLF h5 hu6 hg6
    (WorkMono.of_unch h5.work hu6 (fun z hz e => hbcS (e ▸ by revert z; simp [workG, SLoc.blocks]))
      (fun z hz e => (c5.locs _ (by simp)).2.1 (e ▸ hz)))
    (fun z hz => .inr (.inr (.inr (.inl (hz ▸ by simp)))))
    (fun z _ => hK6 z) ⟨cv5, hcv5.unch hu6 bc6⟩ (hK6 bt)
    (by rw [hu6.load _ _ _ (fun e => d14 e)]; exact c5.ncv) (ld hA6)
  have h6 := h5.unch hu6 (fun z hz e => hbcS (e ▸ hz)) (fun z hz e => (c5.locs _ (by simp)).2.1 (e ▸ hz))
  simp only [seqPost, Post.after, E0_append]
  -- the target cell
  have hpf := (SearchInf.PartOk.visit hn0 hnI hl1 (SearchInf.PartOk.of_nodeOk hnI hok) ⟨rowsOf G⟩).facts hn0 hnI
  rw [hvv] at hpf
  obtain ⟨btS6, btW6, btV6, -, -⟩ := c6.ntc
  have nbt : ∀ z ∈ L.list, bt ≠ z := fun z hz e =>
    ((c6.locs _ hz).2.2 _ (List.mem_of_getElem? c6.own)).2 e
  obtain ⟨_, -, hbzA⟩ := arrayAt_of_access (c6.locs L.bz (by simp)).1
  wp_step
  refine wp_chooseOff (nc := v.1) h6 c6.uaV (TcChain.headValid c6.tcc) (bnc := L.bnc)
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
      · exact ⟨hLS _ (by simp), Alloc.valid_of_access (c6.locs _ (by simp)).1, (c6.locs _ (by simp)).2.1⟩
      · exact ⟨hLS _ (by simp), Alloc.valid_of_access (c6.locs _ (by simp)).1, (c6.locs _ (by simp)).2.1⟩)
    ⟨fun e => nbt _ (by simp) e.symm, d13, d14⟩
    (by rw [k4 _ (by decide) (by decide) (by decide)]; exact htcl1) hE.enc hE.ez hE.ec (hE.gl _)
    c6.ncv hpf.numcellsLe ⟨cv5, hcv5.unch hu6 bc6⟩ hbzA hA6
    (by rw [k4 _ (by decide) (by decide) (by decide)]; exact hlab1)
    (by rw [k4 _ (by decide) (by decide) (by decide)]; exact hptn1)
    (by rw [k4 _ (by decide) (by decide) (by decide)]; exact hlev1) hl1 hln
    (fun hlt => by
      rw [compareCodes_ptn']
      exact exists_gt_of_bcount (n := n) (ptn := v.2.2.ptn) (by rw [← hpf.count]; exact hlt)) ?_
  intro le7 m7 h7 hc7 hch7 ht7 hz7 hU7 hg7 hwm7 hK7 hle7
  generalize hctg : chooseTarget false ⟨rowsOf G⟩ 100 level v.1
    (compareCodes level v.2.1 v.2.2) = ct at h7 hc7 hch7
  have nbnc7 : ¬ (S.Chg L.bnc ∨ ¬ Mem.valid_block m6 L.bnc ∨ IsWork m6 L.bnc ∨ L.bnc = bt ∨
      L.bnc = L.bz ∨ L.bnc = L.bc) := by
    rintro (h | h | h | h | h | h)
    · exact hbncS h.1
    · exact h (Alloc.valid_of_access (c6.locs _ (by simp)).1)
    · exact (c6.locs _ (by simp)).2.1 h
    · exact nbt _ (by simp) h.symm
    · exact d13 h
    · exact d14 h
  have nloc7 : ∀ z ∈ [L.bk, L.bq], ¬ (S.Chg z ∨ ¬ Mem.valid_block m6 z ∨ IsWork m6 z ∨ z = bt ∨
      z = L.bz ∨ z = L.bc) := by
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
  have k7 : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.tcnode_this, dense.id.tcell],
      PTree.get x le7 = PTree.get x le1 := fun x hx => by
    rw [hle7 x (by revert x; decide) (by revert x; decide) (by revert x; decide),
      k4 x (by revert x; decide) (by revert x; decide) (by revert x; decide)]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at k7
  obtain ⟨k7a, k7b, k7c, k7d, k7e⟩ := k7
  simp only [seqPost, Post.after, E0_append]
  -- the node callback
  wp_step
  refine wp_userNode h7 (hgl _ (by decide)) ?_
  simp only [seqPost, Post.after, E0_append]
  -- HexGraphIso's node, unfolded
  have hN : hexNode false ⟨rowsOf G⟩ level nc st =
      node false ⟨rowsOf G⟩ nautyInf 100 (n + 2 - level + 1) level nc st := by
    show node _ _ _ _ (n + 3 - level) _ _ _ = _
    rw [show n + 3 - level = n + 2 - level + 1 by omega]
  rw [node_false_succ] at hN
  simp only [hvv, hctg] at hN
  have hL := hLaw level nc st hl1 hln
  simp only [hvv, hctg] at hL
  have hlok := proc_leafOk hok ⟨rowsOf G⟩ 100
  simp only [hvv, hctg] at hlok
  have hlt := SearchInf.node_hlt hok ⟨rowsOf G⟩ 100
  simp only [hvv, hctg] at hlt
  -- processnode
  refine wp_nodeProcess h7 (Processnode.processnode_satisfies S ⟨rowsOf G⟩ ct.2.2.2 level v.1) hcb hl1
    hln hpf.numcellsLe hlok (h7.valid_all c7.uaV (TcChain.headValid c7.tcc)) c7.uaP hE.enc c7.ncv
    (hgl _ (by decide)) (by rw [k7a]; exact hlab1) (by rw [k7b]; exact hptn1) (by rw [k7c]; exact hlev1)
    hfr hlt (SearchInf.node_hnf _ _ _ _) ?_ ?_
  · intro t m' hnd hS' hw hF hW
    obtain ⟨-, -, btV7, -, -⟩ := c7.ntc
    have hout : ∀ z, z ∉ S.blocks → Mem.valid_block m7 z → ¬ IsWork m7 z →
        ¬ (S.Chg z ∨ ¬ Mem.valid_block m7 z ∨ IsWork m7 z) := by
      rintro z h1 h2 h3 (h | h | h)
      · exact h1 h.1
      · exact h h2
      · exact h3 h
    have hloc : ∀ z ∈ L.list, ¬ (S.Chg z ∨ ¬ Mem.valid_block m7 z ∨ IsWork m7 z) := fun z hz =>
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
    have hnf := SearchInf.node_hnf ⟨rowsOf G⟩ level v.1 ct.2.2.2
    simp only [procExit, procWords] at hS' hw hnd hnf hL hN ⊢
    generalize leafExit (classify ⟨rowsOf G⟩ level v.1 ct.2.2.2).1 level
      (classify ⟨rowsOf G⟩ level v.1 ct.2.2.2).2 = lx at hS' hw hnd hnf hL hN ⊢
    obtain ⟨ex, s1⟩ := lx
    cases ex with
    | done => exact absurd rfl hnd
    | fuel => exact absurd rfl hnf
    | unwind tg sh =>
      have hr : hexNode false ⟨rowsOf G⟩ level nc st = (.unwind tg sh, s1) := hN
      exact oPost hLS hLF hLd hS' c' hok (by rw [hr]) (by rw [hr]) (by
        rw [hL]; simpa using emits_killEv.append hw.emits)
  · intro t le' m' hd' hS' hw hF hW hle'
    obtain ⟨-, -, btV7, -, -⟩ := c7.ntc
    have hout : ∀ z, z ∉ S.blocks → Mem.valid_block m7 z → ¬ IsWork m7 z →
        ¬ (S.Chg z ∨ ¬ Mem.valid_block m7 z ∨ IsWork m7 z) := by
      rintro z h1 h2 h3 (h | h | h)
      · exact h1 h.1
      · exact h h2
      · exact h3 h
    have hloc : ∀ z ∈ L.list, ¬ (S.Chg z ∨ ¬ Mem.valid_block m7 z ∨ IsWork m7 z) := fun z hz =>
      hout z (hLS z hz) (Alloc.valid_of_access (c7.locs z hz).1) (c7.locs z hz).2.1
    have hbt7 := hout bt btS6 btV7 c7.ntc.2.1
    -- the node chose its target cell
    have hdn := SearchInf.node_hDone hn0 hnI hok ⟨rowsOf G⟩ 100
    simp only [hvv, hctg] at hdn
    obtain ⟨hnc', hcho⟩ := hdn hd'
    obtain ⟨⟨cw7, hcw7, hrep7⟩, -⟩ := hch7 ⟨hnc', hcho⟩
    have hct0 : 0 ≤ ct.1 := by
      rw [← hctg, chooseTarget_false_eq, ite_eq_left ⟨hnc', hcho⟩]; exact Int.natCast_nonneg _
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
    have hsw := SearchInf.nodeOk_sweepOff hn0 hnI hok ⟨rowsOf G⟩ 100
    simp only [hvv, hctg] at hsw
    have hsw' := hsw hd'
    have hnf0 := SearchInf.nodeOk_noFuel hn0 hnI hok ⟨rowsOf G⟩ 100 hln
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
    simp only [procExit, procWords] at hS' hw hd' hsw' hL hN
    generalize leafExit (classify ⟨rowsOf G⟩ level v.1 ct.2.2.2).1 level
      (classify ⟨rowsOf G⟩ level v.1 ct.2.2.2).2 = lx at hS' hw hd' hsw' hL hN
    obtain ⟨ex, s1⟩ := lx
    simp only at hd'
    subst hd'
    simp only [ite_true] at hL hN
    rw [show n + 2 - level = nodeFuel n (level + 1) by simp only [nodeFuel]; omega] at hN
    refine wp_otherTail (Em := Em) (tc := ct.1.toNat) hE hfr hS' c' ⟨cw7, hcw7.unch hF.1 hbt7, hrep7⟩
      (ka.trans hlab1) (kb.trans hptn1) (kc'.trans hlev1) (kd.trans hthis1) (ke.trans htcl1) hln hnc'
      hcb (fun s ch => hRec s (v.1 + 1) ch) hsw' ?_ ?_ ?_
    · intro hf
      apply hnf0
      show (hexNode false ⟨rowsOf G⟩ level nc st).1 = .fuel
      rw [hN]
      have hf' : (sweep false ⟨rowsOf G⟩ nautyInf 100 (nodeFuel n (level + 1)) (n + 1) level v.1
          ct.1.toNat ((ct.2.1.nextElem none).getD 0) (ct.2.1.nextElem none) ct.2.1 0
          (cheapCheck false level s1)).1 = .fuel := hf
      rw [hf']
    · intro t2 m2 ch2 hd2 hEm2 hS2 hc2
      have hd2' : (sweep false ⟨rowsOf G⟩ nautyInf 100 (nodeFuel n (level + 1)) (n + 1) level v.1
          ct.1.toNat ((ct.2.1.nextElem none).getD 0) (ct.2.1.nextElem none) ct.2.1 0
          (cheapCheck false level s1)).1 = .done := hd2
      have hr : hexNode false ⟨rowsOf G⟩ level nc st = (.unwind (level - 1) false,
          (oSweep G level v.1 ct.1.toNat ((ct.2.1.nextElem none).getD 0) (n + 1) (ct.2.1.nextElem none)
            ct.2.1 (cheapCheck false level s1)).2.2) := by
        rw [hN, hd2']; simp [afterSweep]
      have := oPost (Em := Em) (xi := xi) (v := ((level - 1 : Nat) : Int)) (args := args)
        (chain := chain) hLS hLF hLd hS2 hc2 hok (by rw [hr]) (by rw [hr]; rfl) (by
          rw [hL]; simpa using emits_killEv.append (hw.emits.append hEm2))
      rw [show ((level - 1 : Nat) : Int) = (level : Int) - 1 by omega] at this
      revert this
      cases Mem.free_list m2 (blocks_of_env ge (oEnv L)) <;> simp [Post.after]
    · intro t2 m2 tg sh ch2 hu2 htg hS2 hau hEm2 hc2
      have hu2' : (sweep false ⟨rowsOf G⟩ nautyInf 100 (nodeFuel n (level + 1)) (n + 1) level v.1
          ct.1.toNat ((ct.2.1.nextElem none).getD 0) (ct.2.1.nextElem none) ct.2.1 0
          (cheapCheck false level s1)).1 = .unwind tg sh := hu2
      have hr : hexNode false ⟨rowsOf G⟩ level nc st = (.unwind tg sh,
          (oSweep G level v.1 ct.1.toNat ((ct.2.1.nextElem none).getD 0) (n + 1) (ct.2.1.nextElem none)
            ct.2.1 (cheapCheck false level s1)).2.2) := by
        rw [hN, hu2']
      have := oPost (Em := Em) (xi := xi) (v := (tg : Int)) (args := args)
        (chain := chain) hLS hLF hLd hS2 hc2 hok (by rw [hr]) (by rw [hr]; rfl) (by
          rw [hL]; simpa using emits_killEv.append (hw.emits.append hEm2))
      revert this
      cases Mem.free_list m2 (blocks_of_env ge (oEnv L)) <;> simp [Post.after]

end NautyVerified.Proofs.Search
