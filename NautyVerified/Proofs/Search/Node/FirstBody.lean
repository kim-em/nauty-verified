import NautyVerified.Proofs.Search.Node.FirstInit
import NautyVerified.Proofs.Search.Node.FirstBodySteps
import NautyVerified.Proofs.Search.Node.ProcFacts
import NautyVerified.Proofs.Refine1.Nontrivial
import NautyVerified.Proofs.Search.Node.OtherBody

/-!
# `firstpathnode0` meets its specification

`firstpathnode_bodyG`: nauty.c's `firstpathnode0` satisfies the first-path
`nodeSpecG` at `level` for any dispatch record `D`, search policy `P` linked to
`D`'s operations by `Lk` and HexGraphIso laws `Lw`, given `firstpathnode0`'s
and `othernode0`'s specifications at `level + 1` for its children and the
emission law `EmLawFirstG`.

The body: the locals are allocated on entry (`fpn_entryG`), the prologue finds
this level's target-cell entry (`wp_nodePrologueG`), then the node count, the
refinement (`wp_nodeVisitG`), the first-path code (`wp_recordFirstG`), the
target cell (`wp_fpnTargetG`, `wp_firsttcStoreG`), the first leaf
(`wp_fpnLeafG`), the kill check, the cheap-automorphism test, the child loop
(`wp_fpnLoopG`) and the end of the sweep (`wp_fpnGrpG`, `wp_fpnLastG`);
HexGraphIso's side is `node_true_succG`. Memory is carried in `HeadAtG` before
the loop and `LoopAtG` during it; `HeadAtG.post` gives the postcondition at each
return. The C states are HexGraphIso's; `PolicyLink`'s equations and `Same`
move them to the policy's.

`firstpathnode_body` is the dense instance (`Dispatch.dense`, `denseLink`,
`denseLaws`, through `nodeSpec_toG` and `nodeSpec_ofG`).
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

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

/-! ### For any dispatch representation and search policy -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)
open NautyVerified.Proofs.Maketargetcell (mtcOf)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}

/-- The node's locals are allocated apart from everything of `S` and the list (`oAlloc`). -/
theorem fpnAllocG {D : DispatchRep ge O} {m₀ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre : Bool}
    {chain : List (block × block)} {Lo : OLocs}
    (h : SearchAtG D m₀ S gl cl G st pre false) (hvU : Mem.valid_block m₀ S.bUA)
    (hTc : TcChain m₀ S.M E.tcnode0 chain) (hTo : TcOkG D m₀ S gl cl chain)
    (hu : Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z))
    (hg : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m z)
    (hLF : ∀ z ∈ Lo.list, ¬ Mem.valid_block m₀ z) :
    SearchAtG D m S gl cl G st pre false ∧ TcChain m S.M E.tcnode0 chain ∧
      TcOkG D m S gl cl chain ∧ WorkMonoG D m₀ m ∧ (∀ z ∈ Lo.list, z ∉ S.blocksG D gl cl) ∧
      (∀ z ∈ Lo.list, ¬ IsWorkG D m z) ∧ (∀ z ∈ Lo.list, ∀ p ∈ chain, p.1 ≠ z ∧ p.2 ≠ z) := by
  have hvT : Mem.valid_block m₀ E.tcnode0 := TcChain.head_valid hTc
  have hvA := h.valid_all hvU hvT
  have hwk : ∀ z, IsWorkG D m₀ z → ¬ ¬ Mem.valid_block m₀ z := fun z hz hn => hn hz.valid
  have hback : ∀ z, IsWorkG D m z → IsWorkG D m₀ z := fun z hz =>
    (h.work.unch hu (fun z hz hn => hn (hvA z (SLoc.globs_mem (D.wglobs_sub z hz))))
      ⟨fun hn => hn (hvA _ (SLoc.mem_litG (by simp [SLoc.litG]))),
        fun hn => hn (hvA _ (SLoc.mem_litG (by simp [SLoc.litG])))⟩ hwk hg).2 z hz
  have wm : WorkMonoG D m₀ m := fun z hz => .inl (hback z hz)
  refine ⟨h.unch hu (fun z hz hn => hn (hvA z hz)) hwk hg, hTc.unch hu ?_, TcOkG.mono hTo hg wm,
    wm, fun z hz hS => hLF z hz (hvA z hS), fun z hz hw => hLF z hz (hback z hw).valid,
    fun z hz p hp => ⟨fun e => hLF z hz (e ▸ (hTo.valid p hp).1),
      fun e => hLF z hz (e ▸ (hTo.valid p hp).2)⟩⟩
  intro z hz hn
  simp only [tcBlocks, List.mem_cons] at hz
  rcases hz with rfl | hz
  · exact hn hvT
  · obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · exact hn (hTo.valid p hp).1
    · exact hn (hTo.valid p hp).2

/-- A step writing only some of `S`'s own scalars and arrays (`Ws`): those are
changeable blocks of `S`, and the step keeps the work blocks. -/
theorem SearchAtG.litStep {D : DispatchRep ge O} {m m' : mem} {S : SLoc} {gl : D.GLoc}
    {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {Ws : List block} (hu : Unch m m' (· ∈ Ws))
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hW : ∀ z ∈ Ws, z ∈ S.litG ∧ z ≠ S.bUA ∧ z ≠ E.tcnode0 ∧ z ≠ E.nautilWorkperm ∧
      z ≠ E.nautilWorkpermSz) :
    (∀ z ∈ Ws, S.ChgG D gl cl z) ∧ WorkMonoG D m m' := by
  have hc : ∀ z ∈ Ws, S.ChgG D gl cl z := fun z hz =>
    ⟨SLoc.mem_litG (hW z hz).1, (hW z hz).2.1, (hW z hz).2.2.1⟩
  exact ⟨hc, (SStepG.of_unch h hu hv (fun z hz => .inl (hc z hz))
    (fun z hz hz' => h.lit_globs z (hW z hz').1 (D.wglobs_sub _ hz))
    ⟨fun hz => (hW _ hz).2.2.2.1 rfl, fun hz => (hW _ hz).2.2.2.2 rfl⟩).2⟩

theorem HeadAtG.same {D : DispatchRep ge O} {L : LCtxG D n} {m : mem}
    {s t : SearchState n (O.Canon n)} {pre nsp : Bool} {ch : List (block × block)}
    (h : HeadAtG L m s pre nsp ch) (hs : Same O s t) : HeadAtG L m t pre nsp ch :=
  { h with search := h.search.same hs }

/-- `fPost` for `D` and the policy `P`. -/
theorem fPostG [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]
    {D : DispatchRep ge O} {NodeOk : Bool → Nat → Nat → SearchState n (O.Canon n) → Prop}
    {Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int}
    {L : LCtxG D n} {Lo : OLocs} {st : SearchState n (O.Canon n)} {nc : Nat} {args : List val}
    {m : mem} {ch : List (block × block)} {s : SearchState n (O.Canon n)} {ns : Bool} {v : Int}
    {t : trace}
    (H : HeadAtG L m s false ns ch) (hfresh : ∀ z ∈ L.locals, ¬ Mem.valid_block L.m₀ z)
    (hLO : ∀ z ∈ [Lo.bq, Lo.bnc, Lo.bc, Lo.bz, Lo.bk], z ∈ L.locals)
    (hnd : [Lo.bq, Lo.bnc, Lo.bc, Lo.bz, Lo.bk].Nodup)
    (hr2 : (hexNodeG true L.G L.level nc st).2 = s)
    (hrv : exitValue L.level (hexNodeG true L.G L.level nc st).1 = (v, ns))
    (hEm : Emits t (Em true L.level nc st))
    (hlt : ∀ tg sh, (hexNodeG true L.G L.level nc st).1 = .unwind tg sh → tg < L.level) :
    match Mem.free_list m (blocks_of_env ge (fEnv Lo)) with
    | some m'' => (nodeSpecG D xi NodeOk Em true L.S L.gl L.cl L.G st L.level nc L.chain₀).post
        args L.m₀ t (.Vint (ir v)) m''
    | none => False := by
  obtain ⟨mf, hfree, hS, hC, hF, hW⟩ := H.post hfresh (blocks_fEnvG Lo) hnd hLO
  rw [hfree]
  refine ⟨by rw [hrv], by rw [hr2, hrv]; exact hS, hEm, hC, hF, hW, hlt⟩

set_option maxHeartbeats 16000000 in
/-- `firstpathnode0` meets the first-path node specification for `D`, the policy
`P` linked to `O` by `Lk` and the laws `Lw` on `G`, given both specifications at
`level + 1` and the emission law. -/
theorem firstpathnode_bodyG [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]
    (D : DispatchC ge O) (Lk : PolicyLink O n) (G : O.Gr n) (Lw : NodeLaws Lk G)
    (Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int) (hLaw : EmLawFirstG Em G)
    (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) (level : Nat)
    (hRecF : ∀ s nc' ch, Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (nodeSpecG D.toDispatchRep xi Lw.NodeOk Em true S gl cl G s (level + 1) nc' ch))
    (hRecO : ∀ s nc' ch, Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (nodeSpecG D.toDispatchRep xi Lw.NodeOk Em false S gl cl G s (level + 1) nc' ch)) :
    ∀ st nc chain, Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (nodeSpecG D.toDispatchRep xi Lw.NodeOk Em true S gl cl G st level nc chain) := by
  intro st nc chain
  refine satisfies_internal (Entry := fun args m₀ e le m => ∃ Lo : OLocs, e = fEnv Lo ∧
      le = fTemps S.bl S.lofs S.bp S.pofs level nc (tcParent chain level) ∧
      (∀ z ∈ Lo.list, ¬ Mem.valid_block m₀ z ∧ Mem.valid_block m z ∧
        Mem.valid_access m .Mint32 z (zOfInt 0) .Freeable) ∧
      Lo.list.Pairwise (· ≠ ·) ∧ Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z) ∧
      (∀ z, Mem.valid_block m₀ z → Mem.valid_block m z)) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    obtain ⟨e, le, m', hfe, Lo, h1, h2, h3⟩ :=
      fpn_entryG (ge := ge) S.bl S.lofs S.bp S.pofs level nc (tcParent chain level) m
    exact ⟨e, le, m', hfe, Lo, h1, h2, h3⟩
  rintro args m₀ ⟨rfl, h0, hTc0, hTo0, hlen, hcb, hl1, hln, hncn, hok, huaV, huaP⟩
  rw [triple_iff_wp]
  rintro e le mA ⟨Lo, rfl, rfl, hLA, hLd, huA, hgA⟩
  have hLF : ∀ z ∈ Lo.list, ¬ Mem.valid_block m₀ z := fun z hz => (hLA z hz).1
  have haccA : ∀ z ∈ Lo.list, Mem.valid_access mA .Mint32 z (zOfInt 0) .Freeable :=
    fun z hz => (hLA z hz).2.2
  have hnl := h0.nlt
  obtain ⟨hSA, hTcA, hToA, hwmA, hLS, hwkA, hcA⟩ :=
    fpnAllocG (Lo := Lo) h0 huaV hTc0 hTo0 huA hgA hLF
  have hgl : ∀ x, x ∉ [dense.id.numcells, dense.id.refcode, dense.id.tcellsize, dense.id.tc,
      dense.id.qinvar] → PTree.get x (fEnv Lo) = none := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := hx
    rw [PTree.gso _ _ h2, PTree.gso _ _ h5, PTree.gso _ _ h4, PTree.gso _ _ h3, PTree.gso _ _ h1]
    rfl
  have gl' : ∀ l : List ident, (∀ x ∈ l, x ∉ [dense.id.numcells, dense.id.refcode,
      dense.id.tcellsize, dense.id.tc, dense.id.qinvar]) → ∀ x ∈ l, PTree.get x (fEnv Lo) = none :=
    fun l hl x hx => hgl x (hl x hx)
  have enc : PTree.get dense.id.numcells (fEnv Lo) = some (Lo.bnc, tint) := by
    (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
  have ez : PTree.get dense.id.tcellsize (fEnv Lo) = some (Lo.bz, tint) := by
    (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
  have ec : PTree.get dense.id.tc (fEnv Lo) = some (Lo.bc, tint) := by
    (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
  have eq : PTree.get dense.id.qinvar (fEnv Lo) = some (Lo.bq, tint) := by
    (repeat (rw [PTree.gso _ _ (by decide)])); exact PTree.gss _ _ _
  have ek : PTree.get dense.id.refcode (fEnv Lo) = some (Lo.bk, tint) := PTree.gss _ _ _
  have hfr : dense.fn.«nauty:firstpathnode0».fn_return = tint := rfl
  have hd := h0.lit
  rw [dense.fn.«nauty:firstpathnode0».fn_body_eq, Firstpathnode.body_eq]
  obtain ⟨_, -, bncA⟩ := arrayAt_of_access (haccA Lo.bnc (by simp))
  refine wp_nodePrologueG (nc := nc) hSA (hgA _ huaV) hTcA hToA hlen hl1 enc bncA
    (hLS _ (by simp)) (hwkA _ (by simp)) (hcA _ (by simp)) (gl' _ (by decide))
    (by simp (config := {decide := true}) only [fTemps, temps_gso, temps_gss])
    (by simp (config := {decide := true}) only [fTemps, temps_gso, temps_gss]) ?_
  intro le1 m1 chain' nd bt hS1 hA1 hTc1 hTo1 hown htake hold hcellE hU1 hg1 hwm1 hK1 hthis1
    htcl1 hle1
  have hlab1 : PTree.get dense.id.lab le1 = some (.Vptr S.bl S.lofs) := by
    rw [hle1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [fTemps, temps_gso, temps_gss]
  have hptn1 : PTree.get dense.id.ptn le1 = some (.Vptr S.bp S.pofs) := by
    rw [hle1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [fTemps, temps_gso, temps_gss]
  have hlev1 : PTree.get dense.id.level le1 = some (.Vint (ir level)) := by
    rw [hle1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [fTemps, temps_gso, temps_gss]
  -- the fixed context of the node
  let v := P.visit G level nc st
  let st₁ := P.recordFirst level v.2.1 v.2.2
  let ct := P.chooseTarget true G 100 level v.1 st₁
  let L : LCtxG D.toDispatchRep n := ⟨S, gl, cl, G, m₀, chain, level, v.1, ct.1.toNat, ct.2.2.1,
    Lo.bnc, Lo.bq, Lo.bk, Lo.bc, Lo.bz, nd, bt⟩
  have hLL : ∀ z ∈ L.locals, z ∈ Lo.list := by
    intro z hz
    simp only [L, LCtxG.locals, OLocs.list, List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢
    rcases hz with h | h | h | h | h <;> simp [h]
  have hfresh : ∀ z ∈ L.locals, ¬ Mem.valid_block L.m₀ z := fun z hz => hLF z (hLL z hz)
  have H1 : HeadAtG L m1 st true false chain' :=
    HeadAtG.init (L := L) h0 hTo0 hl1 hlen huaV huaP hfresh (fun z hz => hLS z (hLL z hz)) huA hgA
      hwmA (fun z hz => haccA z (hLL z hz)) (fun z hz => hwkA z (hLL z hz))
      (fun z hz => hcA z (hLL z hz)) hS1 hTc1 hTo1 hown htake hold hcellE hU1 hg1 hwm1 hK1
  -- the node count
  wp_step; wp_step; wp_step
  refine wp_numnodesG hS1 (hgl _ (by decide)) ?_
  intro m2 h2 hu2 hg2
  have hs2 := hS1.litStep (Ws := [S.bst]) (hu2.mono fun z hz => by simp [hz]) hg2
    (fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; subst hz
      exact ⟨by simp [SLoc.litG, L], by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd⟩)
  have H2 : HeadAtG L m2 { st with numnodes := st.numnodes + 1 } true false chain' :=
    H1.stepS hfresh h2 hu2 (fun z hz => by subst hz; exact .inl (hs2.1 _ (by simp))) hg2 hs2.2
  simp only [seqPost, Post.after, E0_append]
  -- the refinement
  have hLd' := hLd
  simp only [OLocs.list, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true] at hLd'
  obtain ⟨⟨d12, d13, d14, d15⟩, ⟨d23, d24, d25⟩, ⟨d34, d35⟩, d45⟩ := hLd'
  have hloc2 : ∀ z ∈ L.locals, z ∉ S.blocksG D.toDispatchRep gl cl ∧ Mem.valid_block m2 z ∧
      ¬ IsWorkG D.toDispatchRep m2 z := fun z hz =>
    ⟨(H2.locals z hz).2.1, (H2.locals z hz).1, (H2.locals z hz).2.2⟩
  have hbncS : Lo.bnc ∉ S.blocksG D.toDispatchRep gl cl := hLS _ (by simp)
  have hA2 := hA1.unch hu2 (fun e => hbncS (e ▸ SLoc.mem_litG (by simp [SLoc.litG, L])))
  obtain ⟨_, hqA⟩ := H2.locA Lo.bq (by simp [L, LCtxG.locals])
  obtain ⟨_, hkA⟩ := H2.locA Lo.bk (by simp [L, LCtxG.locals])
  have hbtL : ∀ z ∈ L.locals, L.btc ≠ z := fun z hz e =>
    (H2.chain.apart _ (List.mem_of_getElem? H2.chain.own)).2 (e ▸ hz)
  have hI0 := Lw.inv hok
  have hVo := Lw.visitOk hok
  wp_step; wp_step; wp_step
  refine wp_nodeVisitG (st := { st with numnodes := st.numnodes + 1 }) h2 H2.vU
    (TcChain.head_valid H2.chain.chain) (bnc := Lo.bnc) (bq := Lo.bq) (bk := Lo.bk)
    (by
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_singleton _ _⟩⟩
      · intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl
        · exact d15
        · exact d12
      · intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        subst hz; exact fun e => d25 e.symm)
    (fun z hz => hloc2 z (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> simp [L, LCtxG.locals]))
    enc eq ek (gl' _ (by decide)) hA2 ⟨_, hqA⟩ ⟨_, hkA⟩ hlab1 hptn1 hlev1 hl1 hln hncn
    (Lw.visit_active (st := st) hok) { Lw.visit_inv hok hS1.inv with } ?_
  intro m3 h3 hnc3 hk3 hq3 hU3 hg3 hwm3 hK3
  have hsame3 := Lk.visit_same G level nc st hI0 hVo
  have hnc3' : ArrayAt m3 .Mint32 Lo.bnc 0 (fun _ => .Vint (ir (v.1 : Int))) 1 := by
    have := Lk.visit_numcells G level nc st hI0 hVo
    simp only [v]; rw [this]; exact hnc3
  have hk3' : ArrayAt m3 .Mint32 Lo.bk 0 (fun _ => .Vint (ir (v.2.1 : Int))) 1 := by
    have := Lk.visit_code G level nc st hI0 hVo
    simp only [v]; rw [this]; exact hk3
  have H3 : HeadAtG L m3 v.2.2 true false chain' := by
    refine H2.stepL (Ls := [Lo.bnc, Lo.bq, Lo.bk]) hfresh (h3.same hsame3) (hU3.mono fun z hz => ?_)
      (fun z hz => .inr (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> simp [L, LCtxG.locals])) hg3 hwm3 hK3 (fun z hz _ => ?_)
      (fun hb => ?_)
    · rcases hz with h' | h' | h' | h' | h' | h'
      · exact .inl h'
      · exact .inr (.inl h')
      · exact .inr (.inr (.inl h'))
      all_goals (subst h'; exact .inr (.inr (.inr (by simp))))
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨_, hnc3⟩
      · exact ⟨_, hq3⟩
      · exact ⟨_, hk3⟩
    · exfalso
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with e | e | e
      · exact hbtL Lo.bnc (by simp [L, LCtxG.locals]) e
      · exact hbtL Lo.bq (by simp [L, LCtxG.locals]) e
      · exact hbtL Lo.bk (by simp [L, LCtxG.locals]) e
  have ld : ∀ {mm : mem} {b : block} {w : val}, ArrayAt mm .Mint32 b 0 (fun _ => w) 1 →
      Mem.load .Mint32 mm b (zOfInt 0) = some w := fun hA => by
    simpa [elemOfs] using hA.load 0 (by decide)
  have hc := Lw.code_lt hok
  simp only [seqPost, Post.after, E0_append]
  -- `firstcode[level] = refcode`
  wp_step; wp_step; wp_step
  refine wp_recordFirstG H3.search (hgl _ (by decide)) ek (ld hk3') hlev1 hc hln ?_
  intro m4 h4 hu4 hg4
  have hs4 := H3.search.litStep hu4 hg4 (fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; subst hz
      exact ⟨by simp [SLoc.litG, L], by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd⟩)
  have H4 : HeadAtG L m4 st₁ true false chain' := by
    have e1 : st₁ = recordFirst level v.2.1 v.2.2 := Lk.recordFirst_eq _ _ _
    rw [e1]
    exact H3.stepS hfresh h4 hu4 (fun z hz => .inl (hs4.1 z hz)) hg4 hs4.2
  have hq4 : Mem.load .Mint32 m4 Lo.bq (zOfInt 0) = some (.Vint (ir 0)) := by
    rw [hu4.load _ _ _ (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      exact fun e => hLS Lo.bq (by simp) (e ▸ SLoc.mem_litG (by simp [SLoc.litG, L])))]
    exact ld hq3
  simp only [seqPost, Post.after, E0_append]
  -- the invariant statistics
  wp_step
  refine wp_fpnInvstat0G eq hq4 ?_
  simp only [seqPost, Post.after, E0_append]
  -- HexGraphIso's node, unfolded
  have hN : hexNodeG true G level nc st =
      Generic.node true G nautyInf 100 (n + 2 - level + 1) level nc st := by
    show Generic.node _ _ _ _ (n + 3 - level) _ _ _ = _
    rw [show n + 3 - level = n + 2 - level + 1 by omega]
  rw [node_true_succG] at hN
  have hEmL := hLaw level nc st hl1 hln
  have hpf := Lw.visit_part hok
  have hncv : v.1 ≤ n := hpf.numcellsLe
  have hLO : ∀ z ∈ [Lo.bq, Lo.bnc, Lo.bc, Lo.bz, Lo.bk], z ∈ L.locals := by
    intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with h | h | h | h | h <;> simp [L, LCtxG.locals, h]
  have hnd : [Lo.bq, Lo.bnc, Lo.bc, Lo.bz, Lo.bk].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or]
    and_intros <;> first | exact List.nodup_nil | trivial | intro e <;> first | exact absurd e d12 | exact absurd e.symm d12 | exact absurd e d13 | exact absurd e.symm d13 | exact absurd e d14 | exact absurd e.symm d14 | exact absurd e d15 | exact absurd e.symm d15 | exact absurd e d23 | exact absurd e.symm d23 | exact absurd e d24 | exact absurd e.symm d24 | exact absurd e d25 | exact absurd e.symm d25 | exact absurd e d34 | exact absurd e.symm d34 | exact absurd e d35 | exact absurd e.symm d35 | exact absurd e d45 | exact absurd e.symm d45
  -- the target choice of HexGraphIso, through `O`
  have hIn₁ : Lk.Inv G st₁.canong := by
    have : st₁.canong = v.2.2.canong := by
      show (P.recordFirst level v.2.1 v.2.2).canong = _
      rw [Lk.recordFirst_eq]; rfl
    rw [this]; exact Lk.visit_inv G level nc st hI0 hVo
  have hTO : Lk.TargetOk G level v.1 st₁ := by simpa using Lw.targetOk hok
  have hcte := Lk.target_eq true G 100 level v.1 st₁ hIn₁ hTO
  have hcts := Lk.target_same true G 100 level v.1 st₁ hIn₁ hTO
  -- `tc = -1`
  obtain ⟨_, hbcA⟩ := H4.locA Lo.bc (by simp [L, LCtxG.locals])
  have hbcS : Lo.bc ∉ S.blocksG D.toDispatchRep gl cl := hLS _ (by simp)
  wp_step; wp_step; wp_step
  refine wp_localStoreG ec ⟨_, hbcA⟩ (rhs := .Eunop .Oneg (ci 1 tint) tint) (w := -1)
    (by simp [Exec.evalExpr, typeof, cop]) rfl ?_
  intro m5 hA5 hu5 hK5 hg5
  have h5 := H4.search.unch hu5 (fun z hz e => hbcS (e ▸ hz))
    (fun z hz e => (H4.locals Lo.bc (by simp [L, LCtxG.locals])).2.2 (e ▸ hz)) hg5
  have H5 : HeadAtG L m5 st₁ true false chain' :=
    H4.stepL (Ls := [Lo.bc]) hfresh h5 (hu5.mono fun z hz => .inr (.inr (.inr (by simp [hz]))))
      (fun z hz => .inr (by simp at hz; simp [hz, L, LCtxG.locals])) hg5
      (fun z hz => .inl ((H4.search.work.unch hu5
        (fun y hy e => hbcS (e ▸ SLoc.globs_mem (D.wglobs_sub _ hy)))
        ⟨fun e => hbcS (e ▸ SLoc.mem_litG (by simp [SLoc.litG, L])),
          fun e => hbcS (e ▸ SLoc.mem_litG (by simp [SLoc.litG, L]))⟩
        (fun y hy e => (H4.locals Lo.bc (by simp [L, LCtxG.locals])).2.2 (e ▸ hy)) hg5).2 z hz))
      (fun z _ => hK5 z) (fun z hz _ => by simp at hz; subst hz; exact ⟨_, hA5⟩)
      (fun hb => by simp at hb; exact absurd hb (hbtL Lo.bc (by simp [L, LCtxG.locals])))
  simp only [seqPost, Post.after, E0_append]
  -- the target cell
  have hncL : Mem.load .Mint32 m5 Lo.bnc (zOfInt 0) = some (.Vint (ir (v.1 : Int))) := by
    rw [hu5.load _ _ _ (fun e => d14 e), hu4.load _ _ _ (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      exact fun e => hbncS (e ▸ SLoc.mem_litG (by simp [SLoc.litG, L])))]
    exact ld hnc3'
  have hloc5 : ∀ z ∈ L.locals, z ∉ S.blocksG D.toDispatchRep gl cl ∧ Mem.valid_block m5 z ∧
      ¬ IsWorkG D.toDispatchRep m5 z := fun z hz =>
    ⟨(H5.locals z hz).2.1, (H5.locals z hz).1, (H5.locals z hz).2.2⟩
  have hmem5 := List.mem_of_getElem? H5.chain.own
  have btS : bt ∉ S.blocksG D.toDispatchRep gl cl := (H5.chain.ok.apart _ hmem5).2.1
  have btW : ¬ IsWorkG D.toDispatchRep m5 bt := (H5.chain.ok.apart _ hmem5).2.2.2
  have btV : Mem.valid_block m5 bt := (H5.chain.ok.valid _ hmem5).2
  obtain ⟨_, hbzA⟩ := H5.locA Lo.bz (by simp [L, LCtxG.locals])
  obtain ⟨_, hbcA5⟩ := H5.locA Lo.bc (by simp [L, LCtxG.locals])
  have hst₁ : st₁.lab = v.2.2.lab ∧ st₁.ptn = v.2.2.ptn := by
    show (P.recordFirst level v.2.1 v.2.2).lab = _ ∧ (P.recordFirst level v.2.1 v.2.2).ptn = _
    rw [Lk.recordFirst_eq]; exact ⟨rfl, rfl⟩
  wp_step; wp_step; wp_step
  refine wp_fpnTargetG (nc := v.1) H5.search H5.vU (TcChain.head_valid H5.chain.chain)
    (bt := bt) (bz := Lo.bz) (bc := Lo.bc) (bnc := Lo.bnc)
    (by
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_singleton _ _⟩⟩
      · intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl
        · exact hbtL _ (by simp [L, LCtxG.locals])
        · exact hbtL _ (by simp [L, LCtxG.locals])
      · intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        subst hz; exact d34)
    (fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨btS, btV, btW⟩
      · exact hloc5 _ (by simp [L, LCtxG.locals])
      · exact hloc5 _ (by simp [L, LCtxG.locals]))
    htcl1 ez ec (gl' _ (by decide)) (hgl _ (by decide)) H5.cellv ⟨_, hbzA⟩ ⟨_, hbcA5⟩ enc hncL
    hncv hlab1 hptn1 hlev1 hl1 hln
    (fun hne => by
      rw [hst₁.1, hst₁.2]
      exact Lw.target_lt hok (Nat.lt_of_le_of_ne hncv hne) (-1) (by omega))
    ?_ ?_
  · intro hne m6 h6 hws hz6 hc6 hU6 hg6 hwm6 hK6
    have hlt : v.1 < n := Nat.lt_of_le_of_ne hncv hne
    have htl := Lw.target_lt hok hlt (-1) (by omega)
    rw [← hst₁.1, ← hst₁.2] at htl
    -- `chooseTargetG`'s result
    have hctG : chooseTargetG O true G 100 level v.1 st₁ =
        (((mtcOf n st₁.lab st₁.ptn level (O.targetcell G st₁.lab st₁.ptn level 100 (-1))).1 : Int),
         (mtcOf n st₁.lab st₁.ptn level (O.targetcell G st₁.lab st₁.ptn level 100 (-1))).2.1,
         (mtcOf n st₁.lab st₁.ptn level (O.targetcell G st₁.lab st₁.ptn level 100 (-1))).2.2,
         { { st₁ with tctotal := st₁.tctotal +
              (mtcOf n st₁.lab st₁.ptn level (O.targetcell G st₁.lab st₁.ptn level 100 (-1))).2.2 } with
           firsttc := st₁.firsttc.set! level
             ((mtcOf n st₁.lab st₁.ptn level (O.targetcell G st₁.lab st₁.ptn level 100 (-1))).1 : Int) }) := by
      rw [chooseTargetG_true_eq, ite_eq_left hne]
    have hct1 : ct.1 = ((mtcOf n st₁.lab st₁.ptn level
        (O.targetcell G st₁.lab st₁.ptn level 100 (-1))).1 : Int) := by
      rw [hcte.1, hctG]
    have hct2 : ct.2.1 = (mtcOf n st₁.lab st₁.ptn level
        (O.targetcell G st₁.lab st₁.ptn level 100 (-1))).2.1 := by
      rw [hcte.2.1, hctG]
    have hct3 : ct.2.2.1 = (mtcOf n st₁.lab st₁.ptn level
        (O.targetcell G st₁.lab st₁.ptn level 100 (-1))).2.2 := by
      rw [hcte.2.2, hctG]
    have hpos : (mtcOf n st₁.lab st₁.ptn level
        (O.targetcell G st₁.lab st₁.ptn level 100 (-1))).1 < n := by
      simp only [mtcOf]; exact htl.1
    have hbtnL : bt ∉ L.locals := fun hz => hbtL bt hz rfl
    have H6 : HeadAtG L m6 { st₁ with tctotal := st₁.tctotal +
        (mtcOf n st₁.lab st₁.ptn level (O.targetcell G st₁.lab st₁.ptn level 100 (-1))).2.2 }
        true false chain' := by
      refine H5.stepL (Ls := [bt, Lo.bz, Lo.bc]) hfresh h6 (hU6.mono fun z hz => ?_)
        (fun z hz => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          rcases hz with rfl | rfl | rfl
          · exact .inl rfl
          · exact .inr (by simp [L, LCtxG.locals])
          · exact .inr (by simp [L, LCtxG.locals])) hg6 hwm6 hK6 (fun z hz hzl => ?_)
        (fun _ => by obtain ⟨ws, hwa, -⟩ := hws; exact ⟨_, hwa⟩)
      · rcases hz with h' | h' | h' | h' | h' | h'
        · exact .inl h'
        · exact .inr (.inl h')
        · exact .inr (.inr (.inl h'))
        all_goals (subst h'; exact .inr (.inr (.inr (by simp))))
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl
        · exact absurd hzl hbtnL
        · exact ⟨_, hz6⟩
        · exact ⟨_, hc6⟩
    simp only [seqPost, Post.after, E0_append]
    -- `firsttc[level] = tc`
    wp_step; wp_step; wp_step
    refine wp_firsttcStoreG h6 (hgl _ (by decide)) ec (ld hc6) hlev1 (by omega)
      (Int.ofNat_lt.mpr hpos) hln ?_
    intro m7 h7 hu7 hg7
    have hs7 := h6.litStep hu7 hg7 (fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; subst hz
        exact ⟨by simp [SLoc.litG, L], by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd⟩)
    have H7 : HeadAtG L m7 ct.2.2.2 true false chain' := by
      refine (H6.stepS hfresh h7 hu7 (fun z hz => .inl (hs7.1 z hz)) hg7 hs7.2).same ?_
      have := hcts; rw [hctG] at this; exact this
    have nloc7 : ∀ z ∈ L.locals, ¬ z ∈ [S.bTC] := fun z hz e => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
      exact (H6.locals z hz).2.1 (e ▸ SLoc.mem_litG (by simp [SLoc.litG, L]))
    have hncL7 : Mem.load .Mint32 m7 Lo.bnc (zOfInt 0) = some (.Vint (ir (v.1 : Int))) := by
      rw [hu7.load _ _ _ (nloc7 _ (by simp [L, LCtxG.locals])), hU6.load _ _ _ (by
        rintro (h' | h' | h' | h' | h' | h')
        · exact hbncS h'.1
        · exact h' (hloc5 _ (by simp [L, LCtxG.locals])).2.1
        · exact (hloc5 _ (by simp [L, LCtxG.locals])).2.2 h'
        · exact hbtL _ (by simp [L, LCtxG.locals]) h'.symm
        · exact d13 h'
        · exact d14 h')]
      exact hncL
    simp only [seqPost, Post.after, E0_append]
    -- no node callback, not a leaf
    wp_step
    refine wp_fpnUserG H7.search (hgl _ (by decide)) ?_
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine wp_fpnLeafG H7.search (gl' _ (by decide)) hfr enc hncL7 hncv hlab1 hlev1 hl1 hln
      (fun h => absurd h hne) (fun _ => ?_)
    simp only [seqPost, Post.after, E0_append]
    -- the kill check
    have k710 : ∀ x, x ≠ idOf 710 → PTree.get x (PTree.set (idOf 710) (.Vint Int.zero) le1) =
        PTree.get x le1 := fun x h => temps_gso _ _ h
    wp_step
    refine wp_fpnKillG (hgl _ (by decide)) ?_
    simp only [seqPost, Post.after]
    -- the cheap-automorphism test
    wp_step
    refine wp_fpnCheapG H7.search H7.vU (TcChain.head_valid H7.chain.chain)
      (Lk.cheapautom_eq _ _) (hgl _ (by decide)) (hgl _ (by decide)) (hgl _ (by decide))
      (hgl _ (by decide)) (by rw [k710 _ (by decide)]; exact hptn1)
      (by rw [k710 _ (by decide)]; exact hlev1) hl1 hln ?_
    intro le8 m8 h8 hu8 hg8 hwm8 hle8
    have hbt8 : ¬ (bt = E.noncheaplevel ∨ bt ∈ D.wglobs ∨ D.IsWork m7 bt ∨
        ¬ Mem.valid_block m7 bt) := by
      have hmem7 := List.mem_of_getElem? H7.chain.own
      have a2 : bt ∉ S.blocksG D.toDispatchRep gl cl := (H7.chain.ok.apart _ hmem7).2.1
      have a4 : ¬ IsWorkG D.toDispatchRep m7 bt := (H7.chain.ok.apart _ hmem7).2.2.2
      rintro (e | e | e | e)
      · exact a2 (e ▸ SLoc.mem_litG (by simp [SLoc.litG, L]))
      · exact a2 (SLoc.globs_mem (D.wglobs_sub _ e))
      · exact a4 (.inl e)
      · exact e (H7.chain.ok.valid _ hmem7).2
    have nl8 : ∀ z ∈ L.locals, ¬ (z = E.noncheaplevel ∨ z ∈ D.wglobs ∨ D.IsWork m7 z ∨
        ¬ Mem.valid_block m7 z) := fun z hz => by
      obtain ⟨a, b, c⟩ := H7.locals z hz
      rintro (e | e | e | e)
      · exact b (e ▸ SLoc.mem_litG (by simp [SLoc.litG, L]))
      · exact b (SLoc.globs_mem (D.wglobs_sub _ e))
      · exact c (.inl e)
      · exact e a
    have H8 : HeadAtG L m8 (P.cheapCheck true level ct.2.2.2) true false chain' := by
      rw [Lk.cheapCheck_eq]
      obtain ⟨cv, hcv⟩ := H7.cellv
      refine H7.step hfresh h8 (hu8.mono fun z hz => ?_) hg8 hwm8 ⟨cv, hcv.unch hu8 hbt8⟩
        (Alloc.Keep.unch hu8 hbt8)
        (fun z hz => by obtain ⟨w, hw⟩ := H7.locA z hz; exact ⟨w, hw.unch hu8 (nl8 z hz)⟩)
        (fun z hz => Alloc.Keep.unch hu8 (nl8 z hz))
      rcases hz with e | e | e | e
      · subst e
        exact .inl (.inl ⟨SLoc.mem_litG (by simp [SLoc.litG, L]), by sep_ne hd, by sep_ne hd⟩)
      · exact .inl (.inl ⟨SLoc.globs_mem (D.wglobs_sub _ e),
          fun e' => h0.lit_globs S.bUA (by simp [SLoc.litG, L]) (e' ▸ D.wglobs_sub _ e),
          fun e' => h0.lit_globs E.tcnode0 (by simp [SLoc.litG, L]) (e' ▸ D.wglobs_sub _ e)⟩)
      · exact .inl (.inr (.inr (.inl (.inl e))))
      · exact .inl (.inr (.inl e))
    simp only [seqPost, Post.after, E0_append]
    -- `index = 0; childcount = 0;`
    wp_step; wp_step; wp_step; wp_step
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step; wp_step
    simp only [seqPost, Post.after, E0_append]
    generalize hle9 : PTree.set dense.id.childcount _ (PTree.set dense.id.index _ le8) = le9
    have k9 : ∀ x, x ≠ dense.id.childcount → x ≠ dense.id.index → x ≠ idOf 710 → x ≠ idOf 711 →
        x ≠ idOf 712 → PTree.get x le9 = PTree.get x le1 := fun x h1 h2 h3 h4 h5 => by
      rw [← hle9, temps_gso _ _ h1, temps_gso _ _ h2, hle8 x h4 h5, k710 x h3]
    have hidx9 : PTree.get dense.id.index le9 = some (.Vint (ir ((0 : Nat) : Int))) := by
      rw [← hle9, temps_gso _ _ (by decide), temps_gss]; rfl
    have hcc9 : ∃ c, PTree.get dense.id.childcount le9 = some (.Vint c) := by
      rw [← hle9, temps_gss]; exact ⟨_, rfl⟩
    -- the first vertex of the target cell
    obtain ⟨tv1, htv1, hok1⟩ := Lw.first_start hok hne
    obtain ⟨ws, hwa, hwr⟩ := hws
    have nb7 : ¬ bt ∈ [S.bTC] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      intro hw; exact btS (hw ▸ SLoc.mem_litG (by simp [SLoc.litG, L]))
    have hwa8 : ArrayAt m8 .Mint64 bt 0 (longs ws) S.M := (hwa.unch hu7 nb7).unch hu8 hbt8
    wp_step; wp_step
    refine wp_fpnFirstG H8.search (gl' _ (by decide))
      (by rw [k9 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact htcl1)
      hwa8 hwr ?_
    intro r hr
    have htv1' : (mtcOf n st₁.lab st₁.ptn level
        (O.targetcell G st₁.lab st₁.ptn level 100 (-1))).2.1.nextElem none = some tv1 := by
      have h' : ct.2.1.nextElem none = some tv1 := htv1
      rw [hct2] at h'; exact h'
    have hr' : r = tv1 := by
      rcases hr with ⟨h1, -⟩ | ⟨w, h1, h2⟩
      · exact absurd (htv1'.symm.trans h1) (by simp)
      · rw [h2, Option.some.inj (htv1'.symm.trans h1)]
    subst hr'
    simp only [seqPost, Post.after, E0_append]
    -- the child loop
    have hle10 : ∀ x, x ≠ dense.id.tv1 → x ≠ dense.id.tv → x ≠ idOf 714 → x ≠ idOf 713 →
        PTree.get x (PTree.set dense.id.tv1 (.Vint (ir (tv1 : Int))) (PTree.set dense.id.tv
          (.Vint (ir (tv1 : Int))) (PTree.set (idOf 714) (.Vint (ir (tv1 : Int)))
            (PTree.set (idOf 713) (.Vint (ir (tv1 : Int))) le9)))) = PTree.get x le9 :=
      fun x h1 h2 h3 h4 => by rw [temps_gso _ _ h1, temps_gso _ _ h2, temps_gso _ _ h3, temps_gso _ _ h4]
    have k10 : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.tcell,
        dense.id.tcnode_this], PTree.get x (PTree.set dense.id.tv1 (.Vint (ir (tv1 : Int)))
          (PTree.set dense.id.tv (.Vint (ir (tv1 : Int))) (PTree.set (idOf 714) (.Vint (ir (tv1 : Int)))
            (PTree.set (idOf 713) (.Vint (ir (tv1 : Int))) le9)))) = PTree.get x le1 := by
      intro x hx
      rw [hle10 x (by revert x; decide) (by revert x; decide) (by revert x; decide)
        (by revert x; decide), k9 x (by revert x; decide) (by revert x; decide) (by revert x; decide)
        (by revert x; decide) (by revert x; decide)]
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at k10
    obtain ⟨ka, kb, kc, kd, ke⟩ := k10
    have hE : FEnvG (fEnv Lo) L := ⟨enc, ek, ez, ec, eq, hgl⟩
    have hT10 : FTempsG (PTree.set dense.id.tv1 (.Vint (ir (tv1 : Int))) (PTree.set dense.id.tv
        (.Vint (ir (tv1 : Int))) (PTree.set (idOf 714) (.Vint (ir (tv1 : Int)))
          (PTree.set (idOf 713) (.Vint (ir (tv1 : Int))) le9)))) L tv1 :=
      ⟨ka.trans hlab1, kb.trans hptn1, kc.trans hlev1, kd.trans htcl1, ke.trans hthis1,
        temps_gss _ _ _, by rw [hle10 _ (by decide) (by decide) (by decide) (by decide)]; exact hcc9⟩
    -- the locals' values at the loop
    have arr1 : ∀ {mm : mem} {b : block} {w : val}, Mem.load .Mint32 mm b (zOfInt 0) = some w →
        Mem.valid_access mm .Mint32 b (zOfInt 0) .Freeable → ArrayAt mm .Mint32 b 0 (fun _ => w) 1 :=
      fun {mm b w} hl ha => by
        refine ⟨Int.le_refl _, by decide, fun i hi => ?_, fun i hi => ?_⟩
        · obtain rfl : i = 0 := by omega
          exact hl
        · obtain rfl : i = 0 := by omega
          exact Mem.valid_access_implies _ _ _ _ _ _ ha (.perm_F_any _)
    have ld8 : ∀ z ∈ L.locals, Mem.load .Mint32 m8 z (zOfInt 0) = Mem.load .Mint32 m6 z (zOfInt 0) :=
      fun z hz => by rw [hu8.load _ _ _ (nl8 z hz), hu7.load _ _ _ (nloc7 z hz)]
    have hnc8 : ArrayAt m8 .Mint32 Lo.bnc 0 (fun _ => .Vint (ir (L.nc : Int))) 1 :=
      arr1 (by rw [hu8.load _ _ _ (nl8 _ (by simp [L, LCtxG.locals]))]; exact hncL7)
        (H8.fre _ (by simp [L, LCtxG.locals]))
    have hct1' : ((ct.1.toNat : Nat) : Int) = ((mtcOf n st₁.lab st₁.ptn level
        (O.targetcell G st₁.lab st₁.ptn level 100 (-1))).1 : Int) := by
      rw [hct1]; simp
    have lbc : Mem.load .Mint32 m8 Lo.bc (zOfInt 0) =
        some (.Vint (ir ((ct.1.toNat : Nat) : Int))) := by
      rw [ld8 Lo.bc (by simp [L, LCtxG.locals]), hct1']; exact ld hc6
    have lbz : Mem.load .Mint32 m8 Lo.bz (zOfInt 0) = some (.Vint (ir ((ct.2.2.1 : Nat) : Int))) := by
      rw [ld8 Lo.bz (by simp [L, LCtxG.locals]), hct3]; exact ld hz6
    have htc8 : ArrayAt m8 .Mint32 Lo.bc 0 (fun _ => .Vint (ir (L.tc : Int))) 1 :=
      arr1 lbc (H8.fre _ (by simp [L, LCtxG.locals]))
    have htz8 : ArrayAt m8 .Mint32 Lo.bz 0 (fun _ => .Vint (ir (L.tcsize : Int))) 1 :=
      arr1 lbz (H8.fre _ (by simp [L, LCtxG.locals]))
    have hcell8 : ∃ tw, ArrayAt m8 .Mint64 bt 0 (longs tw) S.M ∧
        SetRep (fun w => bv64 (tw w)) S.M ct.2.1 := ⟨ws, hwa8, by rw [hct2]; exact hwr⟩
    have HL := H8.loop hcell8 hnc8 htc8 htz8
    have hlevn : level + 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hpf.levelLe hlt)
    have htv1n : tv1 < n := (Lw.first_args hok1).1
    -- HexGraphIso's sweep
    have hsw : Generic.sweep true G nautyInf 100 (n + 2 - level) (n + 1) level v.1 ct.1.toNat
        ((ct.2.1.nextElem none).getD 0) (ct.2.1.nextElem none) ct.2.1 0
        (P.cheapCheck true level ct.2.2.2) =
        fSweepG L tv1 (n + 1) (some tv1) ct.2.1 0 (P.cheapCheck true level ct.2.2.2) := by
      have h' : ct.2.1.nextElem none = some tv1 := htv1
      rw [h']
      show Generic.sweep _ _ _ _ (n + 2 - level) _ _ _ _ _ _ _ _ _ =
        Generic.sweep _ _ _ _ (n + 3 - (level + 1)) _ _ _ _ _ _ _ _ _
      rw [show n + 3 - (level + 1) = n + 2 - level by omega]
      rfl
    have hNR : hexNodeG true G level nc st =
        match (fSweepG L tv1 (n + 1) (some tv1) ct.2.1 0 (P.cheapCheck true level ct.2.2.2)).1 with
        | .done => (.unwind (level - 1) false, P.afterSweep true level ct.2.2.1
            (fSweepG L tv1 (n + 1) (some tv1) ct.2.1 0 (P.cheapCheck true level ct.2.2.2)).2.1
            (fSweepG L tv1 (n + 1) (some tv1) ct.2.1 0 (P.cheapCheck true level ct.2.2.2)).2.2)
        | _ => ((fSweepG L tv1 (n + 1) (some tv1) ct.2.1 0 (P.cheapCheck true level ct.2.2.2)).1,
            (fSweepG L tv1 (n + 1) (some tv1) ct.2.1 0 (P.cheapCheck true level ct.2.2.2)).2.2) := by
      rw [hN]; dsimp only; rw [ite_eq_right hne, hsw]
      generalize fSweepG L tv1 (n + 1) (some tv1) ct.2.1 0 (P.cheapCheck true level ct.2.2.2) = R
      rcases R with ⟨_ | _ | _, _, _⟩ <;> rfl
    have hnf0 := Lw.noFuel hok hln
    have hEmS : Em true level nc st =
        fSweepEmG Em L tv1 (n + 1) (some tv1) ct.2.1 (P.cheapCheck true level ct.2.2.2) := by
      rw [hEmL]; dsimp only; rw [ite_eq_right hne]
      have h' : ct.2.1.nextElem none = some tv1 := htv1
      show sweepEmFirstG _ _ _ _ _ _ _ (ct.2.1.nextElem none) _ _ = _
      rw [h']; rfl
    refine wp_fpnLoopG Lk (Em := Em) L Lw hE hfr (fun s ch => hRecF s (v.1 + 1) ch)
      (fun s ch => hRecO s (v.1 + 1) ch) hcb hlevn (show v.1 + 1 ≤ n from hlt) htv1n ?_ ?_ ?_
      (k := n + 1)
      ⟨some tv1, ct.2.1, P.cheapCheck true level ct.2.2.2, 0, true, chain', HL, hT10,
        by rw [temps_gso _ _ (by decide), temps_gss]; rfl,
        by rw [hle10 _ (by decide) (by decide) (by decide) (by decide)]; exact hidx9, by omega,
        fun _ => rfl, fun _ => hok1, rfl, [], Emits.nil, rfl⟩
    · intro hf
      apply hnf0
      rw [hNR]
      revert hf
      generalize fSweepG L tv1 (n + 1) (some tv1) ct.2.1 0 (P.cheapCheck true level ct.2.2.2) = R
      intro hf
      rw [hf]
    · intro t le' m' cl' ch hdn hEm hL' hT hidx hidxle
      have hsz : ct.2.2.1 ≤ n := by
        rw [hct3]
        exact mtcOf_size (by rw [hst₁.2]; exact hpf.ptnSize)
          (by rw [hst₁.2]; exact Nat.le_trans hpf.ptnLast hl1) htl.1 htl.2
      -- MULTIPLY
      wp_step
      refine wp_fpnGrpG hL'.search (hgl _ (by decide)) hidx ?_
      intro le'' m'' h'' hu'' hg'' hle''
      have hsG := hL'.search.litStep (Ws := [S.bst]) (hu''.mono fun z hz => by simp [hz, L]) hg''
        (fun z hz => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; subst hz
          exact ⟨by simp [SLoc.litG, L], by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd⟩)
      have H' := hL'.head.stepS hfresh h'' hu'' (fun z hz => by
          subst hz; exact .inl (hsG.1 _ (by simp [L]))) hg'' hsG.2
      have hbzS : Lo.bz ∉ S.blocksG D.toDispatchRep gl cl := hLS _ (by simp)
      have hzv : Mem.load .Mint32 m'' Lo.bz (zOfInt 0) = some (.Vint (ir (L.tcsize : Int))) := by
        rw [hu''.load _ _ _ (fun e => hbzS (by rw [e]; exact SLoc.mem_litG (by simp [SLoc.litG, L])))]
        exact ld hL'.tz
      simp only [seqPost, Post.after, E0_append]
      refine wp_fpnLastG h'' (gl' _ (by decide)) hfr ez hzv
        (by rw [hle'' _ (by decide)]; exact hidx) (by rw [hle'' _ (by decide)]; exact hT.lev)
        hsz hidxle hln ?_
      intro m3 h3 hu3 hg3
      have hs3 := h''.litStep hu3 hg3 (fun z hz => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; subst hz
          exact ⟨by simp [SLoc.litG, L], by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd⟩)
      have H'' := (H'.stepS hfresh h3 hu3 (fun z hz => .inl (hs3.1 z hz)) hg3 hs3.2).same
        (Lk.afterSweep_same true level ct.2.2.1 _ _)
      have hr : hexNodeG true G level nc st = (.unwind (level - 1) false, P.afterSweep true level
          ct.2.2.1 (fSweepG L tv1 (n + 1) (some tv1) ct.2.1 0 (P.cheapCheck true level ct.2.2.2)).2.1
          (fSweepG L tv1 (n + 1) (some tv1) ct.2.1 0 (P.cheapCheck true level ct.2.2.2)).2.2) := by
        rw [hNR, hdn]
      have hEm' := emits_killEv.append hEm
      rw [List.nil_append, ← hEmS] at hEm'
      have := fPostG (xi := xi) (NodeOk := Lw.NodeOk) (Em := Em) (Lo := Lo) (L := L)
        (args := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level), .Vint (ir nc),
          .Vptr (tcParent chain level) Ptrofs.zero])
        (v := ((level - 1 : Nat) : Int)) H'' hfresh hLO hnd
        (by rw [hr]) (by rw [hr]; rfl)
        hEm'
        (fun tg sh h => by rw [hr] at h; cases h; exact Nat.sub_lt hl1 Nat.one_pos)
      rw [Int.ofNat_sub hl1] at this
      revert this
      cases Mem.free_list m3 (blocks_of_env ge (fEnv Lo)) <;> simp only [Post.after, E0_append, append_E0] <;> exact fun h => h
    · intro t m' cl' ch tg sh hu htg hL' hEm
      have hr : hexNodeG true G level nc st = (.unwind tg sh,
          (fSweepG L tv1 (n + 1) (some tv1) ct.2.1 0 (P.cheapCheck true level ct.2.2.2)).2.2) := by
        rw [hNR, hu]
      have hEm' := emits_killEv.append hEm
      rw [List.nil_append, ← hEmS] at hEm'
      have := fPostG (xi := xi) (NodeOk := Lw.NodeOk) (Em := Em) (Lo := Lo) (L := L)
        (args := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level), .Vint (ir nc),
          .Vptr (tcParent chain level) Ptrofs.zero])
        (v := (tg : Int)) hL'.head hfresh hLO hnd
        (by rw [hr]) (by rw [hr]; rfl)
        hEm'
        (fun tg' sh' h => by rw [hr] at h; cases h; exact htg)
      revert this
      cases Mem.free_list m' (blocks_of_env ge (fEnv Lo)) <;> simp only [Post.after, E0_append, append_E0] <;> exact fun h => h
  · intro hv1n
    have hctG : chooseTargetG O true G 100 level v.1 st₁ =
        ((-1 : Int), VSet.empty, 0, { st₁ with firsttc := st₁.firsttc.set! level (-1) }) := by
      rw [chooseTargetG_true_eq, ite_eq_right (fun h => h hv1n)]
    wp_step; wp_step; wp_step
    refine wp_firsttcStoreG H5.search (hgl _ (by decide)) ec (ld hA5) hlev1 (by omega) (by omega)
      hln ?_
    intro m6 h6 hu6 hg6
    have hs6 := H5.search.litStep hu6 hg6 (fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; subst hz
        exact ⟨by simp [SLoc.litG, L], by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd⟩)
    have H6 : HeadAtG L m6 ct.2.2.2 true false chain' := by
      refine (H5.stepS hfresh h6 hu6 (fun z hz => .inl (hs6.1 z hz)) hg6 hs6.2).same ?_
      have := hcts; rw [hctG] at this; exact this
    have hncL6 : Mem.load .Mint32 m6 Lo.bnc (zOfInt 0) = some (.Vint (ir (v.1 : Int))) := by
      rw [hu6.load _ _ _ (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false]
        exact fun e => hbncS (e ▸ SLoc.mem_litG (by simp [SLoc.litG, L])))]
      exact hncL
    simp only [seqPost, Post.after, E0_append]
    wp_step
    refine wp_fpnUserG H6.search (hgl _ (by decide)) ?_
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine wp_fpnLeafG H6.search (gl' _ (by decide)) hfr enc hncL6 hncv hlab1 hlev1 hl1 hln ?_
      (fun h => absurd hv1n h)
    intro _ m7 h7 hF hW
    have H7 := H6.stepS hfresh h7 hF.1 (fun z hz => hz) hF.2 hW
    have hr : hexNodeG true G level nc st =
        (.unwind (level - 1) false, firstterminal level ct.2.2.2) := by
      rw [hN]; dsimp only; rw [ite_eq_left hv1n, Lk.firstterminal_eq]
    have := fPostG (xi := xi) (NodeOk := Lw.NodeOk) (Em := Em) (Lo := Lo) (L := L) (t := E0)
      (args := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level), .Vint (ir nc),
        .Vptr (tcParent chain level) Ptrofs.zero])
      (v := ((level - 1 : Nat) : Int)) H7 hfresh hLO hnd
      (by rw [hr]) (by rw [hr]; rfl)
      (by rw [hEmL]; dsimp only; rw [ite_eq_left hv1n]; exact Emits.nil)
      (fun tg sh h => by rw [hr] at h; cases h; show level - 1 < level; omega)
    rw [show ((level - 1 : Nat) : Int) = (level : Int) - 1 by omega] at this
    revert this
    cases Mem.free_list m7 (blocks_of_env ge (fEnv Lo)) <;> simp only [Post.after] <;> exact fun h => h

end Generic

/-! ### The dense instance -/

section Dense

open NautyVerified.Proofs.Dispatch

/-- `firstpathnode0` on the dense graph `G`: `firstpathnode_bodyG` at `Dispatch.dense`,
`denseLink` and `denseLaws`. -/
theorem firstpathnode_body {k : Nat} (G : Colored n k) (Em : Bool → Nat → Nat → Search n → List Int)
    (hLaw : EmLawFirst Em ⟨rowsOf G⟩) (S : SLoc) (level : Nat)
    (_hRef : Refine.RefineFn xi S.M (.Vptr S.refineBlock Ptrofs.zero))
    (hRecF : ∀ s nc' ch, Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (firstpathnodeSpecG xi G Em S s (level + 1) nc' ch))
    (hRecO : ∀ s nc' ch, Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (othernodeSpecG xi G Em S s (level + 1) nc' ch)) :
    ∀ st nc chain, Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (firstpathnodeSpecG xi G Em S st level nc chain) := by
  intro st nc chain args m hpre
  have h0 := hpre.2.1
  have hn0 := h0.n0
  have hnI : n + 2 < SearchInf.nautyInfinity := by have := h0.nlt; show n + 2 < 2000000002; omega
  exact nodeSpec_ofG (firstpathnode_bodyG Dispatch.dense denseLink ⟨rowsOf G⟩
    (denseLaws G ⟨rowsOf G⟩ hn0 hnI) Em hLaw.toG S () () level
    (fun s nc' ch => nodeSpec_toG h0.gw (hRecF s nc' ch))
    (fun s nc' ch => nodeSpec_toG h0.gw (hRecO s nc' ch)) st nc chain) args m hpre

end Dense

end NautyVerified.Proofs.Search
