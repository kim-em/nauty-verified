import NautyVerified.Proofs.Search.Node.Doref
import NautyVerified.Proofs.Search.Node.ReallocW
import NautyVerified.Proofs.Search.Step
import NautyVerified.Proofs.Dispatch.Doref

/-!
# A node's refinement, with the search state rebuilt

`wp_nodeVisit`: from `SearchAt` at `st` (after `++stats->numnodes`) and the
node's `numcells`, `qinvar` and `refcode` locals, the `doref` call gives
`SearchAt` for `visitSt ctx level numcells st`, the `numcells` local holding
refinement's cell count and `refcode` its code, with the frame and validity
growth. Both `firstpathnode0` and `othernode0` make this call.
`visit_eq`: HexGraphIso's `visit` is `++numnodes` then `visitSt`.

`wp_nodeVisitG` is the call over `SearchAtG D` with `D`'s refinement procedure
(`DispatchC.refine_fn`, through `doref_satisfiesR`), for the state
`visitStG O G level numcells st`; its frame is `D`'s (`SearchAtG.rebuildD`).
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep dyn3Set)
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

/-- `visit` counts the node, then refines. -/
theorem visit_eq {n : Nat} (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (visit ctx level numcells st).2.2 =
      visitSt ctx level numcells { st with numnodes := st.numnodes + 1 } ∧
    (visit ctx level numcells st).1 = (refine ctx level st.lab st.ptn st.active numcells).numcells ∧
    (visit ctx level numcells st).2.1 =
      (refine ctx level st.lab st.ptn st.active numcells).longcode := ⟨rfl, rfl, rfl⟩

/-- New `lab`, `ptn`, `active` and `workperm`, every other array of `S` untouched. -/
theorem Arrays.setRefine {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {W : block → Prop} (h : Arrays m S ctx st) (hu : Unch m m' W)
    (hW : ∀ z ∈ [S.bo, S.bF, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bc, S.bws, Block.fmptr, S.bg],
      ¬ W z)
    {lab ptn : Array Nat} {active : VSet n}
    (hl : ArrayAt m' .Mint32 S.bl S.lb (ints lab) n) (hp : ArrayAt m' .Mint32 S.bp S.pb (ints ptn) n)
    (ha : ∃ aw, ArrayAt m' .Mint64 S.bA 0 (longs aw) S.M ∧ SetRep (fun w => bv64 (aw w)) S.M active)
    (hw : ∃ v, ArrayAt m' .Mint32 S.bWP 0 v n) :
    Arrays m' S ctx { st with lab := lab, ptn := ptn, active := active } := by
  simp only [List.forall_mem_cons] at hW
  obtain ⟨h3, h5, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ := hW
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  exact ⟨hl, hp, h.orbits.unch hu h3, ha, ⟨fw, hf.unch hu h5, hfr⟩, hw, h.firstlab.unch hu h7,
    h.canonlab.unch hu h8, h.firstcode.unch hu h9, h.canoncode.unch hu h10,
    h.firsttc.unch hu h11, h.canong.unch hu h12, h.autos.unch hu h13 h14,
    ⟨h.graph.arr.unch hu h15, h.graph.rep⟩⟩

set_option maxHeartbeats 4000000 in
/-- The node's `doref` call, with `SearchAt` rebuilt for the refined state. -/
theorem wp_nodeVisit {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre : Bool} {level numcells : Nat}
    (h : SearchAt m S ctx st pre false)
    (hvU : Mem.valid_block m S.bUA) (hvT : Mem.valid_block m Block.tcnode0)
    (hRef : Refine.RefineFn xi S.M (.Vptr S.refineBlock Ptrofs.zero))
    {bnc bq bk : block}
    (hloc : [bnc, bq, bk].Pairwise (· ≠ ·))
    (hlocS : ∀ z ∈ [bnc, bq, bk], z ∉ S.blocks ∧ Mem.valid_block m z ∧ ¬ IsWork m z)
    (henc : PTree.get dense.id.«numcells» e = some (bnc, tint))
    (heq : PTree.get dense.id.«qinvar» e = some (bq, tint))
    (hek : PTree.get dense.id.«refcode» e = some (bk, tint))
    (hge : ∀ x ∈ [dense.id.«doref», dense.id.«nauty:g», dense.id.«nauty:workperm»,
      dense.id.«nauty:active», dense.id.«nauty:dispatch», dense.id.«nauty:invarproc»,
      dense.id.«nauty:mininvarlevel», dense.id.«nauty:maxinvarlevel», dense.id.«nauty:invararg»,
      dense.id.«nauty:digraph», dense.id.«nauty:m», dense.id.«nauty:n»], PTree.get x e = none)
    (hnc : ArrayAt m .Mint32 bnc 0 (fun _ => .Vint (ir numcells)) 1)
    (hq : ∃ v, ArrayAt m .Mint32 bq 0 v 1) (hk : ∃ v, ArrayAt m .Mint32 bk 0 v 1)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hl1 : 1 ≤ level) (hln : level ≤ n) (hncn : numcells ≤ n)
    (hinv : SInv (visitSt ctx level numcells st))
    (hQ : ∀ m', SearchAt m' S ctx (visitSt ctx level numcells st) pre false →
      ArrayAt m' .Mint32 bnc 0
        (fun _ => .Vint (ir (refine ctx level st.lab st.ptn st.active numcells).numcells)) 1 →
      ArrayAt m' .Mint32 bk 0
        (fun _ => .Vint (ir (refine ctx level st.lab st.ptn st.active numcells).longcode)) 1 →
      ArrayAt m' .Mint32 bq 0 (fun _ => .Vint (ir 0)) 1 →
      Unch m m' (fun z => S.Chg z ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨ z = bnc ∨
        z = bq ∨ z = bk) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → WorkMono m m' →
      (∀ z ∈ [bnc, bq, bk], Keep m m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f dorefCall Q e le m := by
  have hv := h.valid_all hvU hvT
  have hd := h.distinct
  have hvn := SLoc.vars_ne hd
  have hl1' := hlocS bnc (by simp)
  have hl2' := hlocS bq (by simp)
  have hl3' := hlocS bk (by simp)
  refine wp_nodeDoref h hRef hloc hlocS henc heq hek hge hnc hq hk hlab hptn hlev hl1 hln hncn ?_
  intro L aw cN bN mi ma ia hbg hgofs hgw hbl hlofs hbp hpofs hbn hnofs hbc hcofs hba haofs hbk
    hkofs hlevel hM dW dS dB dN iW iS iB iN t v m' hpost hgrow
  obtain ⟨rfl, m₁, m₂, cN', bN', hu1, hg1, hrp, hu3, hkA3, hqarr, dN', hcN', fN', hvN'⟩ := hpost
  obtain ⟨-, cW', bW', cS', bS', cB', bB', aw', hm2, hcode, hcW, hcB, fW, fS, fB, pWS, pWB, pSB,
    hu2, hk2⟩ := hrp
  -- one frame for the whole call
  let X : block → Prop := fun z => z = S.bl ∨ z = S.bp ∨ z = bnc ∨ z = S.bWP ∨ z = S.bA ∨
    z = bk ∨ z = bq
  have hU : Unch m m' (fun z => dyn3Set m L.capW L.bW L.capS L.bS L.capB L.bB z ∨
      nautilSet m cN bN z ∨ X z) := by
    refine ((hu1.mono fun z hz => .inr (.inl hz)).trans (hu2.mono fun z hz => ?_)).trans
      (hu3.mono fun z hz => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr hz))))))))
    rcases hz with (e | e | e | e | e) | e | h6
    · exact .inr (.inr (.inl (e.trans hbl)))
    · exact .inr (.inr (.inr (.inl (e.trans hbp))))
    · exact .inr (.inr (.inr (.inr (.inl (e.trans hbn)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl (e.trans hbc))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl (e.trans hba)))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (e.trans hbk))))))))
    · left
      unfold dyn3Set at h6 ⊢
      rcases h6 with e | e | e | e | e | e | e | e | e | hnv
      · exact .inl e
      · exact .inr (.inl e)
      · exact .inr (.inr (.inl e))
      · exact .inr (.inr (.inr (.inl e)))
      · exact .inr (.inr (.inr (.inr (.inl e))))
      · exact .inr (.inr (.inr (.inr (.inr (.inl e)))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl e))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl e)))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl e))))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr fun hv => hnv (hg1 z hv)))))))))
  -- old work blocks in use are not blocks of `S`
  have nW : 0 < L.capW → L.bW ∉ S.blocks := fun hc => h.work_not (iW hc)
  have nS : 0 < L.capS → L.bS ∉ S.blocks := fun hc => h.work_not (iS hc)
  have nB : 0 < L.capB → L.bB ∉ S.blocks := fun hc => h.work_not (iB hc)
  have nN : 0 < cN → bN ∉ S.blocks := fun hc => h.work_not (iN hc)
  -- a block of `S` other than the work globals and `X`'s is untouched
  have key : ∀ z ∈ S.blocks, ¬ G8 z → ¬ X z →
      ¬ (dyn3Set m L.capW L.bW L.capS L.bS L.capB L.bB z ∨ nautilSet m cN bN z ∨ X z) := by
    intro z hz hg hx
    rintro (h6 | hN | hx')
    · unfold dyn3Set at h6
      rcases h6 with e | e | e | e | e | e | ⟨hc, e⟩ | ⟨hc, e⟩ | ⟨hc, e⟩ | hnv
      · exact hg (.inl (.inl e))
      · exact hg (.inl (.inr (.inl e)))
      · exact hg (.inl (.inr (.inr (.inl e))))
      · exact hg (.inl (.inr (.inr (.inr (.inl e)))))
      · exact hg (.inl (.inr (.inr (.inr (.inr (.inl e))))))
      · exact hg (.inl (.inr (.inr (.inr (.inr (.inr e))))))
      · exact nW hc (e ▸ hz)
      · exact nS hc (e ▸ hz)
      · exact nB hc (e ▸ hz)
      · exact hnv (hv z hz)
    · rcases hN with e | e | ⟨hc, e⟩ | hnv
      · exact hg (.inr (.inl e))
      · exact hg (.inr (.inr e))
      · exact nN hc (e ▸ hz)
      · exact hnv (hv z hz)
    · exact hx hx'
  have notX : ∀ z ∈ S.blocks, z ≠ S.bl → z ≠ S.bp → z ≠ S.bWP → z ≠ S.bA → ¬ X z := by
    intro z hz h1 h2 h3 h4
    rintro (e | e | e | e | e | e | e)
    · exact h1 e
    · exact h2 e
    · exact hl1'.1 (e ▸ hz)
    · exact h3 e
    · exact h4 e
    · exact hl3'.1 (e ▸ hz)
    · exact hl2'.1 (e ▸ hz)
  have kz : ∀ z ∈ S.blocks, ¬ G8 z → z ≠ S.bl → z ≠ S.bp → z ≠ S.bWP → z ≠ S.bA →
      ¬ (dyn3Set m L.capW L.bW L.capS L.bS L.capB L.bB z ∨ nautilSet m cN bN z ∨ X z) :=
    fun z hz hg h1 h2 h3 h4 => key z hz hg (notX z hz h1 h2 h3 h4)
  -- `Keep` for the eight `DYNALLSTAT` targets
  have nq : ∀ z ∈ S.blocks, z ≠ bq := fun z hz e => hl2'.1 (e ▸ hz)
  have k1 : ∀ z ∈ S.blocks, ¬ G8 z → Keep m m₁ z := fun z hz hg => Keep.unch hu1 (by
    rintro (e | e | ⟨hc, e⟩ | hnv)
    · exact hg (.inr (.inl e))
    · exact hg (.inr (.inr e))
    · exact nN hc (e ▸ hz)
    · exact hnv (hv z hz))
  have hKA : Keep m m' S.bA :=
    ((k1 _ (by simp [SLoc.blocks]) (by simp only [G8, G6, not_or]; refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> sep_ne hd)).trans
      (hba ▸ hk2 L.ba (by simp))).trans (hkA3 _)
  have hKW : Keep m m' S.bWP :=
    ((k1 _ (by simp [SLoc.blocks]) (by simp only [G8, G6, not_or]; refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> sep_ne hd)).trans
      (hbc ▸ hk2 L.bc (by simp))).trans (hkA3 _)
  have hKo : ∀ z ∈ [S.bF, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws], Keep m m' z := by
    intro z hz
    refine Keep.unch hU (kz z (by revert z hz; simp [SLoc.blocks]) ?_ ?_ ?_ ?_ ?_) <;>
      revert z hz <;> sep_all hd
  -- refinement's arrays, under `S`'s names, after the `qinvar` store
  have hl : ArrayAt m' .Mint32 S.bl S.lb
      (ints (refine ctx level st.lab st.ptn st.active numcells).lab) n := by
    have h0 : ArrayAt m₂ .Mint32 L.bl (intOfZ (Ptrofs.unsigned L.lofs)) _ n := hm2.lab
    rw [hbl, hlofs, hlevel] at h0
    exact h0.unch hu3 (nq _ (by simp [SLoc.blocks]))
  have hp : ArrayAt m' .Mint32 S.bp S.pb
      (ints (refine ctx level st.lab st.ptn st.active numcells).ptn) n := by
    have h0 : ArrayAt m₂ .Mint32 L.bp (intOfZ (Ptrofs.unsigned L.pofs)) _ n := hm2.ptn
    rw [hbp, hpofs, hlevel] at h0
    exact h0.unch hu3 (nq _ (by simp [SLoc.blocks]))
  have ha : ∃ aw, ArrayAt m' .Mint64 S.bA 0 (longs aw) S.M ∧
      SetRep (fun w => bv64 (aw w)) S.M (refine ctx level st.lab st.ptn st.active numcells).active := by
    have h0 : ArrayAt m₂ .Mint64 L.ba (intOfZ (Ptrofs.unsigned L.aofs)) (longs aw') L.M := hm2.act
    have h1 : SetRep (fun w => bv64 (aw' w)) L.M
        (refine ctx L.level st.lab st.ptn st.active numcells).active := hm2.actRep
    rw [hba, haofs, hM] at h0
    rw [hM, hlevel] at h1
    exact ⟨aw', h0.unch hu3 (nq _ (by simp [SLoc.blocks])), h1⟩
  have hw : ∃ v, ArrayAt m' .Mint32 S.bWP 0 v n := by
    obtain ⟨v0, h0⟩ := hm2.cnt
    have h0 : ArrayAt m₂ .Mint32 L.bc (intOfZ (Ptrofs.unsigned L.cofs)) v0 n := h0
    rw [hbc, hcofs] at h0
    exact ⟨v0, h0.unch hu3 (nq _ (by simp [SLoc.blocks]))⟩
  have hnc' : ArrayAt m' .Mint32 bnc 0
      (fun _ => .Vint (ir (refine ctx level st.lab st.ptn st.active numcells).numcells)) 1 := by
    have h0 : ArrayAt m₂ .Mint32 L.bn (intOfZ (Ptrofs.unsigned L.nofs)) _ 1 := hm2.nc
    rw [hbn, hnofs, hlevel] at h0
    exact h0.unch hu3 ((List.pairwise_cons.1 hloc).1 bq (by simp))
  have hk' : ArrayAt m' .Mint32 bk 0
      (fun _ => .Vint (ir (refine ctx level st.lab st.ptn st.active numcells).longcode)) 1 := by
    have h0 : ArrayAt m₂ .Mint32 L.bk (intOfZ (Ptrofs.unsigned L.kofs)) _ 1 := hcode
    rw [hbk, hkofs, hlevel] at h0
    exact h0.unch hu3 (by
      have := (List.pairwise_cons.1 (List.pairwise_cons.1 hloc).2).1 bk (by simp)
      exact Ne.symm this)
  -- the new work pairs, in `m'`
  have hglob : ∀ z ∈ [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
      Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz], z ≠ bq :=
    fun z hz => nq z (by revert z hz; simp [SLoc.blocks])
  simp only [List.forall_mem_cons] at hglob
  obtain ⟨q1, q2, q3, q4, q5, q6, -⟩ := hglob
  have dW' : DynAt m' Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW' bW' :=
    hm2.dW.keep hu3 q1 q2 fun _ => hkA3 _
  have dS' : DynAt m' Block.naugraphWorkset Block.naugraphWorksetSz 8 cS' bS' :=
    hm2.dS.keep hu3 q3 q4 fun _ => hkA3 _
  have dB' : DynAt m' Block.naugraphBucket Block.naugraphBucketSz 4 cB' bB' :=
    hm2.dB.keep hu3 q5 q6 fun _ => hkA3 _
  have back : ∀ {b : block} {c c' : Nat} {b₀ : block},
      ((c' = c ∧ b = b₀) ∨ ¬ Mem.valid_block m₁ b) → (c' = c ∧ b = b₀) ∨ ¬ Mem.valid_block m b :=
    fun hf => hf.imp_right fun hnv hv => hnv (hg1 _ hv)
  -- the old work blocks in use, as `h.work` records them
  obtain ⟨cW0, bW0, cS0, bS0, cB0, bB0, cN0, bN0, dW0, dS0, dB0, dN0, -, -, -, -, -, -, -, pNW0,
    pNS0, pNB0⟩ := h.work.arr
  -- the continuation's old work pairs are `h.work`'s
  have sameW := Alloc.DynAt.same_cap dW dW0
  have sameS := Alloc.DynAt.same_cap dS dS0
  have sameB := Alloc.DynAt.same_cap dB dB0
  have sameN := Alloc.DynAt.same_cap dN dN0
  have blkW : 0 < L.capW → bW0 = L.bW := fun hc => Alloc.DynAt.same_block dW dW0 hc
  have blkS : 0 < L.capS → bS0 = L.bS := fun hc => Alloc.DynAt.same_block dS dS0 hc
  have blkB : 0 < L.capB → bB0 = L.bB := fun hc => Alloc.DynAt.same_block dB dB0 hc
  have blkN : 0 < cN → bN0 = bN := fun hc => Alloc.DynAt.same_block dN dN0 hc
  -- nautil.c's new block against naugraph.c's new blocks
  have pN : ∀ {cX cX' : Nat} {bX bX' : block},
      ((cX' = cX ∧ bX' = bX) ∨ ¬ Mem.valid_block m₁ bX') →
      (0 < cN → 0 < cX → bN ≠ bX) → (0 < cX → Mem.valid_block m bX) →
      0 < cN' → 0 < cX' → bN' ≠ bX' := by
    intro cX cX' bX bX' hf hold hvX hcN hcX e
    rcases fN' with ⟨rfl, rfl⟩ | hnvN <;> rcases hf with ⟨rfl, rfl⟩ | hnvX
    · exact hold hcN hcX e
    · exact hnvX (e ▸ hg1 _ (Alloc.Malloced.valid (dN.mal hcN)))
    · exact hnvN (e ▸ hvX hcX)
    · exact hnvX (e ▸ hvN' hcN)
  have oW : 0 < cN → 0 < L.capW → bN ≠ L.bW := fun h1 h2 => by
    rw [← blkN h1, ← blkW h2]; exact pNW0 (sameN ▸ h1) (sameW ▸ h2)
  have oS : 0 < cN → 0 < L.capS → bN ≠ L.bS := fun h1 h2 => by
    rw [← blkN h1, ← blkS h2]; exact pNS0 (sameN ▸ h1) (sameS ▸ h2)
  have oB : 0 < cN → 0 < L.capB → bN ≠ L.bB := fun h1 h2 => by
    rw [← blkN h1, ← blkB h2]; exact pNB0 (sameN ▸ h1) (sameB ▸ h2)
  have hX : ∀ z ∈ S.blocks, X z → z ∈ S.wr := by
    intro z hz hx
    rcases hx with e | e | e | e | e | e | e
    · subst e; simp [SLoc.wr, SLoc.wrV]
    · subst e; simp [SLoc.wr, SLoc.wrV]
    · exact absurd (e ▸ hz) hl1'.1
    · subst e; simp [SLoc.wr, SLoc.wrV]
    · subst e; simp [SLoc.wr, SLoc.wrV]
    · exact absurd (e ▸ hz) hl3'.1
    · exact absurd (e ▸ hz) hl2'.1
  have hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws], Keep m m' z := by
    simp only [List.forall_mem_cons] at hKo ⊢
    exact ⟨hKA, hKo.1, hKW, hKo.2.1, hKo.2.2.1, hKo.2.2.2.1, hKo.2.2.2.2.1, hKo.2.2.2.2.2.1,
      hKo.2.2.2.2.2.2.1, fun _ h => absurd h (List.not_mem_nil)⟩
  have hsc0 : Scalars m' st false := by
    refine h.scalars.unch hU fun z hz => kz z (by revert z hz; simp [SLoc.blocks]) ?_ ?_ ?_ ?_ ?_ <;>
      revert z hz <;> sep_all hd
  have hsc : Scalars m' (visitSt ctx level numcells st) false := { hsc0 with }
  have hst0 : Stats m' S st pre :=
    h.stats.unch hU (kz _ (by simp [SLoc.blocks])
      (by simp only [G8, G6, not_or]; refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> sep_ne hd)
      (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
  have hst : Stats m' S (visitSt ctx level numcells st) pre := { hst0 with }
  have har : Arrays m' S ctx (visitSt ctx level numcells st) :=
    h.arrays.setRefine hU (fun z hz => kz z (by revert z hz; simp [SLoc.blocks])
      (by revert z hz; sep_all hd) (by revert z hz; sep_all hd) (by revert z hz; sep_all hd)
      (by revert z hz; sep_all hd) (by revert z hz; sep_all hd)) hl hp ha hw
  have hSA : SearchAt m' S ctx (visitSt ctx level numcells st) pre false :=
    h.reallocW hvU hvT nW nS nB nN hU hX hK dW' dS' dB' dN' (back fW) (back fS) (back fB) fN'
      (fun _ _ => pWS) (fun _ _ => pWB) (fun _ _ => pSB)
      (pN fW oW fun hc => Alloc.Malloced.valid (dW.mal hc))
      (pN fS oS fun hc => Alloc.Malloced.valid (dS.mal hc))
      (pN fB oB fun hc => Alloc.Malloced.valid (dB.mal hc)) hsc hst har hinv
  have hqarr' : ArrayAt m' .Mint32 bq 0 (fun _ => .Vint (ir 0)) 1 := hqarr
  have hKl : ∀ z ∈ [bnc, bq, bk], Keep m m' z := by
    have k1' : ∀ z, z ∉ S.blocks → Mem.valid_block m z → ¬ IsWork m z → Keep m m₁ z :=
      fun z hzS hzv hzw => Keep.unch hu1 (by
        rintro (e | e | ⟨hc, e⟩ | hnv)
        · exact hzS (e ▸ by simp [SLoc.blocks])
        · exact hzS (e ▸ by simp [SLoc.blocks])
        · exact hzw (e ▸ iN hc)
        · exact hnv hzv)
    simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true] at hloc
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact ((k1' _ hl1'.1 hl1'.2.1 hl1'.2.2).trans (hbn ▸ hk2 L.bn (by simp))).trans (hkA3 _)
    · refine ((k1' _ hl2'.1 hl2'.2.1 hl2'.2.2).trans (Keep.unch hu2 ?_)).trans (hkA3 _)
      rintro ((e | e | e | e | e) | e | h6)
      · exact hl2'.1 (e.trans hbl ▸ by simp [SLoc.blocks])
      · exact hl2'.1 (e.trans hbp ▸ by simp [SLoc.blocks])
      · exact hloc.1.1 (e.trans hbn).symm
      · exact hl2'.1 (e.trans hbc ▸ by simp [SLoc.blocks])
      · exact hl2'.1 (e.trans hba ▸ by simp [SLoc.blocks])
      · exact hloc.2 (e.trans hbk)
      · unfold dyn3Set at h6
        rcases h6 with e | e | e | e | e | e | ⟨hc, e⟩ | ⟨hc, e⟩ | ⟨hc, e⟩ | hnv
        · exact hl2'.1 (e ▸ by simp [SLoc.blocks])
        · exact hl2'.1 (e ▸ by simp [SLoc.blocks])
        · exact hl2'.1 (e ▸ by simp [SLoc.blocks])
        · exact hl2'.1 (e ▸ by simp [SLoc.blocks])
        · exact hl2'.1 (e ▸ by simp [SLoc.blocks])
        · exact hl2'.1 (e ▸ by simp [SLoc.blocks])
        · exact hl2'.2.2 (e ▸ iW hc)
        · exact hl2'.2.2 (e ▸ iS hc)
        · exact hl2'.2.2 (e ▸ iB hc)
        · exact hnv (hg1 _ hl2'.2.1)
    · exact ((k1' _ hl3'.1 hl3'.2.1 hl3'.2.2).trans (hbk ▸ hk2 L.bk (by simp))).trans (hkA3 _)
  refine hQ m' hSA hnc' hk' hqarr' (hU.mono fun z hz => ?_) hgrow
    (WorkMono.of_four dW dS dB dN dW' dS' dB' dN' (back fW) (back fS) (back fB) fN') hKl
  rcases hz with h6 | hN | hx
  · unfold dyn3Set at h6
    rcases h6 with e | e | e | e | e | e | ⟨hc, e⟩ | ⟨hc, e⟩ | ⟨hc, e⟩ | hnv
    all_goals first
      | exact .inr (.inr (.inl (e ▸ iW hc)))
      | exact .inr (.inr (.inl (e ▸ iS hc)))
      | exact .inr (.inr (.inl (e ▸ iB hc)))
      | exact .inr (.inl hnv)
      | exact .inl (by subst e; exact ⟨by simp [SLoc.blocks], by sep_ne h.distinct, by sep_ne h.distinct⟩)
  · rcases hN with e | e | ⟨hc, e⟩ | hnv
    · exact .inl (by subst e; exact ⟨by simp [SLoc.blocks], by sep_ne h.distinct, by sep_ne h.distinct⟩)
    · exact .inl (by subst e; exact ⟨by simp [SLoc.blocks], by sep_ne h.distinct, by sep_ne h.distinct⟩)
    · exact .inr (.inr (.inl (e ▸ iN hc)))
    · exact .inr (.inl hnv)
  · rcases hx with e | e | e | e | e | e | e
    · exact .inl (by subst e; exact ⟨by simp [SLoc.blocks], by sep_ne h.distinct, by sep_ne h.distinct⟩)
    · exact .inl (by subst e; exact ⟨by simp [SLoc.blocks], by sep_ne h.distinct, by sep_ne h.distinct⟩)
    · exact .inr (.inr (.inr (.inl e)))
    · exact .inl (by subst e; exact ⟨by simp [SLoc.blocks], by sep_ne h.distinct, by sep_ne h.distinct⟩)
    · exact .inl (by subst e; exact ⟨by simp [SLoc.blocks], by sep_ne h.distinct, by sep_ne h.distinct⟩)
    · exact .inr (.inr (.inr (.inr (.inr e))))
    · exact .inr (.inr (.inr (.inr (.inl e))))

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC ActiveOk)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}

/-- `visitSt` for `O`: the refined `lab`, `ptn` and `active`. -/
abbrev visitStG {n : Nat} (O : Ops) (G : O.Gr n) (level numcells : Nat)
    (st : SearchState n (O.Canon n)) : SearchState n (O.Canon n) :=
  { st with
    lab := (O.refine G level st.lab st.ptn st.active numcells).lab
    ptn := (O.refine G level st.lab st.ptn st.active numcells).ptn
    active := (O.refine G level st.lab st.ptn st.active numcells).active }

set_option maxHeartbeats 8000000 in
/-- The node's `doref` call with `D`'s refinement procedure, with `SearchAtG`
rebuilt for the refined state. -/
theorem wp_nodeVisitG {D : DispatchC ge O} {n : Nat} {f : function} {Q : Post} {e : env}
    {le : temp_env} {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {pre : Bool} {level numcells : Nat}
    (h : SearchAtG D.toDispatchRep m S gl cl G st pre false)
    (hvU : Mem.valid_block m S.bUA) (hvT : Mem.valid_block m E.tcnode0)
    {bnc bq bk : block}
    (hloc : [bnc, bq, bk].Pairwise (· ≠ ·))
    (hlocS : ∀ z ∈ [bnc, bq, bk], z ∉ S.blocksG D.toDispatchRep gl cl ∧ Mem.valid_block m z ∧
      ¬ IsWorkG D.toDispatchRep m z)
    (henc : PTree.get dense.id.«numcells» e = some (bnc, tint))
    (heq : PTree.get dense.id.«qinvar» e = some (bq, tint))
    (hek : PTree.get dense.id.«refcode» e = some (bk, tint))
    (hge : ∀ x ∈ [dense.id.«doref», dense.id.«nauty:g», dense.id.«nauty:workperm»,
      dense.id.«nauty:active», dense.id.«nauty:dispatch», dense.id.«nauty:invarproc»,
      dense.id.«nauty:mininvarlevel», dense.id.«nauty:maxinvarlevel», dense.id.«nauty:invararg»,
      dense.id.«nauty:digraph», dense.id.«nauty:m», dense.id.«nauty:n»], PTree.get x e = none)
    (hnc : ArrayAt m .Mint32 bnc 0 (fun _ => .Vint (ir numcells)) 1)
    (hq : ∃ v, ArrayAt m .Mint32 bq 0 v 1) (hk : ∃ v, ArrayAt m .Mint32 bk 0 v 1)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hl1 : 1 ≤ level) (hln : level ≤ n) (hncn : numcells ≤ n)
    (hact : ActiveOk st.ptn level numcells st.active)
    (hinv : SInvG O G (visitStG O G level numcells st))
    (hQ : ∀ m', SearchAtG D.toDispatchRep m' S gl cl G (visitStG O G level numcells st) pre false →
      ArrayAt m' .Mint32 bnc 0
        (fun _ => .Vint (ir (O.refine G level st.lab st.ptn st.active numcells).numcells)) 1 →
      ArrayAt m' .Mint32 bk 0
        (fun _ => .Vint (ir (O.refine G level st.lab st.ptn st.active numcells).longcode)) 1 →
      ArrayAt m' .Mint32 bq 0 (fun _ => .Vint (ir 0)) 1 →
      Unch m m' (fun z => S.ChgG D.toDispatchRep gl cl z ∨ ¬ Mem.valid_block m z ∨
        IsWorkG D.toDispatchRep m z ∨ z = bnc ∨ z = bq ∨ z = bk) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → WorkMonoG D.toDispatchRep m m' →
      (∀ z ∈ [bnc, bq, bk], Keep m m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f dorefCall Q e le m := by
  have hv := h.valid_all hvU hvT
  have hd := h.lit
  have hI := h.inv
  have hnl := h.nlt
  have hn0 := h.n0
  simp only [List.forall_mem_cons] at hlocS
  obtain ⟨⟨n1S, n1V, n1W⟩, ⟨n2S, n2V, n2W⟩, ⟨n3S, n3V, n3W⟩, -⟩ := hlocS
  simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true] at hloc
  obtain ⟨⟨hnq, hnk⟩, hqk⟩ := hloc
  obtain ⟨cN, bN, dN, nN, uN⟩ := h.work.nautil
  -- membership in `S.blocksG`
  have mL : ∀ z ∈ S.litG, z ∈ S.blocksG D.toDispatchRep gl cl := fun z hz =>
    (S.litG_sub D.toDispatchRep gl cl).subset hz
  have mG : ∀ z ∈ D.graphBlocks gl S.bg, z ∈ S.blocksG D.toDispatchRep gl cl := fun z hz =>
    SLoc.mem_blocksG_of D.toDispatchRep (.inl hz)
  have ne_loc : ∀ {z x : block}, z ∈ S.blocksG D.toDispatchRep gl cl →
      x ∉ S.blocksG D.toDispatchRep gl cl → z ≠ x := fun hz hx e => hx (e ▸ hz)
  -- the arguments of `refine`
  let A : List block := D.graphBlocks gl S.bg ++ [S.bl, S.bp, bnc, S.bWP, S.bA, bk]
  have hA : ∀ z ∈ A, (z ∈ D.graphBlocks gl S.bg ∨ z ∈ [S.bl, S.bp, S.bWP, S.bA]) ∨
      z = bnc ∨ z = bk := by
    intro z hz
    simp only [A, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with hz | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inl (.inl hz)
    all_goals simp
  have hL4 : ∀ z ∈ [S.bl, S.bp, S.bWP, S.bA], z ∈ S.litG := by simp [SLoc.litG]
  have hAS : ∀ z, z ∈ D.graphBlocks gl S.bg ∨ z ∈ [S.bl, S.bp, S.bWP, S.bA] →
      z ∈ S.blocksG D.toDispatchRep gl cl := by
    rintro z (hz | hz)
    · exact mG z hz
    · exact mL z (hL4 z hz)
  have gsub : (D.graphBlocks gl S.bg).Sublist (S.blocksG D.toDispatchRep gl cl) := by
    unfold SLoc.blocksG
    exact ((((List.sublist_append_left _ _).trans (List.sublist_append_left _ _)).trans
      (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans
      (List.sublist_append_left _ _)
  have hsep : D.Sep m A := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine List.pairwise_append.2 ⟨h.distinct.sublist gsub, ?_, ?_⟩
      · simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
          forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies,
          implies_true]
        refine ⟨⟨by sep_ne hd, ne_loc (mL _ (by simp [SLoc.litG])) n1S, by sep_ne hd, by sep_ne hd,
          ne_loc (mL _ (by simp [SLoc.litG])) n3S⟩,
          ⟨ne_loc (mL _ (by simp [SLoc.litG])) n1S, by sep_ne hd, by sep_ne hd,
          ne_loc (mL _ (by simp [SLoc.litG])) n3S⟩,
          ⟨Ne.symm (ne_loc (mL _ (by simp [SLoc.litG])) n1S),
            Ne.symm (ne_loc (mL _ (by simp [SLoc.litG])) n1S), hnk⟩,
          ⟨by sep_ne hd, ne_loc (mL _ (by simp [SLoc.litG])) n3S⟩,
          ne_loc (mL _ (by simp [SLoc.litG])) n3S⟩
      · intro a ha b hb
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h.graph_ne ha (.inl (by simp))
        · exact h.graph_ne ha (.inl (by simp))
        · exact ne_loc (mG a ha) n1S
        · exact h.graph_ne ha (.inr (.inr (.inl (by simp))))
        · exact h.graph_ne ha (.inr (.inr (.inl (by simp))))
        · exact ne_loc (mG a ha) n3S
    · intro z hz
      rcases hA z hz with hz | rfl | rfl
      · exact hv z (hAS z hz)
      · exact n1V
      · exact n3V
    · intro z hz hw
      rcases hA z hz with hz | rfl | rfl
      · exact h.work.notin z hw (hAS z hz)
      · exact n1W (.inl hw)
      · exact n3W (.inl hw)
    · intro z hz hg
      have hb := SLoc.mem_blocksG_of D.toDispatchRep (S := S) (gl := gl) (cl := cl)
        (.inr (.inr (.inr (.inr (.inr hg)))))
      rcases hA z hz with hz | rfl | rfl
      · rcases hz with hz | hz
        · exact h.globs_ne hg (.inl hz) rfl
        · exact h.lit_globs z (hL4 z hz) hg
      · exact n1S hb
      · exact n3S hb
    · intro z hz
      have hE : ∀ y ∈ [E.nautyBit, E.nautilBit, E.leftbit], y ∈ S.blocksG D.toDispatchRep gl cl :=
        fun y hy => mL y (by revert y; simp [SLoc.litG])
      rcases hA z hz with (hz | hz) | rfl | rfl
      · exact ⟨h.graph_ne hz (.inr (.inr (.inr (.inl (by simp))))),
          h.graph_ne hz (.inr (.inr (.inr (.inl (by simp))))),
          h.graph_ne hz (.inr (.inr (.inr (.inl (by simp)))))⟩
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> exact ⟨by sep_ne hd, by sep_ne hd, by sep_ne hd⟩
      · exact ⟨Ne.symm (ne_loc (hE _ (by simp)) n1S), Ne.symm (ne_loc (hE _ (by simp)) n1S),
          Ne.symm (ne_loc (hE _ (by simp)) n1S)⟩
      · exact ⟨Ne.symm (ne_loc (hE _ (by simp)) n3S), Ne.symm (ne_loc (hE _ (by simp)) n3S),
          Ne.symm (ne_loc (hE _ (by simp)) n3S)⟩
  have hE3 : ∀ y ∈ [E.nautyBit, E.nautilBit, E.leftbit, E.nautilWorkperm, E.nautilWorkpermSz],
      y ∈ S.blocksG D.toDispatchRep gl cl :=
    fun y hy => mL y (by revert y; simp [SLoc.litG])
  have hN : ∀ z ∈ A, z ≠ E.nautilWorkperm ∧ z ≠ E.nautilWorkpermSz ∧ (0 < cN → z ≠ bN) := by
    intro z hz
    have hbN : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, 0 < cN → z ≠ bN :=
      fun z hz hc => ne_loc hz (nN hc)
    rcases hA z hz with (hz | hz) | rfl | rfl
    · exact ⟨h.graph_ne hz (.inr (.inr (.inr (.inl (by simp))))),
        h.graph_ne hz (.inr (.inr (.inr (.inl (by simp))))), hbN z (mG z hz)⟩
    · refine ⟨?_, ?_, hbN z (hAS z (.inr hz))⟩ <;>
        (simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
         rcases hz with rfl | rfl | rfl | rfl <;> sep_ne hd)
    · exact ⟨Ne.symm (ne_loc (hE3 _ (by simp)) n1S), Ne.symm (ne_loc (hE3 _ (by simp)) n1S),
        fun hc e => n1W (e ▸ .inr ⟨cN, hc, dN⟩)⟩
    · exact ⟨Ne.symm (ne_loc (hE3 _ (by simp)) n3S), Ne.symm (ne_loc (hE3 _ (by simp)) n3S),
        fun hc e => n3W (e ▸ .inr ⟨cN, hc, dN⟩)⟩
  have hbN : 0 < cN → bN ∉ D.globs ∧ ¬ D.IsWork m bN ∧ bN ≠ E.nautyBit ∧ bN ≠ E.nautilBit ∧
      bN ≠ E.leftbit := fun hc =>
    ⟨fun hg => nN hc (SLoc.mem_blocksG_of D.toDispatchRep (.inr (.inr (.inr (.inr (.inr hg)))))),
      uN hc, Ne.symm (ne_loc (hE3 _ (by simp)) (nN hc)), Ne.symm (ne_loc (hE3 _ (by simp)) (nN hc)),
      Ne.symm (ne_loc (hE3 _ (by simp)) (nN hc))⟩
  have bqG : bq ∉ D.globs := fun hg =>
    n2S (SLoc.mem_blocksG_of D.toDispatchRep (.inr (.inr (.inr (.inr (.inr hg))))))
  have hqq : bq ∉ A ∧ bq ∉ D.globs ∧ ¬ D.IsWork m bq ∧ Mem.valid_block m bq := by
    refine ⟨fun hz => ?_, bqG, fun hw => n2W (.inl hw), n2V⟩
    rcases hA _ hz with hz | e | e
    · exact n2S (hAS _ hz)
    · exact hnq e.symm
    · exact hqk e
  obtain ⟨aw, haw, hawr⟩ := h.arrays.active
  obtain ⟨wv, hwv⟩ := h.arrays.workperm
  obtain ⟨kv, hkv⟩ := hk
  obtain ⟨qv, hqv⟩ := hq
  let L : Refine.Loc :=
    { bg := S.bg, gofs := S.gofs, gw := S.gw, bl := S.bl, lofs := S.lofs, bp := S.bp,
      pofs := S.pofs, bn := bnc, nofs := Ptrofs.zero, bc := S.bWP, cofs := Ptrofs.zero,
      ba := S.bA, aofs := Ptrofs.zero, bk := bk, kofs := Ptrofs.zero, bW := S.bg, capW := 0,
      bS := S.bg, capS := 0, bB := S.bg, capB := 0, level := level, M := S.M }
  have hRS : (D.refineSpec G gl S.bg S.gofs S.bl S.lofs st.lab S.bp S.pofs st.ptn level bnc
      Ptrofs.zero numcells S.bWP Ptrofs.zero S.bA Ptrofs.zero st.active bk Ptrofs.zero S.M).pre
      (Doref.refArgs L n) m := by
    refine ⟨rfl, ⟨h.work.disp, h.tables.disp, h.tables.env, hn0, hnl, h.M1, h.Mlt, h.nM⟩,
      h.arrays.graph, h.graphOk, h.arrays.lab, h.arrays.ptn, hnc, ⟨wv, hwv⟩, ⟨aw, haw, hawr⟩,
      ⟨kv, hkv⟩, ?_, ?_, hncn, by omega, hsep, hact⟩
    · refine ⟨hI.labSize, fun i hiz => hI.labSmall i (by
        have := hI.labSize; simp only [NautyVerified.Proofs.Dispatch.DispatchRep.initSt] at hiz; omega), hI.ptnSize, ?_⟩
      show st.ptn[st.ptn.size - 1]! ≤ level
      rw [hI.ptnSize]; have := hI.ptnLast; omega
    · intro i hin
      rcases hI.ptnVals i hin with hv' | hv'
      · omega
      · rw [hv']; decide
  obtain ⟨hcarry, hframe⟩ := D.doref_refineT G gl L st.lab st.ptn numcells st.active hRS hN hbN
    (D.globs_valid h.work.disp) (fun z hz => hv z (hE3 z (by revert z; simp))) hqq
  obtain ⟨fd, hfd, hty, hsat⟩ := D.refine_fn xi S.M
  obtain ⟨mi, hmi⟩ := h.fixed.mininv
  obtain ⟨ma, hma⟩ := h.fixed.maxinv
  obtain ⟨ia, hia⟩ := h.fixed.invarg
  have hgn := hge
  have hargs : Exec.evalExprlist ge e le m
      [.Evar dense.id.«nauty:g» (tptr tulong), .Etempvar dense.id.«lab» (tptr tint),
       .Etempvar dense.id.«ptn» (tptr tint), .Etempvar dense.id.«level» tint,
       .Eaddrof (.Evar dense.id.«numcells» tint) (tptr tint),
       .Eaddrof (.Evar dense.id.«qinvar» tint) (tptr tint),
       .Evar dense.id.«nauty:workperm» (tptr tint), .Evar dense.id.«nauty:active» (tptr tulong),
       .Eaddrof (.Evar dense.id.«refcode» tint) (tptr tint),
       .Efield (.Evar dense.id.«nauty:dispatch» (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr))
         dense.id.«refine» (tptr Refine.refprocType),
       .Evar dense.id.«nauty:invarproc»
         (tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tptr tint, tint, tint,
           tint, tint] .Tvoid)),
       .Evar dense.id.«nauty:mininvarlevel» tint, .Evar dense.id.«nauty:maxinvarlevel» tint,
       .Evar dense.id.«nauty:invararg» tint, .Evar dense.id.«nauty:digraph» tint,
       .Evar dense.id.«nauty:m» tint, .Evar dense.id.«nauty:n» tint]
      [tptr tulong, tptr tint, tptr tint, tint, tptr tint, tptr tint, tptr tint,
        tptr tulong, tptr tint, tptr Refine.refprocType,
        tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tptr tint, tint, tint,
          tint, tint] .Tvoid), tint, tint, tint, tint, tint, tint] =
      some [.Vptr S.bg S.gofs, .Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level),
        .Vptr bnc Ptrofs.zero, .Vptr bq Ptrofs.zero, .Vptr S.bWP Ptrofs.zero,
        .Vptr S.bA Ptrofs.zero, .Vptr bk Ptrofs.zero, .Vptr (D.refineAt S.M) Ptrofs.zero,
        Vnullptr, .Vint mi, .Vint ma, .Vint ia, .Vint (ir 0), .Vint (ir S.M), .Vint (ir n)] := by
    have g1 := hgn dense.id.«nauty:g» (by simp)
    have g2 := hgn dense.id.«nauty:workperm» (by simp)
    have g3 := hgn dense.id.«nauty:active» (by simp)
    have g4 := hgn dense.id.«nauty:dispatch» (by simp)
    have g5 := hgn dense.id.«nauty:invarproc» (by simp)
    have g6 := hgn dense.id.«nauty:mininvarlevel» (by simp)
    have g7 := hgn dense.id.«nauty:maxinvarlevel» (by simp)
    have g8 := hgn dense.id.«nauty:invararg» (by simp)
    have g9 := hgn dense.id.«nauty:digraph» (by simp)
    have g10 := hgn dense.id.«nauty:m» (by simp)
    have g11 := hgn dense.id.«nauty:n» (by simp)
    simp only [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, Exec.evalLvalue,
      g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, henc, heq, hek, hlab, hptn, hlev, E.find_g,
      E.find_nautyWorkperm, E.find_nautyActive,
      E.find_dispatch, E.find_invarproc, E.find_mininvarlevel, E.find_maxinvarlevel,
      E.find_invararg, E.find_digraph, E.find_m, E.find_n]
    have hW1 := h.dyns.workperm.ptr (by have := h.dyns.capWP; have := h.n0; omega)
    have hA1 := h.dyns.active.ptr (by have := h.dyns.capA; have := h.M1; omega)
    simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h.fixed.g.load, hW1, hA1,
      h.fixed.invarproc.load, hmi.load, hma.load, hia.load, h.fixed.digraph.load, h.fixed.mm.load,
      h.fixed.nn.load, ite_true, typeof, cop]
    have hd24 : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 24))) = zOfInt 24 := by
      decide
    simp only [field_dRefine, hd24, h.fixed.dRefine.load, cop]
    have hnull : Cfrontend.Cop.sem_cast Vnullptr
        (tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tptr tint, tint, tint, tint,
          tint] .Tvoid))
        (tptr (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tptr tint, tint, tint, tint,
          tint] .Tvoid)) m = some Vnullptr := rfl
    simp only [hnull]
  refine wp_call (vf := .Vptr E.dorefFn Ptrofs.zero) _ _
    (Satisfies.grow (Doref.doref_satisfiesR (xi := xi) (n := n)
      (D.refineSpec G gl S.bg S.gofs S.bl S.lofs st.lab S.bp S.pofs st.ptn level bnc Ptrofs.zero
        numcells S.bWP Ptrofs.zero S.bA Ptrofs.zero st.active bk Ptrofs.zero S.M) L aw bq Ptrofs.zero
      (D.refineAt S.M) mi ma ia (ir 0) cN bN))
    rfl ?_ hargs ?_ rfl ?_ ?_
  · simp [Exec.evalExpr, Exec.lvalOfVar, hgn dense.id.«doref» (by simp), E.find_dorefFn,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  · simp [Genv.find_funct, E.funct_dorefFn]
  · refine ⟨rfl, ⟨fd, hfd, hty, hsat G gl S.bg S.gofs S.bl S.lofs st.lab S.bp S.pofs st.ptn level
      bnc Ptrofs.zero numcells S.bWP Ptrofs.zero S.bA Ptrofs.zero st.active bk Ptrofs.zero⟩,
      hcarry, hframe, haw, h.tables.env.left, ?_, h.M1, h.Mlt, hn0, hnl, dN, ⟨qv, hqv⟩, n2V,
      Ne.symm (ne_loc (hE3 _ (by simp)) n2S), Ne.symm (ne_loc (hE3 _ (by simp)) n2S),
      fun hc e => n2W (e ▸ .inr ⟨cN, hc, dN⟩)⟩
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    have hbN' : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, 0 < cN → z ≠ bN :=
      fun z hz hc => ne_loc hz (nN hc)
    rcases hz with rfl | rfl
    · show Mem.valid_block m S.bA ∧ S.bA ≠ E.nautilWorkperm ∧ S.bA ≠ E.nautilWorkpermSz ∧
        (0 < cN → S.bA ≠ bN)
      exact ⟨hv _ (mL _ (by simp [SLoc.litG])), by sep_ne hd, by sep_ne hd,
        hbN' _ (mL _ (by simp [SLoc.litG]))⟩
    · exact ⟨hv _ (mL _ (by simp [SLoc.litG])), by sep_ne hd, by sep_ne hd,
        hbN' _ (mL _ (by simp [SLoc.litG]))⟩
  rintro t v m' ⟨⟨rfl, m₁, m₂, cN', bN', hu1, hg1, ⟨v₁, hrp⟩, hu3, hkA3, hqarr, dN', hcN', fN',
    hvN', hv3⟩, hgrow⟩
  obtain ⟨-, hl, hp, hncA, ⟨wv', hw'⟩, ⟨aw', ha', har'⟩, hcode, hstep⟩ := hrp
  have hb := fun z => SLoc.mem_blocksG_of D.toDispatchRep (S := S) (gl := gl) (cl := cl) (z := z)
  have mGl : ∀ z ∈ D.globs, z ∈ S.blocksG D.toDispatchRep gl cl :=
    fun z hz => hb z (.inr (.inr (.inr (.inr (.inr hz)))))
  have eB : E.nautilWorkperm ∈ E.blocks ∧ E.nautilWorkpermSz ∈ E.blocks := by
    simp [NautyEnv.blocks]
  have eA : E.nautilWorkperm ∈ Dispatch.envAvoid ∧ E.nautilWorkpermSz ∈ Dispatch.envAvoid := by
    simp
  -- `DYNALLOC1` keeps `D`'s scratch state
  have hw1 := D.work_unch h.work.disp hu1
    (fun z hz hn => by
      rcases hn with rfl | rfl | ⟨hc, rfl⟩ | hnv
      · exact D.globs_env _ (D.wglobs_sub _ hz) eB.2
      · exact D.globs_env _ (D.wglobs_sub _ hz) eB.1
      · exact (hbN hc).1 (D.wglobs_sub _ hz)
      · exact hnv (D.globs_valid h.work.disp _ (D.wglobs_sub _ hz)))
    (fun z hz hn => by
      rcases hn with rfl | rfl | ⟨hc, rfl⟩ | hnv
      · exact (D.isWork_globs h.work.disp hz).2 eA.2
      · exact (D.isWork_globs h.work.disp hz).2 eA.1
      · exact uN hc hz
      · exact hnv (D.isWork_valid hz)) hg1
  have back1 := hw1.2
  -- the whole call's frame
  let L' : List block := [S.bl, S.bp, S.bWP, S.bA]
  let X : block → Prop := fun z => z = bnc ∨ z = bk ∨ z = bq
  have hU : Unch m m' (ChgD D.toDispatchRep m L' cN bN X) := by
    refine ((hu1.mono fun z hz => ?_).trans (hstep.unch.mono fun z hz => ?_)).trans
      (hu3.mono fun z hz => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr hz)))))))))
    · rcases hz with h1 | h1 | h1 | h1
      · exact .inr (.inr (.inr (.inr (.inl h1))))
      · exact .inr (.inr (.inr (.inl h1)))
      · exact .inr (.inr (.inr (.inr (.inr (.inl h1)))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h1))))))
    · rcases hz with h1 | h1 | h1 | h1
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h1
        rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
        · exact .inl (by simp [L'])
        · exact .inl (by simp [L'])
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
        · exact .inl (by simp [L'])
        · exact .inl (by simp [L'])
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))
      · exact .inr (.inl h1)
      · exact .inr (.inr (.inl (back1 z h1)))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl fun hv' => h1 (hg1 _ hv')))))))
  have hX : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, ¬ X z := by
    rintro z hz (rfl | rfl | rfl)
    · exact n1S hz
    · exact n3S hz
    · exact n2S hz
  have hXw : ∀ z, IsWorkG D.toDispatchRep m z → ¬ X z := by
    rintro z hz (rfl | rfl | rfl)
    · exact n1W hz
    · exact n3W hz
    · exact n2W hz
  have key := h.not_chgD hvU hvT (L := L') hX dN
  have kz : ∀ z ∈ S.litG, z ∉ L' → z ≠ E.nautilWorkperm → z ≠ E.nautilWorkpermSz →
      ¬ ChgD D.toDispatchRep m L' cN bN X z :=
    fun z hz h1 h2 h3 => key z (mL z hz) h1 (h.lit_globs z hz) h2 h3
  have kzl : ∀ z ∈ [S.bo, S.bF, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws, E.fmptr, S.bst],
      ¬ ChgD D.toDispatchRep m L' cN bN X z := by
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact kz _ (by simp [SLoc.litG]) (by simp only [L']; sep_notin hd) (by sep_ne hd)
        (by sep_ne hd)
  simp only [List.forall_mem_cons] at kzl
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, -⟩ := kzl
  have kG : ∀ z ∈ D.graphBlocks gl S.bg, ¬ ChgD D.toDispatchRep m L' cN bN X z := fun z hz =>
    key z (mG z hz) (by
      simp only [L', List.mem_cons, List.mem_nil_iff, or_false, not_or]
      exact ⟨h.graph_ne hz (.inl (by simp)), h.graph_ne hz (.inl (by simp)),
        h.graph_ne hz (.inr (.inr (.inl (by simp)))), h.graph_ne hz (.inr (.inr (.inl (by simp))))⟩)
      (fun hg => h.globs_ne hg (.inl hz) rfl)
      (h.graph_ne hz (.inr (.inr (.inr (.inl (by simp))))))
      (h.graph_ne hz (.inr (.inr (.inr (.inl (by simp))))))
  have kC : ∀ z ∈ D.canonBlocks cl S.bc, ¬ ChgD D.toDispatchRep m L' cN bN X z := fun z hz =>
    key z (hb z (.inr (.inr (.inl hz)))) (by
      simp only [L', List.mem_cons, List.mem_nil_iff, or_false, not_or]
      exact ⟨h.canon_ne hz (.inr (.inl (by simp))), h.canon_ne hz (.inr (.inl (by simp))),
        h.canon_ne hz (.inr (.inr (.inl (by simp)))), h.canon_ne hz (.inr (.inr (.inl (by simp))))⟩)
      (fun hg => h.globs_ne hg (.inr (.inr (.inl hz))) rfl)
      (h.canon_ne hz (.inr (.inr (.inr (.inl (by simp))))))
      (h.canon_ne hz (.inr (.inr (.inr (.inl (by simp))))))
  -- `Keep` for the `DYNALLSTAT` targets
  have nNS : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, z ≠ E.nautilWorkperm →
      z ≠ E.nautilWorkpermSz → ¬ Doref.NSet m cN bN z := by
    rintro z hz h1 h2 (e | e | ⟨hc, e⟩ | e)
    · exact h2 e
    · exact h1 e
    · exact nN hc (e ▸ hz)
    · exact e (hv z hz)
  have kOut : ∀ z ∈ [S.bA, S.bWP], Keep m m' z := by
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · exact ((Keep.unch hu1 (nNS _ (mL _ (by simp [SLoc.litG])) (by sep_ne hd) (by sep_ne hd))).trans
        (hstep.keep _ (by simp [L]) (hg1 _ (hv _ (mL _ (by simp [SLoc.litG])))))).trans (hkA3 _)
    · exact ((Keep.unch hu1 (nNS _ (mL _ (by simp [SLoc.litG])) (by sep_ne hd) (by sep_ne hd))).trans
        (hstep.keep _ (by simp [L]) (hg1 _ (hv _ (mL _ (by simp [SLoc.litG])))))).trans (hkA3 _)
  simp only [List.forall_mem_cons] at kOut
  have hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws], Keep m m' z := by
    simp only [List.forall_mem_cons]
    exact ⟨kOut.1, Keep.unch hU z2, kOut.2.1, Keep.unch hU z3, Keep.unch hU z4, Keep.unch hU z5,
      Keep.unch hU z6, Keep.unch hU z7, Keep.unch hU z8, fun _ h => absurd h List.not_mem_nil⟩
  -- `D`'s scratch state after the `qinvar` store
  have nq2 : ∀ z, D.IsWork m₂ z → z ≠ bq := fun z hz e => by
    subst e
    rcases hstep.mono _ hz with h1 | h1
    · exact n2W (.inl (back1 _ h1))
    · exact h1 (hg1 _ n2V)
  have hw3 := D.work_unch hstep.work hu3 (fun z hz e => bqG (e ▸ D.wglobs_sub _ hz))
    (fun z hz e => nq2 z hz e) hv3
  have hmono : ∀ z, D.IsWork m' z → D.IsWork m z ∨ ¬ Mem.valid_block m z := fun z hz => by
    rcases hstep.mono _ (hw3.2 z hz) with h1 | h1
    · exact .inl (back1 _ h1)
    · exact .inr fun hv' => h1 (hg1 _ hv')
  have hNw : 0 < cN' → ¬ D.IsWork m' bN' := fun hc hw => by
    rcases hstep.mono _ (hw3.2 _ hw) with h1 | h1
    · have h0 := back1 _ h1
      rcases fN' with ⟨rfl, rfl⟩ | hnv
      · exact uN hc h0
      · exact hnv (D.isWork_valid h0)
    · exact h1 (hvN' hc)
  -- the new state
  have hAs := h.arrays
  have nbq : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, z ≠ bq := fun z hz => ne_loc hz n2S
  have har : ArraysG D.toDispatchRep m' S gl cl G (visitStG O G level numcells st) :=
    { lab := hl.unch hu3 (nbq _ (mL _ (by simp [SLoc.litG])))
      ptn := hp.unch hu3 (nbq _ (mL _ (by simp [SLoc.litG])))
      orbits := hAs.orbits.unch hU z1
      active := ⟨aw', ha'.unch hu3 (nbq _ (mL _ (by simp [SLoc.litG]))), har'⟩
      fixedpts := let ⟨fw, hf, hr⟩ := hAs.fixedpts; ⟨fw, hf.unch hU z2, hr⟩
      workperm := ⟨wv', hw'.unch hu3 (nbq _ (mL _ (by simp [SLoc.litG])))⟩
      firstlab := hAs.firstlab.unch hU z3
      canonlab := hAs.canonlab.unch hU z4
      firstcode := hAs.firstcode.unch hU z5
      canoncode := hAs.canoncode.unch hU z6
      firsttc := hAs.firsttc.unch hU z7
      canong := D.canon_unch hAs.canong hU kC
      autos := hAs.autos.unch hU z8 z9
      graph := D.graph_unch hAs.graph hU kG }
  have hsc : ScalarsG m' (visitStG O G level numcells st) false :=
    { h.scalars.unch hU (fun z hz => kz z (by revert z hz; simp [SLoc.litG])
        (by simp only [L']; revert z hz; sep_all hd) (by revert z hz; sep_all hd)
        (by revert z hz; sep_all hd)) with }
  have hst : StatsG m' S (visitStG O G level numcells st) pre := { h.stats.unch hU z10 with }
  obtain ⟨hSA, hWM⟩ := h.rebuildD hvU hvT (L := L') (by simp [L']) hX hXw dN hU hgrow hK hw3.1
    hmono dN' fN' hNw hsc hst har hinv
  have nl : ∀ z, z = bnc ∨ z = bk → ¬ Doref.NSet m cN bN z := by
    rintro z (rfl | rfl) (e | e | ⟨hc, e⟩ | e)
    · exact n1S (e ▸ hE3 _ (by simp))
    · exact n1S (e ▸ hE3 _ (by simp))
    · exact n1W (e ▸ .inr ⟨cN, hc, dN⟩)
    · exact e n1V
    · exact n3S (e ▸ hE3 _ (by simp))
    · exact n3S (e ▸ hE3 _ (by simp))
    · exact n3W (e ▸ .inr ⟨cN, hc, dN⟩)
    · exact e n3V
  have hKl : ∀ z ∈ [bnc, bq, bk], Keep m m' z := by
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact ((Keep.unch hu1 (nl _ (.inl rfl))).trans (hstep.keep _ (by simp [L]) (hg1 _ n1V))).trans
        (hkA3 _)
    · refine ((Keep.unch hu1 ?_).trans (Keep.unch hstep.unch ?_)).trans (hkA3 _)
      · rintro (e | e | ⟨hc, e⟩ | e)
        · exact n2S (e ▸ hE3 _ (by simp))
        · exact n2S (e ▸ hE3 _ (by simp))
        · exact n2W (e ▸ .inr ⟨cN, hc, dN⟩)
        · exact e n2V
      · rintro (h1 | h1 | h1 | h1)
        · exact hqq.1 (List.mem_append_right _ (by simpa [L] using h1))
        · exact bqG (D.wglobs_sub _ h1)
        · exact n2W (.inl (back1 _ h1))
        · exact h1 (hg1 _ n2V)
    · exact ((Keep.unch hu1 (nl _ (.inr rfl))).trans (hstep.keep _ (by simp [L]) (hg1 _ n3V))).trans
        (hkA3 _)
  refine hQ m' hSA (hncA.unch hu3 hnq) (hcode.unch hu3 hqk.symm) hqarr (hU.mono fun z hz => ?_)
    hgrow hWM hKl
  rcases hz with h1 | h1 | h1 | h1 | h1 | ⟨hc, h1⟩ | h1 | h1
  · simp only [L', List.mem_cons, List.mem_nil_iff, or_false] at h1
    rcases h1 with rfl | rfl | rfl | rfl <;>
      exact .inl ⟨mL _ (by simp [SLoc.litG]), by sep_ne hd, by sep_ne hd⟩
  · have hg := D.wglobs_sub _ h1
    exact .inl ⟨mGl _ hg, h.globs_ne hg (.inr (.inr (.inr (.inl (by simp))))) ,
      h.globs_ne hg (.inr (.inr (.inr (.inr (by simp)))))⟩
  · exact .inr (.inr (.inl (.inl h1)))
  · subst h1; exact .inl ⟨mL _ (by simp [SLoc.litG]), by sep_ne hd, by sep_ne hd⟩
  · subst h1; exact .inl ⟨mL _ (by simp [SLoc.litG]), by sep_ne hd, by sep_ne hd⟩
  · subst h1; exact .inr (.inr (.inl (.inr ⟨cN, hc, dN⟩)))
  · exact .inr (.inl h1)
  · rcases h1 with h1 | h1 | h1
    · exact .inr (.inr (.inr (.inl h1)))
    · exact .inr (.inr (.inr (.inr (.inr h1))))
    · exact .inr (.inr (.inr (.inr (.inl h1))))

end Generic

theorem visitStG_dense {n : Nat} (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    visitStG NautyVerified.Proofs.Dispatch.denseOps ctx level numcells st =
      visitSt ctx level numcells st := rfl

end NautyVerified.Proofs.Search
