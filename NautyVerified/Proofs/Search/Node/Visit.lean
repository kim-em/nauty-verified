import NautyVerified.Proofs.Search.Node.Doref
import NautyVerified.Proofs.Search.Node.ReallocW

/-!
# A node's refinement, with the search state rebuilt

`wp_nodeVisit`: from `SearchAt` at `st` (after `++stats->numnodes`) and the
node's `numcells`, `qinvar` and `refcode` locals, the `doref` call gives
`SearchAt` for `visitSt ctx level numcells st`, the `numcells` local holding
refinement's cell count and `refcode` its code, with the frame and validity
growth. Both `firstpathnode0` and `othernode0` make this call.
`visit_eq`: HexGraphIso's `visit` is `++numnodes` then `visitSt`.
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
      Unch m m' (fun z => z ∈ S.blocks ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨ z = bnc ∨
        z = bq ∨ z = bk) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
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
  have hKo : ∀ z ∈ [S.bF, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC], Keep m m' z := by
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
  have hK : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC], Keep m m' z := by
    simp only [List.forall_mem_cons] at hKo ⊢
    exact ⟨hKA, hKo.1, hKW, hKo.2.1, hKo.2.2.1, hKo.2.2.2.1, hKo.2.2.2.2.1, hKo.2.2.2.2.2.1,
      fun _ h => absurd h (List.not_mem_nil)⟩
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
  refine hQ m' hSA hnc' hk' hqarr' (hU.mono fun z hz => ?_) hgrow
  rcases hz with h6 | hN | hx
  · unfold dyn3Set at h6
    rcases h6 with e | e | e | e | e | e | ⟨hc, e⟩ | ⟨hc, e⟩ | ⟨hc, e⟩ | hnv
    all_goals first
      | exact .inr (.inr (.inl (e ▸ iW hc)))
      | exact .inr (.inr (.inl (e ▸ iS hc)))
      | exact .inr (.inr (.inl (e ▸ iB hc)))
      | exact .inr (.inl hnv)
      | exact .inl (e ▸ by simp [SLoc.blocks])
  · rcases hN with e | e | ⟨hc, e⟩ | hnv
    · exact .inl (e ▸ by simp [SLoc.blocks])
    · exact .inl (e ▸ by simp [SLoc.blocks])
    · exact .inr (.inr (.inl (e ▸ iN hc)))
    · exact .inr (.inl hnv)
  · rcases hx with e | e | e | e | e | e | e
    · exact .inl (e ▸ by simp [SLoc.blocks])
    · exact .inl (e ▸ by simp [SLoc.blocks])
    · exact .inr (.inr (.inr (.inl e)))
    · exact .inl (e ▸ by simp [SLoc.blocks])
    · exact .inl (e ▸ by simp [SLoc.blocks])
    · exact .inr (.inr (.inr (.inr (.inr e))))
    · exact .inr (.inr (.inr (.inr (.inl e))))

end NautyVerified.Proofs.Search
