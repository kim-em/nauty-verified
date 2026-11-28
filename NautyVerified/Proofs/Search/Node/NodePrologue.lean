import NautyVerified.Proofs.Search.Node.Prologue
import NautyVerified.Proofs.Search.Node.TcOps
import NautyVerified.Proofs.Search.Node.TcFrame
import NautyVerified.Proofs.Search.Node.FirstLocal
import NautyVerified.Proofs.Search.Valid
import NautyVerified.Proofs.Search.Node.Prune

/-!
# The prologue of a search node

`firstpathnode0` and `othernode0` both start with

```
numcells = numcells;                 /* the parameter, into the addressable local */
tcnode_this = tcnode_parent->next;
if (tcnode_this == NULL) { …allocate tcnode_this and its target cell… }
tcell = tcnode_this->tcellptr;
```

`wp_nodePrologue`: from the node specification's list, these statements
leave the list with this level's entry `(nd, bt)` at index `level - 1`
(allocated if missing, `TcChain.snoc`), `tcnode_this = nd`, `tcell = bt`,
and change only the `numcells` local, the parent's `next` field and new
blocks. `SearchAt.unchT`: `SearchAt` survives changes outside its blocks other
than `tcnode0`, which it does not describe.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (Keep)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

theorem SearchAt.unchT {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} {W : block → Prop} (h : SearchAt m S ctx st pre nsp) (hu : Unch m m' W)
    (hS : ∀ z ∈ S.blocks, z ≠ Block.tcnode0 → ¬ W z) (hwk : ∀ z, IsWork m z → ¬ W z) :
    SearchAt m' S ctx st pre nsp :=
  have hd := h.distinct
  { h with
    fixed := h.fixed.unch hu fun z hz => hS z (by revert z; simp [SLoc.blocks])
      (by revert z hz; sep_all hd)
    scalars := h.scalars.unch hu fun z hz => hS z (by revert z; simp [SLoc.blocks])
      (by revert z hz; sep_all hd)
    stats := h.stats.unch hu (hS _ (by simp [SLoc.blocks]) (by sep_ne hd))
    arrays := h.arrays.unch hu fun z hz => hS z (by revert z; simp [SLoc.blocks])
      (by revert z hz; sep_all hd)
    dyns := h.dyns.unch hu fun z hz => hS z (by revert z; simp [SLoc.blocks])
      (by revert z hz; sep_all hd)
    work := h.work.unch hu (fun z hz => hS z (by revert z; simp [SLoc.blocks])
      (by revert z hz; sep_all hd)) hwk
    tables := h.tables.unch hu fun z hz => hS z (by revert z; simp [SLoc.blocks])
      (by revert z hz; sep_all hd) }

theorem perm0_of_va64 {m : mem} {b : block}
    (h : Mem.valid_access m .Mint64 b (zOfInt 0) .Writable) :
    Mem.perm m b (zOfInt 0) .Cur .Nonempty :=
  Mem.perm_implies _ _ _ _ _ _ (h.1 _ ⟨by change intOfZ _ ≤ intOfZ _; omega, by
    change intOfZ _ < intOfZ _; simp only [intOfZ_add, intOfZ_zOfInt]
    have : intOfZ (Common.Memdata.size_chunk .Mint64) = 8 := rfl
    omega⟩) (.perm_any_N _)

/-- The four statements every search node starts with, then `rest`. -/
abbrev nodePrologue (rest : statement) : statement :=
  .Ssequence (.Sassign (.Evar dense.id.numcells tint) (Refine.tv dense.id.numcells))
    (.Ssequence (Set.sk (.Sset dense.id.tcnode_this
        (tcF dense.id.tcnode_parent dense.id.next (tptr tcStruct))))
      (.Ssequence (Set.sk Firstpathnode.tcalloc)
        (.Ssequence (Set.sk (.Sset dense.id.tcell (tcF dense.id.tcnode_this dense.id.tcellptr (tptr tulong))))
          rest)))

variable {xi : ExternalCalls}

set_option maxHeartbeats 4000000 in
theorem wp_nodePrologue {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre : Bool} {level nc : Nat}
    {chain : List (block × block)} {bnc : block} {rest : statement}
    (h : SearchAt m S ctx st pre false) (hvU : Mem.valid_block m S.bUA)
    (hTc : TcChain m S.M Block.tcnode0 chain) (hTo : TcOk m S chain)
    (hlen : level - 1 ≤ chain.length) (hl1 : 1 ≤ level)
    (henc : PTree.get dense.id.numcells e = some (bnc, tint))
    (hncA : ∃ v, ArrayAt m .Mint32 bnc 0 v 1) (hbS : bnc ∉ S.blocks) (hbW : ¬ IsWork m bnc)
    (hbC : ∀ p ∈ chain, p.1 ≠ bnc ∧ p.2 ≠ bnc)
    (hge : ∀ x ∈ [dense.id.«nauty:alloc_m», dense.id.nauty_zalloc], PTree.get x e = none)
    (hnct : PTree.get dense.id.numcells le = some (.Vint (ir nc)))
    (hpar : PTree.get dense.id.tcnode_parent le = some (.Vptr (tcParent chain level) Ptrofs.zero))
    (hQ : ∀ le' m' chain' nd bt,
      SearchAt m' S ctx st pre false →
      ArrayAt m' .Mint32 bnc 0 (fun _ => .Vint (ir nc)) 1 →
      TcChain m' S.M Block.tcnode0 chain' → TcOk m' S chain' →
      chain'[level - 1]? = some (nd, bt) →
      chain'.take (level - 1) = chain.take (level - 1) →
      (∀ p ∈ chain', p ∈ chain ∨ (¬ Mem.valid_block m p.1 ∧ ¬ Mem.valid_block m p.2)) →
      (∃ vals, ArrayAt m' .Mint64 bt 0 vals S.M) →
      Unch m m' (fun z => z = bnc ∨ z = tcParent chain level ∨ ¬ Mem.valid_block m z) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → WorkMono m m' → Keep m m' bnc →
      PTree.get dense.id.tcnode_this le' = some (.Vptr nd Ptrofs.zero) →
      PTree.get dense.id.tcell le' = some (.Vptr bt Ptrofs.zero) →
      (∀ x, x ≠ dense.id.tcnode_this → x ≠ dense.id.tcell → x ≠ idOf 703 → x ≠ idOf 704 →
        x ≠ idOf 705 → x ≠ idOf 706 → x ≠ idOf 707 → PTree.get x le' = PTree.get x le) →
      Wp xi ge f rest Q e le' m') :
    Wp xi ge f (nodePrologue rest) Q e le m := by
  have hd := h.distinct
  have hpw := hTo.pairwise
  have hnl := h.nlt
  have hvT : Mem.valid_block m Block.tcnode0 := by
    cases chain with
    | nil => exact FieldAt.valid hTc
    | cons p rest => exact FieldAt.valid hTc.1
  have hvAll := h.valid_all hvU hvT
  have hparE : tcParent chain level = prevAt Block.tcnode0 chain (level - 1) := tcParent_eq hl1 hlen
  have hparT : tcParent chain level ∈ tcBlocks Block.tcnode0 chain := hparE ▸ prevAt_mem _ _ _
  have h0S : Block.tcnode0 ∈ S.blocks := by simp [SLoc.blocks]
  have hbT : ∀ z ∈ tcBlocks Block.tcnode0 chain, z ≠ bnc := by
    intro z hz e
    subst e
    simp only [tcBlocks, List.mem_cons] at hz
    rcases hz with e | hz
    · exact hbS (e ▸ h0S)
    · obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with e | e
      · exact (hbC p hp).1 e.symm
      · exact (hbC p hp).2 e.symm
  have hlink : FieldAt m .Mint64 (tcParent chain level) 0 (linkAt chain (level - 1)) :=
    hparE ▸ TcChain.next hTc hlen
  -- `numcells = numcells`
  wp_step
  refine wp_localStore henc hncA (rhs := Refine.tv dense.id.numcells) (w := nc)
    (by simp [Exec.evalExpr, Refine.tv, hnct]) rfl ?_
  intro m1 hA1 hu1 hK1 hg1
  simp only [seqPost, Post.after, E0_append]
  have hS1 : SearchAt m1 S ctx st pre false :=
    h.unch hu1 (fun z hz e => hbS (e ▸ hz)) (fun z hz e => hbW (e ▸ hz))
  have hwm1 : WorkMono m m1 := WorkMono.of_unch h.work hu1
    (fun z hz e => hbS (e ▸ by simp only [workG] at hz; revert z hz; simp [SLoc.blocks]))
    (fun z hz e => hbW (e ▸ hz))
  have hTc1 := hTc.unch hu1 (fun z hz e => hbT z hz e)
  have hTo1 := TcOk.mono hTo hg1 hwm1
  -- `tcnode_this = tcnode_parent->next`
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_tcF (off := 0) hpar rfl (by decide) (hlink.unch' hu1 (fun e => hbT _ hparT e))]
  simp only [seqPost, Post.after, E0_append]
  have hQ' := hQ
  rcases hcl : chain[level - 1]? with _ | ⟨nd, bt⟩
  · -- a new entry
    have hl1' : linkAt chain (level - 1) = Vnullptr := by unfold linkAt; rw [hcl]
    rw [hl1']
    have hll : level - 1 = chain.length := by
      rw [List.getElem?_eq_none_iff] at hcl; omega
    have hparL : prevAt Block.tcnode0 chain chain.length = tcParent chain level := by
      rw [hparE, hll]
    have hpW := (hlink.unch' hu1 (fun e => hbT _ hparT e)).writable
    have hal1 : IntAt m1 Block.allocM S.M := h.fixed.allocM.unch' hu1 (fun e => hbS (e ▸ by simp [SLoc.blocks]))
    wp_step; wp_step; wp_step
    simp only [List.forall_mem_cons, List.forall_mem_nil] at hge
    refine wp_tcallocNew (temps_gss _ _ _) (by rw [temps_gso _ _ (by decide)]; exact hpar) hpW
      hge.1 hal1 (by have := h.Mlt; omega) (by have := h.Mlt; omega) h.M1 hge.2.1 ?_
    intro le2 m2 nd tc hnd htc hne hu2 hg2 hp0 hp8 hnd0 hnd8 htcA hmn hmt hkp hthis2 hle2
    simp only [seqPost, Post.after, E0_append]
    -- the frame of the allocation
    have hvAll1 : ∀ z ∈ S.blocks, Mem.valid_block m1 z := fun z hz => hg1 _ (hvAll z hz)
    have hpar0 : ∀ z ∈ S.blocks, z ≠ Block.tcnode0 → z ≠ tcParent chain level := by
      intro z hz hz0 e
      rw [hparE] at e
      rcases prevAt_mem_nodes Block.tcnode0 chain (level - 1) with h' | ⟨p, hp, h'⟩
      · exact hz0 (e.trans h')
      · exact (hTo.apart p hp).1 (h' ▸ e ▸ hz)
    have hWS : ∀ z ∈ S.blocks, z ≠ Block.tcnode0 → ¬ (z = tcParent chain level ∨ ¬ Mem.valid_block m1 z) :=
      fun z hz hz0 => by
        rintro (e | e)
        · exact hpar0 z hz hz0 e
        · exact e (hvAll1 z hz)
    have hwg : ∀ z ∈ [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
        Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
        Block.nautilWorkperm, Block.nautilWorkpermSz],
        ¬ (z = tcParent chain level ∨ ¬ Mem.valid_block m1 z) := by
      intro z hz
      exact hWS z (by revert z hz; simp [SLoc.blocks]) (by revert z hz; decide)
    have hwk1 : ∀ z, IsWork m1 z → ¬ (z = tcParent chain level ∨ ¬ Mem.valid_block m1 z) := by
      intro z hz
      rintro (e | e)
      · rw [hparE] at e
        rcases prevAt_mem_nodes Block.tcnode0 chain (level - 1) with h' | ⟨p, hp, h'⟩
        · exact hS1.work_not hz (e.trans h' ▸ h0S)
        · exact (hTo1.apart p hp).2.2.1 (h' ▸ e ▸ hz)
      · exact e hz.valid
    have hS2 := hS1.unchT hu2 hWS hwk1
    have hwm2 : WorkMono m1 m2 := WorkMono.of_unch hS1.work hu2
      (fun z hz => hwg z (by simpa [workG] using hz)) hwk1
    have hnw : ∀ z, ¬ Mem.valid_block m1 z → ¬ IsWork m2 z := fun z hz hw =>
      hz (IsWork.back hS1 hu2 hwg hw).valid
    -- the new list
    have hfl : ∀ z ∈ chain.flatMap (fun p => [p.1, p.2]), Mem.valid_block m1 z := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl
      · exact (hTo1.valid p hp).1
      · exact (hTo1.valid p hp).2
    have hTd : (tcBlocks Block.tcnode0 chain).Pairwise (· ≠ ·) := by
      rw [tcBlocks, List.pairwise_cons]
      refine ⟨fun z hz e => ?_, hpw⟩
      obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl
      · exact (hTo.apart p hp).1 (e ▸ h0S)
      · exact (hTo.apart p hp).2.1 (e ▸ h0S)
    have hTc2 : TcChain m2 S.M Block.tcnode0 (chain ++ [(nd, tc)]) := by
      refine TcChain.snoc hu2 hTc1 hTd (fun z hz hzl => ?_) (hparL ▸ hp8) (hparL ▸ hp0) hnd0 hnd8
        ⟨_, htcA⟩ hmn hmt (hparL ▸ hkp)
      rintro (e | e)
      · exact hzl (e.trans hparL.symm)
      · simp only [tcBlocks, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact e (hg1 _ hvT)
        · exact e (hfl z hz)
    have hM1 := h.M1
    have hvnd : Mem.valid_block m2 nd := FieldAt.valid hnd0
    have hvtc : Mem.valid_block m2 tc := Alloc.valid_of_access (htcA.writable 0 hM1)
    have hTo2 : TcOk m2 S (chain ++ [(nd, tc)]) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [List.flatMap_append, List.pairwise_append]
        refine ⟨hpw, by simpa using hne, ?_⟩
        intro a ha b hb e
        subst e
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
          List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl
        · exact hnd (hfl _ ha)
        · exact htc (hfl _ ha)
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ⟨hg2 _ (hTo1.valid p hp).1, hg2 _ (hTo1.valid p hp).2⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp; exact ⟨hvnd, hvtc⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨a1, a2, a3, a4⟩ := hTo1.apart p hp
          refine ⟨a1, a2, fun hw => ?_, fun hw => ?_⟩
          · rcases hwm2 _ hw with h' | h'
            · exact a3 h'
            · exact h' (hTo1.valid p hp).1
          · rcases hwm2 _ hw with h' | h'
            · exact a4 h'
            · exact h' (hTo1.valid p hp).2
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp
          exact ⟨fun hz => hnd (hvAll1 _ hz), fun hz => htc (hvAll1 _ hz), hnw _ hnd, hnw _ htc⟩
    have hown : (chain ++ [(nd, tc)])[level - 1]? = some (nd, tc) := by
      rw [hll]; simp
    have htake : (chain ++ [(nd, tc)]).take (level - 1) = chain.take (level - 1) := by
      rw [hll]; simp
    -- `tcell = tcnode_this->tcellptr`
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_tcF (off := 8) hthis2 rfl (by decide) hnd8]
    simp only [E0_append]
    have hbn2 : bnc ≠ tcParent chain level := fun e => hbT _ hparT e.symm
    exact hQ' _ m2 _ nd tc hS2 (hA1.unch hu2 (by
        rintro (e | e)
        · exact hbn2 e
        · exact e (Alloc.valid_of_access (hA1.writable 0 (by decide))))) hTc2 hTo2 hown htake
      (fun p hp => by
        rcases List.mem_append.1 hp with hp | hp
        · exact .inl hp
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp
          exact .inr ⟨fun hv => hnd (hg1 _ hv), fun hv => htc (hg1 _ hv)⟩)
      ⟨_, htcA⟩
      ((hu1.mono fun z hz => .inl hz).trans (hu2.mono fun z hz => by
        rcases hz with e | e
        · exact .inr (.inl e)
        · exact .inr (.inr fun hv => e (hg1 _ hv))))
      (fun z hz => hg2 _ (hg1 _ hz)) (WorkMono.trans hwm1 hg1 hwm2)
      ((hK1 bnc).trans (Keep.unch hu2 (by
        rintro (e | e)
        · exact hbn2 e
        · exact e (Alloc.valid_of_access (hA1.writable 0 (by decide))))))
      (by rw [temps_gso _ _ (by decide)]; exact hthis2) (temps_gss _ _ _)
      (fun x h1 h2 h3 h4 h5 h6 h7 => by
        rw [temps_gso _ _ h2, hle2 x h1 h3 h4 h5 h6 h7, temps_gso _ _ h1])
  · -- the entry exists
    have hl1' : linkAt chain (level - 1) = .Vptr nd Ptrofs.zero := by unfold linkAt; rw [hcl]
    rw [hl1']
    have hlt : level - 1 < chain.length := by
      rw [List.getElem?_eq_some_iff] at hcl; obtain ⟨h1, -⟩ := hcl; exact h1
    have hpn : prevAt Block.tcnode0 chain level = nd := by
      have := prevAt_eq Block.tcnode0 chain (level - 1) (by omega)
      rw [show level - 1 + 1 = level by omega, hcl] at this
      exact this
    have hmem := List.mem_of_getElem? hcl
    have hndT : nd ∈ tcBlocks Block.tcnode0 chain := .tail _ (mem_flat hmem).1
    have hbtT : bt ∈ tcBlocks Block.tcnode0 chain := .tail _ (mem_flat hmem).2
    have hf0 : FieldAt m .Mint64 nd 0 (linkAt chain level) :=
      hpn ▸ TcChain.next hTc (i := level) (by omega)
    have hcellAt := TcChain.cell hTc hcl
    wp_step; wp_step; wp_step
    refine wp_tcallocSkip (temps_gss _ _ _)
      ((Keep.unch hu1 (fun e => hbT _ hndT e)).perm _ _ (perm0_of_va64 hf0.writable)) ?_
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_tcF (off := 8) (temps_gss _ _ _) rfl (by decide)
      (hcellAt.1.unch' hu1 (fun e => hbT _ hndT e))]
    simp only [E0_append]
    obtain ⟨vals, hva⟩ := hcellAt.2
    exact hQ' _ m1 chain nd bt hS1 hA1 hTc1 hTo1 hcl rfl (fun p hp => .inl hp)
      ⟨vals, hva.unch hu1 (fun e => hbT _ hbtT e)⟩ (hu1.mono fun z hz => .inl hz) hg1 hwm1 (hK1 bnc)
      (by rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _) (temps_gss _ _ _)
      (fun x h1 h2 _ _ _ _ _ => by rw [temps_gso _ _ h2, temps_gso _ _ h1])

end NautyVerified.Proofs.Search
