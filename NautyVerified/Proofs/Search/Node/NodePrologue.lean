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

`wp_nodePrologueG` and `SearchAtG.unchT` are the same over `SearchAtG D` for
any `NautyEnv` (the dense `wp_nodePrologue` is their instance), with
`wp_localStoreG`, `wp_localStore` over any global environment.
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

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

omit E in
/-- `wp_localStore` over any global environment. -/
theorem wp_localStoreG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {x : ident} {b : block} (hx : PTree.get x e = some (b, tint))
    (harr : ∃ vals, ArrayAt m .Mint32 b 0 vals 1) {rhs : expr} {w : Int}
    (hr : Exec.evalExpr ge e le m rhs = some (.Vint (ir w))) (hty : typeof rhs = tint)
    (hQ : ∀ m', ArrayAt m' .Mint32 b 0 (fun _ => .Vint (ir w)) 1 → Unch m m' (· = b) →
      Alloc.KeepA m m' → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar x tint) rhs) Q e le m := by
  obtain ⟨vals, ha⟩ := harr
  obtain ⟨m', hst, harr', -⟩ := store_array ha (show 0 < 1 by decide) (.Vint (ir w)) rfl
  apply wp_assign_eval
  rw [hr]
  simp only [Exec.evalLvalue, Exec.lvalOfVar, hx, hty]
  simp only [ite_true, typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
  rw [show Ptrofs.unsigned Ptrofs.zero = elemOfs .Mint32 0 0 from rfl, hst]
  exact hQ m' (harr'.congr fun i hi => by simp [upd, show i = 0 by omega]) (Unch.store hst rfl)
    (Alloc.KeepA.storeArr ha hst) fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz

/-- `SearchAtG` survives changes outside its blocks other than `tcnode0`, which it
does not describe. -/
theorem SearchAtG.unchT {n : Nat} {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool} {W : block → Prop}
    (h : SearchAtG D m S gl cl G st pre nsp) (hu : Unch m m' W)
    (hS : ∀ z ∈ S.blocksG D gl cl, z ≠ E.tcnode0 → ¬ W z) (hwk : ∀ z, IsWorkG D m z → ¬ W z)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) :
    SearchAtG D m' S gl cl G st pre nsp :=
  have hl := h.lit
  have hT : E.tcnode0 ∈ envSearch := by simp
  have hE : ∀ z ∈ envSearch, z ≠ E.tcnode0 → ¬ W z := fun z hz =>
    hS z (SLoc.mem_blocksG_of D (by simp [hz]))
  have hV : ∀ z ∈ [S.bl, S.bp, S.bo, S.bst], ¬ W z := fun z hz =>
    hS z (SLoc.mem_blocksG_of D (.inr (.inl hz))) (by revert z hz; sep_all hl)
  have hV' : ∀ z ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA], ¬ W z :=
    fun z hz => hS z (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inl hz)))))
      (by revert z hz; sep_all hl)
  have hD : ∀ z ∈ D.globs, ¬ W z := fun z hz =>
    hS z (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inr hz))))))
      (h.globs_ne hz (.inr (.inr (.inr (.inr hT)))))
  { h with
    fixed := h.fixed.unch hu fun z hz => hE z (by revert z; simp) (by revert z hz; sep_all hl)
    scalars := h.scalars.unch hu fun z hz => hE z (by revert z; simp) (by revert z hz; sep_all hl)
    stats := h.stats.unch hu (hV _ (by simp))
    arrays := h.arrays.unch hu (fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        iterate 3 exact hV _ (by simp)
        iterate 9 exact hV' _ (by simp)
        exact hE _ (by simp) (by sep_ne hl))
      (fun z hz => hS z (SLoc.mem_blocksG_of D (.inl hz))
        (h.graph_ne hz (.inr (.inr (.inr (.inl hT))))))
      (fun z hz => hS z (SLoc.mem_blocksG_of D (.inr (.inr (.inl hz))))
        (h.canon_ne hz (.inr (.inr (.inr (.inl hT))))))
    dyns := h.dyns.unch hu fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      iterate 16 exact hE _ (by simp) (by sep_ne hl)
      iterate 8 exact hV' _ (by simp)
      exact hD _ D.wsP_mem
      exact hD _ D.wsS_mem
      exact hV' _ (by simp)
    work := (h.work.unch hu (fun z hz => hD z (D.wglobs_sub z hz))
      ⟨hE _ (by simp) (by sep_ne hl), hE _ (by simp) (by sep_ne hl)⟩ hwk hv).1
    tables := h.tables.unch hu (hE _ (by simp) (by sep_ne hl)) (hE _ (by simp) (by sep_ne hl))
      (hE _ (by simp) (by sep_ne hl)) fun z hz _ => hD z hz }

set_option maxHeartbeats 4000000 in
/-- `wp_nodePrologue` over `SearchAtG D`. -/
theorem wp_nodePrologueG {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {pre : Bool} {level nc : Nat}
    {chain : List (block × block)} {bnc : block} {rest : statement}
    (h : SearchAtG D m S gl cl G st pre false) (hvU : Mem.valid_block m S.bUA)
    (hTc : TcChain m S.M E.tcnode0 chain) (hTo : TcOkG D m S gl cl chain)
    (hlen : level - 1 ≤ chain.length) (hl1 : 1 ≤ level)
    (henc : PTree.get dense.id.numcells e = some (bnc, tint))
    (hncA : ∃ v, ArrayAt m .Mint32 bnc 0 v 1) (hbS : bnc ∉ S.blocksG D gl cl)
    (hbW : ¬ IsWorkG D m bnc)
    (hbC : ∀ p ∈ chain, p.1 ≠ bnc ∧ p.2 ≠ bnc)
    (hge : ∀ x ∈ [dense.id.«nauty:alloc_m», dense.id.nauty_zalloc], PTree.get x e = none)
    (hnct : PTree.get dense.id.numcells le = some (.Vint (ir nc)))
    (hpar : PTree.get dense.id.tcnode_parent le = some (.Vptr (tcParent chain level) Ptrofs.zero))
    (hQ : ∀ le' m' chain' nd bt,
      SearchAtG D m' S gl cl G st pre false →
      ArrayAt m' .Mint32 bnc 0 (fun _ => .Vint (ir nc)) 1 →
      TcChain m' S.M E.tcnode0 chain' → TcOkG D m' S gl cl chain' →
      chain'[level - 1]? = some (nd, bt) →
      chain'.take (level - 1) = chain.take (level - 1) →
      (∀ p ∈ chain', p ∈ chain ∨ (¬ Mem.valid_block m p.1 ∧ ¬ Mem.valid_block m p.2)) →
      (∃ vals, ArrayAt m' .Mint64 bt 0 vals S.M) →
      Unch m m' (fun z => z = bnc ∨ z = tcParent chain level ∨ ¬ Mem.valid_block m z) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → WorkMonoG D m m' → Keep m m' bnc →
      PTree.get dense.id.tcnode_this le' = some (.Vptr nd Ptrofs.zero) →
      PTree.get dense.id.tcell le' = some (.Vptr bt Ptrofs.zero) →
      (∀ x, x ≠ dense.id.tcnode_this → x ≠ dense.id.tcell → x ≠ idOf 703 → x ≠ idOf 704 →
        x ≠ idOf 705 → x ≠ idOf 706 → x ≠ idOf 707 → PTree.get x le' = PTree.get x le) →
      Wp xi ge f rest Q e le' m') :
    Wp xi ge f (nodePrologue rest) Q e le m := by
  have hl := h.lit
  have hpw := hTo.pairwise
  have hnl := h.nlt
  have mB : ∀ z ∈ envSearch, z ∈ S.blocksG D gl cl := fun z hz =>
    SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl hz)))))
  have mW : ∀ z ∈ D.wglobs, z ∈ S.blocksG D gl cl := fun z hz =>
    SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inr (D.wglobs_sub z hz))))))
  have hvT : Mem.valid_block m E.tcnode0 := by
    cases chain with
    | nil => exact FieldAt.valid hTc
    | cons p rest => exact FieldAt.valid hTc.1
  have hvAll := h.valid_all hvU hvT
  have hparE : tcParent chain level = prevAt E.tcnode0 chain (level - 1) := tcParent_eq hl1 hlen
  have hparT : tcParent chain level ∈ tcBlocks E.tcnode0 chain := hparE ▸ prevAt_mem _ _ _
  have h0S : E.tcnode0 ∈ S.blocksG D gl cl := mB _ (by simp)
  have hbT : ∀ z ∈ tcBlocks E.tcnode0 chain, z ≠ bnc := by
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
  refine wp_localStoreG henc hncA (rhs := Refine.tv dense.id.numcells) (w := nc)
    (by simp [Exec.evalExpr, Refine.tv, hnct]) rfl ?_
  intro m1 hA1 hu1 hK1 hg1
  simp only [seqPost, Post.after, E0_append]
  have hS1 : SearchAtG D m1 S gl cl G st pre false :=
    h.unch hu1 (fun z hz e => hbS (e ▸ hz)) (fun z hz e => hbW (e ▸ hz)) hg1
  have hwm1 : WorkMonoG D m m1 := fun z hz => .inl ((h.work.unch hu1
    (fun z hz e => hbS (e ▸ mW z hz))
    ⟨fun e => hbS (e ▸ mB _ (by simp)), fun e => hbS (e ▸ mB _ (by simp))⟩
    (fun z hz e => hbW (e ▸ hz)) hg1).2 z hz)
  have hTc1 := hTc.unch hu1 (fun z hz e => hbT z hz e)
  have hTo1 := TcOkG.mono hTo hg1 hwm1
  -- `tcnode_this = tcnode_parent->next`
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_tcF (off := 0) hpar (E.field_tcnodeNext _ _) (by decide)
    (hlink.unch' hu1 (fun e => hbT _ hparT e))]
  simp only [seqPost, Post.after, E0_append]
  have hQ' := hQ
  rcases hcl : chain[level - 1]? with _ | ⟨nd, bt⟩
  · -- a new entry
    have hl1' : linkAt chain (level - 1) = Vnullptr := by unfold linkAt; rw [hcl]
    rw [hl1']
    have hll : level - 1 = chain.length := by
      rw [List.getElem?_eq_none_iff] at hcl; omega
    have hparL : prevAt E.tcnode0 chain chain.length = tcParent chain level := by
      rw [hparE, hll]
    have hpW := (hlink.unch' hu1 (fun e => hbT _ hparT e)).writable
    have hal1 : IntAt m1 E.allocM S.M :=
      h.fixed.allocM.unch' hu1 (fun e => hbS (e ▸ mB _ (by simp)))
    wp_step; wp_step; wp_step
    simp only [List.forall_mem_cons, List.forall_mem_nil] at hge
    refine wp_tcallocNew (temps_gss _ _ _) (by rw [temps_gso _ _ (by decide)]; exact hpar) hpW
      hge.1 hal1 (by have := h.Mlt; omega) (by have := h.Mlt; omega) h.M1 hge.2.1 ?_
    intro le2 m2 nd tc hnd htc hne hu2 hg2 hp0 hp8 hnd0 hnd8 htcA hmn hmt hkp hthis2 hle2
    simp only [seqPost, Post.after, E0_append]
    -- the frame of the allocation
    have hvAll1 : ∀ z ∈ S.blocksG D gl cl, Mem.valid_block m1 z := fun z hz => hg1 _ (hvAll z hz)
    have hpar0 : ∀ z ∈ S.blocksG D gl cl, z ≠ E.tcnode0 → z ≠ tcParent chain level := by
      intro z hz hz0 e
      rw [hparE] at e
      rcases prevAt_mem_nodes E.tcnode0 chain (level - 1) with h' | ⟨p, hp, h'⟩
      · exact hz0 (e.trans h')
      · exact (hTo.apart p hp).1 (h' ▸ e ▸ hz)
    have hWS : ∀ z ∈ S.blocksG D gl cl, z ≠ E.tcnode0 →
        ¬ (z = tcParent chain level ∨ ¬ Mem.valid_block m1 z) :=
      fun z hz hz0 => by
        rintro (e | e)
        · exact hpar0 z hz hz0 e
        · exact e (hvAll1 z hz)
    have hwg : ∀ z ∈ D.wglobs, ¬ (z = tcParent chain level ∨ ¬ Mem.valid_block m1 z) :=
      fun z hz => hWS z (mW z hz)
        (h.globs_ne (D.wglobs_sub z hz) (.inr (.inr (.inr (.inr (by simp))))))
    have hwN : ¬ (E.nautilWorkperm = tcParent chain level ∨
          ¬ Mem.valid_block m1 E.nautilWorkperm) ∧
        ¬ (E.nautilWorkpermSz = tcParent chain level ∨ ¬ Mem.valid_block m1 E.nautilWorkpermSz) :=
      ⟨hWS _ (mB _ (by simp)) (by sep_ne hl), hWS _ (mB _ (by simp)) (by sep_ne hl)⟩
    have hwk1 : ∀ z, IsWorkG D m1 z → ¬ (z = tcParent chain level ∨ ¬ Mem.valid_block m1 z) := by
      intro z hz
      rintro (e | e)
      · rw [hparE] at e
        rcases prevAt_mem_nodes E.tcnode0 chain (level - 1) with h' | ⟨p, hp, h'⟩
        · exact hS1.work_not hz (e.trans h' ▸ h0S)
        · exact (hTo1.apart p hp).2.2.1 (h' ▸ e ▸ hz)
      · exact e hz.valid
    have hS2 := hS1.unchT hu2 hWS hwk1 hg2
    have hwu2 := hS1.work.unch hu2 hwg hwN hwk1 hg2
    have hwm2 : WorkMonoG D m1 m2 := fun z hz => .inl (hwu2.2 z hz)
    have hnw : ∀ z, ¬ Mem.valid_block m1 z → ¬ IsWorkG D m2 z := fun z hz hw =>
      hz (hwu2.2 z hw).valid
    -- the new list
    have hfl : ∀ z ∈ chain.flatMap (fun p => [p.1, p.2]), Mem.valid_block m1 z := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl
      · exact (hTo1.valid p hp).1
      · exact (hTo1.valid p hp).2
    have hTd : (tcBlocks E.tcnode0 chain).Pairwise (· ≠ ·) := by
      rw [tcBlocks, List.pairwise_cons]
      refine ⟨fun z hz e => ?_, hpw⟩
      obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl
      · exact (hTo.apart p hp).1 (e ▸ h0S)
      · exact (hTo.apart p hp).2.1 (e ▸ h0S)
    have hTc2 : TcChain m2 S.M E.tcnode0 (chain ++ [(nd, tc)]) := by
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
    have hTo2 : TcOkG D m2 S gl cl (chain ++ [(nd, tc)]) := by
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
    rw [eval_tcF (off := 8) hthis2 (E.field_tcnodeTcell _ _) (by decide) hnd8]
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
      (fun z hz => hg2 _ (hg1 _ hz)) (WorkMonoG.trans hwm1 hg1 hwm2)
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
    have hpn : prevAt E.tcnode0 chain level = nd := by
      have := prevAt_eq E.tcnode0 chain (level - 1) (by omega)
      rw [show level - 1 + 1 = level by omega, hcl] at this
      exact this
    have hmem := List.mem_of_getElem? hcl
    have hndT : nd ∈ tcBlocks E.tcnode0 chain := .tail _ (mem_flat hmem).1
    have hbtT : bt ∈ tcBlocks E.tcnode0 chain := .tail _ (mem_flat hmem).2
    have hf0 : FieldAt m .Mint64 nd 0 (linkAt chain level) :=
      hpn ▸ TcChain.next hTc (i := level) (by omega)
    have hcellAt := TcChain.cell hTc hcl
    wp_step; wp_step; wp_step
    refine wp_tcallocSkip (temps_gss _ _ _)
      ((Keep.unch hu1 (fun e => hbT _ hndT e)).perm _ _ (perm0_of_va64 hf0.writable)) ?_
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_tcF (off := 8) (temps_gss _ _ _) (E.field_tcnodeTcell _ _) (by decide)
      (hcellAt.1.unch' hu1 (fun e => hbT _ hndT e))]
    simp only [E0_append]
    obtain ⟨vals, hva⟩ := hcellAt.2
    exact hQ' _ m1 chain nd bt hS1 hA1 hTc1 hTo1 hcl rfl (fun p hp => .inl hp)
      ⟨vals, hva.unch hu1 (fun e => hbT _ hbtT e)⟩ (hu1.mono fun z hz => .inl hz) hg1 hwm1 (hK1 bnc)
      (by rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _) (temps_gss _ _ _)
      (fun x h1 h2 _ _ _ _ _ => by rw [temps_gso _ _ h2, temps_gso _ _ h1])

end Generic

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
    Wp xi ge f (nodePrologue rest) Q e le m :=
  wp_nodePrologueG h.toG hvU hTc hTo.toG hlen hl1 henc hncA (fun e => hbS (SLoc.mem_blocksG.1 e))
    (fun e => hbW (isWork_dense.1 e)) hbC hge hnct hpar
    fun le' m' chain' nd bt hS hA hTc' hTo' hown htake hold hcell hu hg hwm hK h1 h2 h3 =>
      hQ le' m' chain' nd bt (hS.dense h.gw) hA hTc' hTo'.dense hown htake hold hcell hu hg
        (workMonoG_dense hwm) hK h1 h2 h3

end NautyVerified.Proofs.Search
