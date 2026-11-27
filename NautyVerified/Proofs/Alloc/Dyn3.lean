import NautyVerified.Proofs.Alloc.Keep
import NautyVerified.Proofs.Alloc.Blocks

/-!
# naugraph.c's three `DYNALLOC1`s

`bestcell` and `refine` both start with
`DYNALLOC1(int, workperm, workperm_sz, n)`,
`DYNALLOC1(set, workset, workset_sz, m)` and
`DYNALLOC1(int, bucket, bucket_sz, n + 2)`. `wp_dyn3` runs the three and
reports the new `DynAt`s, their capacities, where each new block came from,
and one `Unch` for the whole prologue.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Source

variable {xi : ExternalCalls}

theorem Malloced.valid {m : mem} {b : block} {N : Nat} (h : Malloced m b N) :
    Mem.valid_block m b :=
  Mem.perm_valid_block _ _ _ _ _ (h.perm (-1) (by decide) (by omega))

/-- A block valid before a `DYNALLOC1` and none of the blocks it changes is untouched. -/
theorem not_dynSet {m : mem} {z gs gp b b' : block} {cap : Nat} (hv : Mem.valid_block m z)
    (h1 : z ≠ gs) (h2 : z ≠ gp) (h3 : 0 < cap → z ≠ b) :
    ¬ (z = gs ∨ z = gp ∨ (0 < cap ∧ z = b) ∨ (¬ Mem.valid_block m b' ∧ z = b')) := by
  rintro (h | h | ⟨hc, h⟩ | ⟨hb, rfl⟩)
  · exact h1 h
  · exact h2 h
  · exact h3 hc h
  · exact hb hv

/-- The block a `DYNALLOC1` leaves is the old one or was not valid before. -/
theorem ne_new {m : mem} {z b b' : block} {cap cap' : Nat}
    (hb' : (cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') (hv : Mem.valid_block m z)
    (hz : 0 < cap → z ≠ b) (hc : 0 < cap') : z ≠ b' := by
  rcases hb' with ⟨rfl, rfl⟩ | hnv
  · exact hz hc
  · exact fun h => hnv (h ▸ hv)

local notation "WP" => Block.naugraphWorkperm
local notation "WPS" => Block.naugraphWorkpermSz
local notation "WS" => Block.naugraphWorkset
local notation "WSS" => Block.naugraphWorksetSz
local notation "BK" => Block.naugraphBucket
local notation "BKS" => Block.naugraphBucketSz

/-- The blocks the three allocations may change. -/
def dyn3Set (m : mem) (capP : Nat) (bP : block) (capS : Nat) (bS : block) (capB : Nat)
    (bB : block) (z : block) : Prop :=
  z = WPS ∨ z = WP ∨ z = WSS ∨ z = WS ∨ z = BKS ∨ z = BK ∨ (0 < capP ∧ z = bP) ∨
    (0 < capS ∧ z = bS) ∨ (0 < capB ∧ z = bB) ∨ ¬ Mem.valid_block m z

theorem wp_dyn3 {f : function} {Q : Post} {le : temp_env} {m : mem} {rest : statement}
    {xn xm t1 t2 t3 t4 t5 t6 msg : ident} {msgLen : Int} {n M capP capS capB : Nat}
    {bP bS bB : block}
    (hDP : DynAt m WP WPS 4 capP bP) (hDS : DynAt m WS WSS 8 capS bS)
    (hDB : DynAt m BK BKS 4 capB bB)
    (hxn : PTree.get xn le = some (.Vint (ir n))) (hxm : PTree.get xm le = some (.Vint (ir M)))
    (hn : n + 2 < 2147483648) (hM : M < 2147483648)
    (hm1 : xm ≠ t1 ∧ xm ≠ t2) (hn1 : xn ≠ t1 ∧ xn ≠ t2 ∧ xn ≠ t3 ∧ xn ≠ t4)
    (hP : 0 < capP → bP ≠ WS ∧ bP ≠ WSS ∧ bP ≠ BK ∧ bP ≠ BKS ∧ (0 < capS → bP ≠ bS) ∧
      (0 < capB → bP ≠ bB))
    (hS : 0 < capS → bS ≠ WP ∧ bS ≠ WPS ∧ bS ≠ BK ∧ bS ≠ BKS ∧ (0 < capB → bS ≠ bB))
    (hB : 0 < capB → bB ≠ WP ∧ bB ≠ WPS ∧ bB ≠ WS ∧ bB ≠ WSS)
    (hQ : ∀ le' m' capP' bP' capS' bS' capB' bB',
      DynAt m' WP WPS 4 capP' bP' → DynAt m' WS WSS 8 capS' bS' → DynAt m' BK BKS 4 capB' bB' →
      n ≤ capP' → M ≤ capS' → n + 2 ≤ capB' →
      ((capP' = capP ∧ bP' = bP) ∨ ¬ Mem.valid_block m bP') →
      ((capS' = capS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS') →
      ((capB' = capB ∧ bB' = bB) ∨ ¬ Mem.valid_block m bB') →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ k, k ≠ t1 → k ≠ t2 → k ≠ t3 → k ≠ t4 → k ≠ t5 → k ≠ t6 →
        PTree.get k le' = PTree.get k le) →
      Unch m m' (dyn3Set m capP bP capS bS capB bB) →
      (0 < capP' → 0 < capS' → bP' ≠ bS') → (0 < capP' → 0 < capB' → bP' ≠ bB') →
      (0 < capS' → 0 < capB' → bS' ≠ bB') →
      Wp xi ge f rest Q empty_env le' m') :
    Wp xi ge f
      (.Ssequence (dynalloc1 dense.id.«naugraph:workperm_sz» dense.id.«naugraph:workperm» tint
          (.Etempvar xn tint) t1 t2 msg msgLen)
        (.Ssequence (dynalloc1 dense.id.«naugraph:workset_sz» dense.id.«naugraph:workset» tulong
            (.Etempvar xm tint) t3 t4 msg msgLen)
          (.Ssequence (dynalloc1 dense.id.«naugraph:bucket_sz» dense.id.«naugraph:bucket» tint
            (.Ebinop .Oadd (.Etempvar xn tint) (ci 2 tint) tint) t5 t6 msg msgLen) rest)))
      Q empty_env le m := by
  have hvWP : Mem.valid_block m WP := valid_of_access hDP.bpW
  have hvWPS : Mem.valid_block m WPS := valid_of_access hDP.bsW
  have hvWS : Mem.valid_block m WS := valid_of_access hDS.bpW
  have hvWSS : Mem.valid_block m WSS := valid_of_access hDS.bsW
  have hvBK : Mem.valid_block m BK := valid_of_access hDB.bpW
  have hvBKS : Mem.valid_block m BKS := valid_of_access hDB.bsW
  -- workperm
  wp_step
  refine wp_dynalloc1 (c := 4) find_naugraphWorkpermSz find_naugraphWorkperm rfl hDP hxn
    (by omega) (by omega) ?_
  intro le1 m1 capP' bP' hDP1 hcP huP hbP' hgP ho1
  have hDS1 : DynAt m1 WS WSS 8 capS bS :=
    hDS.keep huP (not_dynSet hvWS (by decide) (by decide) fun hc h => (hP hc).1 h.symm)
      (not_dynSet hvWSS (by decide) (by decide) fun hc h => (hP hc).2.1 h.symm)
      fun hc => Keep.unch huP (not_dynSet (Malloced.valid (hDS.mal hc)) (hS hc).2.1 (hS hc).1
        fun hcP h => (hP hcP).2.2.2.2.1 hc h.symm)
  have hDB1 : DynAt m1 BK BKS 4 capB bB :=
    hDB.keep huP (not_dynSet hvBK (by decide) (by decide) fun hc h => (hP hc).2.2.1 h.symm)
      (not_dynSet hvBKS (by decide) (by decide) fun hc h => (hP hc).2.2.2.1 h.symm)
      fun hc => Keep.unch huP (not_dynSet (Malloced.valid (hDB.mal hc)) (hB hc).2.1 (hB hc).1
        fun hcP h => (hP hcP).2.2.2.2.2 hc h.symm)
  -- workset
  wp_step
  refine wp_dynalloc1 (c := 8) (n := M) find_naugraphWorksetSz find_naugraphWorkset rfl hDS1
    (by rw [ho1 _ hm1.1 hm1.2]; exact hxm) hM (by omega) ?_
  intro le2 m2 capS' bS' hDS2 hcS huS hbS' hgS ho2
  have hP'v : 0 < capP' → Mem.valid_block m1 bP' := fun hc => Malloced.valid (hDP1.mal hc)
  have nPS : ∀ z, z = WS ∨ z = WSS ∨ (0 < capS ∧ z = bS) → 0 < capP' → bP' ≠ z := by
    rintro z (rfl | rfl | ⟨hcs, rfl⟩) hc
    · exact Ne.symm (ne_new hbP' hvWS (fun hc h => (hP hc).1 h.symm) hc)
    · exact Ne.symm (ne_new hbP' hvWSS (fun hc h => (hP hc).2.1 h.symm) hc)
    · exact Ne.symm (ne_new hbP' (Malloced.valid (hDS.mal hcs)) (fun hc h => (hP hc).2.2.2.2.1 hcs
        h.symm) hc)
  have hDP2 : DynAt m2 WP WPS 4 capP' bP' :=
    hDP1.keep huS (not_dynSet (hgP _ hvWP) (by decide) (by decide) fun hc h => (hS hc).1 h.symm)
      (not_dynSet (hgP _ hvWPS) (by decide) (by decide) fun hc h => (hS hc).2.1 h.symm)
      fun hc => Keep.unch huS (not_dynSet (hP'v hc) (nPS _ (.inr (.inl rfl)) hc)
        (nPS _ (.inl rfl) hc) fun hcs => nPS _ (.inr (.inr ⟨hcs, rfl⟩)) hc)
  have hDB2 : DynAt m2 BK BKS 4 capB bB :=
    hDB1.keep huS (not_dynSet (hgP _ hvBK) (by decide) (by decide) fun hc h => (hS hc).2.2.1 h.symm)
      (not_dynSet (hgP _ hvBKS) (by decide) (by decide) fun hc h => (hS hc).2.2.2.1 h.symm)
      fun hc => Keep.unch huS (not_dynSet (hgP _ (Malloced.valid (hDB.mal hc))) (hB hc).2.2.2
        (hB hc).2.2.1 fun hcs h => (hS hcs).2.2.2.2 hc h.symm)
  -- bucket
  wp_step
  refine wp_dynalloc1' (c := 4) (n := n + 2)
    (le := le2) (elt := tint) (msg := msg) (msgLen := msgLen) (t1 := t5) (t2 := t6) (szE := .Ebinop .Oadd (.Etempvar xn tint) (ci 2 tint) tint) find_naugraphBucketSz find_naugraphBucket rfl hDB2
    (fun _ => by
      simp only [Exec.evalExpr, ho2 _ hn1.2.2.1 hn1.2.2.2, ho1 _ hn1.1 hn1.2.1, hxn, typeof, cop,
        ir_add]
      push_cast; rfl) rfl hn (by omega) ?_
  intro le3 m3 capB' bB' hDB3 hcB huB hbB' hgB ho3
  have hS'v : 0 < capS' → Mem.valid_block m2 bS' := fun hc => Malloced.valid (hDS2.mal hc)
  have hbS'm : (capS' = capS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS' :=
    hbS'.imp_right fun h hv => h (hgP _ hv)
  have hbB'm : (capB' = capB ∧ bB' = bB) ∨ ¬ Mem.valid_block m bB' :=
    hbB'.imp_right fun h hv => h (hgS _ (hgP _ hv))
  -- the new workperm and workset blocks are not the bucket globals or the old bucket
  have nB : ∀ {cap cap' : Nat} {b b' : block}, ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') →
      (0 < cap → b ≠ BK ∧ b ≠ BKS ∧ (0 < capB → b ≠ bB)) → 0 < cap' →
      Mem.valid_block m2 b' → ¬ (b' = BKS ∨ b' = BK ∨ (0 < capB ∧ b' = bB) ∨
        (¬ Mem.valid_block m2 bB' ∧ b' = bB')) := by
    intro cap cap' b b' hb' hb hc hv
    refine not_dynSet hv ?_ ?_ ?_
    · exact Ne.symm (ne_new hb' hvBKS (fun hc h => (hb hc).2.1 h.symm) hc)
    · exact Ne.symm (ne_new hb' hvBK (fun hc h => (hb hc).1 h.symm) hc)
    · exact fun hcb => Ne.symm (ne_new hb' (Malloced.valid (hDB.mal hcb))
        (fun hc h => (hb hc).2.2 hcb h.symm) hc)
  have hDP3 : DynAt m3 WP WPS 4 capP' bP' :=
    hDP2.keep huB (not_dynSet (hgS _ (hgP _ hvWP)) (by decide) (by decide)
        fun hc h => (hB hc).1 h.symm)
      (not_dynSet (hgS _ (hgP _ hvWPS)) (by decide) (by decide) fun hc h => (hB hc).2.1 h.symm)
      fun hc => Keep.unch huB (nB hbP' (fun hc => ⟨(hP hc).2.2.1, (hP hc).2.2.2.1,
        (hP hc).2.2.2.2.2⟩) hc (hgS _ (hP'v hc)))
  have hDS3 : DynAt m3 WS WSS 8 capS' bS' :=
    hDS2.keep huB (not_dynSet (hgS _ (hgP _ hvWS)) (by decide) (by decide)
        fun hc h => (hB hc).2.2.1 h.symm)
      (not_dynSet (hgS _ (hgP _ hvWSS)) (by decide) (by decide) fun hc h => (hB hc).2.2.2 h.symm)
      fun hc => Keep.unch huB (nB hbS'm (fun hc => ⟨(hS hc).2.2.1, (hS hc).2.2.2.1,
        (hS hc).2.2.2.2⟩) hc (hS'v hc))
  simp only [seqPost, Post.after, E0_append]
  refine hQ le3 m3 capP' bP' capS' bS' capB' bB' hDP3 hDS3 hDB3 hcP hcS hcB hbP' hbS'm hbB'm
    (fun z hz => hgB _ (hgS _ (hgP _ hz))) (fun k h1 h2 h3 h4 h5 h6 => by
      rw [ho3 k h5 h6, ho2 k h3 h4, ho1 k h1 h2]) ?_ ?_ ?_ ?_
  · refine ((huP.mono fun z hz => ?_).trans (huS.mono fun z hz => ?_)).trans (huB.mono fun z hz => ?_)
    · rcases hz with h | h | h | ⟨hv, rfl⟩
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr hv))))))))
    · rcases hz with h | h | h | ⟨hv, rfl⟩
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl h)))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr fun h => hv (hgP _ h)))))))))
    · rcases hz with h | h | h | ⟨hv, rfl⟩
      · exact .inr (.inr (.inr (.inr (.inl h))))
      · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          fun h => hv (hgS _ (hgP _ h))))))))))
  · intro hc hcs h
    rcases hbS' with ⟨rfl, rfl⟩ | hnv
    · exact (nPS _ (.inr (.inr ⟨hcs, rfl⟩)) hc) h
    · exact hnv (h ▸ hP'v hc)
  · intro hc hcb h
    rcases hbB' with ⟨rfl, rfl⟩ | hnv
    · exact (nB hbP' (fun hc => ⟨(hP hc).2.2.1, (hP hc).2.2.2.1, (hP hc).2.2.2.2.2⟩) hc
        (hgS _ (hP'v hc))) (.inr (.inr (.inl ⟨hcb, h⟩)))
    · exact hnv (h ▸ hgS _ (hP'v hc))
  · intro hc hcb h
    rcases hbB' with ⟨rfl, rfl⟩ | hnv
    · exact (nB hbS'm (fun hc => ⟨(hS hc).2.2.1, (hS hc).2.2.2.1, (hS hc).2.2.2.2⟩) hc
        (hS'v hc)) (.inr (.inr (.inl ⟨hcb, h⟩)))
    · exact hnv (h ▸ hS'v hc)

end NautyVerified.Proofs.Alloc
