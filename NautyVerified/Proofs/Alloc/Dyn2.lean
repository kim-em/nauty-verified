import NautyVerified.Proofs.Alloc.Dyn3

/-!
# `refine1`'s two `DYNALLOC1`s

`refine1` starts with `DYNALLOC1(int, workperm, workperm_sz, n)` and
`DYNALLOC1(int, bucket, bucket_sz, n + 2)`; it keeps its splitter set in a
temporary, so naugraph's `workset` is not touched. `wp_dyn2` runs the two and
reports what `wp_dyn3` reports, with the `workset` pair unchanged.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Source

variable {xi : ExternalCalls}

local notation "WP" => Block.naugraphWorkperm
local notation "WPS" => Block.naugraphWorkpermSz
local notation "WS" => Block.naugraphWorkset
local notation "WSS" => Block.naugraphWorksetSz
local notation "BK" => Block.naugraphBucket
local notation "BKS" => Block.naugraphBucketSz

theorem wp_dyn2 {f : function} {Q : Post} {le : temp_env} {m : mem} {rest : statement}
    {xn t1 t2 t3 t4 msg : ident} {msgLen : Int} {n capP capS capB : Nat}
    {bP bS bB : block}
    (hDP : DynAt m WP WPS 4 capP bP) (hDS : DynAt m WS WSS 8 capS bS)
    (hDB : DynAt m BK BKS 4 capB bB)
    (hxn : PTree.get xn le = some (.Vint (ir n))) (hn : n + 2 < 2147483648)
    (hn1 : xn ≠ t1 ∧ xn ≠ t2)
    (hP : 0 < capP → bP ≠ WS ∧ bP ≠ WSS ∧ bP ≠ BK ∧ bP ≠ BKS ∧ (0 < capS → bP ≠ bS) ∧
      (0 < capB → bP ≠ bB))
    (hS : 0 < capS → bS ≠ WP ∧ bS ≠ WPS ∧ bS ≠ BK ∧ bS ≠ BKS ∧ (0 < capB → bS ≠ bB))
    (hB : 0 < capB → bB ≠ WP ∧ bB ≠ WPS ∧ bB ≠ WS ∧ bB ≠ WSS)
    (hQ : ∀ le' m' capP' bP' capB' bB',
      DynAt m' WP WPS 4 capP' bP' → DynAt m' WS WSS 8 capS bS → DynAt m' BK BKS 4 capB' bB' →
      n ≤ capP' → n + 2 ≤ capB' →
      ((capP' = capP ∧ bP' = bP) ∨ ¬ Mem.valid_block m bP') →
      ((capB' = capB ∧ bB' = bB) ∨ ¬ Mem.valid_block m bB') →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ k, k ≠ t1 → k ≠ t2 → k ≠ t3 → k ≠ t4 → PTree.get k le' = PTree.get k le) →
      Unch m m' (dyn3Set m capP bP capS bS capB bB) →
      (0 < capP' → 0 < capS → bP' ≠ bS) → (0 < capP' → 0 < capB' → bP' ≠ bB') →
      (0 < capS → 0 < capB' → bS ≠ bB') →
      Wp xi ge f rest Q empty_env le' m') :
    Wp xi ge f
      (.Ssequence (dynalloc1 dense.id.«naugraph:workperm_sz» dense.id.«naugraph:workperm» tint
          (.Etempvar xn tint) t1 t2 msg msgLen)
        (.Ssequence (dynalloc1 dense.id.«naugraph:bucket_sz» dense.id.«naugraph:bucket» tint
            (.Ebinop .Oadd (.Etempvar xn tint) (ci 2 tint) tint) t3 t4 msg msgLen) rest))
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
  have hP'v : 0 < capP' → Mem.valid_block m1 bP' := fun hc => Malloced.valid (hDP1.mal hc)
  -- bucket
  wp_step
  refine wp_dynalloc1' (c := 4) (n := n + 2)
    (le := le1) (elt := tint) (msg := msg) (msgLen := msgLen) (t1 := t3) (t2 := t4)
    (szE := .Ebinop .Oadd (.Etempvar xn tint) (ci 2 tint) tint) find_naugraphBucketSz
    find_naugraphBucket rfl hDB1
    (fun _ => by
      simp only [Exec.evalExpr, ho1 _ hn1.1 hn1.2, hxn, typeof, cop, ir_add]
      push_cast; rfl) rfl hn (by omega) ?_
  intro le3 m3 capB' bB' hDB3 hcB huB hbB' hgB ho3
  have hbB'm : (capB' = capB ∧ bB' = bB) ∨ ¬ Mem.valid_block m bB' :=
    hbB'.imp_right fun h hv => h (hgP _ hv)
  have nB : ∀ {cap cap' : Nat} {b b' : block}, ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') →
      (0 < cap → b ≠ BK ∧ b ≠ BKS ∧ (0 < capB → b ≠ bB)) → 0 < cap' →
      Mem.valid_block m1 b' → ¬ (b' = BKS ∨ b' = BK ∨ (0 < capB ∧ b' = bB) ∨
        (¬ Mem.valid_block m1 bB' ∧ b' = bB')) := by
    intro cap cap' b b' hb' hb hc hv
    refine not_dynSet hv ?_ ?_ ?_
    · exact Ne.symm (ne_new hb' hvBKS (fun hc h => (hb hc).2.1 h.symm) hc)
    · exact Ne.symm (ne_new hb' hvBK (fun hc h => (hb hc).1 h.symm) hc)
    · exact fun hcb => Ne.symm (ne_new hb' (Malloced.valid (hDB.mal hcb))
        (fun hc h => (hb hc).2.2 hcb h.symm) hc)
  have hDP3 : DynAt m3 WP WPS 4 capP' bP' :=
    hDP1.keep huB (not_dynSet (hgP _ hvWP) (by decide) (by decide)
        fun hc h => (hB hc).1 h.symm)
      (not_dynSet (hgP _ hvWPS) (by decide) (by decide) fun hc h => (hB hc).2.1 h.symm)
      fun hc => Keep.unch huB (nB hbP' (fun hc => ⟨(hP hc).2.2.1, (hP hc).2.2.2.1,
        (hP hc).2.2.2.2.2⟩) hc (hP'v hc))
  have hDS3 : DynAt m3 WS WSS 8 capS bS :=
    hDS1.keep huB (not_dynSet (hgP _ hvWS) (by decide) (by decide)
        fun hc h => (hB hc).2.2.1 h.symm)
      (not_dynSet (hgP _ hvWSS) (by decide) (by decide) fun hc h => (hB hc).2.2.2 h.symm)
      fun hc => Keep.unch huB (nB (.inl ⟨rfl, rfl⟩) (fun hc => ⟨(hS hc).2.2.1, (hS hc).2.2.2.1,
        (hS hc).2.2.2.2⟩) hc (hgP _ (Malloced.valid (hDS.mal hc))))
  simp only [seqPost, Post.after, E0_append]
  refine hQ le3 m3 capP' bP' capB' bB' hDP3 hDS3 hDB3 hcP hcB hbP' hbB'm
    (fun z hz => hgB _ (hgP _ hz)) (fun k h1 h2 h3 h4 => by
      rw [ho3 k h3 h4, ho1 k h1 h2]) ?_ ?_ ?_ ?_
  · refine (huP.mono fun z hz => ?_).trans (huB.mono fun z hz => ?_)
    · rcases hz with h | h | h | ⟨hv, rfl⟩
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr hv))))))))
    · rcases hz with h | h | h | ⟨hv, rfl⟩
      · exact .inr (.inr (.inr (.inr (.inl h))))
      · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          fun h => hv (hgP _ h)))))))))
  · intro hc hcs h
    rcases hbP' with ⟨rfl, rfl⟩ | hnv
    · exact (hP hc).2.2.2.2.1 hcs h
    · exact hnv (h ▸ Malloced.valid (hDS.mal hcs))
  · intro hc hcb h
    rcases hbB' with ⟨rfl, rfl⟩ | hnv
    · exact (nB hbP' (fun hc => ⟨(hP hc).2.2.1, (hP hc).2.2.2.1, (hP hc).2.2.2.2.2⟩) hc
        (hP'v hc)) (.inr (.inr (.inl ⟨hcb, h⟩)))
    · exact hnv (h ▸ hP'v hc)
  · intro hcs hcb h
    rcases hbB' with ⟨rfl, rfl⟩ | hnv
    · exact (hS hcs).2.2.2.2 hcb h
    · exact hnv (h ▸ hgP _ (Malloced.valid (hDS.mal hcs)))

end NautyVerified.Proofs.Alloc
