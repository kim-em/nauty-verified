import NautyVerified.Proofs.Doref.Syntax
import NautyVerified.Proofs.Refine.Fn
import NautyVerified.Logic.OfPre

/-!
# `doref` with no vertex invariant

`dorefSpec`: with `invarproc = NULL`, nauty's `doref` reallocates nautil.c's
`workperm`, calls `refproc` (any `RefineFn`, so `refine` or `refine1`) on its
arguments and sets `*qinvar = 0`. Its postcondition is `refineSpec`'s, for the
memory after the allocation, followed by the store to `*qinvar`.
-/

namespace NautyVerified.Proofs.Doref

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Refine (Loc refineSpec RefineFn)
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

section
variable {ge : genv} [E : NautyEnv ge]
set_option linter.unusedSectionVars false

local notation "NWP" => E.nautilWorkperm
local notation "NWPS" => E.nautilWorkpermSz

variable {xi : ExternalCalls} in
/-- `if (c) x = v;` for a condition that evaluates, and a value `v` that evaluates. -/
theorem wp_ifSet {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {c v : expr}
    {x : ident} {cv : val} {b : Bool}
    (hc : Exec.evalExpr ge e le m c = some cv)
    (hb : Cfrontend.Cop.bool_val cv (typeof c) m = some b) {w : val}
    (hv : Exec.evalExpr ge e le m v = some w)
    (hQ : ∀ le', (∀ k, k ≠ x → PTree.get k le' = PTree.get k le) → Q.normal E0 e le' m) :
    Wp xi ge f (.Sifthenelse c (.Ssequence .Sskip (.Sset x v)) .Sskip) Q e le m := by
  apply wp_if_eval
  rw [hc]
  simp only [hb]
  cases b
  · exact wp_skip (hQ le fun _ _ => rfl)
  · simp only [ite_true]
    wp_step; wp_step
    apply wp_set_eval
    rw [hv]
    exact hQ _ fun k hk => temps_gso _ _ hk

variable {xi : ExternalCalls} in
/-- `if (c) x = v1; else x = v2;`, both values evaluating. -/
theorem wp_ifSet2 {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {c v1 v2 : expr}
    {x : ident} {cv : val} {b : Bool}
    (hc : Exec.evalExpr ge e le m c = some cv)
    (hb : Cfrontend.Cop.bool_val cv (typeof c) m = some b) {w1 w2 : val}
    (hv1 : Exec.evalExpr ge e le m v1 = some w1) (hv2 : Exec.evalExpr ge e le m v2 = some w2)
    (hQ : ∀ le', (∀ k, k ≠ x → PTree.get k le' = PTree.get k le) →
      (∃ w, PTree.get x le' = some w) → Q.normal E0 e le' m) :
    Wp xi ge f (.Sifthenelse c (.Ssequence .Sskip (.Sset x v1)) (.Ssequence .Sskip (.Sset x v2)))
      Q e le m := by
  apply wp_if_eval
  rw [hc]
  simp only [hb]
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    wp_step; wp_step
    apply wp_set_eval
    rw [hv2]
    exact hQ _ (fun k hk => temps_gso _ _ hk) ⟨_, temps_gss _ _ _⟩
  · simp only [ite_true]
    wp_step; wp_step
    apply wp_set_eval
    rw [hv1]
    exact hQ _ (fun k hk => temps_gso _ _ hk) ⟨_, temps_gss _ _ _⟩

/-- `p != NULL` is false for `p = NULL`. -/
theorem ne_null [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
    (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
    (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (ce : Cfrontend.Ctypes.composite_env) (m : mem) (t : Cfrontend.Ctypes.type) :
    Cfrontend.Cop.sem_binary_operation ce .One Vnullptr (tptr t)
      (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
      (tptr .Tvoid) m = some (Val.of_bool false) := rfl

/-- The arguments `doref` passes on to `refproc`. -/
def refArgs (L : Loc) (n : Nat) : List val :=
  [.Vptr L.bg L.gofs, .Vptr L.bl L.lofs, .Vptr L.bp L.pofs, .Vint (ir L.level), .Vptr L.bn L.nofs,
   .Vptr L.bc L.cofs, .Vptr L.ba L.aofs, .Vptr L.bk L.kofs, .Vint (ir L.M), .Vint (ir n)]

/-- The set `DYNALLOC1` of nautil.c's `workperm` may change. -/
abbrev NSet (m : mem) (capN : Nat) (bN : block) (z : block) : Prop :=
  z = NWPS ∨ z = NWP ∨ (0 < capN ∧ z = bN) ∨ ¬ Mem.valid_block m z

/-- `doref` with any refinement procedure `bf` satisfying `RS` on `refArgs L n`:
`RS.pre` holds after nautil.c's `DYNALLOC1` (which changes only `NSet`), and a
call of `bf` after it leaves `*qinvar` and nautil.c's `workperm` pair alone. -/
def dorefSpecR {n : Nat} (xi : ExternalCalls) (RS : FunSpec) (L : Loc) (aw : Nat → Lib.Integers.int64)
    (bq : block) (qofs : ptrofs) (bf : block) (mi ma ia dg : Lib.Integers.int) (capN : Nat)
    (bN : block) : FunSpec where
  pre args m := args = [.Vptr L.bg L.gofs, .Vptr L.bl L.lofs, .Vptr L.bp L.pofs,
      .Vint (ir L.level), .Vptr L.bn L.nofs, .Vptr bq qofs, .Vptr L.bc L.cofs, .Vptr L.ba L.aofs,
      .Vptr L.bk L.kofs, .Vptr bf Ptrofs.zero, Vnullptr, .Vint mi, .Vint ma, .Vint ia, .Vint dg,
      .Vint (ir L.M), .Vint (ir n)] ∧
    (∃ fd, Genv.find_funct ge.genv_genv (.Vptr bf Ptrofs.zero) = some fd ∧
      type_of_fundef fd = Refine.refprocType ∧ Satisfies xi ge fd RS) ∧
    (∀ m₁, Unch m m₁ (NSet m capN bN) → (∀ z, Mem.valid_block m z → Mem.valid_block m₁ z) →
      RS.pre (refArgs L n) m₁) ∧
    (∀ m₁ c' b', Unch m m₁ (NSet m capN bN) → (∀ z, Mem.valid_block m z → Mem.valid_block m₁ z) →
      DynAt m₁ NWP NWPS 4 c' b' → ((c' = capN ∧ b' = bN) ∨ ¬ Mem.valid_block m b') →
      ∀ t v m₂, RS.post (refArgs L n) m₁ t v m₂ → t = E0 ∧
        ∃ W : block → Prop, Unch m₁ m₂ W ∧ ¬ W bq ∧ ¬ W NWP ∧ ¬ W NWPS ∧ (0 < c' → ¬ W b')) ∧
    ArrayAt m .Mint64 L.ba L.ab (longs aw) L.M ∧ Nextelement.LeftbitTable m ∧
    (∀ z ∈ [L.ba, E.leftbit], Mem.valid_block m z ∧ z ≠ NWP ∧ z ≠ NWPS ∧ (0 < capN → z ≠ bN)) ∧
    0 < L.M ∧ L.M < 33554432 ∧ 0 < n ∧ n < 1073741824 ∧
    DynAt m NWP NWPS 4 capN bN ∧
    (∃ qv, ArrayAt m .Mint32 bq (intOfZ (Ptrofs.unsigned qofs)) qv 1) ∧ Mem.valid_block m bq ∧
    bq ≠ NWP ∧ bq ≠ NWPS ∧ (0 < capN → bq ≠ bN)
  post _ m t _ m' := t = E0 ∧ ∃ m₁ m₂ capN' bN',
    Unch m m₁ (fun z => z = NWPS ∨ z = NWP ∨ (0 < capN ∧ z = bN) ∨ ¬ Mem.valid_block m z) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m₁ z) ∧
    (∃ v₁, RS.post (refArgs L n) m₁ E0 v₁ m₂) ∧
    Unch m₂ m' (· = bq) ∧ Alloc.KeepA m₂ m' ∧
    ArrayAt m' .Mint32 bq (intOfZ (Ptrofs.unsigned qofs)) (fun _ => .Vint (ir 0)) 1 ∧
    DynAt m' NWP NWPS 4 capN' bN' ∧ n ≤ capN' ∧
    ((capN' = capN ∧ bN' = bN) ∨ ¬ Mem.valid_block m bN') ∧
    (0 < capN' → Mem.valid_block m₁ bN')

/-- The temporaries on entry. -/
def entryTemps (L : Loc) (n : Nat) (bq : block) (qofs : ptrofs) (bf : block)
    (mi ma ia dg : Lib.Integers.int) : temp_env :=
  PTree.set dense.id.n (.Vint (ir n)) (PTree.set dense.id.m (.Vint (ir L.M))
  (PTree.set dense.id.digraph (.Vint dg) (PTree.set dense.id.invararg (.Vint ia)
  (PTree.set dense.id.maxinvarlev (.Vint ma) (PTree.set dense.id.mininvarlev (.Vint mi)
  (PTree.set dense.id.invarproc Vnullptr (PTree.set dense.id.refproc (.Vptr bf Ptrofs.zero)
  (PTree.set dense.id.code (.Vptr L.bk L.kofs) (PTree.set dense.id.active (.Vptr L.ba L.aofs)
  (PTree.set dense.id.invar (.Vptr L.bc L.cofs) (PTree.set dense.id.qinvar (.Vptr bq qofs)
  (PTree.set dense.id.numcells (.Vptr L.bn L.nofs) (PTree.set dense.id.level (.Vint (ir L.level))
  (PTree.set dense.id.ptn (.Vptr L.bp L.pofs) (PTree.set dense.id.lab (.Vptr L.bl L.lofs)
  (PTree.set dense.id.g (.Vptr L.bg L.gofs)
    (create_undef_temps dense.fn.doref.fn_temps)))))))))))))))))

theorem doref_satisfiesR {xi : ExternalCalls} {n : Nat} (RS : FunSpec) (L : Loc)
    (aw : Nat → Lib.Integers.int64) (bq : block) (qofs : ptrofs) (bf : block)
    (mi ma ia dg : Lib.Integers.int) (capN : Nat) (bN : block) :
    Satisfies xi ge (.Internal dense.fn.doref)
      (dorefSpecR (n := n) xi RS L aw bq qofs bf mi ma ia dg capN bN) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps L n bq qofs bf mi ma ia dg ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps L n bq qofs bf mi ma ia dg, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩,
      rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, ⟨fd, hfd, hfty, hsat⟩, hcarry, hframe, hact, hleft, hsepA, hM1, hMl, hn0,
      hnl, hDN, ⟨qv, hq⟩, hvq, hqN, hqNS, hqbN⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [dense.fn.doref.fn_body_eq, body_eq]
    simp only [body]
    -- `DYNALLOC1(int, workperm, workperm_sz, n)` of nautil.c
    wp_step
    refine Alloc.wp_dynalloc1 (c := 4) (n := n) E.find_nautilWorkpermSz E.find_nautilWorkperm rfl hDN
      (by simp (config := {decide := true}) only [entryTemps, temps_gss]) (by omega) (by omega) ?_
    intro le1 m1 capN' bN' hDN1 hcN huN hbN' hgN ho1
    have huN' : Unch m m1 (NSet m capN bN) := huN.mono fun z hz => by
      rcases hz with h | h | h | ⟨hnv, rfl⟩
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr hnv))
    have sA := hsepA L.ba (by simp)
    have sL := hsepA E.leftbit (by simp)
    have hactM := hact.unch huN (Alloc.not_dynSet sA.1 sA.2.2.1 sA.2.1 sA.2.2.2)
    have hleft1 : Nextelement.LeftbitTable m1 := fun i hi => by
      rw [huN.load _ _ _ (Alloc.not_dynSet sL.1 sL.2.2.1 sL.2.1 sL.2.2.2)]; exact hleft i hi
    have hT1 : ∀ k, k ≠ idOf 703 → k ≠ idOf 704 →
        PTree.get k le1 = PTree.get k (entryTemps L n bq qofs bf mi ma ia dg) := ho1
    have hact1 : PTree.get dense.id.active le1 = some (.Vptr L.ba L.aofs) := by
      rw [hT1 _ (by decide) (by decide)]
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have hm1' : PTree.get dense.id.m le1 = some (.Vint (ir L.M)) := by
      rw [hT1 _ (by decide) (by decide)]
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine wp_call (vf := .Vptr E.nextelement Ptrofs.zero) (targs := [tptr tulong, tint, tint])
      (tres := tint) (cc := Common.AST.cc_default) _ (Nextelement.nextSpec L.ba L.aofs L.M (-1) aw)
      (Nextelement.nextelement_satisfies _ _ _ _ _) rfl
      (by simp only [Exec.evalExpr, Exec.lvalOfVar,
        show PTree.get Source.dense.id.nextelement (empty_env : env) = none from rfl,
        E.find_nextelement, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
      (by simp only [Exec.evalExprlist, Exec.evalExpr, hact1, hm1', Refine.tv, Set.pv, typeof, cop]; rfl)
      (by simp [Common.Globalenvs.Genv.find_funct, E.funct_nextelement]) Isautom.type_nextelement
      ⟨rfl, by decide, by omega, hM1, by omega, Graph.wordsAt_of hactM, hleft1⟩ ?_
    rintro t r m2 ⟨rfl, hmm, r, rfl, -⟩
    rw [hmm]
    simp only [set_opttemp, seqPost, Post.after, E0_append]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, Refine.tv]
    refine wp_ifSet (by simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, temps_gss,
      Refine.tv, typeof, cop]; exact rfl) (by simp only [typeof, cop]; exact rfl)
      (by simp only [Exec.evalExpr]; exact rfl) ?_
    intro le2 ho2
    have hT2 : ∀ k, k ≠ dense.id.tvpos → k ≠ idOf 706 → k ≠ idOf 705 → k ≠ idOf 703 →
        k ≠ idOf 704 → PTree.get k le2 = PTree.get k (entryTemps L n bq qofs bf mi ma ia dg) :=
      fun k h1 h2 h3 h4 h5 => by
        rw [ho2 k h1, temps_gso _ _ h1, temps_gso _ _ h2, temps_gso _ _ h3, hT1 k h4 h5]
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    simp only [refcall]
    refine wp_call (vf := .Vptr bf Ptrofs.zero) fd _ hsat
      ?_ ?_ ?_ hfd hfty (hcarry m1 huN' hgN) ?_
    · rfl
    · simp only [Exec.evalExpr]
      rw [hT2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode]
    · simp only [Exec.evalExprlist, Exec.evalExpr, Set.pv, Refine.pi, Refine.tv]
      have e : ∀ x, x = dense.id.g ∨ x = dense.id.lab ∨ x = dense.id.ptn ∨ x = dense.id.level ∨
          x = dense.id.numcells ∨ x = dense.id.invar ∨ x = dense.id.active ∨ x = dense.id.code ∨
          x = dense.id.m ∨ x = dense.id.n →
          PTree.get x le2 = PTree.get x (entryTemps L n bq qofs bf mi ma ia dg) := by
        intro x hx
        apply hT2 <;> rintro rfl <;> revert hx <;> decide
      rw [e dense.id.g (by simp), e dense.id.lab (by simp), e dense.id.ptn (by simp),
        e dense.id.level (by simp), e dense.id.numcells (by simp), e dense.id.invar (by simp),
        e dense.id.active (by simp), e dense.id.code (by simp), e dense.id.m (by simp),
        e dense.id.n (by simp)]
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss, typeof, cop]
      rfl
    · rintro t v m2 hpost
      have hpost' := hpost
      obtain ⟨rfl, W2, hu2, nq, nNWP, nNWPS, nbN⟩ := hframe m1 capN' bN' huN' hgN hDN1 hbN' t v m2 hpost
      simp only [set_opttemp, seqPost, Post.after, E0_append]
      -- minlev, maxlev
      have hmi2 : PTree.get dense.id.mininvarlev le2 = some (.Vint mi) := by
        rw [hT2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
      wp_step; wp_step; wp_step; wp_step
      apply wp_ifSet2
      · simp only [Exec.evalExpr, Refine.tv, hmi2]; exact rfl
      · simp only [typeof, cop]; exact rfl
      · simp only [Exec.evalExpr, Refine.tv, hmi2, typeof, cop]; exact rfl
      · simp only [Exec.evalExpr, Refine.tv, hmi2, typeof, cop]; exact rfl
      intro le3 ho3 ⟨w3, hw3⟩
      apply wp_set_eval
      simp only [Exec.evalExpr, hw3]
      have hma3 : PTree.get dense.id.maxinvarlev (PTree.set dense.id.minlev w3 le3) =
          some (.Vint ma) := by
        rw [temps_gso _ _ (by decide), ho3 _ (by decide), hT2 _ (by decide) (by decide) (by decide)
          (by decide) (by decide)]
        simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
      simp only [seqPost, Post.after, E0_append]
      wp_step; wp_step; wp_step; wp_step
      apply wp_ifSet2
      · simp only [Exec.evalExpr, Refine.tv, hma3]; exact rfl
      · simp only [typeof, cop]; exact rfl
      · simp only [Exec.evalExpr, Refine.tv, hma3, typeof, cop]; exact rfl
      · simp only [Exec.evalExpr, Refine.tv, hma3, typeof, cop]; exact rfl
      intro le4 ho4 ⟨w4, hw4⟩
      apply wp_set_eval
      simp only [Exec.evalExpr, hw4]
      simp only [seqPost, Post.after, E0_append]
      have hip : PTree.get dense.id.invarproc (PTree.set dense.id.maxlev w4 le4) = some Vnullptr := by
        rw [temps_gso _ _ (by decide), ho4 _ (by decide), temps_gso _ _ (by decide),
          ho3 _ (by decide), hT2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
      wp_step; wp_step; wp_step; wp_step; wp_step
      apply wp_if_eval
      simp only [Exec.evalExpr, hip, typeof, cop, ne_null]
      simp only [Val.of_bool, Bool.false_eq_true, ite_false, cop]
      apply wp_set_eval
      simp only [Exec.evalExpr, seqPost, Post.after, E0_append]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop]
      rw [ite_eq_right (by decide)]
      apply wp_set_eval
      simp only [Exec.evalExpr, seqPost, Post.after, E0_append]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop]
      rw [ite_eq_right (by decide)]
      apply wp_set_eval
      simp only [Exec.evalExpr, seqPost, Post.after, E0_append]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop]
      rw [ite_eq_right (by decide)]
      have hq1 := hq.unch huN (Alloc.not_dynSet hvq hqNS hqN hqbN)
      have hq2 := hq1.unch hu2 nq
      have hDN2 : DynAt m2 NWP NWPS 4 capN' bN' :=
        hDN1.keep hu2 nNWP nNWPS fun hc => Keep.unch hu2 (nbN hc)
      have hqt : PTree.get dense.id.qinvar (PTree.set (idOf 713) (.Vint (ir 0))
          (PTree.set (idOf 712) (.Vint (ir 0)) (PTree.set (idOf 711) (.Vint (ir 0))
          (PTree.set dense.id.maxlev w4 le4)))) = some (.Vptr bq qofs) := by
        rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide),
          temps_gso _ _ (by decide), ho4 _ (by decide), temps_gso _ _ (by decide),
          ho3 _ (by decide), hT2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
      obtain ⟨m3, hst, harr3, -⟩ := store_array hq2 (show 0 < 1 by decide) (.Vint (ir 0)) rfl
      wp_step; wp_step
      apply wp_assign_eval
      simp only [Exec.evalLvalue, Exec.evalExpr, Refine.pi, hqt, typeof, cop, Exec.assignLoc,
        Cfrontend.Ctypes.access_mode, Mem.storev]
      rw [show Ptrofs.unsigned qofs = elemOfs .Mint32 (intOfZ (Ptrofs.unsigned qofs)) 0 by
        unfold elemOfs
        rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ], hst]
      have hu3 : Unch m2 m3 (· = bq) := Unch.store hst rfl
      have hbNq : 0 < capN' → bN' ≠ bq := fun hc => Ne.symm (Alloc.ne_new hbN' hvq hqbN hc)
      refine ⟨m3, Nextelement.free_empty m3, by simp, m1, m2, capN', bN',
        huN.mono fun z hz => ?_, hgN, ⟨v, hpost'⟩, hu3, Alloc.KeepA.storeArr hq2 hst,
        harr3.congr fun i hi => by simp [upd, show i = 0 by omega],
        hDN2.keep hu3 (Ne.symm hqN) (Ne.symm hqNS) (fun hc => Keep.unch hu3 (hbNq hc)), hcN, hbN',
        fun hc => Alloc.Malloced.valid (hDN1.mal hc)⟩
      rcases hz with h | h | h | ⟨hnv, rfl⟩
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr hnv))

end

section
local notation "NWP" => Block.nautilWorkperm
local notation "NWPS" => Block.nautilWorkpermSz

def dorefSpec {n : Nat} (xi : ExternalCalls) (L : Loc) (ctx : Ctx n) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (aw : Nat → Lib.Integers.int64) (bq : block) (qofs : ptrofs)
    (bf : block) (mi ma ia dg : Lib.Integers.int) (capN : Nat) (bN : block) : FunSpec where
  pre args m := args = [.Vptr L.bg L.gofs, .Vptr L.bl L.lofs, .Vptr L.bp L.pofs,
      .Vint (ir L.level), .Vptr L.bn L.nofs, .Vptr bq qofs, .Vptr L.bc L.cofs, .Vptr L.ba L.aofs,
      .Vptr L.bk L.kofs, .Vptr bf Ptrofs.zero, Vnullptr, .Vint mi, .Vint ma, .Vint ia, .Vint dg,
      .Vint (ir L.M), .Vint (ir n)] ∧
    (refineSpec L ctx lab ptn active numcells aw).pre (refArgs L n) m ∧
    RefineFn xi L.M (.Vptr bf Ptrofs.zero) ∧
    DynAt m NWP NWPS 4 capN bN ∧
    (∃ qv, ArrayAt m .Mint32 bq (intOfZ (Ptrofs.unsigned qofs)) qv 1) ∧ Mem.valid_block m bq ∧
    (∀ z ∈ L.blocks, z ≠ bq ∧ z ≠ NWP ∧ z ≠ NWPS ∧ (0 < capN → z ≠ bN)) ∧
    bq ≠ NWP ∧ bq ≠ NWPS ∧ (0 < capN → bq ≠ bN)
  post _ m t _ m' := t = E0 ∧ ∃ m₁ m₂ capN' bN',
    Unch m m₁ (fun z => z = NWPS ∨ z = NWP ∨ (0 < capN ∧ z = bN) ∨ ¬ Mem.valid_block m z) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m₁ z) ∧
    (refineSpec L ctx lab ptn active numcells aw).post (refArgs L n) m₁ E0 .Vundef m₂ ∧
    Unch m₂ m' (· = bq) ∧ Alloc.KeepA m₂ m' ∧
    ArrayAt m' .Mint32 bq (intOfZ (Ptrofs.unsigned qofs)) (fun _ => .Vint (ir 0)) 1 ∧
    DynAt m' NWP NWPS 4 capN' bN' ∧ n ≤ capN' ∧
    ((capN' = capN ∧ bN' = bN) ∨ ¬ Mem.valid_block m bN') ∧
    (0 < capN' → Mem.valid_block m₁ bN')

theorem doref_satisfies {xi : ExternalCalls} {n : Nat} (L : Loc) (ctx : Ctx n)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) (aw : Nat → Lib.Integers.int64)
    (bq : block) (qofs : ptrofs) (bf : block) (mi ma ia dg : Lib.Integers.int) (capN : Nat)
    (bN : block) :
    Satisfies xi Program.ge (.Internal dense.fn.doref)
      (dorefSpec xi L ctx lab ptn active numcells aw bq qofs bf mi ma ia dg capN bN) := by
  refine Satisfies.of_pre fun args m ⟨hargs, hpre, hfn, hDN, hq, hvq, hsep, hqN, hqNS, hqbN⟩ => ?_
  obtain ⟨-, hp, hm, ⟨kv, hk⟩, hv, hok0, hps, hnc⟩ := hpre
  obtain ⟨fd, hfd, hfty, hsat⟩ := hfn
  have hvF := hm.valid_fixed hv
  have hfix : ∀ z ∈ [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk] ++
      [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
       Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
       Block.naugraphBit, Block.naugraphBytecount, Block.leftbit], z ∈ L.blocks := by
    intro z hz
    rw [Refine.Loc.blocks_eq]
    rcases List.mem_append.1 hz with h | h
    · exact List.mem_append.2 (.inl (List.mem_append.2 (.inl h)))
    · exact List.mem_append.2 (.inr h)
  have nS : ∀ z ∈ L.blocks, Mem.valid_block m z → ¬ NSet m capN bN z := fun z hz hzv h => by
    rcases h with h | h | h | h
    · exact (hsep z hz).2.2.1 h
    · exact (hsep z hz).2.1 h
    · exact (hsep z hz).2.2.2 h.1 h.2
    · exact h hzv
  have hLW : L.bW ∈ L.blocks := by simp [Loc.blocks]
  have hLS : L.bS ∈ L.blocks := by simp [Loc.blocks]
  have hLB : L.bB ∈ L.blocks := by simp [Loc.blocks]
  refine ⟨dorefSpecR (n := n) xi (refineSpec L ctx lab ptn active numcells aw) L aw bq qofs bf mi ma
    ia dg capN bN, doref_satisfiesR _ _ _ _ _ _ _ _ _ _ _ _, ⟨hargs, ⟨fd, hfd, hfty,
      hsat L rfl ctx lab ptn active numcells aw⟩, ?_, ?_, hm.act, hm.left, ?_, hp.M1, hp.Mlt,
      hp.n0, hp.nlt, hDN, hq, hvq, hqN, hqNS, hqbN⟩,
    fun t v m' ⟨h1, m₁, m₂, c, b, a1, a2, ⟨_, a3⟩, rest⟩ => ⟨h1, m₁, m₂, c, b, a1, a2, a3, rest⟩⟩
  · intro m₁ hu hg
    have hm1 := hm.unch hu (fun z hz => nS z (hfix z hz) (hvF z hz))
      (fun hc => nS _ hLW (Alloc.Malloced.valid (hm.dW.mal hc)))
      (fun hc => nS _ hLS (Alloc.Malloced.valid (hm.dS.mal hc)))
      (fun hc => nS _ hLB (Alloc.Malloced.valid (hm.dB.mal hc)))
    have hk1 := hk.unch hu (nS _ (by simp [Loc.blocks]) (hv _ (by simp)))
    exact ⟨rfl, hp, hm1, ⟨kv, hk1⟩, fun z hz => hg z (hv z hz), hok0, hps, hnc⟩
  · intro m₁ c' b' hu hg hD1 hb' t v m₂ hpost
    obtain ⟨rfl, cW, bW', cS, bS', cB, bB', aw', -, -, -, -, -, -, -, -, -, -, hu2, -⟩ := hpost
    -- what `refine` may have changed
    have nR : ∀ z, (∀ y ∈ [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk] ++
        [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
         Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
         Block.naugraphBit, Block.naugraphBytecount, Block.leftbit], z ≠ y) →
        (0 < L.capW → z ≠ L.bW) → (0 < L.capS → z ≠ L.bS) → (0 < L.capB → z ≠ L.bB) →
        Mem.valid_block m₁ z →
        ¬ ((z = L.bl ∨ z = L.bp ∨ z = L.bn ∨ z = L.bc ∨ z = L.ba) ∨ z = L.bk ∨
          Alloc.dyn3Set m₁ L.capW L.bW L.capS L.bS L.capB L.bB z) := by
      intro z hy hW hS hB hzv
      rintro ((h | h | h | h | h) | h | h | h | h | h | h | h | ⟨hc, h⟩ | ⟨hc, h⟩ | ⟨hc, h⟩ | h)
      all_goals first
        | exact hW hc h
        | exact hS hc h
        | exact hB hc h
        | exact h hzv
        | exact hy _ (by simp) h
    refine ⟨rfl, _, hu2, nR bq (fun y hy h => (hsep y (hfix y hy)).1 h.symm)
        (fun _ h => (hsep _ hLW).1 h.symm) (fun _ h => (hsep _ hLS).1 h.symm)
        (fun _ h => (hsep _ hLB).1 h.symm) (hg _ hvq), ?_, ?_, ?_⟩
    · have hvNWP := Alloc.valid_of_access hD1.bpW
      exact nR NWP (fun y hy h => (hsep y (hfix y hy)).2.1 h.symm)
        (fun _ h => (hsep _ hLW).2.1 h.symm) (fun _ h => (hsep _ hLS).2.1 h.symm)
        (fun _ h => (hsep _ hLB).2.1 h.symm) hvNWP
    · have hvNWPS := Alloc.valid_of_access hD1.bsW
      exact nR NWPS (fun y hy h => (hsep y (hfix y hy)).2.2.1 h.symm)
        (fun _ h => (hsep _ hLW).2.2.1 h.symm) (fun _ h => (hsep _ hLS).2.2.1 h.symm)
        (fun _ h => (hsep _ hLB).2.2.1 h.symm) hvNWPS
    · intro hc
      exact nR b' (fun y hy => Ne.symm (Alloc.ne_new hb' (hvF y hy)
            (fun _ h => (hsep y (hfix y hy)).2.2.2 (by omega) h) hc))
          (fun hcw => Ne.symm (Alloc.ne_new hb' (Alloc.Malloced.valid (hm.dW.mal hcw))
            (fun _ h => (hsep _ hLW).2.2.2 (by omega) h) hc))
          (fun hcs => Ne.symm (Alloc.ne_new hb' (Alloc.Malloced.valid (hm.dS.mal hcs))
            (fun _ h => (hsep _ hLS).2.2.2 (by omega) h) hc))
          (fun hcb => Ne.symm (Alloc.ne_new hb' (Alloc.Malloced.valid (hm.dB.mal hcb))
            (fun _ h => (hsep _ hLB).2.2.2 (by omega) h) hc))
          (Alloc.Malloced.valid (hD1.mal hc))
  · intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · exact ⟨hv _ (by simp), (hsep _ (by simp [Loc.blocks])).2.1,
        (hsep _ (by simp [Loc.blocks])).2.2.1, (hsep _ (by simp [Loc.blocks])).2.2.2⟩
    · exact ⟨hvF _ (by simp), (hsep _ (by simp [Loc.blocks])).2.1,
        (hsep _ (by simp [Loc.blocks])).2.2.1, (hsep _ (by simp [Loc.blocks])).2.2.2⟩

end

end NautyVerified.Proofs.Doref
