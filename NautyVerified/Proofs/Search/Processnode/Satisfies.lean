import NautyVerified.Proofs.Search.Processnode.Switch
import NautyVerified.Proofs.Dispatch.Dense

/-!
# `processnode` meets its specification

`processnode_satisfies`: nauty.c's `processnode` is HexGraphIso's `classify`
followed by `leafExit` (`processnodeSpec`). The body: `code = 0`, the
classification (`wp_classifyC`), the `maxlevel` update, and the `switch` with
the code after it (`wp_switchTail`); `sr` is allocated on entry and freed on
return (`PAt.finish`).
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv)
open NautyVerified.Proofs.Alloc (Keep)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

/-- The temporaries on entry. -/
def entryTemps (S : SLoc) (level numcells : Nat) : temp_env :=
  PTree.set dense.id.numcells (.Vint (ir numcells)) (PTree.set dense.id.level (.Vint (ir level))
    (PTree.set dense.id.ptn (.Vptr S.bp S.pofs) (PTree.set dense.id.lab (.Vptr S.bl S.lofs)
      (create_undef_temps dense.fn.«nauty:processnode».fn_temps))))

/-- Before the `switch`: `if (code != 0 && level > stats->maxlevel) stats->maxlevel = level;` -/
abbrev maxC : statement :=
  .Ssequence
    (sk (.Sifthenelse (.Ebinop .One (tv dense.id.«code») (ci 0 tint) tint)
      (sk (.Sset (idOf 707)
        (.Ecast (.Ebinop .Ogt (tv dense.id.«level») (statsF dense.id.«maxlevel» tint) tint) tbool)))
      (.Sset (idOf 707) (ci 0 tint))))
    (.Sifthenelse (tv (idOf 707)) (sk (.Sassign (statsF dense.id.«maxlevel» tint) (tv dense.id.«level»)))
      .Sskip)

theorem leafCode_ne (leaf : Leaf) : (leafCode leaf ≠ 0) ↔ (leaf != .internal) = true := by
  cases leaf <;> simp [leafCode] <;> rfl

theorem leafCode_le (leaf : Leaf) : 0 ≤ leafCode leaf ∧ leafCode leaf ≤ 4 := by
  cases leaf <;> simp [leafCode]

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}
variable {n : Nat} {D : DispatchC ge O} {m₀ m₁ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
  {G : O.Gr n} {e : env} {bsr : block} {st : SearchState n (O.Canon n)} {nsp : Bool}

set_option maxHeartbeats 8000000 in
theorem wp_maxC {f : function} {Q : Post} {le : temp_env} {level : Nat} {leaf : Leaf}
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st false)
    (hcode : PTree.get dense.id.code le = some (.Vint (ir (leafCode leaf))))
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (hl : level ≤ n)
    (hQ : ∀ le' m', PAt D m₀ m₁ m' S gl cl G bsr
        (if (leaf != .internal && level > st.maxlevel) then { st with maxlevel := level } else st) false →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Unch m m' (· = S.bst) →
      (∀ x, x ≠ idOf 707 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f maxC Q e le m := by
  have hs := h.search
  have hinv := hs.inv
  have hfit := hs.stats.fits
  have hml := hinv.maxlevelLe
  have hnl := hs.nlt
  obtain ⟨c0, c4⟩ := leafCode_le leaf
  wp_step
  refine wp_sel' (b := decide (leafCode leaf ≠ 0)) (v1 := Val.of_bool (decide ((st.maxlevel : Int) < level)))
    (v2 := .Vint (ir 0)) (eval_neI (show Exec.evalExpr ge e le m (tv dense.id.code) = _ from hcode)
      (eval_ci 0) rfl rfl ⟨by omega, by omega⟩ ⟨by decide, by decide⟩) rfl ?_ (fun _ => eval_ci 0) ?_
  · intro _
    rw [Exec.evalExpr, eval_gtI (show Exec.evalExpr ge e le m (tv dense.id.level) = _ from hlev)
      (eval_statsF (ty := tint) (c.eg _ (by decide)) fld_maxlevel rfl hs.fixed.stats (by decide)
        (by omega) (hs.stats.maxlevel rfl)) rfl rfl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    cases decide ((st.maxlevel : Int) < level) <;> rfl
  simp only [seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, Refine.tv, temps_gss, typeof]
  by_cases h1 : leafCode leaf ≠ 0
  · have hb1 : (leaf != .internal) = true := (leafCode_ne leaf).1 h1
    rw [decide_eq_true h1, if_pos rfl]
    by_cases h2 : st.maxlevel < level
    · rw [decide_eq_true (by exact_mod_cast h2), show Val.of_bool true = .Vint Int.one from rfl]
      simp only [cop]
      rw [ite_eq_left (by decide)]
      wp_step; wp_step
      refine wp_maxlevel c h (by rw [temps_gso _ _ (by decide)]; exact hlev) hl ?_
      intro m' h' hsr hu
      have : (leaf != .internal && level > st.maxlevel) = true := by simp [hb1, h2]
      rw [this, if_pos rfl] at hQ
      exact hQ _ m' h' hsr hu fun x hx => temps_gso _ _ hx
    · rw [decide_eq_false (by exact_mod_cast h2), show Val.of_bool false = .Vint Int.zero from rfl]
      simp only [cop]
      rw [ite_eq_right (by decide)]
      apply wp_skip
      have : (leaf != .internal && level > st.maxlevel) = false := by simp [h2]
      rw [this, if_neg (by decide)] at hQ
      exact hQ _ m h (fun _ h => h) (Unch.refl _ _) fun x hx => temps_gso _ _ hx
  · have hb1 : (leaf != .internal) = false := by
      cases hh : (leaf != .internal)
      · rfl
      · exact absurd ((leafCode_ne leaf).2 hh) h1
    rw [decide_eq_false h1, if_neg (by decide)]
    simp only [cop]
    rw [ite_eq_right (by decide)]
    apply wp_skip
    have : (leaf != .internal && level > st.maxlevel) = false := by simp [hb1]
    rw [this, if_neg (by decide)] at hQ
    exact hQ _ m h (fun _ h => h) (Unch.refl _ _) fun x hx => temps_gso _ _ hx

theorem va_of_perm {m : mem} {b : block} (h : Mem.perm m b (zOfInt 0) .Cur .Nonempty) :
    Mem.valid_access m .Mint8unsigned b (zOfInt 0) .Nonempty := by
  refine ⟨fun o ho => ?_, ⟨zOfInt 0, rfl⟩⟩
  have h1 := ho.1; have h2 := ho.2
  change intOfZ _ ≤ intOfZ _ at h1
  change intOfZ _ < intOfZ _ at h2
  have h8 : intOfZ (Common.Memdata.size_chunk .Mint8unsigned) = 1 := rfl
  simp only [intOfZ_add, intOfZ_zOfInt, h8] at h1 h2
  have : o = zOfInt 0 := by apply intOfZ_injective; simp only [intOfZ_zOfInt]; omega
  rw [this]; exact h

set_option maxHeartbeats 16000000 in
theorem processnode_satisfiesG (D : DispatchC ge O) (C : Classifier O) (S : SLoc) (gl : D.GLoc)
    (cl : D.CLoc) (G : O.Gr n) (st : SearchState n (O.Canon n)) (level numcells : Nat) :
    Satisfies xi ge (.Internal dense.fn.«nauty:processnode»)
      (processnodeSpecG D.toDispatchRep xi S gl cl G st level numcells) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m => ∃ bsr,
    e = PTree.set dense.id.sr (bsr, tint) empty_env ∧
    Mem.alloc m₀ (zOfInt 0) (sizeof ge.genv_cenv tint) = (m, bsr) ∧
    le = entryTemps S level numcells) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    have hal : Mem.alloc m (zOfInt 0) (sizeof ge.genv_cenv tint) =
        ((Mem.alloc m (zOfInt 0) (sizeof ge.genv_cenv tint)).1,
         (Mem.alloc m (zOfInt 0) (sizeof ge.genv_cenv tint)).2) := rfl
    generalize (Mem.alloc m (zOfInt 0) (sizeof ge.genv_cenv tint)).1 = m1 at hal
    generalize (Mem.alloc m (zOfInt 0) (sizeof ge.genv_cenv tint)).2 = b1 at hal
    refine ⟨PTree.set dense.id.sr (b1, tint) empty_env, entryTemps S level numcells, m1,
      ⟨?_, ?_, ?_, .cons _ _ _ _ _ _ _ _ _ hal (.nil _ _), rfl⟩, b1, rfl, hal, rfl⟩
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, h, hcb, hl1, hln, hncl, hlok, hval, hua⟩
    rw [triple_iff_wp]
    rintro e le m₁ ⟨bsr, rfl, hal, rfl⟩
    have hfresh : ¬ Mem.valid_block m₀ bsr := Mem.fresh_block_alloc _ _ _ _ _ hal
    have hv01 : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m₁ z := Mem.valid_block_alloc _ _ _ _ _ hal
    have hvnew : Mem.valid_block m₁ bsr := Mem.valid_new_block _ _ _ _ _ hal
    have hU : Unch m₀ m₁ (· = bsr) := Alloc.Unch.alloc hal
    have hva1 : Mem.valid_access m₁ .Mint32 bsr (zOfInt 0) .Freeable := by
      refine ⟨fun o ho => Mem.perm_alloc_2 _ _ _ _ _ hal o .Cur ⟨?_, ?_⟩, ⟨zOfInt 0, rfl⟩⟩
      · exact ho.1
      · have := ho.2
        change intOfZ _ < intOfZ _ at this ⊢
        have h4 : intOfZ (Common.Memdata.size_chunk .Mint32) = 4 := rfl
        simp only [intOfZ_add, intOfZ_zOfInt, h4, Int.zero_add] at this
        exact this
    have hne : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, z ≠ bsr := fun z hz e => hfresh (e ▸ hval z hz)
    have hwk0 : ∀ z, IsWorkG D.toDispatchRep m₀ z → ¬ z = bsr := fun z hz e => hfresh (e ▸ hz.valid)
    have back := (h.work.unch hU (fun z hz => hne z (SLoc.mem_blocksG_of _
        (.inr (.inr (.inr (.inr (.inr (D.wglobs_sub z hz))))))))
      ⟨hne _ (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp))))))),
        hne _ (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by simp)))))))⟩ hwk0 hv01).2
    have c : PCtx D m₀ m₁ S gl cl (PTree.set dense.id.sr (bsr, tint) empty_env) bsr :=
      { valid0 := hval, fresh := hfresh, valid1 := hvnew, grow01 := hv01
        work10 := back
        esr := PTree.gss _ _ _
        eg := fun x hx => by rw [PTree.gso _ _ hx]; rfl
        eEq := rfl }
    have hP : PAt D m₀ m₁ m₁ S gl cl G bsr st false :=
      { search := h.unch hU hne hwk0 hv01
        frame := ⟨hU.mono fun z hz => .inr (.inl (hz ▸ hfresh)), hv01⟩
        work := fun z hz => .inl hz
        grow1 := fun _ h => h
        srW := hva1
        ua := hU.access _ _ _ _ (hne _ (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inl (by simp)))))))
          (va_of_perm hua) }
    have hinv := h.inv
    have hfr : dense.fn.«nauty:processnode».fn_return = tint := rfl
    rw [dense.fn.«nauty:processnode».fn_body_eq, body_eq]
    simp only [body]
    let le0 := entryTemps S level numcells
    have t0 : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.numcells],
        PTree.get x (PTree.set dense.id.code (.Vint (ir 0)) le0) = PTree.get x le0 := by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact temps_gso _ _ (by decide)
    have hlev0 : PTree.get dense.id.level le0 = some (.Vint (ir level)) := by
      simp (config := {decide := true}) only [le0, entryTemps, temps_gso, temps_gss]
    have hnc0 : PTree.get dense.id.numcells le0 = some (.Vint (ir numcells)) := by
      simp (config := {decide := true}) only [le0, entryTemps, temps_gss]
    have hlab0 : PTree.get dense.id.lab le0 = some (.Vptr S.bl S.lofs) := by
      simp (config := {decide := true}) only [le0, entryTemps, temps_gso, temps_gss]
    have hptn0 : PTree.get dense.id.ptn le0 = some (.Vptr S.bp S.pofs) := by
      simp (config := {decide := true}) only [le0, entryTemps, temps_gso, temps_gss]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_ci]
    simp only [seqPost, Post.after, E0_append]
    wp_step
    refine wp_classifyC C c hP (by rw [t0 _ (by simp)]; exact hlev0) hln
      (by rw [t0 _ (by simp)]; exact hnc0) hncl (by rw [t0 _ (by simp)]; exact hlab0) (temps_gss _ _ _)
      hlok.firstlabSmall hlok.firstlabSurj hlok.canonlabSmall hlok.canonlabSurj ?_
    intro le2 m2 hC
    simp only [seqPost, Post.after, E0_append]
    have hcl := C.classify_eq G level numcells st
    rw [hcl] at hC
    have hk := Keeps.classifyBy (C.update G) G level numcells st
    have hcases := classifyBy_cases C G level numcells st
    generalize hr : classifyBy O (C.update G) G level numcells st = r at hC hk hcases
    have hlev2 : PTree.get dense.id.level le2 = some (.Vint (ir level)) := by
      rw [hC.temps _ (by simp), t0 _ (by simp)]; exact hlev0
    have hlab2 : PTree.get dense.id.lab le2 = some (.Vptr S.bl S.lofs) := by
      rw [hC.temps _ (by simp), t0 _ (by simp)]; exact hlab0
    have hptn2 : PTree.get dense.id.ptn le2 = some (.Vptr S.bp S.pofs) := by
      rw [hC.temps _ (by simp), t0 _ (by simp)]; exact hptn0
    wp_step
    refine wp_maxC c hC.at_ hC.code hlev2 hln ?_
    intro le3 m3 h3 hsr3 hu3 ho3
    simp only [seqPost, Post.after, E0_append]
    generalize hst2 : (if (r.1 != .internal && level > r.2.maxlevel) then
      { r.2 with maxlevel := level } else r.2) = st2 at h3
    have hK2 : Keeps r.2 st2 ∧ st2.workperm = r.2.workperm ∧ st2.samerows = r.2.samerows := by
      rw [← hst2]; split
      · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨Keeps.refl _, rfl, rfl⟩
    have hKK := hk.trans hK2.1
    have hd := h3.search.lit
    refine wp_switchTail (level := level) (leaf := r.1) c h3 hcb hfr
      (by rw [ho3 _ (by decide)]; exact hC.code) (by rw [ho3 _ (by decide)]; exact hlev2) hln
      (by rw [ho3 _ (by decide)]; exact hlab2) (by rw [ho3 _ (by decide)]; exact hptn2)
      (by rw [hKK.eqlevCanon]; exact hlok.eqlevCanon)
      (by rw [hKK.noncheaplevel]; exact hlok.noncheaplevel)
      (by rw [hKK.cosetindex]; exact hlok.cosetindex) ?_ ?_ ?_
    · intro hx
      refine ⟨by rw [hK2.2.1]; exact (hC.perm hx).unch hu3 (by sep_ne hd), ?_⟩
      rw [hK2.2.1]
      rcases hcases with h0 | ⟨hA, hwA⟩ | ⟨hA, w, hwsz, hwA⟩ | ⟨s, hB, -⟩ | hB
      · rcases hx with hx | hx <;> rw [h0] at hx <;> cases hx
      · rw [hwA]
        exact scatterW_inj hinv.workpermSize hlok.firstlabSmall hlok.firstlabSurj hinv.labSmall
          hinv.labSurj
      · rw [hwA]
        exact scatterW_inj (by rw [hwsz]; exact hinv.workpermSize) hlok.canonlabSmall
          hlok.canonlabSurj hinv.labSmall hinv.labSurj
      · rcases hx with hx | hx <;> rw [hB] at hx <;> cases hx
      · rcases hx with hx | hx <;> rw [hB] at hx <;> cases hx
    · intro s hs
      refine ⟨hsr3 _ (hC.sr s hs), ?_⟩
      rw [hK2.2.2]
      rcases hcases with h0 | ⟨hA, -⟩ | ⟨hA, -⟩ | ⟨s', hB, hle⟩ | hB
      · rw [h0] at hs; cases hs
      · rw [hA] at hs; cases hs
      · rw [hA] at hs; cases hs
      · rw [hB] at hs; cases hs; exact hle
      · rw [hB] at hs; cases hs
    · intro m' t h' hW
      obtain ⟨mf, hfree, hS, hF, hWk⟩ := PAt.finish c h'
      refine ⟨mf, hfree, ?_⟩
      have hle : leafExit (O.classify G level numcells st).1 level (O.classify G level numcells st).2 =
          lxBody r.1 level st2 := by
        rw [leafExit_eq, hcl, hr, hst2]
      simp only [processnodeSpecG]
      rw [hle]
      refine ⟨rfl, hS, ?_, hF, hWk⟩
      have hng : st2.numgenerators = st.numgenerators := hKK.numgenerators
      simp only [leafWords, hng] at hW
      exact hW


/-- The dense instance: nauty.c's `processnode` is HexGraphIso's `classify` followed by
`leafExit`. -/
theorem processnode_satisfies (S : SLoc) (ctx : Ctx n) (st : Search n) (level numcells : Nat) :
    Satisfies xi Program.ge (.Internal dense.fn.«nauty:processnode»)
      (processnodeSpec xi S ctx st level numcells) :=
  processnodeSpec_ofG
    (processnode_satisfiesG Dispatch.dense denseClassifier S () () ctx st level numcells)

end NautyVerified.Proofs.Search.Processnode
