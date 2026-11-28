import NautyVerified.Proofs.Search.Processnode.Case3

/-!
# The end of `processnode`

`wp_tailRest`: the computation of the return level and of the short-prune
request from `ispruneok`. `wp_tail`: with the partition's pair recorded when
`level != noncheaplevel`, the whole is HexGraphIso's `pruneReturn`.
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
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}
open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}
variable {n : Nat} {D : DispatchC ge O} {m₀ m₁ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
  {G : O.Gr n} {e : env} {bsr : block} {st : SearchState n (O.Canon n)} {nsp : Bool}

/-- `pruneReturn`'s level. -/
def newLevel {κ : Type} (st : SearchState n κ) : Int :=
  let save : Int := if Int.ofNat st.allsamelevel > st.eqlevCanon then Int.ofNat st.allsamelevel - 1
    else st.eqlevCanon
  if Int.ofNat st.noncheaplevel ≤ save then Int.ofNat st.noncheaplevel - 1 else save

theorem pruneReturn_eq {κ : Type} (level : Nat) (st : SearchState n κ) :
    pruneReturn level st =
      (.unwind (newLevel st).toNat ((level != st.noncheaplevel) && newLevel st != Int.ofNat st.gcaFirst),
        if level != st.noncheaplevel then pushAuto st (fmptn st.lab st.ptn st.noncheaplevel n) else st) := by
  unfold pruneReturn newLevel
  simp only [Id.run, pure]
  split
  · rename_i h
    have : (pushAuto st (fmptn st.lab st.ptn st.noncheaplevel n)).orbits = st.orbits ∧
        (pushAuto st (fmptn st.lab st.ptn st.noncheaplevel n)).workperm = st.workperm := by
      unfold pushAuto; split <;> exact ⟨rfl, rfl⟩
    unfold pushAuto at this ⊢
    split <;> simp_all
  · simp_all

theorem wp_sel {f : function} {Q : Post} {le : temp_env} {cnd a1 a2 : expr} {t : ident} {b : Bool}
    {v1 v2 : val} (hc : Exec.evalExpr ge e le m cnd = some (Val.of_bool b)) (hct : typeof cnd = tint)
    (h1 : b = true → Exec.evalExpr ge e le m a1 = some v1)
    (h2 : b = false → Exec.evalExpr ge e le m a2 = some v2)
    (hQ : Q.normal E0 e (PTree.set t (if b then v1 else v2) le) m) :
    Wp xi ge f (sk (.Sifthenelse cnd (sk (.Sset t a1)) (sk (.Sset t a2)))) Q e le m := by
  wp_step; wp_step
  refine wp_ifB hc hct ?_
  cases b
  · simp only [Bool.false_eq_true, ite_false] at hQ ⊢
    wp_step; wp_step
    apply wp_set_eval; rw [h2 rfl]; exact hQ
  · simp only [ite_true] at hQ ⊢
    wp_step; wp_step
    apply wp_set_eval; rw [h1 rfl]; exact hQ

theorem wp_sel' {f : function} {Q : Post} {le : temp_env} {cnd a1 a2 : expr} {t : ident} {b : Bool}
    {v1 v2 : val} (hc : Exec.evalExpr ge e le m cnd = some (Val.of_bool b)) (hct : typeof cnd = tint)
    (h1 : b = true → Exec.evalExpr ge e le m a1 = some v1)
    (h2 : b = false → Exec.evalExpr ge e le m a2 = some v2)
    (hQ : Q.normal E0 e (PTree.set t (if b then v1 else v2) le) m) :
    Wp xi ge f (sk (.Sifthenelse cnd (sk (.Sset t a1)) (.Sset t a2))) Q e le m := by
  wp_step; wp_step
  refine wp_ifB hc hct ?_
  cases b
  · simp only [Bool.false_eq_true, ite_false] at hQ ⊢
    apply wp_set_eval; rw [h2 rfl]; exact hQ
  · simp only [ite_true] at hQ ⊢
    wp_step; wp_step
    apply wp_set_eval; rw [h1 rfl]; exact hQ

theorem ofBool_ir (b : Bool) : Val.of_bool b = .Vint (ir (if b then 1 else 0)) := by
  cases b <;> rfl

/-- `needshortprune = 1`. -/
theorem wp_nsp1 {f : function} {Q : Post} {le : temp_env} (c : PCtx D m₀ m₁ S gl cl e bsr)
    (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    (hQ : ∀ m', PAt D m₀ m₁ m' S gl cl G bsr st true → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar dense.id.«nauty:needshortprune» tint) (ci 1 tint)) Q e le m := by
  have hs := h.search
  have hd := hs.lit
  refine wp_gint (c.eg _ (by decide)) E.find_needshortprune hs.scalars.needshortprune.writable
    (eval_ci 1) rfl ?_
  intro m' hI hu hv
  have hu' : Unch m m' (· ∈ [E.needshortprune]) := hu.mono fun z hz => by simp [hz]
  have sc := hs.scalars
  exact hQ m' (PAt.next c h hu' (by simp) (keeps hd, hu) hv
    ⟨sc.gcaFirst.unch hu (by sep_ne hd), sc.gcaCanon.unch hu (by sep_ne hd),
      sc.noncheaplevel.unch hu (by sep_ne hd), sc.allsamelevel.unch hu (by sep_ne hd),
      sc.eqlevFirst.unch hu (by sep_ne hd), sc.eqlevCanon.unch hu (by sep_ne hd),
      sc.compCanon.unch hu (by sep_ne hd), sc.samerows.unch hu (by sep_ne hd),
      sc.canonlevel.unch hu (by sep_ne hd), sc.stabvertex.unch hu (by sep_ne hd),
      sc.cosetindex.unch hu (by sep_ne hd), by simpa using hI⟩
    (hs.stats.unch hu (by sep_ne hd)) (hs.arrays.unch hu' (by sep_all hd) (hs.graph_notin (by simp)) (hs.canon_notin (by simp))) hs.inv)

set_option maxHeartbeats 8000000 in
theorem wp_tailRest {f : function} {Q : Post} {le : temp_env} {ok : Bool}
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st false) (hfr : f.fn_return = tint)
    (hec : 0 ≤ st.eqlevCanon) (hnc : 1 ≤ st.noncheaplevel)
    (hok : PTree.get dense.id.ispruneok le = some (.Vint (ir (if ok then 1 else 0))))
    (hR : ∀ m', PAt D m₀ m₁ m' S gl cl G bsr st (ok && newLevel st != Int.ofNat st.gcaFirst) →
      ∃ mf, Mem.free_list m' (blocks_of_env ge e) = some mf ∧
        Q.ret E0 (.Vint (ir (newLevel st))) mf) :
    Wp xi ge f tailRest Q e le m := by
  have hs := h.search
  have hinv := hs.inv
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, -, -, -, -, -⟩ := hinv.scalars
  have sc := hs.scalars
  let S1 : Int := if Int.ofNat st.allsamelevel > st.eqlevCanon then Int.ofNat st.allsamelevel - 1
    else st.eqlevCanon
  have hS1 : 0 ≤ S1 ∧ S1 < 2147483648 := by
    simp only [S1]; split <;> simp only [Int.ofNat_eq_coe] at * <;> omega
  wp_step; wp_step
  refine wp_sel (b := decide (st.eqlevCanon < st.allsamelevel))
    (v1 := .Vint (ir ((st.allsamelevel : Int) - 1))) (v2 := .Vint (ir st.eqlevCanon))
    (eval_gtI (eval_gint (c.eg _ (by decide)) E.find_allsamelevel sc.allsamelevel)
      (eval_gint (c.eg _ (by decide)) E.find_eqlevCanon sc.eqlevCanon) rfl rfl
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl
    (fun _ => by
      rw [Exec.evalExpr, Exec.evalExpr, eval_gint (c.eg _ (by decide)) E.find_allsamelevel
        sc.allsamelevel, eval_ci]
      simp only [typeof, cop, ir_sub])
    (fun _ => by
      rw [Exec.evalExpr, eval_gint (c.eg _ (by decide)) E.find_eqlevCanon sc.eqlevCanon]
      simp only [typeof, cop]) ?_
  have e714 : (if decide (st.eqlevCanon < st.allsamelevel) then val.Vint (ir ((st.allsamelevel : Int) - 1))
      else .Vint (ir st.eqlevCanon)) = .Vint (ir S1) := by
    by_cases hh : st.eqlevCanon < st.allsamelevel <;> simp [S1, hh]
  rw [e714]
  simp only [seqPost, Post.after, E0_append]
  apply wp_set_eval
  simp only [Exec.evalExpr, Refine.tv, temps_gss]
  simp only [seqPost, Post.after, E0_append]
  let le1 := PTree.set dense.id.save (.Vint (ir S1)) (PTree.set (idOf 714) (.Vint (ir S1)) le)
  have hsave : PTree.get dense.id.save le1 = some (.Vint (ir S1)) := temps_gss _ _ _
  let N : Int := if Int.ofNat st.noncheaplevel ≤ S1 then Int.ofNat st.noncheaplevel - 1 else S1
  have hN : N = newLevel st := rfl
  have hN0 : 0 ≤ N ∧ N < 2147483648 := by
    simp only [N]; split <;> simp only [Int.ofNat_eq_coe] at * <;> omega
  wp_step; wp_step
  refine wp_sel (b := decide ((st.noncheaplevel : Int) ≤ S1))
    (v1 := .Vint (ir ((st.noncheaplevel : Int) - 1))) (v2 := .Vint (ir S1))
    (eval_leI (eval_gint (c.eg _ (by decide)) E.find_noncheaplevel sc.noncheaplevel)
      (show Exec.evalExpr ge e le1 m (tv dense.id.save) = _ from hsave) rfl rfl
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl
    (fun _ => by
      rw [Exec.evalExpr, Exec.evalExpr, eval_gint (c.eg _ (by decide)) E.find_noncheaplevel
        sc.noncheaplevel, eval_ci]
      simp only [typeof, cop, ir_sub])
    (fun _ => by
      rw [Exec.evalExpr, show Exec.evalExpr ge e le1 m (tv dense.id.save) = _ from hsave]
      simp only [typeof, cop]) ?_
  have e715 : (if decide ((st.noncheaplevel : Int) ≤ S1) then val.Vint (ir ((st.noncheaplevel : Int) - 1))
      else .Vint (ir S1)) = .Vint (ir N) := by
    by_cases hh : (st.noncheaplevel : Int) ≤ S1 <;> simp [N, hh]
  rw [e715]
  simp only [seqPost, Post.after, E0_append]
  apply wp_set_eval
  simp only [Exec.evalExpr, Refine.tv, temps_gss]
  simp only [seqPost, Post.after, E0_append]
  let le2 := PTree.set dense.id.newlevel (.Vint (ir N)) (PTree.set (idOf 715) (.Vint (ir N)) le1)
  have hnl : PTree.get dense.id.newlevel le2 = some (.Vint (ir N)) := temps_gss _ _ _
  have hok2 : Exec.evalExpr ge e le2 m (tv dense.id.ispruneok) = some (Val.of_bool ok) := by
    show PTree.get dense.id.ispruneok le2 = _
    simp only [le2, le1]
    rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide),
      temps_gso _ _ (by decide), hok, ofBool_ir]
  have hcmp := eval_neI (show Exec.evalExpr ge e le2 m (tv dense.id.newlevel) = _ from hnl)
    (eval_gint (c.eg _ (by decide)) E.find_gcaFirst sc.gcaFirst) rfl rfl
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  wp_step; wp_step
  refine wp_sel' (b := ok) (v1 := Val.of_bool (decide (N ≠ (st.gcaFirst : Int))))
    (v2 := .Vint (ir 0)) hok2 rfl
    (fun _ => by
      rw [Exec.evalExpr, hcmp]
      cases decide (N ≠ (st.gcaFirst : Int)) <;> rfl)
    (fun _ => eval_ci 0) ?_
  simp only [seqPost, Post.after, E0_append]
  have hret : ∀ m' nsp' v716, PAt D m₀ m₁ m' S gl cl G bsr st nsp' →
      nsp' = (ok && newLevel st != Int.ofNat st.gcaFirst) →
      Wp xi ge f (sk (.Sreturn (some (tv dense.id.newlevel)))) Q e
        (PTree.set (idOf 716) v716 le2) m' := by
    intro m' nsp' v716 h' hnsp
    subst hnsp
    obtain ⟨mf, hfree, hQr⟩ := hR m' h'
    wp_step; wp_step
    refine wp_return_some (v' := .Vint (ir N))
      (show PTree.get dense.id.newlevel _ = _ by rw [temps_gso _ _ (by decide)]; exact hnl)
      (by rw [hfr]; rfl) hfree ?_
    exact hQr
  apply wp_if_eval
  simp only [Exec.evalExpr, Refine.tv, temps_gss]
  by_cases hk : ok = true
  · subst hk
    by_cases hne : N = (st.gcaFirst : Int)
    · simp only [ite_true, typeof]
      rw [show decide (N ≠ (st.gcaFirst : Int)) = false from by simp [hne],
        show Val.of_bool false = .Vint Int.zero from rfl]
      simp only [cop]
      rw [ite_eq_right (by decide)]
      apply wp_skip
      simp only [seqPost, Post.after, E0_append]
      refine hret m false _ h ?_
      rw [← hN, hne]; simp
    · simp only [ite_true, typeof]
      rw [decide_eq_true hne, show Val.of_bool true = .Vint Int.one from rfl]
      simp only [cop]
      rw [ite_eq_left (by decide)]
      wp_step; wp_step
      refine wp_nsp1 c h ?_
      intro m' h'
      simp only [seqPost, Post.after, E0_append]
      refine hret m' true _ h' ?_
      rw [← hN]; simp [hne]
  · have hk' : ok = false := by simpa using hk
    subst hk'
    simp only [Bool.false_eq_true, ite_false, typeof, cop]
    rw [ite_eq_right (by decide)]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    exact hret m false _ h (by simp)

theorem newLevel_nonneg (hec : 0 ≤ st.eqlevCanon) (hnc : 1 ≤ st.noncheaplevel) :
    0 ≤ newLevel st := by
  unfold newLevel; simp only [Int.ofNat_eq_coe]; split <;> split <;> omega

set_option maxHeartbeats 8000000 in
theorem wp_tail {f : function} {Q : Post} {le : temp_env} {level : Nat}
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st false) (hfr : f.fn_return = tint)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (hl : level ≤ n)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.ptn le = some (.Vptr S.bp S.pofs))
    (hec : 0 ≤ st.eqlevCanon) (hnc : 1 ≤ st.noncheaplevel)
    (hR : ∀ m', PAt D m₀ m₁ m' S gl cl G bsr (pruneReturn level st).2
        (exitValue level (pruneReturn level st).1).2 →
      ∃ mf, Mem.free_list m' (blocks_of_env ge e) = some mf ∧
        Q.ret E0 (.Vint (ir (exitValue level (pruneReturn level st).1).1)) mf) :
    Wp xi ge f tailC Q e le m := by
  have hs := h.search
  have hinv := hs.inv
  have hnl := hs.nlt
  obtain ⟨-, -, a3, -, -, -, -, -, -, -, -, -⟩ := hinv.scalars
  rw [pruneReturn_eq] at hR
  simp only [exitValue] at hR
  have hN := newLevel_nonneg hec hnc
  rw [Int.toNat_of_nonneg hN] at hR
  wp_step; wp_step; wp_step
  refine wp_ifB (eval_neI (show Exec.evalExpr ge e le m (tv dense.id.level) = _ from hlev)
    (eval_gint (c.eg _ (by decide)) E.find_noncheaplevel hs.scalars.noncheaplevel) rfl rfl
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
  by_cases hne : level = st.noncheaplevel
  · rw [decide_eq_false (by exact_mod_cast not_not_intro hne), ite_eq_right (by decide)]
    have hb : (level != st.noncheaplevel) = false := by simp [hne]
    simp only [hb, Bool.false_eq_true, ite_false, Bool.false_and] at hR
    wp_step; wp_step
    apply wp_set_eval
    rw [eval_ci]
    simp only [seqPost, Post.after, E0_append]
    exact wp_tailRest (ok := false) c h hfr hec hnc (temps_gss _ _ _) fun m' h' => hR m' h'
  · rw [decide_eq_true (by exact_mod_cast hne), ite_eq_left rfl]
    have hb : (level != st.noncheaplevel) = true := by simp [hne]
    simp only [hb, ite_true, Bool.true_and] at hR
    rw [pushAuto_eq _ _ hinv.wsCap] at hR
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_ci]
    simp only [seqPost, Post.after, E0_append]
    refine wp_pushPtn c h hnc (by rw [temps_gso _ _ (by decide)]; exact hlab)
      (by rw [temps_gso _ _ (by decide)]; exact hptn) ?_
    intro m1 h1 _
    rw [pushAuto_eq _ _ hinv.wsCap] at h1
    simp only [seqPost, Post.after, E0_append]
    exact wp_tailRest (ok := true) c h1 hfr hec hnc (temps_gss _ _ _) fun m' h' => hR m' h'

end NautyVerified.Proofs.Search.Processnode
