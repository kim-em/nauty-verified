import NautyVerified.Proofs.Search.Processnode.Leaf

/-!
# `processnode`'s classification

`wp_classifyC`: `processnode`'s code up to the `switch` computes HexGraphIso's
`classify`, leaving its code in `code`.
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
variable {n : Nat} {m₀ m₁ m : mem} {S : SLoc} {ctx : Ctx n} {e : env} {bsr : block}
  {st : Search n} {nsp : Bool}

theorem canonTestS_canonlab (ctx : Ctx n) (level : Nat) (st : Search n) :
    (canonTestS ctx level st).1.canonlab = st.canonlab := by
  unfold canonTestS; split
  · split <;> rfl
  · rfl

theorem pickCanon_ne (st : Search n) (s : Nat) : (pickCanon st s).1 ≠ .autoFirst := by
  unfold pickCanon; split
  · simp
  · split <;> simp

theorem pickCanon_better (st : Search n) {s s' : Nat} (h : (pickCanon st s).1 = .better s') :
    s' = s := by
  revert h; unfold pickCanon; split
  · simp
  · split
    · simp; omega
    · simp

/-- What the C leaves for the classification `r`. -/
structure Classified (m₀ m₁ m' : mem) (S : SLoc) (ctx : Ctx n) (bsr : block) (le le' : temp_env)
    (r : Leaf × Search n) : Prop where
  at_ : PAt m₀ m₁ m' S ctx bsr r.2 false
  code : PTree.get dense.id.code le' = some (.Vint (ir (leafCode r.1)))
  perm : r.1 = .autoFirst ∨ r.1 = .autoCanon → ArrayAt m' .Mint32 S.bWP 0 (ints r.2.workperm) n
  sr : ∀ s, r.1 = .better s → SrAt m' bsr s
  temps : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.numcells],
    PTree.get x le' = PTree.get x le

/-- The canonical comparison and its code, from `code == 0`. -/
theorem wp_canonBranch {f : function} {Q : Post} {le : temp_env} {level : Nat}
    (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st false)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (hlv : level < 2147483648)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hcode : PTree.get dense.id.code le = some (.Vint (ir 0)))
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ v < n, ∃ i < n, st.canonlab[i]! = v)
    (hQ : ∀ le' m', Classified m₀ m₁ m' S ctx bsr le le' (classifyCanon ctx level st) →
      Q.normal E0 e le' m') :
    Wp xi ge f (sk (.Sifthenelse (.Ebinop .Oeq (tv dense.id.«code») (ci 0 tint) tint)
      (sk (.Sifthenelse (.Evar dense.id.«nauty:getcanon» tint)
        (.Ssequence (sk (.Sassign (.Evar dense.id.«sr» tint) (ci 0 tint)))
          (.Ssequence canonTest canonPick))
        (sk (.Sset dense.id.«code» (ci 4 tint)))))
      .Sskip)) Q e le m := by
  have hs := h.search
  rw [classifyCanon_pick] at hQ
  wp_step; wp_step
  refine wp_ifB (eval_eqI (show Exec.evalExpr ge e le m (tv dense.id.code) = _ from hcode)
    (eval_ci 0) rfl rfl ⟨by decide, by decide⟩ ⟨by decide, by decide⟩) rfl ?_
  simp only [decide_true, ite_true]
  wp_step; wp_step
  apply wp_if_eval
  rw [eval_gint (c.eg _ (by decide)) find_getcanon hs.fixed.getcanon]
  simp only [typeof, cop]
  rw [ite_eq_left (by decide)]
  wp_step; wp_step; wp_step
  refine wp_sr0 c h ?_
  intro m2 h2 hsr2
  simp only [seqPost, Post.after, E0_append]
  wp_step
  refine wp_canonTest c h2 hsr2 hlev hlv hlab hcl hcs ?_
  intro le3 m3 h3 hsr3 ho3
  simp only [seqPost, Post.after, E0_append]
  refine wp_canonPick (s := (canonTestS ctx level st).2) c h3 (by rw [canonTestS_canonlab]; exact hcl)
    (by rw [canonTestS_canonlab]; exact hcs)
    (by rw [ho3 _ (by decide)]; exact hlab) ?_
  intro le4 m4 h4 hc4 hp4 hsr4 ho4
  refine hQ le4 m4 ⟨h4, hc4, fun hx => hp4 (by
      rcases hx with hx | hx
      · exact absurd hx (pickCanon_ne _ _)
      · exact hx), fun s hb => ?_, fun x hx => ?_⟩
  · rw [pickCanon_better _ hb]; exact hsr4 _ hsr3
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rw [ho4 x (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide),
      ho3 x (by rcases hx with rfl | rfl | rfl | rfl <;> decide)]

set_option maxHeartbeats 4000000 in
theorem wp_classifyC {f : function} {Q : Post} {le : temp_env} {level numcells : Nat}
    (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st false)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (hlv : level ≤ n)
    (hnc : PTree.get dense.id.numcells le = some (.Vint (ir numcells))) (hncn : numcells ≤ n)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hcode : PTree.get dense.id.code le = some (.Vint (ir 0)))
    (hfl : ∀ i < n, st.firstlab[i]! < n) (hfs : ∀ v < n, ∃ i < n, st.firstlab[i]! = v)
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ v < n, ∃ i < n, st.canonlab[i]! = v)
    (hQ : ∀ le' m', Classified m₀ m₁ m' S ctx bsr le le' (classify ctx level numcells st) →
      Q.normal E0 e le' m') :
    Wp xi ge f classifyC Q e le m := by
  have hs := h.search
  have hinv := hs.inv
  have hnlt := hs.nlt
  obtain ⟨-, -, -, -, a5, -, -, b8, b9, -, -, -⟩ := hinv.scalars
  rw [Spec.classify_eq] at hQ
  -- the numcells branch, entered with `code == 0`
  have hN : ∀ le2, ¬ (st.eqlevFirst ≠ level ∧ st.compCanon < 0) →
      (∀ x, x ≠ idOf 706 → PTree.get x le2 = PTree.get x le) →
      Wp xi ge f (sk
        (.Sifthenelse
          (.Ebinop .Oeq (tv dense.id.«numcells») (.Evar dense.id.«nauty:n» tint) tint)
          (.Ssequence
            (sk (.Sifthenelse
              (.Ebinop .Oeq (.Evar dense.id.«nauty:eqlev_first» tint) (tv dense.id.«level») tint)
              firstC .Sskip))
            (sk (.Sifthenelse (.Ebinop .Oeq (tv dense.id.«code») (ci 0 tint) tint)
              (sk (.Sifthenelse (.Evar dense.id.«nauty:getcanon» tint)
                (.Ssequence (sk (.Sassign (.Evar dense.id.«sr» tint) (ci 0 tint)))
                  (.Ssequence canonTest canonPick))
                (sk (.Sset dense.id.«code» (ci 4 tint)))))
              .Sskip)))
          .Sskip)) Q e le2 m := by
    intro le2 hAB ho2
    rw [if_neg hAB] at hQ
    have g : ∀ x, x ≠ idOf 706 → PTree.get x le2 = PTree.get x le := ho2
    wp_step; wp_step
    refine wp_ifB (eval_eqI (show Exec.evalExpr ge e le2 m (tv dense.id.numcells) = _ by
        rw [show Exec.evalExpr ge e le2 m (tv dense.id.numcells) = PTree.get dense.id.numcells le2
          from rfl, g _ (by decide)]; exact hnc)
      (eval_gint (c.eg _ (by decide)) find_n hs.fixed.nn) rfl rfl ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩) rfl ?_
    by_cases hnn : numcells = n
    · rw [decide_eq_true (by exact_mod_cast hnn), ite_eq_left rfl]
      rw [if_neg (show ¬ numcells ≠ n from fun h => h hnn)] at hQ
      have hlev2 : PTree.get dense.id.level le2 = some (.Vint (ir level)) := by
        rw [g _ (by decide)]; exact hlev
      have hlab2 : PTree.get dense.id.lab le2 = some (.Vptr S.bl S.lofs) := by
        rw [g _ (by decide)]; exact hlab
      have hcode2 : PTree.get dense.id.code le2 = some (.Vint (ir 0)) := by
        rw [g _ (by decide)]; exact hcode
      have key : firstAuto ctx st = true ↔ (st.gcaFirst ≥ st.noncheaplevel ∨
          isautom ctx (scatter st.firstlab st).workperm = true) := by simp [firstAuto]
      have tl : ∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.numcells],
          x ≠ dense.id.i ∧ x ≠ idOf 703 ∧ x ≠ idOf 704 ∧ x ≠ dense.id.code ∧ x ≠ idOf 705 ∧
            x ≠ idOf 706 := by decide
      wp_step; wp_step; wp_step
      refine wp_ifB (eval_eqI (eval_gint (c.eg _ (by decide)) find_eqlevFirst hs.scalars.eqlevFirst)
        (show Exec.evalExpr ge e le2 m (tv dense.id.level) = _ from hlev2) rfl rfl
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
      by_cases hel : st.eqlevFirst = level
      · rw [decide_eq_true (by exact_mod_cast hel), ite_eq_left rfl]
        rw [if_pos hel] at hQ
        refine wp_firstC c h hfl hfs hlab2 ?_
        intro le3 m3 h3 ha3 hT hF hsr3 ho3
        simp only [seqPost, Post.after, E0_append]
        cases hfa : firstAuto ctx st
        · rw [if_neg (fun hh => by rw [← key, hfa] at hh; exact absurd hh (by decide))] at hQ
          refine wp_canonBranch c h3 (by rw [ho3 _ (by decide) (by decide) (by decide) (by decide)]; exact hlev2)
            (by omega) (by rw [ho3 _ (by decide) (by decide) (by decide) (by decide)]; exact hlab2)
            (by rw [hF hfa]; exact hcode2) (by rw [Spec.scatter_eq]; exact hcl)
            (by rw [Spec.scatter_eq]; exact hcs) ?_
          intro le4 m4 hC
          exact hQ le4 m4 ⟨hC.at_, hC.code, hC.perm, hC.sr, fun x hx => by
            obtain ⟨t1, t2, t3, t4, -, t6⟩ := tl x hx
            rw [hC.temps x hx, ho3 x t1 t2 t3 t4, g x t6]⟩
        · rw [if_pos (key.1 hfa)] at hQ
          wp_step; wp_step
          refine wp_ifB (eval_eqI (show Exec.evalExpr ge e le3 m3 (tv dense.id.code) = _ from hT hfa)
            (eval_ci 0) rfl rfl ⟨by decide, by decide⟩ ⟨by decide, by decide⟩) rfl ?_
          simp only [show ((1 : Int) = 0) = False from by decide, decide_false, Bool.false_eq_true,
            ite_false]
          apply wp_skip
          exact hQ le3 m3 ⟨h3, hT hfa, fun _ => ha3, (fun _ hx => by cases hx), fun x hx => by
            obtain ⟨t1, t2, t3, t4, -, t6⟩ := tl x hx
            rw [ho3 x t1 t2 t3 t4, g x t6]⟩
      · rw [decide_eq_false (by exact_mod_cast hel), ite_eq_right (by decide)]
        rw [if_neg hel] at hQ
        apply wp_skip
        simp only [seqPost, Post.after, E0_append]
        refine wp_canonBranch c h hlev2 (by omega) hlab2 hcode2 hcl hcs ?_
        intro le4 m4 hC
        exact hQ le4 m4 ⟨hC.at_, hC.code, hC.perm, hC.sr, fun x hx => by
          rw [hC.temps x hx, g x (tl x hx).2.2.2.2.2]⟩
    · rw [decide_eq_false (by exact_mod_cast hnn), ite_eq_right (by decide)]
      rw [if_pos hnn] at hQ
      apply wp_skip
      exact hQ le2 m ⟨h, (by rw [g _ (by decide)]; exact hcode),
        (fun hx => by rcases hx with hx | hx <;> cases hx),
        (fun _ hx => by cases hx), fun x hx => g x (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl <;> decide)⟩
  wp_step; wp_step; wp_step
  refine wp_ifB (eval_neI (eval_gint (c.eg _ (by decide)) find_eqlevFirst hs.scalars.eqlevFirst)
    (show Exec.evalExpr ge e le m (tv dense.id.level) = _ from hlev) rfl rfl
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
  by_cases hel : st.eqlevFirst = level
  · rw [decide_eq_false (by exact_mod_cast not_not_intro hel), ite_eq_right (by decide)]
    apply wp_set_eval
    rw [eval_ci]
    simp only [seqPost, Post.after, E0_append]
    apply wp_if_eval
    simp only [Exec.evalExpr, Refine.tv, temps_gss, typeof, cop]
    rw [show (!Int.eq (ir 0) Int.zero) = false from rfl, if_neg (by decide)]
    exact hN _ (fun hh => hh.1 hel) fun x hx => temps_gso _ _ hx
  · rw [decide_eq_true (by exact_mod_cast hel), ite_eq_left rfl]
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, eval_gint (c.eg _ (by decide)) find_getcanon hs.fixed.getcanon]
    simp only [typeof, cop]
    rw [show (!!Int.eq (ir 1) Int.zero) = false from rfl, if_neg (by decide)]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, eval_ltI (eval_gint (c.eg _ (by decide)) find_compCanon hs.scalars.compCanon)
      (eval_ci 0) rfl rfl ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
    by_cases hcn : st.compCanon < 0
    · simp only [decide_eq_true hcn, typeof, cop, seqPost, Post.after, E0_append]
      apply wp_set_eval
      simp only [Exec.evalExpr, Refine.tv, temps_gss, typeof, cop]
      apply wp_if_eval
      simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, typeof, cop, ite_true]
      rw [if_pos ⟨hel, hcn⟩] at hQ
      wp_step; wp_step
      apply wp_set_eval
      rw [eval_ci]
      exact hQ _ m ⟨h, temps_gss _ _ _, (fun hx => by rcases hx with hx | hx <;> cases hx),
        (fun _ hx => by cases hx), fun x hx => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl <;>
            simp (config := {decide := true}) only [temps_gso, ne_eq, not_false_eq_true]⟩
    · simp only [decide_eq_false hcn, typeof, cop, seqPost, Post.after, E0_append]
      apply wp_set_eval
      simp only [Exec.evalExpr, Refine.tv, temps_gss, typeof, cop]
      apply wp_if_eval
      simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, typeof, cop, ite_false]
      exact hN _ (fun hh => hcn hh.2) fun x hx => by rw [temps_gso _ _ hx, temps_gso _ _ hx]

end NautyVerified.Proofs.Search.Processnode
