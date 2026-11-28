import NautyVerified.Proofs.Search.Processnode.CanonTest

/-!
# `processnode`'s scatter over `SearchAt`

`wp_scatterAt`: the scatter loop through `ref`, holding `R`, leaves the search
state `scatter R st`, with `workperm` holding its permutation.
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
open NautyVerified.Proofs.Refine (tv ix)
open NautyVerified.Proofs.Alloc (gat Keep)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}
variable {n : Nat} {m₀ m₁ m : mem} {S : SLoc} {ctx : Ctx n} {e : env} {bsr : block}
  {st : Search n} {nsp : Bool}

theorem wp_scatterAt {f : function} {Q : Post} {le : temp_env} {ref : ident} {bgR bR : block}
    {R : Array Nat} (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (href : ref ≠ dense.id.sr) (hgR : Genv.find_symbol ge.genv_genv ref = some bgR)
    (hpR : Mem.load .Mint64 m bgR (zOfInt 0) = some (.Vptr bR Ptrofs.zero))
    (hra : ArrayAt m .Mint32 bR 0 (ints R) n)
    (hRsm : ∀ i < n, R[i]! < n) (hRs : ∀ j < n, ∃ i < n, R[i]! = j)
    (hbR : S.bWP ≠ bR) (hbgR : S.bWP ≠ bgR)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hQ : ∀ le' m', PAt m₀ m₁ m' S ctx bsr (scatter R st) nsp →
      ArrayAt m' .Mint32 S.bWP 0 (ints (scatter R st).workperm) n →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) →
      (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f (forLoopC dense.id.i
      (.Ebinop .Olt (tv dense.id.i) (.Evar dense.id.«nauty:n» tint) tint)
      (sk (.Sassign (gat dense.id.«nauty:workperm» (gat ref (tv dense.id.i)))
        (ix dense.id.lab (tv dense.id.i))))) Q e le m := by
  have hs := h.search
  have hd := hs.distinct
  have hinv := hs.inv
  have hn0 := hs.n0
  have hcWP : 0 < S.capWP := by have := hs.dyns.capWP; omega
  obtain ⟨v0, ha0⟩ := hs.arrays.workperm
  refine wp_scatter (by have := hs.nlt; omega) hinv.workpermSize hRsm (c.eg _ (by decide))
    find_nautyWorkperm (hs.dyns.workperm.ptr hcWP) ha0 hRs (c.eg _ href) hgR hpR hra hlab
    hs.arrays.lab (c.eg _ (by decide)) hs.fixed.nn (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)
    hbR hbgR ?_
  intro le' m' ha' hu hk hv ho
  rw [Spec.scatter_eq] at hQ
  have hu' : Unch m m' (· ∈ [S.bWP]) := hu.mono fun z hz => by simp [hz]
  refine hQ le' m' (PAt.next c h hu' (by simp [SLoc.wr, SLoc.wrV]) ?_ hv
      ((hs.scalars.unch hu (by sep_all hd)).cast rfl) ((hs.stats.unch hu (by sep_ne hd)).cast rfl)
      (hs.arrays.wp hd hu ⟨_, ha'⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      { hinv with
        workpermSmall := fun i hi =>
          scatterW_small (ref := R) hinv.labSmall
            (fun x hx => hinv.workpermSmall x (by rw [hinv.workpermSize] at hx; exact hx)) n
            (Nat.le_refl n) i (by rw [hinv.workpermSize]; exact hi)
        workpermSize := by rw [scatterW_size, hinv.workpermSize] })
    ha' (fun v hv' => hv'.unch hu fun e => h.work_ne c (by
      exact absurd (e ▸ (show S.bWP ∈ S.blocks by simp [SLoc.blocks])) (c.ne_blocks · rfl)) rfl) ho
  intro z hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hk | exact Keep.unch hu (by sep_ne hd)

/-- The code `processnode` gives each classification. -/
def leafCode : Leaf → Int
  | .internal => 0
  | .autoFirst => 1
  | .autoCanon => 2
  | .better _ => 3
  | .bad => 4

/-- The end of `classifyCanon`, from the state after the comparison and `sr`. -/
def pickCanon (st : Search n) (sr : Nat) : Leaf × Search n :=
  if st.compCanon = 0 then (.autoCanon, scatter st.canonlab st)
  else if st.compCanon > 0 then (.better sr, st)
  else (.bad, st)

theorem classifyCanon_pick (ctx : Ctx n) (level : Nat) (st : Search n) :
    classifyCanon ctx level st = pickCanon (canonTestS ctx level st).1 (canonTestS ctx level st).2 :=
  rfl

theorem wp_canonPick {f : function} {Q : Post} {le : temp_env} {s : Nat}
    (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ v < n, ∃ i < n, st.canonlab[i]! = v)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hQ : ∀ le' m', PAt m₀ m₁ m' S ctx bsr (pickCanon st s).2 nsp →
      PTree.get dense.id.code le' = some (.Vint (ir (leafCode (pickCanon st s).1))) →
      ((pickCanon st s).1 = .autoCanon →
        ArrayAt m' .Mint32 S.bWP 0 (ints (pickCanon st s).2.workperm) n) →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) →
      (∀ x, x ≠ dense.id.i → x ≠ dense.id.code → PTree.get x le' = PTree.get x le) →
      Q.normal E0 e le' m') :
    Wp xi ge f canonPick Q e le m := by
  have hs := h.search
  have hd := hs.distinct
  have hinv := hs.inv
  obtain ⟨-, -, -, -, -, -, -, b8, b9, -, -, -⟩ := hinv.scalars
  have hcCL : 0 < S.capCL := by have := hs.dyns.capCL; have := hs.n0; omega
  wp_step; wp_step
  refine wp_ifB (eval_eqI (eval_gint (c.eg _ (by decide)) find_compCanon hs.scalars.compCanon)
    (eval_ci 0) rfl rfl ⟨by omega, by omega⟩ ⟨by decide, by decide⟩) rfl ?_
  by_cases hc0 : st.compCanon = 0
  · rw [decide_eq_true hc0, ite_eq_left rfl]
    have ep : pickCanon st s = (.autoCanon, scatter st.canonlab st) := by simp [pickCanon, hc0]
    rw [ep] at hQ
    wp_step
    refine wp_scatterAt c h (by decide) find_nautyCanonlab (hs.dyns.canonlab.ptr hcCL)
      hs.arrays.canonlab hcl hcs (by sep_ne hd) (by sep_ne hd) hlab ?_
    intro le' m' h' ha' hsr' ho
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    apply wp_set_eval
    rw [eval_ci]
    exact hQ _ m' h' (temps_gss _ _ _) (fun _ => ha') hsr' fun x h1 h2 => by
      rw [temps_gso _ _ h2, ho x h1]
  · rw [decide_eq_false hc0, ite_eq_right (by decide)]
    wp_step; wp_step
    refine wp_ifB (eval_gtI (eval_gint (c.eg _ (by decide)) find_compCanon hs.scalars.compCanon)
      (eval_ci 0) rfl rfl ⟨by omega, by omega⟩ ⟨by decide, by decide⟩) rfl ?_
    by_cases hgt : 0 < st.compCanon
    · rw [decide_eq_true hgt, ite_eq_left rfl]
      have ep : pickCanon st s = (.better s, st) := by simp [pickCanon, hc0, hgt]
      rw [ep] at hQ
      wp_step; wp_step
      apply wp_set_eval
      rw [eval_ci]
      exact hQ _ m h (temps_gss _ _ _) (fun h => nomatch h) (fun _ h => h)
        fun x _ h2 => temps_gso _ _ h2
    · rw [decide_eq_false hgt, ite_eq_right (by decide)]
      have ep : pickCanon st s = (.bad, st) := by
        simp only [pickCanon, hc0, if_false]; rw [if_neg (by omega)]
      rw [ep] at hQ
      wp_step; wp_step
      apply wp_set_eval
      rw [eval_ci]
      exact hQ _ m h (temps_gss _ _ _) (fun h => nomatch h) (fun _ h => h)
        fun x _ h2 => temps_gso _ _ h2

abbrev isautomCall : statement :=
  .Scall (some (idOf 704))
    (.Ederef
      (.Efield (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr)) dense.id.«isautom»
        (tptr (tfun [(tptr tulong), (tptr tint), tint, tint, tint] tint)))
      (tfun [(tptr tulong), (tptr tint), tint, tint, tint] tint))
    [(.Evar dense.id.«nauty:g» (tptr tulong)),
     (.Evar dense.id.«nauty:workperm» (tptr tint)),
     (.Evar dense.id.«nauty:digraph» tint),
     (.Evar dense.id.«nauty:m» tint),
     (.Evar dense.id.«nauty:n» tint)]

theorem wp_isautom {f : function} {Q : Post} {le : temp_env} {w : Array Nat}
    (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (hw : ArrayAt m .Mint32 S.bWP 0 (ints w) n) (hws : ∀ i < n, w[i]! < n)
    (hQ : Q.normal E0 e
      (PTree.set (idOf 704) (.Vint (ir (if isautom ctx w then 1 else 0))) le) m) :
    Wp xi ge f isautomCall Q e le m := by
  have hs := h.search
  have hcWP : 0 < S.capWP := by have := hs.dyns.capWP; have := hs.n0; omega
  refine wp_call (vf := .Vptr Block.isautomFn Ptrofs.zero)
    (targs := [tptr tulong, tptr tint, tint, tint, tint]) (tres := tint)
    (cc := cc_default) (vargs := [.Vptr S.bg S.gofs, .Vptr S.bWP Ptrofs.zero, .Vint (ir 0),
      .Vint (ir S.M), .Vint (ir n)]) _ _
    (Isautom.isautom_satisfies S.bg S.gofs S.gw ctx.g S.bWP Ptrofs.zero w S.M) rfl
    (eval_dispatch (c.eg _ (by decide)) field_dIsautom rfl (by decide) (by decide)
      hs.fixed.dIsautom)
    ?_ (by simp [Genv.find_funct, funct_isautomFn]) type_isautom
    ⟨rfl, hs.arrays.graph, hw, hws, hs.tables.naugraphBit, hs.tables.left, hs.M1,
      by have := hs.Mlt; omega, hs.nM⟩ ?_
  · simp only [Exec.evalExprlist,
      eval_gptr (ty := tptr tulong) (c.eg _ (by decide)) find_g rfl hs.fixed.g,
      eval_gptr (ty := tptr tint) (c.eg _ (by decide)) find_nautyWorkperm rfl
        ⟨hs.dyns.workperm.ptr hcWP, hs.dyns.workperm.bpW⟩,
      eval_gint (c.eg _ (by decide)) find_digraph hs.fixed.digraph,
      eval_gint (c.eg _ (by decide)) find_m hs.fixed.mm,
      eval_gint (c.eg _ (by decide)) find_n hs.fixed.nn, typeof, cop]
  · rintro t v m' ⟨rfl, rfl, rfl⟩
    exact hQ

/-- `processnode`'s first-leaf test: `true` for code 1. -/
def firstAuto (ctx : Ctx n) (st : Search n) : Bool :=
  decide (st.gcaFirst ≥ st.noncheaplevel) || isautom ctx (scatter st.firstlab st).workperm

theorem wp_firstC {f : function} {Q : Post} {le : temp_env}
    (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (hfl : ∀ i < n, st.firstlab[i]! < n) (hfs : ∀ v < n, ∃ i < n, st.firstlab[i]! = v)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hQ : ∀ le' m', PAt m₀ m₁ m' S ctx bsr (scatter st.firstlab st) nsp →
      ArrayAt m' .Mint32 S.bWP 0 (ints (scatter st.firstlab st).workperm) n →
      (firstAuto ctx st = true → PTree.get dense.id.code le' = some (.Vint (ir 1))) →
      (firstAuto ctx st = false → PTree.get dense.id.code le' = PTree.get dense.id.code le) →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) →
      (∀ x, x ≠ dense.id.i → x ≠ idOf 703 → x ≠ idOf 704 → x ≠ dense.id.code →
        PTree.get x le' = PTree.get x le) →
      Q.normal E0 e le' m') :
    Wp xi ge f firstC Q e le m := by
  have hs := h.search
  have hd := hs.distinct
  have hinv := hs.inv
  have hFL : 0 < S.capFL := by have := hs.dyns.capFL; have := hs.n0; omega
  wp_step
  refine wp_scatterAt c h (by decide) find_nautyFirstlab (hs.dyns.firstlab.ptr hFL)
    hs.arrays.firstlab hfl hfs (by sep_ne hd) (by sep_ne hd) hlab ?_
  intro le1 m1 h1 ha1 hsr1 ho1
  simp only [seqPost, Post.after, E0_append]
  have hs1 := h1.search
  have hinv1 := hs1.inv
  obtain ⟨a1, -, a3, -, -, -, -, -, -, -, -, -⟩ := hinv1.scalars
  have hwsm : ∀ i < n, (scatter st.firstlab st).workperm[i]! < n := hinv1.workpermSmall
  -- the test, into temporary 703
  have hT : ∀ le2, PTree.get (idOf 703) le2 = some (.Vint (ir (if firstAuto ctx st then 1 else 0))) →
      (∀ x, x ≠ idOf 703 → x ≠ idOf 704 → PTree.get x le2 = PTree.get x le1) →
      Wp xi ge f (.Sifthenelse (tv (idOf 703)) (sk (.Sset dense.id.code (ci 1 tint))) .Sskip)
        Q e le2 m1 := by
    intro le2 h703 ho2
    apply wp_if_eval
    rw [show Exec.evalExpr ge e le2 m1 (tv (idOf 703)) = _ from h703]
    cases hb : firstAuto ctx st
    · simp only [Bool.false_eq_true, ite_false, typeof, cop]
      apply wp_skip
      exact hQ le2 m1 h1 ha1 (fun h' => by rw [hb] at h'; exact absurd h' (by decide)) (fun _ => by rw [ho2 _ (by decide) (by decide),
        ho1 _ (by decide)]) hsr1 fun x h1' h2 h3 _ => by rw [ho2 x h2 h3, ho1 x h1']
    · simp only [ite_true, typeof, cop]
      wp_step; wp_step
      apply wp_set_eval
      rw [eval_ci]
      exact hQ _ m1 h1 ha1 (fun _ => temps_gss _ _ _)
        (fun h' => by rw [hb] at h'; exact absurd h' (by decide)) hsr1
        fun x h1' h2 h3 h4 => by rw [temps_gso _ _ h4, ho2 x h2 h3, ho1 x h1']
  wp_step; wp_step; wp_step
  refine wp_ifB (eval_geI (eval_gint (c.eg _ (by decide)) find_gcaFirst hs1.scalars.gcaFirst)
    (eval_gint (c.eg _ (by decide)) find_noncheaplevel hs1.scalars.noncheaplevel) rfl rfl
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
  by_cases hge : st.noncheaplevel ≤ st.gcaFirst
  · rw [decide_eq_true (by exact_mod_cast hge), ite_eq_left rfl]
    apply wp_set_eval
    rw [eval_ci]
    simp only [seqPost, Post.after, E0_append]
    refine hT _ ?_ fun x h1 _ => temps_gso _ _ h1
    rw [temps_gss]
    have : firstAuto ctx st = true := by simp [firstAuto, hge]
    rw [this]; rfl
  · rw [decide_eq_false (by exact_mod_cast hge), ite_eq_right (by decide)]
    wp_step; wp_step; wp_step
    refine wp_isautom c h1 ha1 hwsm ?_
    simp only [seqPost, Post.after, E0_append]
    apply wp_set_eval
    have hfa : firstAuto ctx st = isautom ctx (scatter st.firstlab st).workperm := by
      simp [firstAuto, show ¬ st.noncheaplevel ≤ st.gcaFirst from hge]
    simp only [Exec.evalExpr, Refine.tv, temps_gss, typeof]
    cases hb : isautom ctx (scatter st.firstlab st).workperm
    · simp only [Bool.false_eq_true, ite_false]
      refine hT _ ?_ fun x h1 h2 => by rw [temps_gso _ _ h1, temps_gso _ _ h2]
      rw [temps_gss, hfa, hb]; rfl
    · simp only [ite_true]
      refine hT _ ?_ fun x h1 h2 => by rw [temps_gso _ _ h1, temps_gso _ _ h2]
      rw [temps_gss, hfa, hb]; rfl

end NautyVerified.Proofs.Search.Processnode
