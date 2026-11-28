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
open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}
variable {n : Nat} {D : DispatchC ge O} {m₀ m₁ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
  {G : O.Gr n} {e : env} {bsr : block} {st : SearchState n (O.Canon n)} {nsp : Bool}

theorem wp_scatterAt {f : function} {Q : Post} {le : temp_env} {ref : ident} {bgR bR : block}
    {R : Array Nat} (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    (href : ref ≠ dense.id.sr) (hgR : Genv.find_symbol ge.genv_genv ref = some bgR)
    (hpR : Mem.load .Mint64 m bgR (zOfInt 0) = some (.Vptr bR Ptrofs.zero))
    (hra : ArrayAt m .Mint32 bR 0 (ints R) n)
    (hRsm : ∀ i < n, R[i]! < n) (hRs : ∀ j < n, ∃ i < n, R[i]! = j)
    (hbR : S.bWP ≠ bR) (hbgR : S.bWP ≠ bgR)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hQ : ∀ le' m', PAt D m₀ m₁ m' S gl cl G bsr (scatter R st) nsp →
      ArrayAt m' .Mint32 S.bWP 0 (ints (scatter R st).workperm) n →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) →
      (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f (forLoopC dense.id.i
      (.Ebinop .Olt (tv dense.id.i) (.Evar dense.id.«nauty:n» tint) tint)
      (sk (.Sassign (gat dense.id.«nauty:workperm» (gat ref (tv dense.id.i)))
        (ix dense.id.lab (tv dense.id.i))))) Q e le m := by
  have hs := h.search
  have hd := hs.lit
  have hinv := hs.inv
  have hn0 := hs.n0
  have hcWP : 0 < S.capWP := by have := hs.dyns.capWP; omega
  obtain ⟨v0, ha0⟩ := hs.arrays.workperm
  refine wp_scatter (by have := hs.nlt; omega) hinv.workpermSize hRsm (c.eg _ (by decide))
    E.find_nautyWorkperm (hs.dyns.workperm.ptr hcWP) ha0 hRs (c.eg _ href) hgR hpR hra hlab
    hs.arrays.lab (c.eg _ (by decide)) hs.fixed.nn (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)
    hbR hbgR ?_
  intro le' m' ha' hu hk hv ho
  rw [Spec.scatter_eq] at hQ
  have hu' : Unch m m' (· ∈ [S.bWP]) := hu.mono fun z hz => by simp [hz]
  refine hQ le' m' (PAt.next c h hu' (by simp) ?_ hv
      ((hs.scalars.unch hu (by sep_all hd)).cast rfl) ((hs.stats.unch hu (by sep_ne hd)).cast rfl)
      (hs.arrays.wp hs hu ⟨_, ha'⟩ rfl)
      { hinv with
        workpermSmall := fun i hi =>
          scatterW_small (ref := R) hinv.labSmall
            (fun x hx => hinv.workpermSmall x (by rw [hinv.workpermSize] at hx; exact hx)) n
            (Nat.le_refl n) i (by rw [hinv.workpermSize]; exact hi)
        workpermSize := by rw [scatterW_size, hinv.workpermSize] })
    ha' (fun v hv' => hv'.unch hu fun e =>
      c.ne_blocks (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inl (by simp)))))) e.symm) ho
  intro z hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hk | exact Keep.unch hu (by sep_ne hd)

/-- The code `processnode` gives each classification. -/
def leafCode : Leaf → Int
  | .internal => 0
  | .autoFirst => 1
  | .autoCanon => 2
  | .better _ => 3
  | .bad => 4

theorem classifyCanonG_pick (upd : O.Canon n → Array Nat → Nat → O.Canon n) (level : Nat)
    (st : SearchState n (O.Canon n)) :
    classifyCanonG O upd G level st =
      pickCanon (canonTestG O upd G level st).1 (canonTestG O upd G level st).2 :=
  rfl

theorem wp_canonPick {f : function} {Q : Post} {le : temp_env} {s : Nat}
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ v < n, ∃ i < n, st.canonlab[i]! = v)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hQ : ∀ le' m', PAt D m₀ m₁ m' S gl cl G bsr (pickCanon st s).2 nsp →
      PTree.get dense.id.code le' = some (.Vint (ir (leafCode (pickCanon st s).1))) →
      ((pickCanon st s).1 = .autoCanon →
        ArrayAt m' .Mint32 S.bWP 0 (ints (pickCanon st s).2.workperm) n) →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) →
      (∀ x, x ≠ dense.id.i → x ≠ dense.id.code → PTree.get x le' = PTree.get x le) →
      Q.normal E0 e le' m') :
    Wp xi ge f canonPick Q e le m := by
  have hs := h.search
  have hd := hs.lit
  have hinv := hs.inv
  obtain ⟨-, -, -, -, -, -, -, b8, b9, -, -, -⟩ := hinv.scalars
  have hcCL : 0 < S.capCL := by have := hs.dyns.capCL; have := hs.n0; omega
  wp_step; wp_step
  refine wp_ifB (eval_eqI (eval_gint (c.eg _ (by decide)) E.find_compCanon hs.scalars.compCanon)
    (eval_ci 0) rfl rfl ⟨by omega, by omega⟩ ⟨by decide, by decide⟩) rfl ?_
  by_cases hc0 : st.compCanon = 0
  · rw [decide_eq_true hc0, ite_eq_left rfl]
    have ep : pickCanon st s = (.autoCanon, scatter st.canonlab st) := by simp [pickCanon, hc0]
    rw [ep] at hQ
    wp_step
    refine wp_scatterAt c h (by decide) E.find_nautyCanonlab (hs.dyns.canonlab.ptr hcCL)
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
    refine wp_ifB (eval_gtI (eval_gint (c.eg _ (by decide)) E.find_compCanon hs.scalars.compCanon)
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
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    (hw : ArrayAt m .Mint32 S.bWP 0 (ints w) n) (hws : ∀ i < n, w[i]! < n)
    (hQ : ∀ m', PAt D m₀ m₁ m' S gl cl G bsr st nsp → ArrayAt m' .Mint32 S.bWP 0 (ints w) n →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) →
      Q.normal E0 e (PTree.set (idOf 704) (.Vint (ir (if O.isautom G w then 1 else 0))) le) m') :
    Wp xi ge f isautomCall Q e le m := by
  have hs := h.search
  have hcWP : 0 < S.capWP := by have := hs.dyns.capWP; have := hs.n0; omega
  obtain ⟨fd, hfd, hty, hsat⟩ := D.isautom_fn xi
  refine wp_call (vf := .Vptr D.isautom Ptrofs.zero)
    (targs := [tptr tulong, tptr tint, tint, tint, tint]) (tres := tint)
    (cc := cc_default) (vargs := [.Vptr S.bg S.gofs, .Vptr S.bWP Ptrofs.zero, .Vint (ir 0),
      .Vint (ir S.M), .Vint (ir n)]) fd _
    (hsat G gl S.bg S.gofs S.bWP Ptrofs.zero w S.M) rfl
    (eval_dispatch (c.eg _ (by decide)) E.field_dIsautom rfl (by decide) (by decide)
      hs.fixed.dIsautom)
    ?_ hfd hty
    ⟨rfl, hs.ctx, hs.arrays.graph, hs.graphOk, hw, hws, h.sepG c (by simp) (by simp [ArgBlock])⟩ ?_
  · simp only [Exec.evalExprlist,
      eval_gptr (ty := tptr tulong) (c.eg _ (by decide)) E.find_g rfl hs.fixed.g,
      eval_gptr (ty := tptr tint) (c.eg _ (by decide)) E.find_nautyWorkperm rfl
        ⟨hs.dyns.workperm.ptr hcWP, hs.dyns.workperm.bpW⟩,
      eval_gint (c.eg _ (by decide)) E.find_digraph hs.fixed.digraph,
      eval_gint (c.eg _ (by decide)) E.find_m hs.fixed.mm,
      eval_gint (c.eg _ (by decide)) E.find_n hs.fixed.nn, typeof, cop]
  · rintro t v m' ⟨rfl, rfl, hstep⟩
    have ho : ∀ z, False → z ∈ D.canonBlocks cl S.bc ∨ z = bsr := fun _ h => h.elim
    have hb := h.bsrNot c (out := fun _ => False) id
    exact hQ m' (h.callSame c hstep (fun _ h => h.elim) (hstep.unch.access _ _ _ _ hb h.srW))
      (hw.unch hstep.unch (h.stepNotV c ho (.inr (by simp)))) fun v hv => hv.unch hstep.unch hb

/-- `processnode`'s first-leaf test: `true` for code 1. -/
def firstAuto (O : Ops) (G : O.Gr n) (st : SearchState n (O.Canon n)) : Bool :=
  decide (st.gcaFirst ≥ st.noncheaplevel) || O.isautom G (scatter st.firstlab st).workperm

theorem wp_firstC {f : function} {Q : Post} {le : temp_env}
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    (hfl : ∀ i < n, st.firstlab[i]! < n) (hfs : ∀ v < n, ∃ i < n, st.firstlab[i]! = v)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hQ : ∀ le' m', PAt D m₀ m₁ m' S gl cl G bsr (scatter st.firstlab st) nsp →
      ArrayAt m' .Mint32 S.bWP 0 (ints (scatter st.firstlab st).workperm) n →
      (firstAuto O G st = true → PTree.get dense.id.code le' = some (.Vint (ir 1))) →
      (firstAuto O G st = false → PTree.get dense.id.code le' = PTree.get dense.id.code le) →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) →
      (∀ x, x ≠ dense.id.i → x ≠ idOf 703 → x ≠ idOf 704 → x ≠ dense.id.code →
        PTree.get x le' = PTree.get x le) →
      Q.normal E0 e le' m') :
    Wp xi ge f firstC Q e le m := by
  have hs := h.search
  have hd := hs.lit
  have hinv := hs.inv
  have hFL : 0 < S.capFL := by have := hs.dyns.capFL; have := hs.n0; omega
  wp_step
  refine wp_scatterAt c h (by decide) E.find_nautyFirstlab (hs.dyns.firstlab.ptr hFL)
    hs.arrays.firstlab hfl hfs (by sep_ne hd) (by sep_ne hd) hlab ?_
  intro le1 m1 h1 ha1 hsr1 ho1
  simp only [seqPost, Post.after, E0_append]
  have hs1 := h1.search
  have hinv1 := hs1.inv
  obtain ⟨a1, -, a3, -, -, -, -, -, -, -, -, -⟩ := hinv1.scalars
  have hwsm : ∀ i < n, (scatter st.firstlab st).workperm[i]! < n := hinv1.workpermSmall
  -- the test, into temporary 703
  have hT : ∀ le2 m2, PAt D m₀ m₁ m2 S gl cl G bsr (scatter st.firstlab st) nsp →
      ArrayAt m2 .Mint32 S.bWP 0 (ints (scatter st.firstlab st).workperm) n →
      (∀ v, SrAt m bsr v → SrAt m2 bsr v) →
      PTree.get (idOf 703) le2 = some (.Vint (ir (if firstAuto O G st then 1 else 0))) →
      (∀ x, x ≠ idOf 703 → x ≠ idOf 704 → PTree.get x le2 = PTree.get x le1) →
      Wp xi ge f (.Sifthenelse (tv (idOf 703)) (sk (.Sset dense.id.code (ci 1 tint))) .Sskip)
        Q e le2 m2 := by
    intro le2 m2 h2 ha2 hsr2 h703 ho2
    apply wp_if_eval
    rw [show Exec.evalExpr ge e le2 m2 (tv (idOf 703)) = _ from h703]
    cases hb : firstAuto O G st
    · simp only [Bool.false_eq_true, ite_false, typeof, cop]
      apply wp_skip
      exact hQ le2 m2 h2 ha2 (fun h' => by rw [hb] at h'; exact absurd h' (by decide))
        (fun _ => by rw [ho2 _ (by decide) (by decide), ho1 _ (by decide)]) hsr2
        fun x h1' h2 h3 _ => by rw [ho2 x h2 h3, ho1 x h1']
    · simp only [ite_true, typeof, cop]
      wp_step; wp_step
      apply wp_set_eval
      rw [eval_ci]
      exact hQ _ m2 h2 ha2 (fun _ => temps_gss _ _ _)
        (fun h' => by rw [hb] at h'; exact absurd h' (by decide)) hsr2
        fun x h1' h2 h3 h4 => by rw [temps_gso _ _ h4, ho2 x h2 h3, ho1 x h1']
  wp_step; wp_step; wp_step
  refine wp_ifB (eval_geI (eval_gint (c.eg _ (by decide)) E.find_gcaFirst hs1.scalars.gcaFirst)
    (eval_gint (c.eg _ (by decide)) E.find_noncheaplevel hs1.scalars.noncheaplevel) rfl rfl
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
  by_cases hge : st.noncheaplevel ≤ st.gcaFirst
  · rw [decide_eq_true (by exact_mod_cast hge), ite_eq_left rfl]
    apply wp_set_eval
    rw [eval_ci]
    simp only [seqPost, Post.after, E0_append]
    refine hT _ m1 h1 ha1 hsr1 ?_ fun x h1 _ => temps_gso _ _ h1
    rw [temps_gss]
    have : firstAuto O G st = true := by simp [firstAuto, hge]
    rw [this]; rfl
  · rw [decide_eq_false (by exact_mod_cast hge), ite_eq_right (by decide)]
    wp_step; wp_step; wp_step
    refine wp_isautom c h1 ha1 hwsm ?_
    intro m2 h2 ha2 hsr2
    simp only [seqPost, Post.after, E0_append]
    apply wp_set_eval
    have hfa : firstAuto O G st = O.isautom G (scatter st.firstlab st).workperm := by
      simp [firstAuto, show ¬ st.noncheaplevel ≤ st.gcaFirst from hge]
    simp only [Exec.evalExpr, Refine.tv, temps_gss, typeof]
    cases hb : O.isautom G (scatter st.firstlab st).workperm
    · simp only [Bool.false_eq_true, ite_false]
      refine hT _ m2 h2 ha2 (fun v hv => hsr2 v (hsr1 v hv)) ?_
        fun x h1 h2 => by rw [temps_gso _ _ h1, temps_gso _ _ h2]
      rw [temps_gss, hfa, hb]; rfl
    · simp only [ite_true]
      refine hT _ m2 h2 ha2 (fun v hv => hsr2 v (hsr1 v hv)) ?_
        fun x h1 h2 => by rw [temps_gso _ _ h1, temps_gso _ _ h2]
      rw [temps_gss, hfa, hb]; rfl

end NautyVerified.Proofs.Search.Processnode
