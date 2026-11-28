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

end NautyVerified.Proofs.Search.Processnode
