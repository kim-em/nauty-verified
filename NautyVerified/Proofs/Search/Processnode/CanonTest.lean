import NautyVerified.Proofs.Search.Processnode.Cmp

/-!
# `processnode`'s test against the best leaf

`wp_canonTest`: `if (comp_canon == 0) { if (level < canonlevel) comp_canon = 1;
else { updatecan(…); samerows = n; comp_canon = testcanlab(…, &sr, …); } }`
is `canonTestS`.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Refine (tv)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}
open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}
variable {n : Nat} {D : DispatchC ge O} {m₀ m₁ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
  {G : O.Gr n} {e : env} {bsr : block} {st : SearchState n (O.Canon n)} {nsp : Bool}

set_option maxHeartbeats 4000000 in
theorem wp_canonTest {f : function} {Q : Post} {le : temp_env} {level : Nat} (C : Classifier O)
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp) (hs0 : SrAt m bsr 0)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (hlv : level < 2147483648)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ v < n, ∃ i < n, st.canonlab[i]! = v)
    (hfit : st.compCanon = 0 → O.Fits G (O.rows st.canong) st.canonlab st.samerows)
    (hQ : ∀ le' m', PAt D m₀ m₁ m' S gl cl G bsr (canonTestG O (C.update G) G level st).1 nsp →
      SrAt m' bsr ((canonTestG O (C.update G) G level st).2 : Int) →
      (∀ x, x ≠ idOf 705 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f canonTest Q e le m := by
  have hs := h.search
  have hinv := hs.inv
  obtain ⟨-, -, -, -, -, -, -, b8, b9, b10, -, -⟩ := hinv.scalars
  wp_step; wp_step
  refine wp_ifB (eval_eqI (eval_gint (c.eg _ (by decide)) E.find_compCanon hs.scalars.compCanon)
    (eval_ci 0) rfl rfl ⟨by omega, by omega⟩ ⟨by decide, by decide⟩) rfl ?_
  by_cases hc0 : st.compCanon = 0
  · rw [decide_eq_true hc0, if_pos rfl]
    wp_step; wp_step
    refine wp_ifB (eval_ltI (show Exec.evalExpr ge e le m (tv dense.id.level) = _ from hlev)
      (eval_gint (c.eg _ (by decide)) E.find_canonlevel hs.scalars.canonlevel) rfl rfl
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
    by_cases hlt : level < st.canonlevel
    · rw [decide_eq_true (by exact_mod_cast hlt), if_pos rfl]
      wp_step; wp_step
      refine wp_compCanon c h (x := 1) ⟨by decide, by decide⟩ (eval_ci 1) rfl ?_
      intro m' h' hsr'
      have e1 : canonTestG O (C.update G) G level st = ({ st with compCanon := 1 }, 0) := by
        simp [canonTestG, hc0, hlt]
      rw [e1] at hQ
      exact hQ le m' h' (hsr' _ hs0) fun _ _ => rfl
    · rw [decide_eq_false (by exact_mod_cast hlt), if_neg (by decide)]
      wp_step; wp_step; wp_step
      refine wp_updatecan C c h hcl hcs (hfit hc0) ?_
      intro m2 h2 hfull hsr2
      simp only [seqPost, Post.after, E0_append]
      wp_step; wp_step; wp_step
      refine wp_samerowsN c h2 hfull ?_
      intro m3 h3 hsr3
      simp only [seqPost, Post.after, E0_append]
      wp_step; wp_step; wp_step
      refine wp_testcanlab c h3 rfl (hsr3 _ (hsr2 _ hs0)) hlab ?_
      intro m4 h4 hsr4
      simp only [seqPost, Post.after, E0_append]
      obtain ⟨r1, r2, r3⟩ := C.testcanlab_range G (O.rows (C.update G st.canong st.canonlab st.samerows)) st.lab
      refine wp_compCanon c h4 ⟨r1, r2⟩ (by simp only [Exec.evalExpr, tv, temps_gss]) rfl ?_
      intro m5 h5 hsr5
      have e1 : canonTestG O (C.update G) G level st =
          Prod.mk (α := SearchState n (O.Canon n))
            { st with canong := C.update G st.canong st.canonlab st.samerows, samerows := n,
                      compCanon := (O.testcanlab G (O.rows (C.update G st.canong st.canonlab
                        st.samerows)) st.lab).1 }
            (O.testcanlab G (O.rows (C.update G st.canong st.canonlab st.samerows)) st.lab).2 := by
        simp [canonTestG, hc0, hlt]
      rw [e1] at hQ
      exact hQ _ m5 h5 (hsr5 _ hsr4) fun x hx => temps_gso _ _ hx
  · rw [decide_eq_false hc0, if_neg (by decide)]
    apply wp_skip
    have e1 : canonTestG O (C.update G) G level st = (st, 0) := by simp [canonTestG, hc0]
    rw [e1] at hQ
    exact hQ le m h hs0 fun _ _ => rfl

end NautyVerified.Proofs.Search.Processnode
