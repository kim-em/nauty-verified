import NautyVerified.Proofs.Search.Processnode.Finish
import NautyVerified.Logic.Switch

/-!
# `processnode`'s `switch`

`wp_switchTail`: the `switch (code)` and the code after it carry out
HexGraphIso's `leafExit` body (`lxBody`) for the classification `leaf`.
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

abbrev switchC : statement :=
  sk (.Sswitch (tv dense.id.«code»)
    (.LScons (some (zOfInt 0)) case0
      (.LScons (some (zOfInt 1)) case1
        (.LScons (some (zOfInt 2)) case2
          (.LScons (some (zOfInt 3)) case3 (.LScons (some (zOfInt 4)) case4 .LSnil))))))

theorem pushAuto_numgen {κ : Type} (st : SearchState n κ) (pair : VSet n × VSet n) :
    (pushAuto st pair).numgenerators = st.numgenerators := by
  unfold pushAuto; split <;> rfl

theorem pruneReturn_numgen {κ : Type} (level : Nat) (st : SearchState n κ) :
    (pruneReturn level st).2.numgenerators = st.numgenerators := by
  rw [pruneReturn_eq]; simp only []; split
  · exact pushAuto_numgen _ _
  · rfl

set_option maxHeartbeats 16000000 in
theorem wp_switchTail {f : function} {Q : Post} {le : temp_env} {level : Nat} {leaf : Leaf}
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st false) (hcb : AutomCb xi S.bUA)
    (hfr : f.fn_return = tint)
    (hcode : PTree.get dense.id.code le = some (.Vint (ir (leafCode leaf))))
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (hl : level ≤ n)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.ptn le = some (.Vptr S.bp S.pofs))
    (hec : 0 ≤ st.eqlevCanon) (hnc : 1 ≤ st.noncheaplevel) (hci : st.cosetindex < n)
    (hperm : leaf = .autoFirst ∨ leaf = .autoCanon →
      ArrayAt m .Mint32 S.bWP 0 (ints st.workperm) n ∧
      ∀ x y, x < n → y < n → st.workperm[x]! = st.workperm[y]! → x = y)
    (hbetter : ∀ s, leaf = .better s → SrAt m bsr s ∧ s ≤ st.samerows)
    (hFin : ∀ m' t, PAt D m₀ m₁ m' S gl cl G bsr (lxBody leaf level st).2
        (exitValue level (lxBody leaf level st).1).2 →
      Writes t (leafWords st (lxBody leaf level st).2) →
      ∃ mf, Mem.free_list m' (blocks_of_env ge e) = some mf ∧
        Q.ret t (.Vint (ir (exitValue level (lxBody leaf level st).1).1)) mf) :
    Wp xi ge f (.Ssequence switchC tailC) Q e le m := by
  have hinv := h.search.inv
  wp_step; wp_step; wp_step
  cases leaf with
  | internal =>
    refine wp_switch (v := .Vint (ir 0)) (z := zOfInt 0) hcode rfl ?_
    show Wp xi ge f (.Ssequence case0 (.Ssequence case1 (.Ssequence case2 (.Ssequence case3
      (.Ssequence case4 .Sskip))))) _ _ _ _
    wp_step; wp_step; wp_step
    obtain ⟨mf, hfree, hret⟩ := hFin m E0 h (by simp [leafWords, lxBody]; exact .nil)
    exact wp_return_some (v' := .Vint (ir level)) hlev (by rw [hfr]; rfl) hfree
      (by simpa [switchPost, seqPost, Post.after, lxBody, exitValue] using hret)
  | autoFirst =>
    refine wp_switch (v := .Vint (ir 1)) (z := zOfInt 1) hcode rfl ?_
    show Wp xi ge f (.Ssequence case1 (.Ssequence case2 (.Ssequence case3
      (.Ssequence case4 .Sskip)))) _ _ _ _
    obtain ⟨hw, hinj⟩ := hperm (.inl rfl)
    wp_step
    simp only [switchPost, seqPost, Post.after, E0_append]
    refine wp_case1 (level := level) c h hcb hfr hw hinv.workpermSize hinv.workpermSmall hinj ?_
    intro m' t h' hW
    have ev : (exitValue level (lxBody .autoFirst level st).1).1 = (st.gcaFirst : Int) := by
      simp only [lxBody, exitValue, admit_eq]
      rw [pushAuto_eq { st with genTrace := st.genTrace.push st.workperm } _ hinv.wsCap]
    have e1 : (lxBody .autoFirst level st).2.numgenerators = st.numgenerators + 1 := by
      simp only [lxBody, admit_eq, pushAuto_numgen]
    have e2 : (lxBody .autoFirst level st).2.workperm = st.workperm := by
      simp only [lxBody, admit_eq]
      unfold pushAuto; split <;> rfl
    obtain ⟨mf, hf, hr⟩ := hFin m' t h' (by simp only [leafWords, e1, ite_true, e2]; exact hW)
    rw [ev] at hr
    exact ⟨mf, hf, hr⟩
  | autoCanon =>
    refine wp_switch (v := .Vint (ir 2)) (z := zOfInt 2) hcode rfl ?_
    show Wp xi ge f (.Ssequence case2 (.Ssequence case3 (.Ssequence case4 .Sskip))) _ _ _ _
    obtain ⟨hw, hinj⟩ := hperm (.inr rfl)
    wp_step
    simp only [switchPost, seqPost, Post.after, E0_append]
    exact wp_case2 c h hcb hfr hci hw hinv.workpermSize hinv.workpermSmall hinj hFin
  | better s =>
    refine wp_switch (v := .Vint (ir 3)) (z := zOfInt 3) hcode rfl ?_
    show Wp xi ge f (.Ssequence case3 (.Ssequence case4 .Sskip)) _ _ _ _
    obtain ⟨hsr, hss⟩ := hbetter s rfl
    wp_step
    refine wp_case3 c h hsr hss hlev hl hlab ?_
    intro le' m' h' ho
    simp only [switchPost, seqPost, Post.after, E0_append]
    refine wp_tail c h' hfr (by rw [ho _ (by simp)]; exact hlev) hl (by rw [ho _ (by simp)]; exact hlab)
      (by rw [ho _ (by simp)]; exact hptn) (by show (0 : Int) ≤ Int.ofNat level; simp) hnc ?_
    intro m'' h''
    exact hFin m'' E0 h'' (by simp [leafWords, lxBody, pruneReturn_numgen, install]; exact .nil)
  | bad =>
    refine wp_switch (v := .Vint (ir 4)) (z := zOfInt 4) hcode rfl ?_
    show Wp xi ge f (.Ssequence case4 .Sskip) _ _ _ _
    wp_step
    refine wp_case4 c h ?_
    intro m' h'
    simp only [switchPost, seqPost, Post.after, E0_append]
    refine wp_tail c h' hfr hlev hl hlab hptn hec hnc ?_
    intro m'' h''
    exact hFin m'' E0 h'' (by simp [leafWords, lxBody, pruneReturn_numgen, install]; exact .nil)

end NautyVerified.Proofs.Search.Processnode
