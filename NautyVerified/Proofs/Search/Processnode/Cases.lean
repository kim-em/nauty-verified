import NautyVerified.Proofs.Search.Processnode.Callback
import NautyVerified.Proofs.Search.Node.InvSteps

/-!
# `processnode`'s first two cases

`wp_case1`: code 1, an automorphism mapping the first leaf here: record it,
join the orbits, count and report it, return `gca_first`.
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

/-- `genTrace` is not in memory. -/
theorem PAt.genTrace (h : PAt D m₀ m₁ m S gl cl G bsr st nsp) (g : Array (Array Nat)) :
    PAt D m₀ m₁ m S gl cl G bsr { st with genTrace := g } nsp :=
  { h with
    search := { h.search with
      scalars := h.search.scalars.cast rfl
      stats := h.search.stats.cast rfl
      arrays := h.search.arrays.cast rfl
      inv := { h.search.inv with } } }

/-- `if (g) s;` for an `int` global holding 0. -/
theorem wp_ifG0 {f : function} {Q : Post} {le : temp_env} {g : ident} {b : block} {s : statement}
    (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some b) (hI : IntAt m b 0)
    (hQ : Q.normal E0 e le m) :
    Wp xi ge f (sk (.Sifthenelse (.Evar g tint) s .Sskip)) Q e le m := by
  wp_step; wp_step
  apply wp_if_eval
  rw [eval_gint hge hg hI]
  simp only [typeof, cop]
  rw [ite_eq_right (by decide)]
  exact wp_skip hQ

theorem admit_eq {κ : Type} (st : SearchState n κ) :
    admit st = { pushAuto { st with genTrace := st.genTrace.push st.workperm } (fmperm st.workperm n) with
      orbits := (orbjoin st.orbits st.workperm n).1, numorbits := (orbjoin st.orbits st.workperm n).2 } := by
  unfold admit
  simp only [Id.run, pure]
  have : (pushAuto { st with genTrace := st.genTrace.push st.workperm } (fmperm st.workperm n)).orbits =
        st.orbits ∧
      (pushAuto { st with genTrace := st.genTrace.push st.workperm } (fmperm st.workperm n)).workperm =
        st.workperm := by
    unfold pushAuto; split <;> exact ⟨rfl, rfl⟩
  rw [this.1, this.2]

set_option maxHeartbeats 8000000 in
theorem wp_case1 {f : function} {Q : Post} {le : temp_env} {level : Nat}
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st false) (hcb : AutomCb xi S.bUA)
    (hfr : f.fn_return = tint)
    (hw : ArrayAt m .Mint32 S.bWP 0 (ints st.workperm) n) (hwsz : st.workperm.size = n)
    (hws : ∀ i < n, st.workperm[i]! < n)
    (hwi : ∀ x y, x < n → y < n → st.workperm[x]! = st.workperm[y]! → x = y)
    (hR : ∀ m' t, PAt D m₀ m₁ m' S gl cl G bsr (lxBody .autoFirst level st).2 false →
      Writes t (genWords st.workperm n) →
      ∃ mf, Mem.free_list m' (blocks_of_env ge e) = some mf ∧
        Q.ret t (.Vint (ir st.gcaFirst)) mf) :
    Wp xi ge f case1 Q e le m := by
  have hinv := h.search.inv
  have h1 := h.genTrace (st.genTrace.push st.workperm)
  simp only [lxBody, admit_eq] at hR
  rw [pushAuto_eq { st with genTrace := st.genTrace.push st.workperm } _ hinv.wsCap] at hR
  refine wp_pushPerm c h1 hw hwsz hws hwi ?_
  intro m2 h2 hw2 hsr2
  rw [pushAuto_eq { st with genTrace := st.genTrace.push st.workperm } _ hinv.wsCap] at h2
  wp_step
  refine wp_ifG0 (c.eg _ (by decide)) E.find_writeautoms h2.search.fixed.writeautoms ?_
  simp only [seqPost, Post.after, E0_append]
  wp_step
  refine wp_orbjoin (t := idOf 708) c h2 hw2 hws ?_
  intro m3 h3 hw3 hsr3
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_numgenerators c h3 ?_
  intro m4 h4 hsr4 hu4
  simp only [seqPost, Post.after, E0_append]
  have hd := h4.search.lit
  wp_step
  refine wp_callback c h4 hcb (hw3.unch hu4 (by sep_ne hd)) hws ?_
  intro t hW
  simp only [seqPost, Post.after, E0_append]
  wp_step
  refine wp_ifG0 (c.eg _ (by decide)) E.find_doschreier h4.search.fixed.doschreier ?_
  simp only [seqPost, Post.after, E0_append, E0_left, E0_right]
  wp_step; wp_step
  obtain ⟨mf, hfree, hret⟩ := hR m4 t h4 hW
  refine wp_return_some (v' := .Vint (ir st.gcaFirst)) (eval_gint (c.eg _ (by decide)) E.find_gcaFirst h4.search.scalars.gcaFirst)
    (by rw [hfr]; rfl) hfree ?_
  simpa using hret

end NautyVerified.Proofs.Search.Processnode
