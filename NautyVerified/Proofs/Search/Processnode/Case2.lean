import NautyVerified.Proofs.Search.Processnode.Cases

/-!
# `processnode`'s case 2

`wp_case2`: code 2, an automorphism mapping the best leaf here: record it and
join the orbits; if the orbits did not change, return `gca_canon` (asking for a
short prune off the first path); otherwise count and report it, and return
`gca_first` if `cosetindex` is no longer least in its orbit, else `gca_canon`.
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
open NautyVerified.Proofs.Alloc (gat Keep)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}
open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}
variable {n : Nat} {D : DispatchC ge O} {m₀ m₁ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
  {G : O.Gr n} {e : env} {bsr : block} {st : SearchState n (O.Canon n)} {nsp : Bool}

/-- `if (gca_canon != gca_first) needshortprune = 1;` -/
abbrev nspIf : statement :=
  sk (.Sifthenelse
    (.Ebinop .One (.Evar dense.id.«nauty:gca_canon» tint) (.Evar dense.id.«nauty:gca_first» tint) tint)
    (sk (.Sassign (.Evar dense.id.«nauty:needshortprune» tint) (ci 1 tint))) .Sskip)

theorem wp_nspIf {f : function} {Q : Post} {le : temp_env} (c : PCtx D m₀ m₁ S gl cl e bsr)
    (h : PAt D m₀ m₁ m S gl cl G bsr st false)
    (hQ : ∀ m', PAt D m₀ m₁ m' S gl cl G bsr st (st.gcaCanon != st.gcaFirst) →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Q.normal E0 e le m') :
    Wp xi ge f nspIf Q e le m := by
  have hs := h.search
  have hd := hs.lit
  have hinv := hs.inv
  obtain ⟨a1, a2, -, -, -, -, -, -, -, -, -, -⟩ := hinv.scalars
  wp_step; wp_step
  refine wp_ifB (eval_neI (eval_gint (c.eg _ (by decide)) E.find_gcaCanon hs.scalars.gcaCanon)
    (eval_gint (c.eg _ (by decide)) E.find_gcaFirst hs.scalars.gcaFirst) rfl rfl
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
  by_cases hne : st.gcaCanon = st.gcaFirst
  · rw [decide_eq_false (by exact_mod_cast not_not_intro hne), ite_eq_right (by decide)]
    apply wp_skip
    exact hQ m (by rw [show (st.gcaCanon != st.gcaFirst) = false by simp [hne]]; exact h) fun _ h => h
  · rw [decide_eq_true (by exact_mod_cast hne), ite_eq_left rfl]
    wp_step; wp_step
    refine wp_gint (c.eg _ (by decide)) E.find_needshortprune hs.scalars.needshortprune.writable
      (eval_ci 1) rfl ?_
    intro m' hI hu hv
    have hu' : Unch m m' (· ∈ [E.needshortprune]) := hu.mono fun z hz => by simp [hz]
    have sc := hs.scalars
    refine hQ m' ?_ fun v hv' => hv'.unch hu fun e => c.ne_blocks (SLoc.mem_blocksG_lit (by simp [SLoc.litG])) e.symm
    rw [show (st.gcaCanon != st.gcaFirst) = true by simp [hne]]
    exact PAt.next c h hu' (by simp) (keeps hd, hu) hv
      ⟨sc.gcaFirst.unch hu (by sep_ne hd), sc.gcaCanon.unch hu (by sep_ne hd),
        sc.noncheaplevel.unch hu (by sep_ne hd), sc.allsamelevel.unch hu (by sep_ne hd),
        sc.eqlevFirst.unch hu (by sep_ne hd), sc.eqlevCanon.unch hu (by sep_ne hd),
        sc.compCanon.unch hu (by sep_ne hd), sc.samerows.unch hu (by sep_ne hd),
        sc.canonlevel.unch hu (by sep_ne hd), sc.stabvertex.unch hu (by sep_ne hd),
        sc.cosetindex.unch hu (by sep_ne hd), by simpa using hI⟩
      (hs.stats.unch hu (by sep_ne hd))
      (hs.arrays.unch hu' (by sep_all hd) (hs.graph_notin (by simp)) (hs.canon_notin (by simp))) hinv

/-- `orbits[cosetindex] < cosetindex`. -/
theorem eval_coset {le : temp_env} (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    (hci : st.cosetindex < n) :
    Exec.evalExpr ge e le m (.Ebinop .Olt (gat dense.id.«nauty:orbits» (.Evar dense.id.«nauty:cosetindex» tint))
      (.Evar dense.id.«nauty:cosetindex» tint) tint) =
      some (Val.of_bool (decide (st.orbits[st.cosetindex]! < st.cosetindex))) := by
  have hs := h.search
  have hnl := hs.nlt
  have harr := hs.arrays.orbits
  have ho : Exec.evalExpr ge e le m (gat dense.id.«nauty:orbits» (.Evar dense.id.«nauty:cosetindex» tint)) =
      some (ints st.orbits st.cosetindex) := by
    simp only [Exec.evalExpr, Exec.lvalOfVar, c.eg _ (by decide : dense.id.«nauty:orbits» ≠ dense.id.sr),
      E.find_orbits, Exec.derefLoc, access_mode, Mem.loadv, Alloc.Mptr_eq,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hs.fixed.orbits.load,
      c.eg _ (by decide : dense.id.«nauty:cosetindex» ≠ dense.id.sr), E.find_cosetindex,
      hs.scalars.cosetindex.load, typeof, cop]
    apply load_array harr hci
    apply addr_elem S.oofs _ .Mint32 rfl rfl (by omega)
    have hf := harr.fits
    have h4 : csize .Mint32 = 4 := rfl
    have hob : S.ob = intOfZ (Ptrofs.unsigned S.oofs) := rfl
    rw [h4] at hf ⊢
    omega
  have := eval_ltI ho (eval_gint (c.eg _ (by decide)) E.find_cosetindex hs.scalars.cosetindex) rfl rfl
    ⟨by have := hs.inv.orbitsSmall _ hci; omega, by have := hs.inv.orbitsSmall _ hci; omega⟩
    ⟨by omega, by omega⟩
  rw [show decide ((st.orbits[st.cosetindex]! : Int) < st.cosetindex) =
    decide (st.orbits[st.cosetindex]! < st.cosetindex) from by simp] at this
  exact this

/-- What `processnode` writes for an exit from `st`. -/
abbrev leafWords {κ : Type} (st r : SearchState n κ) : List Int :=
  if r.numgenerators = st.numgenerators + 1 then genWords r.workperm n else []

set_option maxHeartbeats 16000000 in
theorem wp_case2 {f : function} {Q : Post} {le : temp_env} {level : Nat}
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st false) (hcb : AutomCb xi S.bUA)
    (hfr : f.fn_return = tint) (hci : st.cosetindex < n)
    (hw : ArrayAt m .Mint32 S.bWP 0 (ints st.workperm) n) (hwsz : st.workperm.size = n)
    (hws : ∀ i < n, st.workperm[i]! < n)
    (hwi : ∀ x y, x < n → y < n → st.workperm[x]! = st.workperm[y]! → x = y)
    (hR : ∀ m' t, PAt D m₀ m₁ m' S gl cl G bsr (lxBody .autoCanon level st).2
        (exitValue level (lxBody .autoCanon level st).1).2 →
      Writes t (leafWords st (lxBody .autoCanon level st).2) →
      ∃ mf, Mem.free_list m' (blocks_of_env ge e) = some mf ∧
        Q.ret t (.Vint (ir (exitValue level (lxBody .autoCanon level st).1).1)) mf) :
    Wp xi ge f case2 Q e le m := by
  have hinv := h.search.inv
  have hnl := h.search.nlt
  have h1 := h.genTrace (st.genTrace.push st.workperm)
  simp only [lxBody, admit_eq] at hR
  rw [pushAuto_eq { st with genTrace := st.genTrace.push st.workperm } _ hinv.wsCap] at hR
  refine wp_pushPerm c h1 hw hwsz hws hwi ?_
  intro m2 h2 hw2 hsr2
  rw [pushAuto_eq { st with genTrace := st.genTrace.push st.workperm } _ hinv.wsCap] at h2
  have hfit := h2.search.stats.fits
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_statsF (ty := tint) (c.eg _ (by decide)) fld_numorbits rfl h2.search.fixed.stats (by decide)
    (by omega) h2.search.stats.numorbits]
  simp only [seqPost, Post.after, E0_append]
  wp_step
  refine wp_orbjoin (t := idOf 709) c h2 hw2 hws ?_
  intro m3 h3 hw3 hsr3
  simp only [seqPost, Post.after, E0_append]
  have hfit3 := h3.search.stats.fits
  obtain ⟨-, hle'⟩ := orbjoin_facts hinv.orbitsDesc hws
  have hsv : PTree.get dense.id.save (PTree.set (idOf 709) (.Vint (ir (orbjoin st.orbits st.workperm n).2))
      (PTree.set dense.id.save (.Vint (ir st.numorbits)) le)) = some (.Vint (ir st.numorbits)) := by
    rw [temps_gso _ _ (by decide), temps_gss]
  wp_step; wp_step; wp_step
  refine wp_ifB (eval_eqI (eval_statsF (ty := tint) (c.eg _ (by decide)) fld_numorbits rfl
      h3.search.fixed.stats (by decide) (by omega) h3.search.stats.numorbits)
    (show Exec.evalExpr ge e _ m3 (tv dense.id.save) = _ from hsv) rfl rfl
    ⟨by dsimp only; omega, by dsimp only; omega⟩ ⟨by have := hinv.numorbitsLe; omega, by have := hinv.numorbitsLe; omega⟩) rfl ?_
  by_cases heq : (orbjoin st.orbits st.workperm n).2 = st.numorbits
  · rw [decide_eq_true (by exact_mod_cast heq), ite_eq_left rfl]
    simp only [heq, beq_self_eq_true, ite_true, exitValue] at hR
    wp_step
    refine wp_nspIf c h3 ?_
    intro m4 h4 hsr4
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    rw [heq] at h4
    obtain ⟨mf, hfree, hret⟩ := hR m4 E0 h4 (by
      simp only [leafWords]; rw [if_neg (by omega)]; exact .nil)
    refine wp_return_some (v' := .Vint (ir st.gcaCanon))
      (eval_gint (c.eg _ (by decide)) E.find_gcaCanon h4.search.scalars.gcaCanon) (by rw [hfr]; rfl)
      hfree ?_
    simpa using hret
  · rw [decide_eq_false (by exact_mod_cast heq), ite_eq_right (by decide)]
    have hb : ((orbjoin st.orbits st.workperm n).2 == st.numorbits) = false := by simp [heq]
    simp only [hb, Bool.false_eq_true, ite_false, exitValue] at hR
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    wp_step
    refine wp_ifG0 (c.eg _ (by decide)) E.find_writeautoms h3.search.fixed.writeautoms ?_
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
    have hWt : Writes t (leafWords st { st with
        autos := pushA st.autos (fmperm st.workperm n), genTrace := st.genTrace.push st.workperm,
        orbits := (orbjoin st.orbits st.workperm n).1, numorbits := (orbjoin st.orbits st.workperm n).2,
        numgenerators := st.numgenerators + 1 }) := by
      simp only [leafWords, ite_true]; exact hW
    wp_step; wp_step; wp_step
    refine wp_ifB (eval_coset c h4 hci) rfl ?_
    by_cases hlt : (orbjoin st.orbits st.workperm n).1[st.cosetindex]! < st.cosetindex
    · rw [decide_eq_true hlt, ite_eq_left rfl]
      simp only [hlt, ite_true] at hR
      wp_step; wp_step
      obtain ⟨mf, hfree, hret⟩ := hR m4 t h4 hWt
      refine wp_return_some (v' := .Vint (ir st.gcaFirst))
        (eval_gint (c.eg _ (by decide)) E.find_gcaFirst h4.search.scalars.gcaFirst) (by rw [hfr]; rfl)
        hfree ?_
      simpa using hret
    · rw [decide_eq_false hlt, ite_eq_right (by decide)]
      simp only [hlt, ite_false] at hR
      apply wp_skip
      simp only [seqPost, Post.after, E0_append, E0_left, E0_right]
      wp_step
      refine wp_nspIf c h4 ?_
      intro m5 h5 hsr5
      simp only [seqPost, Post.after, E0_append, E0_left, E0_right]
      wp_step; wp_step
      obtain ⟨mf, hfree, hret⟩ := hR m5 t h5 hWt
      refine wp_return_some (v' := .Vint (ir st.gcaCanon))
        (eval_gint (c.eg _ (by decide)) E.find_gcaCanon h5.search.scalars.gcaCanon) (by rw [hfr]; rfl)
        hfree ?_
      simpa using hret

end NautyVerified.Proofs.Search.Processnode
