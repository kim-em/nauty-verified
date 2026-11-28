import NautyVerified.Proofs.Search.Processnode.Case2
import NautyVerified.Proofs.Search.Firstterminal.Copy

/-!
# `processnode`'s cases 3 and 4

`wp_case3`: code 3, a better leaf: count the update, copy `lab` to `canonlab`,
record this leaf's level, code and `sr` (HexGraphIso's `install`), then break.
`wp_case4`: code 4, a bad leaf: count it and break.
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

/-- `canonlab[i] = lab[i]` for all `i`. -/
theorem wp_copyCanon {f : function} {Q : Post} {le : temp_env} (c : PCtx D m₀ m₁ S gl cl e bsr)
    (h : PAt D m₀ m₁ m S gl cl G bsr st nsp) (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hQ : ∀ le' m', PAt D m₀ m₁ m' S gl cl G bsr { st with canonlab := st.lab } nsp →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) →
      (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f (forLoopC dense.id.i
      (.Ebinop .Olt (tv dense.id.i) (.Evar dense.id.«nauty:n» tint) tint)
      (sk (.Sassign (gat dense.id.«nauty:canonlab» (tv dense.id.i)) (ix dense.id.lab (tv dense.id.i)))))
      Q e le m := by
  have hs := h.search
  have hd := hs.lit
  have hinv := hs.inv
  have hCL : 0 < S.capCL := by have := hs.dyns.capCL; have := hs.n0; omega
  refine Firstterminal.wp_copyIntsG (by have := hs.nlt; omega) (c.eg _ (by decide)) (c.eg _ (by decide))
    E.find_nautyCanonlab (hs.dyns.canonlab.ptr hCL) hs.arrays.canonlab hlab hs.arrays.lab hs.fixed.nn
    (by decide) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) ?_
  intro le' m' ha hu hk hv ho
  have hu' : Unch m m' (· ∈ [S.bCL]) := hu.mono fun z hz => by simp [hz]
  refine hQ le' m' (PAt.next c h hu' (by simp) ?_ hv
    ((hs.scalars.unch hu (by sep_all hd)).cast rfl) ((hs.stats.unch hu (by sep_ne hd)).cast rfl)
    (hs.arrays.set hu (hs.arrays.lab.unch hu (by sep_ne hd)) (hs.arrays.ptn.unch hu (by sep_ne hd))
      (hs.arrays.orbits.unch hu (by sep_ne hd)) (hs.arrays.active' hu (by sep_ne hd))
      (hs.arrays.fixedpts' hu (by sep_ne hd)) (hs.arrays.workperm' hu (by sep_ne hd))
      (hs.arrays.firstlab.unch hu (by sep_ne hd)) ha (hs.arrays.firstcode.unch hu (by sep_ne hd))
      (hs.arrays.canoncode.unch hu (by sep_ne hd)) (hs.arrays.firsttc.unch hu (by sep_ne hd))
      (D.canon_unch hs.arrays.canong hu fun z hz e => hs.canon_ne hz (.inr (.inr (.inl (by simp)))) e)
      (hs.arrays.autos.unch hu (by sep_ne hd) (by sep_ne hd))
      (fun z hz e => hs.graph_ne hz (.inr (.inr (.inl (by simp)))) e))
    { hinv with canonlabSize := hinv.labSize }) (fun v hv' => hv'.unch hu fun e =>
      c.ne_blocks (SLoc.mem_blocksG_lit (by simp [SLoc.litG])) e.symm) ho
  intro z hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hk | exact Keep.unch hu (by sep_ne hd)

/-- The stores recording a better leaf at `level` with `sr` rows agreeing. -/
abbrev recordC (rest : statement) : statement :=
  .Ssequence
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (sk (.Sset (idOf 710) (.Ecast (tv dense.id.«level») tint)))
            (.Sassign (.Evar dense.id.«nauty:gca_canon» tint) (tv (idOf 710))))
          (.Sset (idOf 711) (.Ecast (tv (idOf 710)) tint)))
        (.Sassign (.Evar dense.id.«nauty:eqlev_canon» tint) (tv (idOf 711))))
      (.Sassign (.Evar dense.id.«nauty:canonlevel» tint) (tv (idOf 711))))
    (.Ssequence
      (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint)))
      (.Ssequence
        (sk (.Sassign (gats dense.id.«nauty:canoncode» (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint))
          (ci 32767 tint)))
        (.Ssequence
          (sk (.Sassign (.Evar dense.id.«nauty:samerows» tint) (.Evar dense.id.«sr» tint)))
          rest)))

set_option maxHeartbeats 8000000 in
theorem wp_record {f : function} {Q : Post} {le : temp_env} {level s : Nat} {rest : statement}
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp) (hsr : SrAt m bsr s)
    (hss : s ≤ st.samerows) (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hl : level ≤ n)
    (hQ : ∀ le' m', PAt D m₀ m₁ m' S gl cl G bsr { st with
        canonlevel := level, eqlevCanon := Int.ofNat level, gcaCanon := level, compCanon := 0,
        canoncode := st.canoncode.set! (level + 1) codeSentinel, samerows := s } nsp →
      (∀ x, x ≠ idOf 710 → x ≠ idOf 711 → PTree.get x le' = PTree.get x le) →
      Wp xi ge f rest Q e le' m') :
    Wp xi ge f (recordC rest) Q e le m := by
  have hs := h.search
  have hd := hs.lit
  have hinv := hs.inv
  have hnl := hs.nlt
  have sc := hs.scalars
  have hCC : 0 < S.capCC := by have := hs.dyns.capCC; omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, show Exec.evalExpr ge e le m (tv dense.id.level) = _ from hlev]
  simp only [typeof, cop]
  simp only [seqPost, Post.after, E0_append]
  have g710 : PTree.get (idOf 710) (PTree.set (idOf 710) (.Vint (ir level)) le) = some (.Vint (ir level)) :=
    temps_gss _ _ _
  refine wp_gint (x := level) (c.eg _ (by decide)) E.find_gcaCanon sc.gcaCanon.writable g710 rfl ?_
  intro m3 i3 u3 v3
  have hU3 : Unch m m3 (· ∈ [E.gcaCanon]) := u3.mono fun z hz => by simp [hz]
  simp only [seqPost, Post.after, E0_append]
  apply wp_set_eval
  rw [Exec.evalExpr, show Exec.evalExpr ge e _ m3 (tv (idOf 710)) = _ from g710]
  simp only [typeof, cop]
  simp only [seqPost, Post.after, E0_append]
  have g711 : PTree.get (idOf 711) (PTree.set (idOf 711) (.Vint (ir level))
      (PTree.set (idOf 710) (.Vint (ir level)) le)) = some (.Vint (ir level)) := temps_gss _ _ _
  refine wp_gint (x := level) (c.eg _ (by decide)) E.find_eqlevCanon
    (sc.eqlevCanon.unch hU3 (by sep_notin hd)).writable g711 rfl ?_
  intro m4 i4 u4 v4
  have hU4 := hU3.snoc u4
  fwd hd u4 [i3]
  simp only [seqPost, Post.after, E0_append]
  refine wp_gint (x := level) (c.eg _ (by decide)) E.find_canonlevel
    (sc.canonlevel.unch hU4 (by sep_notin hd)).writable g711 rfl ?_
  intro m5 i5 u5 v5
  have hU5 := hU4.snoc u5
  fwd hd u5 [i3 i4]
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gint (x := 0) (c.eg _ (by decide)) E.find_compCanon
    (sc.compCanon.unch hU5 (by sep_notin hd)).writable (eval_ci 0) rfl ?_
  intro m6 i6 u6 v6
  have hU6 := hU5.snoc u6
  fwd hd u6 [i3 i4 i5]
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  have hlev6 : PTree.get dense.id.level (PTree.set (idOf 711) (.Vint (ir level))
      (PTree.set (idOf 710) (.Vint (ir level)) le)) = some (.Vint (ir level)) := by
    rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hlev
  refine wp_gstoreS (c.eg _ (by decide)) E.find_nautyCanoncode
    (by rw [hU6.load _ _ _ (by sep_notin hd)]; exact hs.dyns.canoncode.ptr hCC)
    (hs.arrays.canoncode.unch hU6 (by sep_notin hd)) (by omega)
    (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint) (level + 1) (by omega)
    (by rw [Exec.evalExpr, show Exec.evalExpr ge e _ m6 (tv dense.id.level) = _ from hlev6, eval_ci]
        simp only [typeof, cop, ir_add]; push_cast; rfl) rfl
    (ci 32767 tint) 32767 (by decide) (eval_ci 32767) (.inl rfl) ?_
  intro m7 a7 u7 k7 v7
  have hU7 := hU6.snoc u7
  fwd hd u7 [i3 i4 i5 i6]
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  have hsr7 : SrAt m7 bsr s := hsr.unch hU7 (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      exact fun e => c.ne_blocks (SLoc.mem_blocksG_lit (by simp [SLoc.litG])) e.symm)
  refine wp_gint (x := s) (c.eg _ (by decide)) E.find_samerows
    (sc.samerows.unch hU7 (by sep_notin hd)).writable ?_ rfl ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, c.esr, ite_true, Exec.derefLoc, access_mode, Mem.loadv,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]
    exact hsr7.load 0 (by decide)
  intro m8 i8 u8 v8
  have hU8 := hU7.snoc u8
  fwd hd u8 [i3 i4 i5 i6 a7]
  simp only [seqPost, Post.after, E0_append]
  have hv : ∀ z, Mem.valid_block m z → Mem.valid_block m8 z :=
    fun z hz => v8 _ (v7 _ (v6 _ (v5 _ (v4 _ (v3 _ hz)))))
  obtain ⟨a1, -, a3, a4, a5, -, -, -, -, -, a11, a12⟩ := hinv.scalars
  have hccs := hinv.canoncodeSize
  refine hQ _ m8 (PAt.next c h hU8 (by simp) ?_ hv
    ⟨sc.gcaFirst.unch hU8 (by sep_notin hd), i3, sc.noncheaplevel.unch hU8 (by sep_notin hd),
      sc.allsamelevel.unch hU8 (by sep_notin hd), sc.eqlevFirst.unch hU8 (by sep_notin hd),
      i4, i6, i8, i5, sc.stabvertex.unch hU8 (by sep_notin hd),
      sc.cosetindex.unch hU8 (by sep_notin hd), sc.needshortprune.unch hU8 (by sep_notin hd)⟩
    ((hs.stats.unch hU8 (by sep_notin hd)).cast rfl)
    (hs.arrays.set hU8 (hs.arrays.lab.unch hU8 (by sep_notin hd)) (hs.arrays.ptn.unch hU8 (by sep_notin hd))
      (hs.arrays.orbits.unch hU8 (by sep_notin hd)) (hs.arrays.active' hU8 (by sep_notin hd))
      (hs.arrays.fixedpts' hU8 (by sep_notin hd)) (hs.arrays.workperm' hU8 (by sep_notin hd))
      (hs.arrays.firstlab.unch hU8 (by sep_notin hd)) (hs.arrays.canonlab.unch hU8 (by sep_notin hd))
      (hs.arrays.firstcode.unch hU8 (by sep_notin hd))
      (by rw [shorts_set (by omega)]; exact a7)
      (hs.arrays.firsttc.unch hU8 (by sep_notin hd))
      (D.canon_le (D.canon_unch hs.arrays.canong hU8 (hs.canon_notin (by simp))) hss)
      (hs.arrays.autos.unch hU8 (by sep_notin hd) (by sep_notin hd)) (hs.graph_notin (by simp)))
    { hinv with
      codesSmall := fun i hi => ⟨(hinv.codesSmall i hi).1, by
        show (st.canoncode.set! (level + 1) codeSentinel)[i]! < 32768
        by_cases hi' : i = level + 1
        · subst hi'; rw [Array.getElem!_set!_self _ _ _ (by omega)]; decide
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hi')]; exact (hinv.codesSmall i hi).2⟩
      samerows := by have := hinv.samerows; show s ≤ n; omega
      canoncodeSize := by show (st.canoncode.set! (level + 1) codeSentinel).size = n + 2; simp [hccs]
      scalars := ⟨a1, by show level < 2147483648; omega, a3, a4, a5,
        by show (-1 : Int) ≤ Int.ofNat level; simp only [Int.ofNat_eq_coe]; omega,
        by show Int.ofNat level < 2147483648; simp only [Int.ofNat_eq_coe]; omega,
        by show (-1 : Int) ≤ 0; omega, by show (0 : Int) ≤ 1; omega,
        by show level < 2147483648; omega, a11, a12⟩ }) ?_
  · intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact (Keep.unch hU6 (by sep_notin hd)).trans (k7.trans (Keep.unch u8 (by sep_ne hd)))
      | exact Keep.unch hU8 (by sep_notin hd)
  · intro x h1 h2; rw [temps_gso _ _ h2, temps_gso _ _ h1]

set_option maxHeartbeats 8000000 in
theorem wp_case3 {f : function} {Q : Post} {le : temp_env} {level s : Nat}
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st false) (hsr : SrAt m bsr s)
    (hss : s ≤ st.samerows) (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hl : level ≤ n) (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hQ : ∀ le' m', PAt D m₀ m₁ m' S gl cl G bsr (install level s st) false →
      (∀ x ∈ [dense.id.lab, dense.id.ptn, dense.id.level, dense.id.numcells],
        PTree.get x le' = PTree.get x le) → Q.brk E0 e le' m') :
    Wp xi ge f case3 Q e le m := by
  wp_step; wp_step; wp_step
  refine wp_canupdates c h ?_
  intro m1 h1 hsr1 _
  simp only [seqPost, Post.after, E0_append]
  wp_step
  refine wp_copyCanon c h1 hlab ?_
  intro le2 m2 h2 hsr2 ho2
  simp only [seqPost, Post.after, E0_append]
  have hlev2 : PTree.get dense.id.level le2 = some (.Vint (ir level)) := by
    rw [ho2 _ (by decide)]; exact hlev
  refine wp_record c h2 (hsr2 _ (hsr1 _ hsr)) hss hlev2 hl ?_
  intro le3 m3 h3 ho3
  have hs3 := h3.search
  wp_step; wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [eval_gint (c.eg _ (by decide)) E.find_getcanon hs3.fixed.getcanon]
  simp only [typeof, cop]
  rw [ite_eq_left (by decide)]
  wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, Exec.evalExpr, eval_gptr (c.eg _ (by decide)) E.find_usercanonproc rfl
    hs3.fixed.usercanonproc]
  simp only [Exec.evalExpr, typeof, cop]
  have hne : Cfrontend.Cop.sem_binary_operation ge.genv_cenv .One Vnullptr
      (tptr (tfun [tptr tulong, tptr tint, tptr tulong, tulong, tint, tint, tint] tint))
      (.Vlong (Int64.repr (Int.signed (Lib.Integers.Int.repr (zOfInt 0))))) (tptr .Tvoid) m3 =
      some (Val.of_bool false) := rfl
  rw [hne]
  simp only [cop]
  apply wp_if_eval
  simp only [Exec.evalExpr, Refine.tv, temps_gss, typeof, cop]
  simp (config := {decide := true}) only [ite_false]
  apply wp_skip
  apply wp_break
  simp only [E0_append]
  exact hQ _ m3 h3 fun x hx => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    have h713 : x ≠ idOf 713 := by rcases hx with rfl | rfl | rfl | rfl <;> decide
    have h710 : x ≠ idOf 710 := by rcases hx with rfl | rfl | rfl | rfl <;> decide
    have h711 : x ≠ idOf 711 := by rcases hx with rfl | rfl | rfl | rfl <;> decide
    have hi : x ≠ dense.id.i := by rcases hx with rfl | rfl | rfl | rfl <;> decide
    rw [temps_gso _ _ h713, ho3 x h710 h711, ho2 x hi]

theorem wp_case4 {f : function} {Q : Post} {le : temp_env}
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st false)
    (hQ : ∀ m', PAt D m₀ m₁ m' S gl cl G bsr { st with numbadleaves := st.numbadleaves + 1 } false →
      Q.brk E0 e le m') :
    Wp xi ge f case4 Q e le m := by
  wp_step; wp_step; wp_step
  refine wp_numbadleaves c h ?_
  intro m1 h1 _ _
  simp only [seqPost, Post.after, E0_append]
  exact wp_break (hQ m1 h1)

end NautyVerified.Proofs.Search.Processnode
