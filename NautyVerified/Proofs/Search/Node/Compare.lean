import NautyVerified.Proofs.Search.Node.Rebuild
import NautyVerified.Proofs.Search.Node.Othernode
import NautyVerified.Proofs.Search.Ops

/-!
# `othernode0`'s code comparisons

HexGraphIso's `compareCodes level code` is `cmpCanon` after `cmpFirst`
(`compareCodes_eq`): the comparison with the first leaf's code at `level`, then
with the best leaf's. `wp_codeFirst` and `wp_codeCanon` are the two C pieces
(`codeFirst` with the assignment of `eqlev_first`, and `codeCanon`), with the
refinement code in the `short` temporary `code`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat} {κ : Type}

/-- The comparison with the first leaf's code. -/
def cmpFirst (level code : Nat) (st : SearchState n κ) : SearchState n κ :=
  if st.eqlevFirst == level - 1 ∧ code == st.firstcode[level]! then
    { st with eqlevFirst := level } else st

/-- The comparison with the best leaf's code, and the update of its code. -/
def cmpCanon (level code : Nat) (st : SearchState n κ) : SearchState n κ :=
  let st :=
    if st.eqlevCanon == Int.ofNat level - 1 then
      if code < st.canoncode[level]! then { st with compCanon := -1 }
      else if code > st.canoncode[level]! then { st with compCanon := 1 }
      else { st with compCanon := 0, eqlevCanon := Int.ofNat level }
    else st
  if st.compCanon > (0 : Int) then { st with canoncode := st.canoncode.set! level code } else st

theorem compareCodes_eq (level code : Nat) (st : SearchState n κ) :
    compareCodes level code st = cmpCanon level code (cmpFirst level code st) := by
  unfold compareCodes cmpCanon cmpFirst
  simp only [Id.run, bind, pure]
  cases h1 : (st.eqlevFirst == level - 1) <;>
  cases h2 : (code == st.firstcode[level]!) <;>
  cases h3 : (st.eqlevCanon == Int.ofNat level - 1) <;>
  by_cases hc : code < st.canoncode[level]! <;>
  by_cases hd : code > st.canoncode[level]! <;>
  by_cases he : st.compCanon > (0 : Int) <;>
  simp (config := {decide := true}) only [h1, h2, h3, hc, hd, he, ite_true, ite_false, and_self,
    and_true, true_and, and_false, false_and, Bool.false_eq_true] <;> rfl

/-- The best-leaf comparison. -/
def cmpCanonA (level code : Nat) (st : SearchState n κ) : SearchState n κ :=
  if st.eqlevCanon == Int.ofNat level - 1 then
    if code < st.canoncode[level]! then { st with compCanon := -1 }
    else if code > st.canoncode[level]! then { st with compCanon := 1 }
    else { st with compCanon := 0, eqlevCanon := Int.ofNat level }
  else st

/-- Saving the code when the node is better. -/
def cmpCanonB (level code : Nat) (st : SearchState n κ) : SearchState n κ :=
  if st.compCanon > (0 : Int) then { st with canoncode := st.canoncode.set! level code } else st

theorem cmpCanon_eq (level code : Nat) (st : SearchState n κ) :
    cmpCanon level code st = cmpCanonB level code (cmpCanonA level code st) := rfl

section Cop
variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
variable (ce : Cfrontend.Ctypes.composite_env) (m : mem) (x y : Lib.Integers.int)
  (a b : Cfrontend.Ctypes.attr)

@[simp, cop] theorem eq_ss : Cfrontend.Cop.sem_binary_operation ce .Oeq (.Vint x)
    (Cfrontend.Ctypes.Tint .I16 .Signed a) (.Vint y) (Cfrontend.Ctypes.Tint .I16 .Signed b) m =
      some (Val.of_bool (Lib.Integers.Int.eq x y)) := rfl
@[simp, cop] theorem lt_ss : Cfrontend.Cop.sem_binary_operation ce .Olt (.Vint x)
    (Cfrontend.Ctypes.Tint .I16 .Signed a) (.Vint y) (Cfrontend.Ctypes.Tint .I16 .Signed b) m =
      some (Val.of_bool (Lib.Integers.Int.lt x y)) := rfl
@[simp, cop] theorem gt_ss : Cfrontend.Cop.sem_binary_operation ce .Ogt (.Vint x)
    (Cfrontend.Ctypes.Tint .I16 .Signed a) (.Vint y) (Cfrontend.Ctypes.Tint .I16 .Signed b) m =
      some (Val.of_bool (Lib.Integers.Int.lt y x)) := rfl
end Cop

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

/-- `ArraysG` after a store into `canoncode` only. -/
theorem ArraysG.setCanoncode {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {m₀ : mem} {st₀ : SearchState n (O.Canon n)}
    {pre nsp : Bool} (h : ArraysG D m S gl cl G st)
    (h₀ : SearchAtG D m₀ S gl cl G st₀ pre nsp) (hu : Unch m m' (· = S.bCC))
    {cc : Array Nat} (hcc : ArrayAt m' .Mint16signed S.bCC 0 (shorts cc) (n + 2)) :
    ArraysG D m' S gl cl G { st with canoncode := cc } := by
  have hd := h₀.lit
  obtain ⟨aw, ha, har⟩ := h.active
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  obtain ⟨wv, hwv⟩ := h.workperm
  exact ⟨h.lab.unch hu (by sep_ne hd), h.ptn.unch hu (by sep_ne hd),
    h.orbits.unch hu (by sep_ne hd), ⟨aw, ha.unch hu (by sep_ne hd), har⟩,
    ⟨fw, hf.unch hu (by sep_ne hd), hfr⟩, ⟨wv, hwv.unch hu (by sep_ne hd)⟩,
    h.firstlab.unch hu (by sep_ne hd), h.canonlab.unch hu (by sep_ne hd),
    h.firstcode.unch hu (by sep_ne hd), hcc, h.firsttc.unch hu (by sep_ne hd),
    D.canon_unch h.canong hu fun z hz e => h₀.canon_ne hz (.inr (.inr (.inl (by simp)))) e,
    h.autos.unch hu (by sep_ne hd) (by sep_ne hd),
    D.graph_unch h.graph hu fun z hz e => h₀.graph_ne hz (.inr (.inr (.inl (by simp)))) e⟩

theorem SearchAtG.setCompCanon {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) (hu : Unch m m' (· ∈ [E.compCanon]))
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    {v : Int} (iCC : IntAt m' E.compCanon v) (hv1 : -1 ≤ v) (hv2 : v ≤ 1) :
    SearchAtG D m' S gl cl G { st with compCanon := v } pre nsp := by
  have sc := h.scalars
  refine h.setScalars hu (fun z hz => by simp at hz; subst hz; simp) hv
    ⟨sc.gcaFirst.unch hu (by sep_notin h.lit), sc.gcaCanon.unch hu (by sep_notin h.lit),
      sc.noncheaplevel.unch hu (by sep_notin h.lit), sc.allsamelevel.unch hu (by sep_notin h.lit),
      sc.eqlevFirst.unch hu (by sep_notin h.lit), sc.eqlevCanon.unch hu (by sep_notin h.lit), iCC,
      sc.samerows.unch hu (by sep_notin h.lit), sc.canonlevel.unch hu (by sep_notin h.lit),
      sc.stabvertex.unch hu (by sep_notin h.lit), sc.cosetindex.unch hu (by sep_notin h.lit),
      sc.needshortprune.unch hu (by sep_notin h.lit)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, -, -, s10⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, s3, s4, s5, s6, s7, hv1, hv2, s10⟩ }

theorem SearchAtG.setEqlevCanon {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) (hu : Unch m m' (· ∈ [E.eqlevCanon]))
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    {v : Int} (iEC : IntAt m' E.eqlevCanon v) (hv1 : -1 ≤ v) (hv2 : v < 2147483648) :
    SearchAtG D m' S gl cl G { st with eqlevCanon := v } pre nsp := by
  have sc := h.scalars
  refine h.setScalars hu (fun z hz => by simp at hz; subst hz; simp) hv
    ⟨sc.gcaFirst.unch hu (by sep_notin h.lit), sc.gcaCanon.unch hu (by sep_notin h.lit),
      sc.noncheaplevel.unch hu (by sep_notin h.lit), sc.allsamelevel.unch hu (by sep_notin h.lit),
      sc.eqlevFirst.unch hu (by sep_notin h.lit), iEC, sc.compCanon.unch hu (by sep_notin h.lit),
      sc.samerows.unch hu (by sep_notin h.lit), sc.canonlevel.unch hu (by sep_notin h.lit),
      sc.stabvertex.unch hu (by sep_notin h.lit), sc.cosetindex.unch hu (by sep_notin h.lit),
      sc.needshortprune.unch hu (by sep_notin h.lit)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, s3, s4, s5, -, -, s8⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, s3, s4, s5, hv1, hv2, s8⟩ }

/-- `t709 = eqlev_first == level - 1 && code == firstcode[level]; if (t709) eqlev_first = level;` -/
theorem wp_codeFirstG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool} {level c : Nat}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (hE1 : PTree.get dense.id.«nauty:eqlev_first» e = none)
    (hE2 : PTree.get dense.id.«nauty:firstcode» e = none)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hcode : PTree.get dense.id.code le = some (.Vint (ir c)))
    (hc : c < 32768) (h1 : 1 ≤ level) (hn : level ≤ n)
    (hQ : ∀ le' m', SearchAtG D m' S gl cl G (cmpFirst level c st) pre nsp →
      Unch m m' (· ∈ [E.eqlevFirst]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 709 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f (.Ssequence (sk Othernode.codeFirst)
      (.Sifthenelse (tv (idOf 709))
        (sk (.Sassign (.Evar dense.id.«nauty:eqlev_first» tint) (tv dense.id.level))) .Sskip))
      Q e le m := by
  have hnl := h.nlt
  obtain ⟨-, -, -, -, hef, -⟩ := h.inv.scalars
  simp only [Othernode.codeFirst, sk]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_gint hE1 E.find_eqlevFirst h.scalars.eqlevFirst]
  simp only [Exec.evalExpr, hlev, tv, typeof, cop, ir_sub]
  rw [ir_eq (a := (st.eqlevFirst : Int)) (b := (level : Int) - 1) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩]
  have hd := h.lit
  have hfc := h.inv.codesSmall level (by omega)
  have hFC : Exec.evalExpr ge e le m (gats dense.id.«nauty:firstcode» (tv dense.id.level)) =
      some (.Vint (ir (st.firstcode[level]! : Int))) :=
    eval_gats hE2 E.find_nautyFirstcode (h.dyns.firstcode.ptr (by have := h.dyns.capFC; omega))
      h.arrays.firstcode (by omega) (tv dense.id.level) level (by omega) hlev rfl
  -- the store `eqlev_first = level`, or nothing
  have fin : ∀ le', (∀ x, x ≠ idOf 709 → PTree.get x le' = PTree.get x le) →
      PTree.get dense.id.level le' = some (.Vint (ir level)) →
      PTree.get (idOf 709) le' = some (Val.of_bool
        (decide ((st.eqlevFirst : Int) = level - 1) && decide (c = st.firstcode[level]!))) →
      Wp xi ge f (.Sifthenelse (tv (idOf 709))
        (sk (.Sassign (.Evar dense.id.«nauty:eqlev_first» tint) (tv dense.id.level))) .Sskip)
        Q e le' m := by
    intro le' ho hlev' h709
    apply wp_if_eval
    simp only [Exec.evalExpr, tv, h709, typeof, cop]
    by_cases hB : (st.eqlevFirst : Int) = level - 1 ∧ c = st.firstcode[level]!
    · rw [ite_eq_left (by simp [hB.1, hB.2])]
      wp_step; wp_step
      refine wp_gint hE1 E.find_eqlevFirst h.scalars.eqlevFirst.writable
        (show Exec.evalExpr ge e le' m (tv dense.id.level) = _ from hlev') rfl ?_
      intro m' iEF hu hv
      have hU : Unch m m' (· ∈ [E.eqlevFirst]) := hu.mono fun z hz => by simp [hz]
      have hcf : cmpFirst level c st = { st with eqlevFirst := level } := by
        unfold cmpFirst
        rw [ite_eq_left (by simp; omega)]
      refine hQ le' m' ?_ hU hv ho
      rw [hcf]
      have sc := h.scalars
      refine h.setScalars hU (fun z hz => by simp at hz; subst hz; simp) hv
        ⟨sc.gcaFirst.unch hU (by sep_notin h.lit), sc.gcaCanon.unch hU (by sep_notin h.lit),
          sc.noncheaplevel.unch hU (by sep_notin h.lit), sc.allsamelevel.unch hU (by sep_notin h.lit), iEF,
          sc.eqlevCanon.unch hU (by sep_notin h.lit), sc.compCanon.unch hU (by sep_notin h.lit),
          sc.samerows.unch hU (by sep_notin h.lit), sc.canonlevel.unch hU (by sep_notin h.lit),
          sc.stabvertex.unch hU (by sep_notin h.lit), sc.cosetindex.unch hU (by sep_notin h.lit),
          sc.needshortprune.unch hU (by sep_notin h.lit)⟩
        { h.arrays with } { h.stats with } ?_
      obtain ⟨s1, s2, s3, s4, -, s6⟩ := h.inv.scalars
      exact { h.inv with scalars := ⟨s1, s2, s3, s4, show level < 2147483648 by omega, s6⟩ }
    · rw [ite_eq_right (by simpa using hB)]
      apply wp_skip
      have hcf : cmpFirst level c st = st := by
        unfold cmpFirst
        rw [ite_eq_right (by simp; omega)]
      exact hQ le' m (by rw [hcf]; exact h) (Unch.refl _ _) (fun _ h => h) ho
  by_cases hA : (st.eqlevFirst : Int) = level - 1
  · rw [ite_eq_left (by simpa using hA)]
    wp_step; wp_step
    apply wp_set_eval
    have hcmp : Exec.evalExpr ge e le m (.Ebinop .Oeq (.Etempvar dense.id.code tshort)
        (gats dense.id.«nauty:firstcode» (tv dense.id.level)) tint) =
        some (Val.of_bool (decide ((c : Int) = st.firstcode[level]!))) := by
      rw [Exec.evalExpr, show Exec.evalExpr ge e le m (.Etempvar dense.id.code tshort) = _ from
        hcode, hFC]
      simp only [typeof, cop]
      rw [ir_eq (a := (c : Int)) (b := (st.firstcode[level]! : Int)) ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩]
    simp only [Exec.evalExpr] at hcmp ⊢
    rw [hcmp]
    have hcast : ∀ b : Bool, Cfrontend.Cop.sem_cast (Val.of_bool b) tint tbool m =
        some (Val.of_bool b) := fun b => by cases b <;> rfl
    simp only [typeof, hcast, seqPost, Post.after, E0_append]
    refine fin (PTree.set (idOf 709) (Val.of_bool (decide ((c : Int) = st.firstcode[level]!))) le)
      (fun x hx => temps_gso _ _ hx) (by rw [temps_gso _ _ (by decide)]; exact hlev) ?_
    rw [temps_gss]
    simp only [hA, decide_true, Bool.true_and]
    congr 2
    exact decide_eq_decide.2 ⟨fun h => by omega, fun h => by omega⟩
  · rw [ite_eq_right (by simpa using hA)]
    apply wp_set_eval
    simp only [Exec.evalExpr, seqPost, Post.after, E0_append]
    refine fin (PTree.set (idOf 709) (.Vint (Lib.Integers.Int.repr (zOfInt 0))) le)
      (fun x hx => temps_gso _ _ hx) (by rw [temps_gso _ _ (by decide)]; exact hlev) ?_
    rw [temps_gss]
    simp only [hA, decide_false, Bool.false_and]
    rfl

/-- `if (comp_canon > 0) canoncode[level] = code;` -/
theorem wp_canonBG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool} {level c : Nat}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (hE1 : PTree.get dense.id.«nauty:comp_canon» e = none)
    (hE2 : PTree.get dense.id.«nauty:canoncode» e = none)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hcode : PTree.get dense.id.code le = some (.Vint (ir c)))
    (hc : c < 32768) (hn : level ≤ n)
    (hQ : ∀ m', SearchAtG D m' S gl cl G (cmpCanonB level c st) pre nsp → Unch m m' (· ∈ [S.bCC]) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (.Sifthenelse (.Ebinop .Ogt (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint) tint)
      (sk (.Sassign (gats dense.id.«nauty:canoncode» (tv dense.id.level))
        (.Etempvar dense.id.code tshort))) .Sskip) Q e le m := by
  have hnl := h.nlt
  have hd := h.lit
  obtain ⟨-, -, -, -, -, -, -, hc1, hc2, -⟩ := h.inv.scalars
  apply wp_if_eval
  rw [Exec.evalExpr, eval_gint hE1 E.find_compCanon h.scalars.compCanon]
  simp only [Exec.evalExpr, typeof, cop]
  rw [ir_lt (a := 0) (b := st.compCanon) ⟨by decide, by decide⟩ ⟨by omega, by omega⟩]
  by_cases hp : (0 : Int) < st.compCanon
  · rw [ite_eq_left (by simpa using hp)]
    wp_step; wp_step
    refine wp_gstoreS hE2 E.find_nautyCanoncode
      (h.dyns.canoncode.ptr (by have := h.dyns.capCC; omega)) h.arrays.canoncode (by omega)
      (tv dense.id.level) level (by omega) hlev rfl (.Etempvar dense.id.code tshort) c hc hcode
      (.inr rfl) ?_
    intro m' harr hu hk hv
    have hU : Unch m m' (· ∈ [S.bCC]) := hu.mono fun z hz => by simp [hz]
    have hcs := h.inv.canoncodeSize
    have hcB : cmpCanonB level c st = { st with canoncode := st.canoncode.set! level c } := by
      unfold cmpCanonB; rw [ite_eq_left (by omega)]
    refine hQ m' ?_ hU hv
    rw [hcB]
    refine h.rebuild hU (fun z hz => by simp at hz; subst hz; exact .inr (.inl (by simp)))
      (fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact hk | exact Keep.unch hu (by sep_ne hd)) hv
      { h.scalars.unch hu (by sep_all hd) with } { h.stats.unch hu (by sep_ne hd) with }
      (h.arrays.setCanoncode h hu (by rw [shorts_set (by omega)]; exact harr)) ?_
    have i := h.inv
    exact { i with
      codesSmall := fun j hj => by
        refine ⟨(i.codesSmall j hj).1, ?_⟩
        show (st.canoncode.set! level c)[j]! < 32768
        by_cases hjl : j = level
        · subst hjl; rw [Array.getElem!_set!_self _ _ _ (by omega)]; omega
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hjl)]; exact (i.codesSmall j hj).2
      canoncodeSize := by show (st.canoncode.set! level c).size = n + 2; simp [hcs] }
  · rw [ite_eq_right (by simpa using hp)]
    apply wp_skip
    have hcB : cmpCanonB level c st = st := by unfold cmpCanonB; rw [ite_eq_right (by omega)]
    exact hQ m (by rw [hcB]; exact h) (Unch.refl _ _) fun _ h => h

/-- `if (eqlev_canon == level - 1) { if (code < canoncode[level]) comp_canon = -1; else if … }` -/
theorem wp_canonAG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool} {level c : Nat}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (hE1 : PTree.get dense.id.«nauty:comp_canon» e = none)
    (hE2 : PTree.get dense.id.«nauty:canoncode» e = none)
    (hE3 : PTree.get dense.id.«nauty:eqlev_canon» e = none)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hcode : PTree.get dense.id.code le = some (.Vint (ir c)))
    (hc : c < 32768) (h1 : 1 ≤ level) (hn : level ≤ n)
    (hQ : ∀ m', SearchAtG D m' S gl cl G (cmpCanonA level c st) pre nsp →
      Unch m m' (· ∈ [E.compCanon, E.eqlevCanon]) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f
      (.Sifthenelse
        (.Ebinop .Oeq (.Evar dense.id.«nauty:eqlev_canon» tint)
          (.Ebinop .Osub (tv dense.id.level) (ci 1 tint) tint) tint)
        (sk (.Sifthenelse
          (.Ebinop .Olt (.Etempvar dense.id.code tshort) (gats dense.id.«nauty:canoncode» (tv dense.id.level)) tint)
          (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (.Eunop .Oneg (ci 1 tint) tint)))
          (sk (.Sifthenelse
            (.Ebinop .Ogt (.Etempvar dense.id.code tshort) (gats dense.id.«nauty:canoncode» (tv dense.id.level)) tint)
            (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (ci 1 tint)))
            (.Ssequence
              (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint)))
              (sk (.Sassign (.Evar dense.id.«nauty:eqlev_canon» tint) (tv dense.id.level))))))))
        .Sskip) Q e le m := by
  have hnl := h.nlt
  have hd := h.lit
  obtain ⟨-, -, -, -, -, he1, he2, -⟩ := h.inv.scalars
  have hcc := h.inv.codesSmall level (by omega)
  have hCC : Exec.evalExpr ge e le m (gats dense.id.«nauty:canoncode» (tv dense.id.level)) =
      some (.Vint (ir (st.canoncode[level]! : Int))) :=
    eval_gats hE2 E.find_nautyCanoncode (h.dyns.canoncode.ptr (by have := h.dyns.capCC; omega))
      h.arrays.canoncode (by omega) (tv dense.id.level) level (by omega) hlev rfl
  have hcd : Exec.evalExpr ge e le m (.Etempvar dense.id.code tshort) = some (.Vint (ir c)) := hcode
  have mono2 : ∀ {m'}, Unch m m' (· ∈ [E.compCanon]) →
      Unch m m' (· ∈ [E.compCanon, E.eqlevCanon]) :=
    fun hu => hu.mono fun z hz => by simp at hz ⊢; exact .inl hz
  apply wp_if_eval
  rw [Exec.evalExpr, eval_gint hE3 E.find_eqlevCanon h.scalars.eqlevCanon]
  simp only [Exec.evalExpr, hlev, tv, typeof, cop, ir_sub]
  rw [ir_eq (a := st.eqlevCanon) (b := (level : Int) - 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hA : st.eqlevCanon = (level : Int) - 1
  · rw [ite_eq_left (by simpa using hA)]
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, hcd, hCC]
    simp only [typeof, cop]
    rw [ir_lt (a := (c : Int)) (b := (st.canoncode[level]! : Int)) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    by_cases hlt : c < st.canoncode[level]!
    · rw [ite_eq_left (by simp; omega)]
      wp_step; wp_step
      refine wp_gint hE1 E.find_compCanon h.scalars.compCanon.writable (x := -1)
        (by simp [Exec.evalExpr, typeof, cop]) rfl ?_
      intro m' iCC hu hv
      have hU : Unch m m' (· ∈ [E.compCanon]) := hu.mono fun z hz => by simp [hz]
      have hA' : cmpCanonA level c st = { st with compCanon := -1 } := by
        unfold cmpCanonA; simp [hA, hlt]
      exact hQ m' (by rw [hA']; exact h.setCompCanon hU hv iCC (by decide) (by decide)) (mono2 hU) hv
    · rw [ite_eq_right (by simp; omega)]
      wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, hcd, hCC]
      simp only [typeof, cop]
      rw [ir_lt (a := (st.canoncode[level]! : Int)) (b := (c : Int)) ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩]
      by_cases hgt : st.canoncode[level]! < c
      · rw [ite_eq_left (by simp; omega)]
        wp_step; wp_step
        refine wp_gint hE1 E.find_compCanon h.scalars.compCanon.writable (x := 1)
          (by simp [Exec.evalExpr, typeof, cop]) rfl ?_
        intro m' iCC hu hv
        have hU : Unch m m' (· ∈ [E.compCanon]) := hu.mono fun z hz => by simp [hz]
        have hA' : cmpCanonA level c st = { st with compCanon := 1 } := by
          unfold cmpCanonA; simp [hA, hlt, hgt]
        exact hQ m' (by rw [hA']; exact h.setCompCanon hU hv iCC (by decide) (by decide)) (mono2 hU) hv
      · rw [ite_eq_right (by simp; omega)]
        wp_step; wp_step; wp_step
        refine wp_gint hE1 E.find_compCanon h.scalars.compCanon.writable (x := 0)
          (by simp [Exec.evalExpr, typeof, cop]) rfl ?_
        intro m₁ iCC hu₁ hv₁
        have hU₁ : Unch m m₁ (· ∈ [E.compCanon]) := hu₁.mono fun z hz => by simp [hz]
        have h₁ := h.setCompCanon hU₁ hv₁ iCC (by decide) (by decide)
        simp only [seqPost, Post.after, E0_append]
        wp_step; wp_step
        refine wp_gint hE3 E.find_eqlevCanon h₁.scalars.eqlevCanon.writable (x := level)
          (show Exec.evalExpr ge e le m₁ (tv dense.id.level) = _ from hlev) rfl ?_
        intro m₂ iEC hu₂ hv₂
        have hU₂ : Unch m₁ m₂ (· ∈ [E.eqlevCanon]) := hu₂.mono fun z hz => by simp [hz]
        have hA' : cmpCanonA level c st =
            { { st with compCanon := 0 } with eqlevCanon := (level : Int) } := by
          unfold cmpCanonA; simp [hA, hlt, hgt]
        refine hQ m₂ (by rw [hA']; exact h₁.setEqlevCanon hU₂ hv₂ iEC (by omega) (by omega)) ?_
          fun z hz => hv₂ z (hv₁ z hz)
        exact (mono2 hU₁).trans (hU₂.mono fun z hz => by simp at hz ⊢; exact .inr hz)
  · rw [ite_eq_right (by simpa using hA)]
    apply wp_skip
    have hA' : cmpCanonA level c st = st := by unfold cmpCanonA; simp [hA]
    exact hQ m (by rw [hA']; exact h) (Unch.refl _ _) fun _ h => h

/-- `codeCanon`: `cmpCanon`, the best-leaf half of `compareCodes`. -/
theorem wp_codeCanonG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool} {level c : Nat}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (hE0 : PTree.get dense.id.«nauty:getcanon» e = none)
    (hE1 : PTree.get dense.id.«nauty:comp_canon» e = none)
    (hE2 : PTree.get dense.id.«nauty:canoncode» e = none)
    (hE3 : PTree.get dense.id.«nauty:eqlev_canon» e = none)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hcode : PTree.get dense.id.code le = some (.Vint (ir c)))
    (hc : c < 32768) (h1 : 1 ≤ level) (hn : level ≤ n)
    (hQ : ∀ m', SearchAtG D m' S gl cl G (cmpCanon level c st) pre nsp →
      Unch m m' (· ∈ [E.compCanon, E.eqlevCanon, S.bCC]) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f Othernode.codeCanon Q e le m := by
  simp only [Othernode.codeCanon]
  apply wp_if_eval
  rw [eval_gint hE0 E.find_getcanon h.fixed.getcanon]
  simp only [typeof, cop]
  rw [ite_eq_left (by decide)]
  wp_step; wp_step; wp_step
  refine wp_canonAG h hE1 hE2 hE3 hlev hcode hc h1 hn ?_
  intro m₁ h₁ hu₁ hv₁
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step
  refine wp_canonBG h₁ hE1 hE2 hlev hcode hc hn ?_
  intro m₂ h₂ hu₂ hv₂
  refine hQ m₂ (by rw [cmpCanon_eq]; exact h₂) ?_ fun z hz => hv₂ z (hv₁ z hz)
  exact (hu₁.mono fun z hz => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢
    rcases hz with hz | hz
    · exact .inl hz
    · exact .inr (.inl hz)).trans (hu₂.mono fun z hz => by
    simp at hz ⊢; exact .inr (.inr hz))

/-- `t711 = numcells < n && (eqlev_first == level || (getcanon && comp_canon >= 0))`: whether
`othernode0` needs a target cell, `chooseTarget false`'s condition. -/
theorem wp_targetG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool} {level nc : Nat} {bnc : block}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (hEn : PTree.get dense.id.«nauty:n» e = none)
    (hE0 : PTree.get dense.id.«nauty:getcanon» e = none)
    (hE1 : PTree.get dense.id.«nauty:comp_canon» e = none)
    (hE3 : PTree.get dense.id.«nauty:eqlev_first» e = none)
    (hnc : PTree.get dense.id.numcells e = some (bnc, tint))
    (hncv : Mem.load .Mint32 m bnc (zOfInt 0) = some (.Vint (ir nc))) (hncl : nc ≤ n)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (hln : level ≤ n)
    (hQ : ∀ le', PTree.get (idOf 711) le' = some (Val.of_bool
        (decide (nc < n ∧ (st.eqlevFirst = level ∨ 0 ≤ st.compCanon)))) →
      (∀ x, x ≠ idOf 711 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m) :
    Wp xi ge f Othernode.target Q e le m := by
  have hnl := h.nlt
  obtain ⟨-, -, -, -, hef, -, -, hc1, hc2, -⟩ := h.inv.scalars
  have hcast : ∀ b : Bool, Cfrontend.Cop.sem_cast (Val.of_bool b) tint tbool m =
      some (Val.of_bool b) := fun b => by cases b <;> rfl
  have hncE : Exec.evalExpr ge e le m (.Evar dense.id.numcells tint) = some (.Vint (ir nc)) := by
    simp only [Exec.evalExpr, Exec.lvalOfVar, hnc, Exec.derefLoc, Cfrontend.Ctypes.access_mode,
      Mem.loadv, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hncv]
    simp [hncv, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]
  simp only [Othernode.target, sk]
  apply wp_if_eval
  rw [Exec.evalExpr, hncE, eval_gint hEn E.find_n h.fixed.nn]
  simp only [typeof, cop]
  rw [ir_lt (a := (nc : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hlt : nc < n
  · rw [ite_eq_left (by simpa using hlt)]
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, eval_gint hE3 E.find_eqlevFirst h.scalars.eqlevFirst,
      show Exec.evalExpr ge e le m (tv dense.id.level) = _ from hlev]
    simp only [typeof, cop]
    rw [ir_eq (a := (st.eqlevFirst : Int)) (b := (level : Int)) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    by_cases heq : st.eqlevFirst = level
    · rw [ite_eq_left (by simp [heq])]
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, typeof, cop]
      exact hQ _ (by rw [temps_gss]; simp [hlt, heq]; rfl) fun x hx => temps_gso _ _ hx
    · rw [ite_eq_right (by simp; omega)]
      wp_step; wp_step
      apply wp_if_eval
      rw [eval_gint hE0 E.find_getcanon h.fixed.getcanon]
      simp only [typeof, cop]
      rw [ite_eq_left (by decide)]
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [Exec.evalExpr, Exec.evalExpr, eval_gint hE1 E.find_compCanon h.scalars.compCanon]
      simp only [Exec.evalExpr, typeof, cop]
      rw [ir_lt (a := st.compCanon) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
      have hb : (!decide (st.compCanon < 0)) = decide (0 ≤ st.compCanon) := by
        by_cases h0 : st.compCanon < 0 <;> simp [h0] <;> omega
      rw [hb, hcast]
      simp only [seqPost, Post.after, E0_append]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss, typeof, hcast]
      simp only [seqPost, Post.after, E0_append]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss, typeof, hcast]
      refine hQ _ (by rw [temps_gss]; simp [hlt, heq]) fun x hx => ?_
      rw [temps_gso _ _ hx, temps_gso _ _ hx, temps_gso _ _ hx]
  · rw [ite_eq_right (by simpa using hlt)]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    exact hQ _ (by rw [temps_gss]; simp [hlt]; rfl) fun x hx => temps_gso _ _ hx

end Generic

/-- `t709 = eqlev_first == level - 1 && code == firstcode[level]; if (t709) eqlev_first = level;` -/
theorem wp_codeFirst {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level c : Nat}
    (h : SearchAt m S ctx st pre nsp)
    (hE1 : PTree.get dense.id.«nauty:eqlev_first» e = none)
    (hE2 : PTree.get dense.id.«nauty:firstcode» e = none)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hcode : PTree.get dense.id.code le = some (.Vint (ir c)))
    (hc : c < 32768) (h1 : 1 ≤ level) (hn : level ≤ n)
    (hQ : ∀ le' m', SearchAt m' S ctx (cmpFirst level c st) pre nsp →
      Unch m m' (· ∈ [Block.eqlevFirst]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 709 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f (.Ssequence (sk Othernode.codeFirst)
      (.Sifthenelse (tv (idOf 709))
        (sk (.Sassign (.Evar dense.id.«nauty:eqlev_first» tint) (tv dense.id.level))) .Sskip))
      Q e le m :=
  wp_codeFirstG h.toG hE1 hE2 hlev hcode hc h1 hn fun le' m' h' hu hv ho =>
    hQ le' m' (h'.dense h.gw) hu hv ho

/-- `Arrays` after a store into `canoncode` only. -/
theorem Arrays.setCanoncode {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    (h : Arrays m S ctx st) (hu : Unch m m' (· = S.bCC)) (hd : S.blocks.Pairwise (· ≠ ·))
    {cc : Array Nat} (hcc : ArrayAt m' .Mint16signed S.bCC 0 (shorts cc) (n + 2)) :
    Arrays m' S ctx { st with canoncode := cc } := by
  obtain ⟨aw, ha, har⟩ := h.active
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  obtain ⟨wv, hwv⟩ := h.workperm
  exact ⟨h.lab.unch hu (by sep_ne hd), h.ptn.unch hu (by sep_ne hd),
    h.orbits.unch hu (by sep_ne hd), ⟨aw, ha.unch hu (by sep_ne hd), har⟩,
    ⟨fw, hf.unch hu (by sep_ne hd), hfr⟩, ⟨wv, hwv.unch hu (by sep_ne hd)⟩,
    h.firstlab.unch hu (by sep_ne hd), h.canonlab.unch hu (by sep_ne hd),
    h.firstcode.unch hu (by sep_ne hd), hcc, h.firsttc.unch hu (by sep_ne hd),
    h.canong.unch hu (by sep_ne hd), h.autos.unch hu (by sep_ne hd) (by sep_ne hd),
    ⟨h.graph.arr.unch hu (by sep_ne hd), h.graph.rep⟩⟩

theorem SearchAt.setCompCanon {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) (hu : Unch m m' (· ∈ [Block.compCanon]))
    {v : Int} (iCC : IntAt m' Block.compCanon v) (hv1 : -1 ≤ v) (hv2 : v ≤ 1) :
    SearchAt m' S ctx { st with compCanon := v } pre nsp := by
  have sc := h.scalars
  refine h.setScalars hu (fun z hz => by simp at hz; subst hz; decide)
    ⟨sc.gcaFirst.unch hu (by decide), sc.gcaCanon.unch hu (by decide),
      sc.noncheaplevel.unch hu (by decide), sc.allsamelevel.unch hu (by decide),
      sc.eqlevFirst.unch hu (by decide), sc.eqlevCanon.unch hu (by decide), iCC,
      sc.samerows.unch hu (by decide), sc.canonlevel.unch hu (by decide),
      sc.stabvertex.unch hu (by decide), sc.cosetindex.unch hu (by decide),
      sc.needshortprune.unch hu (by decide)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, -, -, s10⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, s3, s4, s5, s6, s7, hv1, hv2, s10⟩ }

theorem SearchAt.setEqlevCanon {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) (hu : Unch m m' (· ∈ [Block.eqlevCanon]))
    {v : Int} (iEC : IntAt m' Block.eqlevCanon v) (hv1 : -1 ≤ v) (hv2 : v < 2147483648) :
    SearchAt m' S ctx { st with eqlevCanon := v } pre nsp := by
  have sc := h.scalars
  refine h.setScalars hu (fun z hz => by simp at hz; subst hz; decide)
    ⟨sc.gcaFirst.unch hu (by decide), sc.gcaCanon.unch hu (by decide),
      sc.noncheaplevel.unch hu (by decide), sc.allsamelevel.unch hu (by decide),
      sc.eqlevFirst.unch hu (by decide), iEC, sc.compCanon.unch hu (by decide),
      sc.samerows.unch hu (by decide), sc.canonlevel.unch hu (by decide),
      sc.stabvertex.unch hu (by decide), sc.cosetindex.unch hu (by decide),
      sc.needshortprune.unch hu (by decide)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, s3, s4, s5, -, -, s8⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, s3, s4, s5, hv1, hv2, s8⟩ }

/-- `if (comp_canon > 0) canoncode[level] = code;` -/
theorem wp_canonB {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level c : Nat}
    (h : SearchAt m S ctx st pre nsp)
    (hE1 : PTree.get dense.id.«nauty:comp_canon» e = none)
    (hE2 : PTree.get dense.id.«nauty:canoncode» e = none)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hcode : PTree.get dense.id.code le = some (.Vint (ir c)))
    (hc : c < 32768) (hn : level ≤ n)
    (hQ : ∀ m', SearchAt m' S ctx (cmpCanonB level c st) pre nsp → Unch m m' (· ∈ [S.bCC]) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (.Sifthenelse (.Ebinop .Ogt (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint) tint)
      (sk (.Sassign (gats dense.id.«nauty:canoncode» (tv dense.id.level))
        (.Etempvar dense.id.code tshort))) .Sskip) Q e le m :=
  wp_canonBG h.toG hE1 hE2 hlev hcode hc hn fun m' h' hu hv => hQ m' (h'.dense h.gw) hu hv

/-- `if (eqlev_canon == level - 1) { if (code < canoncode[level]) comp_canon = -1; else if … }` -/
theorem wp_canonA {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level c : Nat}
    (h : SearchAt m S ctx st pre nsp)
    (hE1 : PTree.get dense.id.«nauty:comp_canon» e = none)
    (hE2 : PTree.get dense.id.«nauty:canoncode» e = none)
    (hE3 : PTree.get dense.id.«nauty:eqlev_canon» e = none)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hcode : PTree.get dense.id.code le = some (.Vint (ir c)))
    (hc : c < 32768) (h1 : 1 ≤ level) (hn : level ≤ n)
    (hQ : ∀ m', SearchAt m' S ctx (cmpCanonA level c st) pre nsp →
      Unch m m' (· ∈ [Block.compCanon, Block.eqlevCanon]) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f
      (.Sifthenelse
        (.Ebinop .Oeq (.Evar dense.id.«nauty:eqlev_canon» tint)
          (.Ebinop .Osub (tv dense.id.level) (ci 1 tint) tint) tint)
        (sk (.Sifthenelse
          (.Ebinop .Olt (.Etempvar dense.id.code tshort) (gats dense.id.«nauty:canoncode» (tv dense.id.level)) tint)
          (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (.Eunop .Oneg (ci 1 tint) tint)))
          (sk (.Sifthenelse
            (.Ebinop .Ogt (.Etempvar dense.id.code tshort) (gats dense.id.«nauty:canoncode» (tv dense.id.level)) tint)
            (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (ci 1 tint)))
            (.Ssequence
              (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint)))
              (sk (.Sassign (.Evar dense.id.«nauty:eqlev_canon» tint) (tv dense.id.level))))))))
        .Sskip) Q e le m :=
  wp_canonAG h.toG hE1 hE2 hE3 hlev hcode hc h1 hn fun m' h' hu hv =>
    hQ m' (h'.dense h.gw) hu hv

/-- `codeCanon`: `cmpCanon`, the best-leaf half of `compareCodes`. -/
theorem wp_codeCanon {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level c : Nat}
    (h : SearchAt m S ctx st pre nsp)
    (hE0 : PTree.get dense.id.«nauty:getcanon» e = none)
    (hE1 : PTree.get dense.id.«nauty:comp_canon» e = none)
    (hE2 : PTree.get dense.id.«nauty:canoncode» e = none)
    (hE3 : PTree.get dense.id.«nauty:eqlev_canon» e = none)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hcode : PTree.get dense.id.code le = some (.Vint (ir c)))
    (hc : c < 32768) (h1 : 1 ≤ level) (hn : level ≤ n)
    (hQ : ∀ m', SearchAt m' S ctx (cmpCanon level c st) pre nsp →
      Unch m m' (· ∈ [Block.compCanon, Block.eqlevCanon, S.bCC]) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f Othernode.codeCanon Q e le m :=
  wp_codeCanonG h.toG hE0 hE1 hE2 hE3 hlev hcode hc h1 hn fun m' h' hu hv =>
    hQ m' (h'.dense h.gw) hu hv

/-- `t711 = numcells < n && (eqlev_first == level || (getcanon && comp_canon >= 0))`: whether
`othernode0` needs a target cell, `chooseTarget false`'s condition. -/
theorem wp_target {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level nc : Nat} {bnc : block}
    (h : SearchAt m S ctx st pre nsp)
    (hEn : PTree.get dense.id.«nauty:n» e = none)
    (hE0 : PTree.get dense.id.«nauty:getcanon» e = none)
    (hE1 : PTree.get dense.id.«nauty:comp_canon» e = none)
    (hE3 : PTree.get dense.id.«nauty:eqlev_first» e = none)
    (hnc : PTree.get dense.id.numcells e = some (bnc, tint))
    (hncv : Mem.load .Mint32 m bnc (zOfInt 0) = some (.Vint (ir nc))) (hncl : nc ≤ n)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (hln : level ≤ n)
    (hQ : ∀ le', PTree.get (idOf 711) le' = some (Val.of_bool
        (decide (nc < n ∧ (st.eqlevFirst = level ∨ 0 ≤ st.compCanon)))) →
      (∀ x, x ≠ idOf 711 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m) :
    Wp xi ge f Othernode.target Q e le m :=
  wp_targetG h.toG hEn hE0 hE1 hE3 hnc hncv hncl hlev hln hQ

end NautyVerified.Proofs.Search
