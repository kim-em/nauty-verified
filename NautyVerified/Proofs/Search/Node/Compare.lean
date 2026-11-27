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

variable {xi : ExternalCalls} {n : Nat}

/-- The comparison with the first leaf's code. -/
def cmpFirst (level code : Nat) (st : Search n) : Search n :=
  if st.eqlevFirst == level - 1 ∧ code == st.firstcode[level]! then
    { st with eqlevFirst := level } else st

/-- The comparison with the best leaf's code, and the update of its code. -/
def cmpCanon (level code : Nat) (st : Search n) : Search n :=
  let st :=
    if st.eqlevCanon == Int.ofNat level - 1 then
      if code < st.canoncode[level]! then { st with compCanon := -1 }
      else if code > st.canoncode[level]! then { st with compCanon := 1 }
      else { st with compCanon := 0, eqlevCanon := Int.ofNat level }
    else st
  if st.compCanon > (0 : Int) then { st with canoncode := st.canoncode.set! level code } else st

theorem compareCodes_eq (level code : Nat) (st : Search n) :
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
      Q e le m := by
  have hnl := h.nlt
  obtain ⟨-, -, -, -, hef, -⟩ := h.inv.scalars
  simp only [Othernode.codeFirst, sk]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_gint hE1 find_eqlevFirst h.scalars.eqlevFirst]
  simp only [Exec.evalExpr, hlev, tv, typeof, cop, ir_sub]
  rw [ir_eq (a := (st.eqlevFirst : Int)) (b := (level : Int) - 1) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩]
  have hd := h.distinct
  have hfc := h.inv.codesSmall level (by omega)
  have hFC : Exec.evalExpr ge e le m (gats dense.id.«nauty:firstcode» (tv dense.id.level)) =
      some (.Vint (ir (st.firstcode[level]! : Int))) :=
    eval_gats hE2 Program.find_nautyFirstcode (h.dyns.firstcode.ptr (by have := h.dyns.capFC; omega))
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
      refine wp_gint hE1 find_eqlevFirst h.scalars.eqlevFirst.writable
        (show Exec.evalExpr ge e le' m (tv dense.id.level) = _ from hlev') rfl ?_
      intro m' iEF hu hv
      have hU : Unch m m' (· ∈ [Block.eqlevFirst]) := hu.mono fun z hz => by simp [hz]
      have hcf : cmpFirst level c st = { st with eqlevFirst := level } := by
        unfold cmpFirst
        rw [ite_eq_left (by simp; omega)]
      refine hQ le' m' ?_ hU hv ho
      rw [hcf]
      have sc := h.scalars
      refine h.setScalars hU (fun z hz => by simp at hz; subst hz; decide)
        ⟨sc.gcaFirst.unch hU (by decide), sc.gcaCanon.unch hU (by decide),
          sc.noncheaplevel.unch hU (by decide), sc.allsamelevel.unch hU (by decide), iEF,
          sc.eqlevCanon.unch hU (by decide), sc.compCanon.unch hU (by decide),
          sc.samerows.unch hU (by decide), sc.canonlevel.unch hU (by decide),
          sc.stabvertex.unch hU (by decide), sc.cosetindex.unch hU (by decide),
          sc.needshortprune.unch hU (by decide)⟩
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

end NautyVerified.Proofs.Search
