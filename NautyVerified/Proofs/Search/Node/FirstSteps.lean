import NautyVerified.Proofs.Search.Node.Compare
import NautyVerified.Proofs.Search.Node.OtherSteps

/-!
# Straight-line steps of `firstpathnode0`

`wp_recordFirst`: `firstcode[level] = (short)refcode` is HexGraphIso's
`recordFirst level code`, for the `refcode` local holding `code`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Refine (tv)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

theorem Arrays.setFirstcode {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    (h : Arrays m S ctx st) (hu : Unch m m' (· = S.bFC)) (hd : S.blocks.Pairwise (· ≠ ·))
    {fc : Array Nat} (hfc : ArrayAt m' .Mint16signed S.bFC 0 (shorts fc) (n + 2)) :
    Arrays m' S ctx { st with firstcode := fc } := by
  obtain ⟨aw, ha, har⟩ := h.active
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  obtain ⟨wv, hwv⟩ := h.workperm
  exact ⟨h.lab.unch hu (by sep_ne hd), h.ptn.unch hu (by sep_ne hd),
    h.orbits.unch hu (by sep_ne hd), ⟨aw, ha.unch hu (by sep_ne hd), har⟩,
    ⟨fw, hf.unch hu (by sep_ne hd), hfr⟩, ⟨wv, hwv.unch hu (by sep_ne hd)⟩,
    h.firstlab.unch hu (by sep_ne hd), h.canonlab.unch hu (by sep_ne hd), hfc,
    h.canoncode.unch hu (by sep_ne hd), h.firsttc.unch hu (by sep_ne hd),
    h.canong.unch hu (by sep_ne hd), h.autos.unch hu (by sep_ne hd) (by sep_ne hd),
    ⟨h.graph.arr.unch hu (by sep_ne hd), h.graph.rep⟩⟩

/-- `firstcode[level] = (short)refcode;` -/
theorem wp_recordFirst {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level code : Nat} {bk : block}
    (h : SearchAt m S ctx st pre nsp)
    (hE : PTree.get dense.id.«nauty:firstcode» e = none)
    (hek : PTree.get dense.id.«refcode» e = some (bk, tint))
    (hkv : Mem.load .Mint32 m bk (zOfInt 0) = some (.Vint (ir code)))
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (hc : code < 32768) (hn : level ≤ n)
    (hQ : ∀ m', SearchAt m' S ctx (recordFirst level code st) pre nsp → Unch m m' (· ∈ [S.bFC]) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (gats dense.id.«nauty:firstcode» (tv dense.id.level))
      (.Ecast (.Evar dense.id.«refcode» tint) tshort)) Q e le m := by
  have hnl := h.nlt
  have hd := h.distinct
  have hrhs : Exec.evalExpr ge e le m (.Ecast (.Evar dense.id.«refcode» tint) tshort) =
      some (.Vint (ir (code : Int))) := by
    rw [Exec.evalExpr, eval_local hek hkv]
    simp only [typeof, Cfrontend.Cop.sem_cast, Cfrontend.Cop.classify_cast, Cfrontend.Cop.cast_int_int]
    exact congrArg (fun x => some (val.Vint x)) (sign_ext16_ir (a := code) (by omega) (by omega))
  refine wp_gstoreS hE Program.find_nautyFirstcode
    (h.dyns.firstcode.ptr (by have := h.dyns.capFC; omega)) h.arrays.firstcode (by omega)
    (tv dense.id.level) level (by omega) hlev rfl _ code hc hrhs (.inr rfl) ?_
  intro m' harr hu hk hv
  have hU : Unch m m' (· ∈ [S.bFC]) := hu.mono fun z hz => by simp [hz]
  have hfs := h.inv.firstcodeSize
  refine hQ m' ?_ hU hv
  refine h.rebuild hU (fun z hz => by simp at hz; subst hz; simp [SLoc.wr, SLoc.wrV])
    (fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hk | exact Keep.unch hu (by sep_ne hd))
    { h.scalars.unch hu (by sep_all hd) with } { h.stats.unch hu (by sep_ne hd) with }
    (h.arrays.setFirstcode hu hd (by rw [shorts_set (by omega)]; exact harr)) ?_
  have i := h.inv
  exact { i with
    codesSmall := fun j hj => by
      refine ⟨?_, (i.codesSmall j hj).2⟩
      show (st.firstcode.set! level code)[j]! < 32768
      by_cases hjl : j = level
      · subst hjl; rw [Array.getElem!_set!_self _ _ _ (by omega)]; omega
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hjl)]; exact (i.codesSmall j hj).1
    firstcodeSize := by show (st.firstcode.set! level code).size = n + 2; simp [hfs] }

end NautyVerified.Proofs.Search
