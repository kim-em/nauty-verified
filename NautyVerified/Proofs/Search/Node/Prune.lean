import NautyVerified.Proofs.Search.Node.OtherSteps
import NautyVerified.Proofs.Prune.Short
import NautyVerified.Proofs.Set.Inter
import NautyVerified.Logic.Grow

/-!
# Consuming a short-prune request

`wp_prune0`: `if (needshortprune) { needshortprune = FALSE; shortprune(tcell,
fmptr - M, M); }` intersects the target cell with the `mcr` of the last stored
automorphism pair (HexGraphIso's `shortprune`), and clears the request.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Set (sk longs andW setRep_andW)
open NautyVerified.Proofs.Refine (tv)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

/-- `p - j` for `p` at element `k + j`. -/
theorem sub_ptrTo_n (base : Int) (sz : Z) (k j : Nat) (hj : (j : Int) < 2147483648) :
    Ptrofs.sub (ptrTo base (intOfZ sz) (k + j)) (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_ints (ir j))) =
      ptrTo base (intOfZ sz) k := by
  apply bvp_inj.1
  rw [bvp_sub, bvp_mul, bvp_repr, bvp_of_ints, toInt_ir ⟨by omega, hj⟩, bvp_repr,
    bvp_repr, intOfZ_zOfInt, intOfZ_zOfInt, ← BitVec.ofInt_mul]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add]
  congr 1
  push_cast
  rw [Int.mul_add]
  omega

/-- The last stored pair's `mcr`. -/
theorem shortprune_last {cell : VSet n} {st : Search n} (h : 0 < st.autos.size) :
    shortprune cell st = cell.inter st.autos[st.autos.size - 1]!.2 := by
  unfold shortprune
  rw [Array.back?_eq_getElem?, getElem?_pos st.autos (st.autos.size - 1) (by omega)]
  simp [getElem!_pos st.autos (st.autos.size - 1) (by omega)]

/-- A work block after a change that avoids the work arrays' globals was one before. -/
theorem IsWork.back {m m₁ : mem} {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    (h : SearchAt m S ctx st pre nsp) {W : block → Prop} (hu : Unch m m₁ W)
    (hW : ∀ z ∈ [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
      Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
      Block.nautilWorkperm, Block.nautilWorkpermSz], ¬ W z) {z : block} (hz : IsWork m₁ z) :
    IsWork m z := by
  simp only [List.forall_mem_cons] at hW
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, -⟩ := hW
  obtain ⟨cW, bW, cS, bS, cB, bB, cN, bN, dW, dS, dB, dN, -⟩ := h.work.arr
  have back : ∀ {bp bs : block} {c c₀ cap : Nat} {b₀ : block}, ¬ W bp → ¬ W bs →
      DynAt m bp bs c c₀ b₀ → DynAt m₁ bp bs c cap z → 0 < cap → c₀ = cap ∧ b₀ = z := by
    intro bp bs c c₀ cap b₀ hp hs d d₁ hc
    have hcap : c₀ = cap := by
      have := d.capLd.symm.trans ((hu.load _ _ _ hs).symm.trans d₁.capLd)
      simp only [Option.some.injEq, val.Vlong.injEq] at this
      exact lr_nat_inj d.capLt d₁.capLt this
    refine ⟨hcap, ?_⟩
    have := (d.ptr (hcap ▸ hc)).symm.trans ((hu.load _ _ _ hp).symm.trans (d₁.ptr hc))
    simp only [Option.some.injEq, val.Vptr.injEq] at this
    exact this.1
  rcases hz with ⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩
  · obtain ⟨rfl, rfl⟩ := back g1 g2 dW d hc; exact .inl ⟨_, hc, dW⟩
  · obtain ⟨rfl, rfl⟩ := back g3 g4 dS d hc; exact .inr (.inl ⟨_, hc, dS⟩)
  · obtain ⟨rfl, rfl⟩ := back g5 g6 dB d hc; exact .inr (.inr (.inl ⟨_, hc, dB⟩))
  · obtain ⟨rfl, rfl⟩ := back g7 g8 dN d hc; exact .inr (.inr (.inr ⟨_, hc, dN⟩))

theorem sizeof_tulong8 : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong) = 8 := rfl

/-- `if (needshortprune) { needshortprune = FALSE; shortprune(tcell, fmptr - M, M); }` -/
theorem wp_prune0 {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    (hE1 : PTree.get dense.id.«nauty:needshortprune» e = none)
    (hE2 : PTree.get dense.id.«nauty:fmptr» e = none)
    (hE3 : PTree.get dense.id.«nauty:m» e = none)
    (hE4 : PTree.get dense.id.«shortprune» e = none)
    {btc : block} (htl : PTree.get dense.id.tcell le = some (.Vptr btc Ptrofs.zero))
    {tw : Nat → Lib.Integers.int64} (htw : ArrayAt m .Mint64 btc 0 (longs tw) S.M)
    {cell : VSet n} (hrep : SetRep (fun w => bv64 (tw w)) S.M cell)
    (hbS : btc ∉ S.blocks) (hbW : ¬ IsWork m btc) (hnz : nsp = true → 0 < st.autos.size)
    (hQ : ∀ m' (tw' : Nat → Lib.Integers.int64), SearchAt m' S ctx st pre false →
      ArrayAt m' .Mint64 btc 0 (longs tw') S.M →
      SetRep (fun w => bv64 (tw' w)) S.M (if nsp then shortprune cell st else cell) →
      Unch m m' (fun z => z = Block.needshortprune ∨ z = btc) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f Othernode.prune0 Q e le m := by
  have hd := h.distinct
  have hM1 := h.M1
  have hMl := h.Mlt
  simp only [Othernode.prune0, sk]
  apply wp_if_eval
  rw [eval_gint hE1 find_needshortprune h.scalars.needshortprune]
  cases nsp
  · simp only [Bool.false_eq_true, ite_false, typeof, cop]
    rw [ite_eq_right (by decide)]
    apply wp_skip
    exact hQ m tw h htw (by simpa using hrep) (Unch.refl _ _) fun _ h => h
  · simp only [ite_true, typeof, cop]
    rw [ite_eq_left (by decide)]
    have hk := hnz rfl
    wp_step; wp_step; wp_step
    refine wp_gint hE1 find_needshortprune h.scalars.needshortprune.writable (x := 0)
      (by simp [Exec.evalExpr]) rfl ?_
    intro m₁ iN hu₁ hv₁
    have hU₁ : Unch m m₁ (· ∈ [Block.needshortprune]) := hu₁.mono fun z hz => by simp [hz]
    have sc := h.scalars
    have h₁ : SearchAt m₁ S ctx st pre false :=
      h.setScalars hU₁ (fun z hz => by simp at hz; subst hz; decide)
        ⟨sc.gcaFirst.unch hU₁ (by decide), sc.gcaCanon.unch hU₁ (by decide),
          sc.noncheaplevel.unch hU₁ (by decide), sc.allsamelevel.unch hU₁ (by decide),
          sc.eqlevFirst.unch hU₁ (by decide), sc.eqlevCanon.unch hU₁ (by decide),
          sc.compCanon.unch hU₁ (by decide), sc.samerows.unch hU₁ (by decide),
          sc.canonlevel.unch hU₁ (by decide), sc.stabvertex.unch hU₁ (by decide),
          sc.cosetindex.unch hU₁ (by decide), iN⟩
        h.arrays h.stats h.inv
    have hbtc : btc ≠ Block.needshortprune := fun he => hbS (by rw [he]; simp [SLoc.blocks])
    have htw₁ := htw.unch hU₁ (by simpa using hbtc)
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    -- the last pair's `mcr`
    obtain ⟨ww, hww, hpairs⟩ := h₁.arrays.autos.arr
    have hsz := h₁.arrays.autos.size
    have hlast := (hpairs (st.autos.size - 1) (by omega)).2
    let j := 2 * S.M * (st.autos.size - 1) + S.M
    have hj2 : 2 * S.M * st.autos.size = j + S.M := by
      obtain ⟨k, hk'⟩ : ∃ k, st.autos.size = k + 1 := ⟨st.autos.size - 1, by omega⟩
      simp only [j]; rw [hk', Nat.add_sub_cancel, Nat.mul_succ]; omega
    have hjb : j + S.M ≤ 2 * wsPairs * S.M := by
      rw [← hj2]
      calc 2 * S.M * st.autos.size ≤ 2 * S.M * wsPairs := Nat.mul_le_mul_left _ hsz
        _ = 2 * wsPairs * S.M := Nat.mul_right_comm _ _ _
    have hslice := hww.slice j S.M hjb
    have hfits := hww.fits
    have hfm := h₁.arrays.autos.fmptr
    have ho2 : Ptrofs.sub (Ptrofs.repr (zOfInt (S.wb + 8 * (2 * (S.M : Int) * (st.autos.size : Int)))))
        (Ptrofs.mul (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong))
          (Ptrofs.of_ints (ir (S.M : Int)))) = ptrTo S.wb 8 j := by
      have hj2' := congrArg (fun x : Nat => (x : Int)) hj2
      push_cast at hj2'
      rw [show (Ptrofs.repr (zOfInt (S.wb + 8 * (2 * (S.M : Int) * (st.autos.size : Int))))) =
        ptrTo S.wb (intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) (j + S.M) by
          rw [sizeof_tulong8]; simp only [ptrTo]; congr 2; push_cast; omega]
      rw [sub_ptrTo_n _ _ _ _ (by omega), sizeof_tulong8]
    have hu2 : intOfZ (Ptrofs.unsigned (ptrTo S.wb 8 j)) = S.wb + csize .Mint64 * j := by
      rw [unsigned_ptrTo (by have := hww.base_nonneg; omega)
        (by have : csize .Mint64 = 8 := rfl; rw [this] at hfits
            have := Nat.mul_le_mul_left 8 hjb; omega)]
      rfl
    refine wp_call (vf := .Vptr Block.shortpruneFn Ptrofs.zero) (targs := [tptr tulong, tptr tulong, tint])
      (tres := .Tvoid) (cc := Common.AST.cc_default) (.Internal dense.fn.shortprune)
      _
      (Prune.shortprune_satisfies btc Ptrofs.zero S.bws (ptrTo S.wb 8 j) S.M tw (fun i => ww (j + i))).grow rfl ?_ ?_
      (by simp [Common.Globalenvs.Genv.find_funct, funct_shortpruneFn]) rfl
      ⟨rfl, htw₁, by rw [hu2]; exact hslice, fun he => hbS (he ▸ by simp [SLoc.blocks]), by omega⟩ ?_
    · simp only [Exec.evalExpr, Exec.lvalOfVar, hE4, find_shortpruneFn, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode]
    · simp only [Exec.evalExprlist, Exec.evalExpr, htl, Exec.lvalOfVar, hE2, hE3, find_fmptr,
        find_m, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
        show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hfm.load, h₁.fixed.mm.load, typeof,
        cop, Alloc.Mptr_eq]
      rw [ho2]
    rintro t v m₂ ⟨⟨rfl, harr₂, hu₂, -⟩, hg₂⟩
    have hU₂ : Unch m₁ m₂ (fun z => z = btc) := hu₂
    refine hQ m₂ _ (h₁.unch hU₂ (fun z hz he => hbS (he ▸ hz))
        (fun z hz he => hbW (he ▸ IsWork.back h hU₁ (by
          intro z hz hzL; simp at hzL; subst hzL; revert hz; decide) hz)))
      harr₂ ?_ ?_ fun z hz => hg₂ z (hv₁ z hz)
    · simp only [ite_true]
      rw [shortprune_last hk]
      have e : (fun w => bv64 (ww (j + w))) =
          (fun w => bv64 (ww (2 * S.M * (st.autos.size - 1) + S.M + w))) := rfl
      exact setRep_andW hrep (by rw [e]; exact hlast)
    · exact (hU₁.mono fun z hz => by simp at hz; exact .inl hz).trans
        (hU₂.mono fun z hz => .inr hz)

end NautyVerified.Proofs.Search
