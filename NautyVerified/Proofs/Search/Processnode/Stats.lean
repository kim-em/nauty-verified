import NautyVerified.Proofs.Search.Processnode.Classify
import NautyVerified.Proofs.Search.Node.Steps

/-!
# `processnode`'s stores to the `statsblk`

`PAt.stat`: a store into the `statsblk` that gives the new `Stats`. The
`wp_*` lemmas: `stats->maxlevel = level` and the
increments of `numgenerators`, `canupdates` and `numbadleaves`.
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
open NautyVerified.Proofs.Alloc (Keep)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}
variable {n : Nat} {m₀ m₁ m : mem} {S : SLoc} {ctx : Ctx n} {e : env} {bsr : block}
  {st : Search n} {nsp : Bool}

theorem PAt.stat {m' : mem} {st' : Search n} (c : PCtx m₀ m₁ S e bsr)
    (h : PAt m₀ m₁ m S ctx bsr st nsp) {chunk : memory_chunk} {ofs : Z} {w : val}
    (hst : Mem.store chunk m S.bst ofs w = some m') (hs' : Stats m' S st' false)
    (e1 : scalView st' = scalView st) (e2 : arrView st' = arrView st) (hinv : SInv st') :
    PAt m₀ m₁ m' S ctx bsr st' nsp ∧ (∀ v, SrAt m bsr v → SrAt m' bsr v) ∧ Unch m m' (· = S.bst) := by
  have hs := h.search
  have hd := hs.distinct
  have hu : Unch m m' (· = S.bst) := Unch.store hst rfl
  have hu' : Unch m m' (· ∈ [S.bst]) := hu.mono fun z hz => by simp [hz]
  refine ⟨PAt.next c h hu' (by simp [SLoc.wr, SLoc.wrV]) ?_
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)
    ((hs.scalars.unch hu (by sep_all hd)).cast e1) hs' ((hs.arrays.unch hu (by sep_all hd)).cast e2)
    hinv, fun v hv => hv.unch hu fun e => c.ne_blocks (by simp [SLoc.blocks]) e.symm, hu⟩
  intro z hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Keep.unch hu (by sep_ne hd)

/-- `stats->maxlevel = level`. -/
theorem wp_maxlevel {f : function} {Q : Post} {le : temp_env} {level : Nat}
    (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (hl : level ≤ n)
    (hQ : ∀ m', PAt m₀ m₁ m' S ctx bsr { st with maxlevel := level } nsp →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Unch m m' (· = S.bst) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (statsF dense.id.maxlevel tint) (tv dense.id.level)) Q e le m := by
  have hs := h.search
  have hfit := hs.stats.fits
  refine wp_statsStore (off := 40) (chunk := .Mint32) (c.eg _ (by decide)) fld_maxlevel rfl
    hs.fixed.stats (by decide) (by omega) hs.stats.maxlevelW
    (w := .Vint (ir level)) (w' := .Vint (ir level)) hlev rfl ?_
  intro m' hst
  have sS := hs.stats
  obtain ⟨hP, hS, hU⟩ := PAt.stat (st' := { st with maxlevel := level }) c h hst
    { (sS.fix.store hst (by first | omega | (simp only [csize32, csize64]; omega))) with
      numorbits := sS.numorbits.store_other hst (by simp only [csize32]; omega)
      numgenerators := sS.numgenerators.store_other hst (by simp only [csize32]; omega)
      numnodes := sS.numnodes.store_other hst (by simp only [csize32, csize64]; omega)
      numbadleaves := sS.numbadleaves.store_other hst (by simp only [csize32, csize64]; omega)
      maxlevel := fun _ => FieldAt.store_same hst sS.maxlevelW
      maxlevelW := Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ sS.maxlevelW
      tctotal := sS.tctotal.store_other hst (by simp only [csize32, csize64]; omega)
      canupdates := sS.canupdates.store_other hst (by simp only [csize32, csize64]; omega)
      fits := sS.fits } rfl rfl { hs.inv with maxlevelLe := hl }
  exact hQ m' hP hS hU

/-- `stats->numgenerators += 1`. -/
theorem wp_numgenerators {f : function} {Q : Post} {le : temp_env}
    (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (hQ : ∀ m', PAt m₀ m₁ m' S ctx bsr { st with numgenerators := st.numgenerators + 1 } nsp →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Unch m m' (· = S.bst) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (statsF dense.id.numgenerators tint)
      (.Ebinop .Oadd (statsF dense.id.numgenerators tint) (ci 1 tint) tint)) Q e le m := by
  have hs := h.search
  have hfit := hs.stats.fits
  refine wp_statsStore (off := 16) (chunk := .Mint32) (c.eg _ (by decide)) fld_numgenerators rfl
    hs.fixed.stats (by decide) (by omega) hs.stats.numgenerators.writable
    (w := .Vint (ir ((st.numgenerators + 1 : Nat) : Int)))
    (w' := .Vint (ir ((st.numgenerators + 1 : Nat) : Int))) ?_ rfl ?_
  · have hv := eval_statsF (le := le) (ty := tint) (c.eg _ (by decide)) fld_numgenerators rfl
      hs.fixed.stats (by decide) (by omega) hs.stats.numgenerators
    rw [Exec.evalExpr, hv, eval_ci]
    simp only [typeof, cop, ir_add]
    push_cast; rfl
  intro m' hst
  have sS := hs.stats
  obtain ⟨hP, hS, hU⟩ := PAt.stat (st' := { st with numgenerators := st.numgenerators + 1 }) c h hst
    { (sS.fix.store hst (by first | omega | (simp only [csize32, csize64]; omega))) with
      numorbits := sS.numorbits.store_other hst (by simp only [csize32]; omega)
      numgenerators := FieldAt.store_same hst sS.numgenerators.writable
      numnodes := sS.numnodes.store_other hst (by simp only [csize32, csize64]; omega)
      numbadleaves := sS.numbadleaves.store_other hst (by simp only [csize32, csize64]; omega)
      maxlevel := fun hp => (sS.maxlevel hp).store_other hst (by simp only [csize32]; omega)
      maxlevelW := Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ sS.maxlevelW
      tctotal := sS.tctotal.store_other hst (by simp only [csize32, csize64]; omega)
      canupdates := sS.canupdates.store_other hst (by simp only [csize32, csize64]; omega)
      fits := sS.fits } rfl rfl { hs.inv with }
  exact hQ m' hP hS hU

/-- `stats->canupdates += 1`. -/
theorem wp_canupdates {f : function} {Q : Post} {le : temp_env}
    (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (hQ : ∀ m', PAt m₀ m₁ m' S ctx bsr { st with canupdates := st.canupdates + 1 } nsp →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Unch m m' (· = S.bst) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (statsF dense.id.canupdates tulong)
      (.Ebinop .Oadd (statsF dense.id.canupdates tulong) (ci 1 tint) tulong)) Q e le m := by
  have hs := h.search
  have hfit := hs.stats.fits
  refine wp_statsStore (off := 56) (chunk := .Mint64) (c.eg _ (by decide)) fld_canupdates rfl
    hs.fixed.stats (by decide) (by omega) hs.stats.canupdates.writable
    (w := .Vlong (lr ((st.canupdates + 1 : Nat) : Int)))
    (w' := .Vlong (lr ((st.canupdates + 1 : Nat) : Int))) ?_ rfl ?_
  · have hv := eval_statsF (le := le) (ty := tulong) (c.eg _ (by decide)) fld_canupdates rfl
      hs.fixed.stats (by decide) (by omega) hs.stats.canupdates
    rw [Exec.evalExpr, hv]
    simp only [Exec.evalExpr, typeof, cop, lr_succ]
  intro m' hst
  have sS := hs.stats
  obtain ⟨hP, hS, hU⟩ := PAt.stat (st' := { st with canupdates := st.canupdates + 1 }) c h hst
    { (sS.fix.store hst (by first | omega | (simp only [csize32, csize64]; omega))) with
      numorbits := sS.numorbits.store_other hst (by simp only [csize32, csize64]; omega)
      numgenerators := sS.numgenerators.store_other hst (by simp only [csize32, csize64]; omega)
      numnodes := sS.numnodes.store_other hst (by simp only [csize64]; omega)
      numbadleaves := sS.numbadleaves.store_other hst (by simp only [csize64]; omega)
      maxlevel := fun hp => (sS.maxlevel hp).store_other hst (by simp only [csize32, csize64]; omega)
      maxlevelW := Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ sS.maxlevelW
      tctotal := sS.tctotal.store_other hst (by simp only [csize64]; omega)
      canupdates := FieldAt.store_same hst sS.canupdates.writable
      fits := sS.fits } rfl rfl { hs.inv with }
  exact hQ m' hP hS hU

/-- `stats->numbadleaves += 1`. -/
theorem wp_numbadleaves {f : function} {Q : Post} {le : temp_env}
    (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (hQ : ∀ m', PAt m₀ m₁ m' S ctx bsr { st with numbadleaves := st.numbadleaves + 1 } nsp →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Unch m m' (· = S.bst) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (statsF dense.id.numbadleaves tulong)
      (.Ebinop .Oadd (statsF dense.id.numbadleaves tulong) (ci 1 tint) tulong)) Q e le m := by
  have hs := h.search
  have hfit := hs.stats.fits
  refine wp_statsStore (off := 32) (chunk := .Mint64) (c.eg _ (by decide)) fld_numbadleaves rfl
    hs.fixed.stats (by decide) (by omega) hs.stats.numbadleaves.writable
    (w := .Vlong (lr ((st.numbadleaves + 1 : Nat) : Int)))
    (w' := .Vlong (lr ((st.numbadleaves + 1 : Nat) : Int))) ?_ rfl ?_
  · have hv := eval_statsF (le := le) (ty := tulong) (c.eg _ (by decide)) fld_numbadleaves rfl
      hs.fixed.stats (by decide) (by omega) hs.stats.numbadleaves
    rw [Exec.evalExpr, hv]
    simp only [Exec.evalExpr, typeof, cop, lr_succ]
  intro m' hst
  have sS := hs.stats
  obtain ⟨hP, hS, hU⟩ := PAt.stat (st' := { st with numbadleaves := st.numbadleaves + 1 }) c h hst
    { (sS.fix.store hst (by first | omega | (simp only [csize32, csize64]; omega))) with
      numorbits := sS.numorbits.store_other hst (by simp only [csize32, csize64]; omega)
      numgenerators := sS.numgenerators.store_other hst (by simp only [csize32, csize64]; omega)
      numnodes := sS.numnodes.store_other hst (by simp only [csize64]; omega)
      numbadleaves := FieldAt.store_same hst sS.numbadleaves.writable
      maxlevel := fun hp => (sS.maxlevel hp).store_other hst (by simp only [csize32, csize64]; omega)
      maxlevelW := Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ sS.maxlevelW
      tctotal := sS.tctotal.store_other hst (by simp only [csize64]; omega)
      canupdates := sS.canupdates.store_other hst (by simp only [csize64]; omega)
      fits := sS.fits } rfl rfl { hs.inv with }
  exact hQ m' hP hS hU

end NautyVerified.Proofs.Search.Processnode
