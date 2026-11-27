import NautyVerified.Proofs.Search.Processnode.Canon

/-!
# `processnode`'s stores to nauty.c's statics and to `sr`
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (Keep DynAt)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}
variable {n : Nat} {m₀ m₁ m : mem} {S : SLoc} {ctx : Ctx n} {e : env} {bsr : block}
  {st : Search n} {nsp : Bool}

/-- The `DYNALLSTAT` blocks are kept by a store elsewhere. -/
theorem keeps_of {m m' : mem} {b : block} (hd : S.blocks.Pairwise (· ≠ ·)) (hu : Unch m m' (· = b))
    (hb : ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC], z ≠ b) :
    ∀ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC], Keep m m' z :=
  fun z hz => Keep.unch hu (hb z hz)

/-- The `DYNALLSTAT` blocks across a store to a global `b` outside them. -/
macro "keeps " hd:term ", " hu:term : term =>
  `(keeps_of $hd $hu (by
      simp only [List.forall_mem_cons]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ h => absurd h List.not_mem_nil⟩ <;> sep_ne $hd))

/-- `comp_canon = rhs`. -/
theorem wp_compCanon {f : function} {Q : Post} {le : temp_env} (c : PCtx m₀ m₁ S e bsr)
    (h : PAt m₀ m₁ m S ctx bsr st nsp) {rhs : expr} {x : Int} (hx : -1 ≤ x ∧ x ≤ 1)
    (hr : Exec.evalExpr ge e le m rhs = some (.Vint (ir x))) (hrt : typeof rhs = tint)
    (hQ : ∀ m', PAt m₀ m₁ m' S ctx bsr { st with compCanon := x } nsp →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) rhs) Q e le m := by
  have hs := h.search
  have hd := hs.distinct
  have hinv := hs.inv
  refine wp_gint (c.eg _ (by decide)) find_compCanon hs.scalars.compCanon.writable hr hrt ?_
  intro m' hI hu hv
  have hu' : Unch m m' (· ∈ [Block.compCanon]) := hu.mono fun z hz => by simp [hz]
  have sc := hs.scalars
  refine hQ m' (PAt.next c h hu' (by simp [SLoc.wr, wrG])
    (keeps hd, hu)
    hv ⟨sc.gcaFirst.unch hu (by sep_ne hd), sc.gcaCanon.unch hu (by sep_ne hd),
      sc.noncheaplevel.unch hu (by sep_ne hd), sc.allsamelevel.unch hu (by sep_ne hd),
      sc.eqlevFirst.unch hu (by sep_ne hd), sc.eqlevCanon.unch hu (by sep_ne hd), hI,
      sc.samerows.unch hu (by sep_ne hd), sc.canonlevel.unch hu (by sep_ne hd),
      sc.stabvertex.unch hu (by sep_ne hd), sc.cosetindex.unch hu (by sep_ne hd),
      sc.needshortprune.unch hu (by sep_ne hd)⟩
    ((hs.stats.unch hu (by sep_ne hd)).cast rfl) ((hs.arrays.unch hu (by sep_all hd)).cast rfl)
    { hinv with
      scalars := by
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, -, -, a10, a11, a12⟩ := hinv.scalars
        exact ⟨a1, a2, a3, a4, a5, a6, a7, hx.1, hx.2, a10, a11, a12⟩ })
    fun v hv' => hv'.unch hu fun e => c.ne_blocks (by simp [SLoc.blocks]) e.symm

/-- `samerows = n`, once `canong` holds all `n` rows. -/
theorem wp_samerowsN {f : function} {Q : Post} {le : temp_env} (c : PCtx m₀ m₁ S e bsr)
    (h : PAt m₀ m₁ m S ctx bsr st nsp) (hfull : CanongAt m S st.canong n)
    (hQ : ∀ m', PAt m₀ m₁ m' S ctx bsr { st with samerows := n } nsp →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar dense.id.«nauty:samerows» tint) (.Evar dense.id.«nauty:n» tint))
      Q e le m := by
  have hs := h.search
  have hd := hs.distinct
  have hinv := hs.inv
  refine wp_gint (x := n) (c.eg _ (by decide)) find_samerows hs.scalars.samerows.writable
    (eval_gint (c.eg _ (by decide)) find_n hs.fixed.nn) rfl ?_
  intro m' hI hu hv
  have hu' : Unch m m' (· ∈ [Block.samerows]) := hu.mono fun z hz => by simp [hz]
  have sc := hs.scalars
  have ar := hs.arrays.unch hu (by sep_all hd)
  refine hQ m' (PAt.next c h hu' (by simp [SLoc.wr, wrG]) (keeps hd, hu)
    hv ⟨sc.gcaFirst.unch hu (by sep_ne hd), sc.gcaCanon.unch hu (by sep_ne hd),
      sc.noncheaplevel.unch hu (by sep_ne hd), sc.allsamelevel.unch hu (by sep_ne hd),
      sc.eqlevFirst.unch hu (by sep_ne hd), sc.eqlevCanon.unch hu (by sep_ne hd),
      sc.compCanon.unch hu (by sep_ne hd), hI, sc.canonlevel.unch hu (by sep_ne hd),
      sc.stabvertex.unch hu (by sep_ne hd), sc.cosetindex.unch hu (by sep_ne hd),
      sc.needshortprune.unch hu (by sep_ne hd)⟩
    ((hs.stats.unch hu (by sep_ne hd)).cast rfl)
    { ar with canong := hfull.unch hu (by sep_ne hd) }
    { hinv with samerows := Nat.le_refl n })
    fun v hv' => hv'.unch hu fun e => c.ne_blocks (by simp [SLoc.blocks]) e.symm

/-- `sr = 0`. -/
theorem wp_sr0 {f : function} {Q : Post} {le : temp_env} (c : PCtx m₀ m₁ S e bsr)
    (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (hQ : ∀ m', PAt m₀ m₁ m' S ctx bsr st nsp → SrAt m' bsr 0 → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar dense.id.«sr» tint) (ci 0 tint)) Q e le m := by
  have hw : Mem.valid_access m .Mint32 bsr (zOfInt 0) .Writable :=
    Mem.valid_access_implies _ _ _ _ _ _ h.srW (.perm_F_any _)
  obtain ⟨m', hst⟩ := Mem.valid_access_store _ _ _ _ (.Vint (ir 0)) hw
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, c.esr, typeof, cop, ite_true,
    Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hst]
  have hu : Unch m m' (· = bsr) := (Unch.store hst rfl).mono fun z hz => hz.symm
  refine hQ m' (PAt.sr c h hu (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)
    (Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ h.srW)) ⟨by decide, by decide, fun i hi => ?_,
      fun i hi => ?_⟩
  · have : i = 0 := by omega
    subst this
    rw [show elemOfs .Mint32 (intOfZ (Ptrofs.unsigned Ptrofs.zero)) 0 = zOfInt 0 from rfl,
      Mem.load_store_same _ _ _ _ _ _ hst]
    rfl
  · have : i = 0 := by omega
    subst this
    exact Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ hw

end NautyVerified.Proofs.Search.Processnode
