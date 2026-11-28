import NautyVerified.Proofs.Search.Processnode.Orb
import NautyVerified.Proofs.Top.NautyMain

/-!
# Reporting a generator

`wp_callback`: `if (userautomproc != NULL) (*userautomproc)(stats->numgenerators,
workperm, orbits, stats->numorbits, stabvertex, n);` with `workperm` holding `w`
writes `genWords w n` and changes nothing.
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
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}
variable {n : Nat} {m₀ m₁ m : mem} {S : SLoc} {ctx : Ctx n} {e : env} {bsr : block}
  {st : Search n} {nsp : Bool}

abbrev cbType : type := tfun [tint, tptr tint, tptr tint, tint, tint, tint] .Tvoid

abbrev callbackC : statement :=
  sk (.Sifthenelse
    (.Ebinop .One (.Evar dense.id.«nauty:userautomproc» (tptr cbType))
      (.Ecast (ci 0 tint) (tptr .Tvoid)) tint)
    (sk (.Scall none (.Ederef (.Evar dense.id.«nauty:userautomproc» (tptr cbType)) cbType)
      [(statsF dense.id.«numgenerators» tint), (.Evar dense.id.«nauty:workperm» (tptr tint)),
       (.Evar dense.id.«nauty:orbits» (tptr tint)), (statsF dense.id.«numorbits» tint),
       (.Evar dense.id.«nauty:stabvertex» tint), (.Evar dense.id.«nauty:n» tint)]))
    .Sskip)

theorem perm_of_va {m : mem} {b : block}
    (h : Mem.valid_access m .Mint8unsigned b (zOfInt 0) .Nonempty) :
    Mem.perm m b (zOfInt 0) .Cur .Nonempty :=
  h.1 _ ⟨by change intOfZ _ ≤ intOfZ _; omega, by
    change intOfZ _ < intOfZ _; simp only [intOfZ_add, intOfZ_zOfInt]
    have : intOfZ (Common.Memdata.size_chunk .Mint8unsigned) = 1 := rfl
    omega⟩

theorem wp_callback {f : function} {Q : Post} {le : temp_env} {w : Array Nat}
    (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp) (hcb : AutomCb xi S.bUA)
    (hw : ArrayAt m .Mint32 S.bWP 0 (ints w) n) (hws : ∀ i < n, w[i]! < n)
    (hQ : ∀ t, Writes t (genWords w n) → Q.normal t e le m) :
    Wp xi ge f callbackC Q e le m := by
  have hs := h.search
  have hfit := hs.stats.fits
  have hnl := hs.nlt
  have hcWP : 0 < S.capWP := by have := hs.dyns.capWP; have := hs.n0; omega
  have hua := hs.fixed.userautomproc
  obtain ⟨fd, hfd, hty, hsat⟩ := hcb
  wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_gptr (c.eg _ (by decide)) find_userautomproc rfl hua]
  simp only [Exec.evalExpr, typeof, cop, Top.ne_pl, Top.cmp_null_ne (perm_of_va h.ua), Option.map]
  simp only [cop, ite_true]
  wp_step; wp_step
  refine wp_call (vf := .Vptr S.bUA Ptrofs.zero)
    (targs := [tint, tptr tint, tptr tint, tint, tint, tint]) (tres := .Tvoid) (cc := cc_default)
    (vargs := [.Vint (ir st.numgenerators), .Vptr S.bWP Ptrofs.zero, .Vptr S.bo S.oofs,
      .Vint (ir st.numorbits), .Vint (ir st.stabvertex), .Vint (ir n)]) fd _
    (hsat (ir st.numgenerators) S.bWP Ptrofs.zero w n S.bo S.oofs (ir st.numorbits)
      (ir st.stabvertex)) rfl ?_ ?_ hfd hty ⟨rfl, hw, by omega, fun i hi => by have := hws i hi; omega⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, c.eg _ (by decide : dense.id.«nauty:userautomproc» ≠ dense.id.sr),
      find_userautomproc, Exec.derefLoc, access_mode, Mem.loadv, Alloc.Mptr_eq,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hua.load]
  · simp only [Exec.evalExprlist,
      eval_statsF (ty := tint) (c.eg _ (by decide)) fld_numgenerators rfl hs.fixed.stats (by decide)
        (by omega) hs.stats.numgenerators,
      eval_gptr (ty := tptr tint) (c.eg _ (by decide)) find_nautyWorkperm rfl
        ⟨hs.dyns.workperm.ptr hcWP, hs.dyns.workperm.bpW⟩,
      eval_gptr (ty := tptr tint) (c.eg _ (by decide)) find_orbits rfl hs.fixed.orbits,
      eval_statsF (ty := tint) (c.eg _ (by decide)) fld_numorbits rfl hs.fixed.stats (by decide)
        (by omega) hs.stats.numorbits,
      eval_gint (c.eg _ (by decide)) find_stabvertex hs.scalars.stabvertex,
      eval_gint (c.eg _ (by decide)) find_n hs.fixed.nn, typeof, cop]
  · rintro t r m' ⟨hW, rfl⟩
    simp only [set_opttemp]
    exact hQ t hW

end NautyVerified.Proofs.Search.Processnode
