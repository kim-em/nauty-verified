import NautyVerified.Proofs.Top.Check
import NautyVerified.Proofs.Sparse.Isautom.Loops

/-!
# `nausparse_check`

nausparse.c is compiled with `MAXN = 0`, so `nausparse_check` tests only the
word size and the version. Called with `WORDSIZE = 64` and nauty's version
`29300`, both tests pass and it returns without touching memory
(`checkSpec`, the dense checks' specification).
-/

namespace NautyVerified.Proofs.Sparse

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv)

/-- `if (<c>) { fprintf(ERRFILE, <msg>); exit(1); }` -/
abbrev failIf (c : expr) (msg : ident) (len : Int) : statement :=
  sk (.Sifthenelse c
    (.Ssequence
      (sk (.Scall none
        (.Evar sparse.id.fprintf
          (.Tfunction [tptr (.Tstruct sparse.id.«_IO_FILE» Cfrontend.Ctypes.noattr), tptr tschar] tint
            ⟨some (zOfInt 2), false, false⟩))
        [.Evar sparse.id.stderr (tptr (.Tstruct sparse.id.«_IO_FILE» Cfrontend.Ctypes.noattr)),
         .Evar msg (tarray tschar len)]))
      (sk (.Scall none (.Evar sparse.id.exit (tfun [tint] .Tvoid)) [ci 1 tint])))
    .Sskip)

abbrev checkBody : statement :=
  .Ssequence
    (failIf (.Ebinop .One (tv sparse.id.wordsize) (ci 64 tint) tint) sparse.id.«nausparse:__stringlit_20» 41)
    (failIf (.Ebinop .Olt (tv sparse.id.version) (.Ebinop .Oadd (ci 29300 tint) (ci 0 tint) tint) tint)
      sparse.id.«nausparse:__stringlit_21» 37)

kernel_rfl check_eq : sparse.body.nausparse_check = checkBody

/-- `nausparse_check(64, m, n, 29300)` returns, changing nothing. -/
theorem check_satisfies {xi : ExternalCalls} (mv nv : val) :
    Satisfies xi sge (.Internal sparse.fn.nausparse_check) (Top.checkSpec mv nv) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m => e = empty_env ∧
    PTree.get sparse.id.wordsize le = some (.Vint (ir 64)) ∧
    PTree.get sparse.id.version le = some (.Vint (ir 29300)) ∧ m = m₀) ?_ ?_
  · rintro args m rfl
    refine ⟨empty_env, PTree.set sparse.id.version (.Vint (ir 29300)) (PTree.set sparse.id.n nv
      (PTree.set sparse.id.m mv (PTree.set sparse.id.wordsize (.Vint (ir 64))
        (create_undef_temps sparse.fn.nausparse_check.fn_temps)))), m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, ?_, ?_, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
    · simp (config := {decide := true}) only [temps_gso, temps_gss]
    · simp (config := {decide := true}) only [temps_gss]
  · rintro args m₀ rfl
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, hw, hv, rfl⟩
    rw [sparse.fn.nausparse_check.fn_body_eq, check_eq]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, tv, hw, typeof, cop]
    rw [show Lib.Integers.Int.repr (zOfInt 64) = ir 64 from rfl,
      ir_eq (a := 64) (b := 64) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
    simp only [decide_true, Bool.not_true, Bool.false_eq_true, ite_false, cop]
    apply wp_skip
    simp only [E0_append]
    wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hv, typeof, cop]
    rw [show Lib.Integers.Int.repr (zOfInt 29300) = ir 29300 from rfl,
      show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl, ir_add,
      ir_lt (a := 29300) (b := 29300 + 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
    simp only [show decide ((29300 : Int) < 29300 + 0) = false from rfl,
      Bool.false_eq_true, ite_false, cop]
    apply wp_skip
    exact ⟨m, Isautom.free_empty m, rfl, rfl⟩

end NautyVerified.Proofs.Sparse
