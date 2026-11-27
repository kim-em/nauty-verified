import NautyVerified.Proofs.Top.Init
import NautyVerified.Proofs.Nextelement.Satisfies
import NautyVerified.Proofs.Refine.Syntax

/-!
# `nautil_check` and `naugraph_check`

Called with `WORDSIZE = 64` and nauty's version `29300`, both checks pass and
return without touching memory (`checkSpec`).
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word
open NautyVerified.Source

set_option linter.unusedSimpArgs false

open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv)

abbrev nautil_checkBody : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .One (tv dense.id.«wordsize») (ci 64 tint) tint)
        (.Ssequence
          (sk
            (.Scall none
              (.Evar dense.id.«fprintf»
                (.Tfunction
                  [(tptr (.Tstruct dense.id.«_IO_FILE» Cfrontend.Ctypes.noattr)), (tptr tschar)]
                  tint
                  ⟨
                  (some (zOfInt 2))
                  ,
                  false
                  ,
                  false⟩))
              [(.Evar dense.id.«stderr» (tptr (.Tstruct dense.id.«_IO_FILE» Cfrontend.Ctypes.noattr))),
               (.Evar dense.id.«nautil:__stringlit_7» (tarray tschar 38))]))
          (sk (.Scall none (.Evar dense.id.«exit» (tfun [tint] .Tvoid)) [(ci 1 tint)])))
        .Sskip))
    (sk
      (.Sifthenelse
        (.Ebinop .Olt (tv dense.id.«version») (.Ebinop .Oadd (ci 29300 tint) (ci 0 tint) tint) tint)
        (.Ssequence
          (sk
            (.Scall none
              (.Evar dense.id.«fprintf»
                (.Tfunction
                  [(tptr (.Tstruct dense.id.«_IO_FILE» Cfrontend.Ctypes.noattr)), (tptr tschar)]
                  tint
                  ⟨
                  (some (zOfInt 2))
                  ,
                  false
                  ,
                  false⟩))
              [(.Evar dense.id.«stderr» (tptr (.Tstruct dense.id.«_IO_FILE» Cfrontend.Ctypes.noattr))),
               (.Evar dense.id.«nautil:__stringlit_8» (tarray tschar 34))]))
          (sk (.Scall none (.Evar dense.id.«exit» (tfun [tint] .Tvoid)) [(ci 1 tint)])))
        .Sskip)))

abbrev naugraph_checkBody : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .One (tv dense.id.«wordsize») (ci 64 tint) tint)
        (.Ssequence
          (sk
            (.Scall none
              (.Evar dense.id.«fprintf»
                (.Tfunction
                  [(tptr (.Tstruct dense.id.«_IO_FILE» Cfrontend.Ctypes.noattr)), (tptr tschar)]
                  tint
                  ⟨
                  (some (zOfInt 2))
                  ,
                  false
                  ,
                  false⟩))
              [(.Evar dense.id.«stderr» (tptr (.Tstruct dense.id.«_IO_FILE» Cfrontend.Ctypes.noattr))),
               (.Evar dense.id.«naugraph:__stringlit_8» (tarray tschar 40))]))
          (sk (.Scall none (.Evar dense.id.«exit» (tfun [tint] .Tvoid)) [(ci 1 tint)])))
        .Sskip))
    (sk
      (.Sifthenelse
        (.Ebinop .Olt (tv dense.id.«version») (.Ebinop .Oadd (ci 29300 tint) (ci 0 tint) tint) tint)
        (.Ssequence
          (sk
            (.Scall none
              (.Evar dense.id.«fprintf»
                (.Tfunction
                  [(tptr (.Tstruct dense.id.«_IO_FILE» Cfrontend.Ctypes.noattr)), (tptr tschar)]
                  tint
                  ⟨
                  (some (zOfInt 2))
                  ,
                  false
                  ,
                  false⟩))
              [(.Evar dense.id.«stderr» (tptr (.Tstruct dense.id.«_IO_FILE» Cfrontend.Ctypes.noattr))),
               (.Evar dense.id.«naugraph:__stringlit_9» (tarray tschar 36))]))
          (sk (.Scall none (.Evar dense.id.«exit» (tfun [tint] .Tvoid)) [(ci 1 tint)])))
        .Sskip)))


kernel_rfl nautil_check_eq : dense.body.nautil_check = nautil_checkBody
kernel_rfl naugraph_check_eq : dense.body.naugraph_check = naugraph_checkBody

/-- `xxx_check(64, m, n, 29300)` returns, changing nothing. -/
def checkSpec (mv nv : val) : FunSpec where
  pre args _ := args = [.Vint (ir 64), mv, nv, .Vint (ir 29300)]
  post _ m t _ m' := t = E0 ∧ m' = m

theorem nautil_check_satisfies {xi : ExternalCalls} (mv nv : val) :
    Satisfies xi ge (.Internal dense.fn.nautil_check) (checkSpec mv nv) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m => e = empty_env ∧
    PTree.get dense.id.wordsize le = some (.Vint (ir 64)) ∧
    PTree.get dense.id.version le = some (.Vint (ir 29300)) ∧ m = m₀) ?_ ?_
  · rintro args m rfl
    refine ⟨empty_env, PTree.set dense.id.version (.Vint (ir 29300)) (PTree.set dense.id.n nv
      (PTree.set dense.id.m mv (PTree.set dense.id.wordsize (.Vint (ir 64))
        (create_undef_temps dense.fn.nautil_check.fn_temps)))), m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, ?_, ?_, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
    · simp (config := {decide := true}) only [temps_gso, temps_gss]
    · simp (config := {decide := true}) only [temps_gss]
  · rintro args m₀ rfl
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, hw, hv, rfl⟩
    rw [dense.fn.nautil_check.fn_body_eq, nautil_check_eq]
    simp only [nautil_checkBody]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, tv, hw, typeof, cop]
    rw [show Lib.Integers.Int.repr (zOfInt 64) = ir 64 from rfl,
      ir_eq (a := 64) (b := 64) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
    simp only [decide_true, Bool.not_true, Val.of_bool, Bool.false_eq_true, ite_false, cop]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, tv, hv, typeof, cop]
    rw [show Lib.Integers.Int.repr (zOfInt 29300) = ir 29300 from rfl,
      show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl, ir_add,
      ir_lt (a := 29300) (b := 29300 + 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
    simp only [show decide ((29300 : Int) < 29300 + 0) = false from rfl, Val.of_bool,
      Bool.false_eq_true, ite_false, cop]
    apply wp_skip
    exact ⟨m, Nextelement.free_empty m, rfl, rfl⟩

theorem naugraph_check_satisfies {xi : ExternalCalls} (mv nv : val) :
    Satisfies xi ge (.Internal dense.fn.naugraph_check) (checkSpec mv nv) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m => e = empty_env ∧
    PTree.get dense.id.wordsize le = some (.Vint (ir 64)) ∧
    PTree.get dense.id.version le = some (.Vint (ir 29300)) ∧ m = m₀) ?_ ?_
  · rintro args m rfl
    refine ⟨empty_env, PTree.set dense.id.version (.Vint (ir 29300)) (PTree.set dense.id.n nv
      (PTree.set dense.id.m mv (PTree.set dense.id.wordsize (.Vint (ir 64))
        (create_undef_temps dense.fn.naugraph_check.fn_temps)))), m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, ?_, ?_, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
    · simp (config := {decide := true}) only [temps_gso, temps_gss]
    · simp (config := {decide := true}) only [temps_gss]
  · rintro args m₀ rfl
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, hw, hv, rfl⟩
    rw [dense.fn.naugraph_check.fn_body_eq, naugraph_check_eq]
    simp only [naugraph_checkBody]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, tv, hw, typeof, cop]
    rw [show Lib.Integers.Int.repr (zOfInt 64) = ir 64 from rfl,
      ir_eq (a := 64) (b := 64) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
    simp only [decide_true, Bool.not_true, Val.of_bool, Bool.false_eq_true, ite_false, cop]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, tv, hv, typeof, cop]
    rw [show Lib.Integers.Int.repr (zOfInt 29300) = ir 29300 from rfl,
      show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl, ir_add,
      ir_lt (a := 29300) (b := 29300 + 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
    simp only [show decide ((29300 : Int) < 29300 + 0) = false from rfl, Val.of_bool,
      Bool.false_eq_true, ite_false, cop]
    apply wp_skip
    exact ⟨m, Nextelement.free_empty m, rfl, rfl⟩

end NautyVerified.Proofs.Top
