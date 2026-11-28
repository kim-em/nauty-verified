"""Writes NautyVerified/Program/Env.lean (class NautyEnv, NautyEnv.dense, env_ne)
from the field list in entries.py: `python3 scripts/env/genenv.py`."""
import os
ROOT=os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),"..",".."))
import sys; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from entries import ENTRIES
E=ENTRIES
NS={"P":"Block","S":"Search.Block","T":"Top.Block"}
FNS={"P":"Program.","S":"Search.","T":"Top."}
def funct(f,kind,fn,b):
    if kind=="fn": return "some (.Internal dense.fn.%s)"%(fn if fn.startswith("«") else fn)
    if kind=="malloc": return "some (.External .EF_malloc [tulong] (tptr .Tvoid) Common.AST.cc_default)"
    if kind=="free": return "some (.External .EF_free [tptr .Tvoid] .Tvoid Common.AST.cc_default)"
out=[]
w=out.append
w("""import NautyVerified.Proofs.Alloc.Blocks
import NautyVerified.Proofs.Search.Blocks

/-!
# The globals the shared proofs use, for any linked program

`NautyEnv ge`: the block of every global and function of `nauty.c`, `nautil.c`
and the allocator that the proofs of those files mention, with
`Genv.find_symbol` of its identifier (the identifiers are `dense.id.*` in every
program linked extending `dense`), `Genv.find_funct_ptr` of each function block
(the bodies are `dense.fn.*`, the same Clight in the sparse program by
`Source/Shared.lean`), the variable information of each variable block (equal
to the dense program's, so the initial-memory facts transfer), and the
pairwise distinctness of all of them (for `sep_ne`).

Proofs about these functions take `[E : NautyEnv ge]` and write `E.x` for the
block of `x`. The global environment is an `outParam`, so a specification that
mentions only `E.x` still determines `ge`. `NautyEnv.dense` is the dense
program's instance, made of the kernel-checked facts in `Program/Dense.lean`,
`Proofs/Alloc/Blocks.lean` and `Proofs/Search/Blocks.lean`.
-/

namespace NautyVerified.Program

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open NautyVerified.Source NautyVerified.Proofs

/-- The blocks of the shared globals and functions in `ge`, with their facts. -/
class NautyEnv (ge : outParam genv) where""")
for f,ns,k,kind,fn in E: w("  %s : block"%f)
for f,ns,k,kind,fn in E:
    w("  find_%s : Genv.find_symbol ge.genv_genv dense.id.%s = some %s"%(f,k,f))
for f,ns,k,kind,fn in E:
    if kind!="var":
        w("  funct_%s : Genv.find_funct_ptr ge.genv_genv %s =\n    %s"%(f,f,funct(f,kind,fn,f)))
for f,ns,k,kind,fn in E:
    if kind=="var":
        w("  var_%s : Genv.find_var_info ge.genv_genv %s =\n    Genv.find_var_info Program.ge.genv_genv %s.%s"%(f,f,NS[ns],f))
lst=", ".join(f for f,*_ in E)
w("  /-- The blocks are pairwise distinct. -/")
w("  distinct : List.Pairwise (· ≠ ·)\n    [%s]"%lst)
w("""
namespace NautyEnv

variable {ge : genv} (E : NautyEnv ge)

/-- `permset`'s block, under the name the search proofs use. -/
abbrev permsetFn : block := E.permset

theorem find_permsetFn : Genv.find_symbol ge.genv_genv dense.id.permset = some E.permsetFn :=
  E.find_permset

theorem funct_permsetFn :
    Genv.find_funct_ptr ge.genv_genv E.permsetFn = some (.Internal dense.fn.permset) :=
  E.funct_permset

theorem ne_of_pairwise {l : List block} (h : l.Pairwise (· ≠ ·)) (i j : Nat) (hij : i < j)
    (hj : j < l.length) : l[i]'(Nat.lt_trans hij hj) ≠ l[j] := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons a l ih =>
    rw [List.pairwise_cons] at h
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => exact h.1 _ (List.getElem_mem _)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact ih h.2 i j (by omega) (by simpa using hj)

/-- Every block of `E`, in the order of `distinct`. -/
def blocks : List block :=
  [%s]

end NautyEnv

open Lean Meta in
/-- The entries of a list literal, after unfolding. -/
partial def listEntriesD (e : Expr) : MetaM (Array Expr) := do
  let e ← whnfD e
  match e.getAppFnArgs with
  | (``List.cons, #[_, x, rest]) => return #[x] ++ (← listEntriesD rest)
  | _ => return #[]

open Lean Meta Elab Tactic in
/-- `env_ne`: closes `a ≠ b` for two distinct blocks of a `NautyEnv` (`E.x ≠ E.y`),
from `NautyEnv.distinct`. -/
elab "env_ne" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (_, a, b) := (← whnfR ty).not?.bind (·.eq?) |>.orElse fun _ =>
      (ty.app3? ``Ne).map fun (α, a, b) => (α, a, b)
    | throwError "env_ne: goal is not a disequality"
  let instOf (x : Expr) : MetaM (Option Expr) := do
    let x ← instantiateMVars x
    let fn := x.getAppFn
    let args := x.getAppArgs
    if let .const n _ := fn then
      if (`NautyVerified.Program.NautyEnv).isPrefixOf n && args.size == 2 then
        return some args[1]!
    return none
  let some inst ← (do if let some i ← instOf a then pure (some i) else instOf b)
    | throwError "env_ne: neither side is a block of a NautyEnv"
  let dist ← mkAppOptM ``NautyEnv.distinct #[none, inst]
  let dT ← whnf (← inferType dist)
  let l := dT.appArg!
  let es ← listEntriesD l
  let idx (x : Expr) : MetaM (Option Nat) := do
    for i in [0:es.size] do
      if ← withReducible (isDefEq es[i]! x) then return some i
    return none
  let some i ← idx a | throwError "env_ne: {a} is not a block of the environment"
  let some j ← idx b | throwError "env_ne: {b} is not a block of the environment"
  let distStx ← Term.exprToSyntax dist
  if i < j then
    evalTactic (← `(tactic| exact NautyVerified.Program.NautyEnv.ne_of_pairwise $distStx
      $(Syntax.mkNumLit (toString i)) $(Syntax.mkNumLit (toString j)) (by decide) (by simp)))
  else if j < i then
    evalTactic (← `(tactic| exact Ne.symm (NautyVerified.Program.NautyEnv.ne_of_pairwise $distStx
      $(Syntax.mkNumLit (toString j)) $(Syntax.mkNumLit (toString i)) (by decide) (by simp))))
  else throwError "env_ne: both sides are the same block"

kernel_rfl dense_distinct : decide (List.Pairwise (· ≠ ·)
    [%s]) = true

/-- The dense program's blocks (reducible, so `E.x` unfolds to `Block.x` at
reducible transparency). -/
@[reducible] instance NautyEnv.dense : NautyEnv ge where""" % (", ".join("E."+f for f,*_ in E), ", ".join(NS[ns]+"."+f for f,ns,*_ in E)))
for f,ns,k,kind,fn in E: w("  %s := %s.%s"%(f,NS[ns],f))
for f,ns,k,kind,fn in E: w("  find_%s := %sfind_%s"%(f,FNS[ns],f))
for f,ns,k,kind,fn in E:
    if kind!="var": w("  funct_%s := %sfunct_%s"%(f,FNS[ns],f))
for f,ns,k,kind,fn in E:
    if kind=="var": w("  var_%s := rfl"%f)
w("  distinct := of_decide_eq_true dense_distinct")
w("\n/-! The dense instance's blocks are the dense `Block` constants. -/\n")
for f,ns,k,kind,fn in E:
    w("@[simp] theorem NautyEnv.dense_%s : (NautyEnv.%s : block) = %s.%s := rfl"%(f,f,NS[ns],f))
w("\nend NautyVerified.Program")
open(os.path.join(ROOT,"NautyVerified/Program/Env.lean"),"w").write("\n".join(out)+"\n")
