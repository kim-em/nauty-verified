import Lean

/-!
# Permutations of list literals

`perm_lit`: closes `l₁.Perm l₂` for two lists that unfold to literals with
the same entries (compared at reducible and instance transparency, so a block
`E.x` of a reducible `NautyEnv` instance matches the block it names), in any
order. The proof moves each entry of `l₁` to the front of `l₂` with
`List.perm_middle`.
-/

namespace NautyVerified.Logic

open Lean Meta Elab Tactic

/-- The entries of a list literal, after unfolding (`[a] ++ l`, definitions). -/
partial def permEntries (e : Expr) : MetaM (Array Expr) := do
  let e ← whnfD e
  match e.getAppFnArgs with
  | (``List.cons, #[_, a, rest]) => return #[a] ++ (← permEntries rest)
  | (``List.nil, _) => return #[]
  | _ => throwError "perm_lit: not a list literal: {e}"

/-- The list literal of `xs`. -/
def permList (α : Expr) (xs : Array Expr) : MetaM Expr := do
  let mut l ← mkAppOptM ``List.nil #[α]
  for x in xs.reverse do
    l ← mkAppOptM ``List.cons #[α, x, l]
  return l

/-- A proof that `xs` is a permutation of `ys`. -/
partial def permProof (α : Expr) (xs ys : Array Expr) : MetaM Expr := do
  if xs.isEmpty then
    unless ys.isEmpty do throwError "perm_lit: the second list has extra entries"
    return ← mkAppOptM ``List.Perm.nil #[α]
  let a := xs[0]!
  let mut idx : Option Nat := none
  for i in [0:ys.size] do
    if ← withReducibleAndInstances (isDefEq ys[i]! a) then
      idx := some i
      break
  let some i := idx | throwError "perm_lit: {a} is not in the second list"
  let p := ys.extract 0 i
  let q := ys.extract (i + 1) ys.size
  let rec_ ← permProof α (xs.extract 1 xs.size) (p ++ q)
  let pL ← permList α p
  let qL ← permList α q
  let h1 ← mkAppOptM ``List.Perm.cons #[α, a, none, none, rec_]
  let mid ← mkAppOptM ``List.perm_middle #[α, a, pL, qL]
  let h2 ← mkAppOptM ``List.Perm.symm #[α, none, none, mid]
  mkAppOptM ``List.Perm.trans #[α, none, none, none, h1, h2]

/-- `l₁.Perm l₂` for two list literals with the same entries. -/
elab "perm_lit" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let some (α, l₁, l₂) := ty.app3? ``List.Perm
    | throwError "perm_lit: goal is not a `List.Perm`"
  let xs ← permEntries l₁
  let ys ← permEntries l₂
  let pf ← permProof α xs ys
  let pf ← mkExpectedTypeHint pf ty
  goal.assign pf

end NautyVerified.Logic
