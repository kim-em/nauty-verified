import NautyVerified.Source.Rename

/-!
# Linking translation units

`c_link prog := u₁ u₂ … uₙ` links translation units already introduced by
`c_unit` into one program, the way the system linker combines their objects:

1. Every C name gets one shared identifier, numbered by first occurrence
   across the units in order. A global with `static` storage is file-local, so
   it is keyed by `unit:name` instead of `name` (nauty defines `workperm`, for
   example, as a separate static in several files). Every other name is keyed
   by itself.
2. Each unit is renamed into the shared numbering by `Rename` (`renameProgram`):
   global symbol positions use the keys above, other identifier positions the
   plain name.
3. The renamed units are linked left to right by CompCert's own
   `Ctypes.link_program` (`linkUnits`).

The command adds `prog.sigma.<unit>` and `prog.sigmaG.<unit>` (the renaming
of each unit, for identifiers in general and for global symbols),
`prog.id.<key>`, `prog.keys` (the key of each shared identifier, in order),
`prog.names` (each identifier with its key), `prog.program` with its parts,
and `prog.link_eq`:
`linkUnits [(prog.sigma.u₁, prog.sigmaG.u₁, u₁.program), …] = some prog.program`, checked by
the kernel. It then adds `prog.clight` and `prog.locals` as `c_unit` does.

`c_link prog := u₁ … uₙ extending base` numbers identifiers so that every
function `prog` shares with the earlier link `base` has the same Clight:

- every key of `base` keeps its identifier (`base.keys`);
- the other keys are numbered from `base.fresh + gap`, so they stay apart
  from the temporaries SimplExpr creates, which start at `base.fresh` in
  every function;
- `prog.fresh` is `base.fresh`.

A function's Clight depends only on its renamed `Csyntax`, the composites it
uses and the first temporary, so a unit linked into both programs gets the
same Clight in both. `prog.keys` is then omitted (the numbering has a gap).
-/

namespace NautyVerified.Source

open Lean Elab Command Meta
open CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

deriving instance ToExpr for PTree.tree'
deriving instance ToExpr for PTree.tree

instance : ToExpr (PTree.t positive) := inferInstanceAs (ToExpr (PTree.tree positive))

/-- The renaming a table describes; identifiers outside the table are unchanged. -/
def sigmaOf (t : PTree.t positive) (p : positive) : positive :=
  (PTree.get p t).getD p

/-- Rename a program, global symbols by `σg` and other identifiers by `σ`;
`none` if the renamed composites do not build. -/
def renameProgram (σ σg : positive → positive) (p : Cfrontend.Csyntax.program) :
    Option Cfrontend.Csyntax.program :=
  let types := p.prog_types.map (Rename.composite σ)
  match h : Cfrontend.Ctypes.build_composite_env types with
  | .OK env =>
      some { prog_defs := Rename.defs σ σg p.prog_defs, prog_public := p.prog_public.map σg,
             prog_main := σg p.prog_main, prog_types := types,
             prog_comp_env := env, prog_comp_env_eq := h }
  | .Error _ => none

/-- Rename and link translation units, left to right, with CompCert's C linker. -/
noncomputable def linkUnits
    (us : List (PTree.t positive × PTree.t positive × Cfrontend.Csyntax.program)) :
    Option Cfrontend.Csyntax.program :=
  match us.mapM (fun (s, sg, p) => renameProgram (sigmaOf s) (sigmaOf sg) p) with
  | none | some [] => none
  | some (p :: ps) =>
      ps.foldlM (fun acc q =>
        Cfrontend.Ctypes.link_program
          Cfrontend.Ctypes.linker_program_certificate_proof.composite_defs acc q) p

/-- A program's data; its composite environment is determined by its types. -/
def parts (p : Cfrontend.Csyntax.program) :
    List (positive × CGlobdef) × List positive × positive ×
      List Cfrontend.Ctypes.composite_definition :=
  (p.prog_defs, p.prog_public, p.prog_main, p.prog_types)

theorem eq_of_parts {p q : Cfrontend.Csyntax.program} (h : parts p = parts q) : p = q := by
  cases p with
  | mk d pub m ty env henv =>
    cases q with
    | mk d' pub' m' ty' env' henv' =>
      simp only [parts] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have : env = env' := by
        rw [henv] at henv'
        cases henv'
        rfl
      subst this
      rfl

theorem eq_some_of_parts {o : Option Cfrontend.Csyntax.program} {p : Cfrontend.Csyntax.program}
    (h : o.map parts = some (parts p)) : o = some p := by
  cases o with
  | none => cases h
  | some q =>
    simp only [Option.map_some, Option.some.injEq] at h
    rw [eq_of_parts h]

/-- `link_program` on parts, without the composite environment: a computable
twin of `linkUnits` used to compute the linked program at elaboration time.
The result is checked against `linkUnits` by the kernel. -/
def linkParts (p q : Cfrontend.Csyntax.program) :
    Option (List (positive × CGlobdef) × List positive × positive ×
      List Cfrontend.Ctypes.composite_definition) := do
  let ast ← Common.Linking.link (Cfrontend.Ctypes.program_of_program p)
    (Cfrontend.Ctypes.program_of_program q)
  let types ← Cfrontend.Ctypes.link_composite_defs p.prog_types q.prog_types
  return (ast.prog_defs, ast.prog_public, ast.prog_main, types)

/-- The program with the given parts, if its composites build. -/
def ofParts (x : List (positive × CGlobdef) × List positive × positive ×
      List Cfrontend.Ctypes.composite_definition) : Option Cfrontend.Csyntax.program :=
  match h : Cfrontend.Ctypes.build_composite_env x.2.2.2 with
  | .OK env => some { prog_defs := x.1, prog_public := x.2.1, prog_main := x.2.2.1,
                      prog_types := x.2.2.2, prog_comp_env := env, prog_comp_env_eq := h }
  | .Error _ => none

/-- The value of a constant that `toExpr` built from a list of strings. -/
partial def stringsOf (e : Expr) : Option (List String) :=
  match e.getAppFnArgs with
  | (``List.nil, _) => some []
  | (``List.cons, #[_, .lit (.strVal s), rest]) => (s :: ·) <$> stringsOf rest
  | _ => none

/-- Identifiers numbered `base.fresh + linkGap` and above are keys new to an
extending link. -/
def linkGap : Nat := 65536

syntax "c_link " ident " := " ident+ (" extending " ident)? : command

elab_rules : command
  | `(c_link $id := $units* $[extending $ext]?) => do
    let ns ← getCurrNamespace
    let base := ns ++ id.getId
    -- Shared numbering: the extended link's keys, then by first occurrence.
    let mut table : Std.HashMap String Nat := {}
    let mut keys : Array String := #[]
    let mut baseKeys : Nat := 0
    if let some ext := ext then
      let extName := ns ++ ext.getId
      let some info := (← getEnv).find? (extName ++ `keys)
        | throwError "c_link: {extName}.keys not found"
      let some ks := info.value?.bind stringsOf
        | throwError "c_link: {extName}.keys is not a list of strings"
      for k in ks do
        keys := keys.push k
        table := table.insert k keys.size
      baseKeys := keys.size
    -- The identifier of the `j`th key (from 0).
    let idOf (j : Nat) : Nat :=
      if ext.isNone || j < baseKeys then j + 1 else baseKeys + 1 + linkGap + (j - baseKeys)
    let mut sigmas : Array (PTree.t positive × PTree.t positive) := #[]
    let mut renamed : Array Cfrontend.Csyntax.program := #[]
    for u in units do
      let uname := u.getId.toString
      let f ← readUnitFile s!"c/csyntax/{uname}.json"
      let mut sigma : PTree.t positive := PTree.empty positive
      let mut sigmaG : PTree.t positive := PTree.empty positive
      for (i, str) in f.names do
        let mut js : Array Nat := #[]
        for key in [str, if f.statics.contains i then s!"{uname}:{str}" else str] do
          match table[key]? with
          | some j => js := js.push j
          | none =>
              let j := idOf keys.size
              table := table.insert key j
              keys := keys.push key
              js := js.push j
        let a := PArith.BinPos.Pos.of_nat i
        sigma := PTree.set a (PArith.BinPos.Pos.of_nat js[0]!) sigma
        sigmaG := PTree.set a (PArith.BinPos.Pos.of_nat js[1]!) sigmaG
      let some p := renameProgram (sigmaOf sigma) (sigmaOf sigmaG) f.program
        | throwError "c_link: renamed composites of {uname} do not build"
      sigmas := sigmas.push (sigma, sigmaG)
      renamed := renamed.push p
    for u in units, (sigma, sigmaG) in sigmas do
      addDef (base ++ `sigma ++ u.getId) (toTypeExpr (PTree.t positive)) (toExpr sigma)
      addDef (base ++ `sigmaG ++ u.getId) (toTypeExpr (PTree.t positive)) (toExpr sigmaG)
    let some first := renamed[0]? | throwError "c_link: no units"
    let mut acc := first
    for q in renamed[1:] do
      let some x := linkParts acc q | throwError "c_link: CompCert's linker rejects the units"
      let some p := ofParts x | throwError "c_link: linked composites do not build"
      acc := p
    let names := (keys.toList.zipIdx 0).map fun (s, j) => (idOf j, s)
    let nameOf := nameLookup names
    let fresh := PArith.BinPos.Pos.of_nat (if ext.isSome then baseKeys + 1 else keys.size + 1)
    emitNames base names
    if ext.isNone then
      addDef (base ++ `keys) (toTypeExpr (List String)) (toExpr keys.toList)
    addDef (base ++ `names) (toTypeExpr (List (Nat × String))) (toExpr names)
    emitProgram base nameOf acc fresh
    let entries ← units.mapM fun u =>
      `(($(rootIdent (base ++ `sigma ++ u.getId)), $(rootIdent (base ++ `sigmaG ++ u.getId)),
          $(rootIdent (ns ++ u.getId ++ `program))))
    let partsName := base ++ `link_parts
    addKernelRfl partsName (← elabType (← `(
      (linkUnits [$entries,*]).map parts = some (parts $(rootIdent (base ++ `program))))))
    elabCommand (← `(command|
      theorem $(rootIdent (base ++ `link_eq)) :
          linkUnits [$entries,*] = some $(rootIdent (base ++ `program)) :=
        eq_some_of_parts $(rootIdent partsName)))
    emitPasses base nameOf acc fresh

end NautyVerified.Source
