import CompCert4Lean.Prototype.Main
import NautyVerified.Source.ToExpr

/-!
# C translation units as Lean definitions

`c_unit foo from "c/csyntax/foo.json"` reads the CompCert frontend's
`Csyntax` interchange file for one translation unit, decodes it with
CompCert4Lean's own decoder (`Prototype.decodeSource`, the one the compiler
driver runs), and adds:

* `foo.id.<c_name> : positive`, the frontend's identifier for each C name;
* `foo.program.<c_name>` for each global definition and `foo.defs`, `foo.pub`,
  `foo.main`, `foo.types`, `foo.fresh`;
* `foo.program : Csyntax.program`, whose composite environment is computed by
  `build_composite_env` and checked by the kernel.

`emitPasses` (used by `c_unit` and by `c_link`) then adds:

* `foo.clight` (and `foo.clight.<c_name>`), the output of CompCert4Lean's
  `SimplExpr.transl_program`, with `foo.clight_eq` stating so;
* `foo.locals` (and `foo.locals.<c_name>`), the output of
  `SimplLocals.transf_program` on `foo.clight` under any configuration with
  debug information off, with `foo.locals_eq` stating so.

The definitions are closed constructor terms produced by meta code, which is
not trusted: the equations are checked by the kernel evaluating
CompCert4Lean's own passes. Trusted are the frontend that wrote the file and
the decoder, both of which the compiler driver also runs.
-/

namespace NautyVerified.Source

open Lean Elab Command Meta
open CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

abbrev CGlobdef :=
  Common.AST.globdef (Cfrontend.Ctypes.fundef Cfrontend.Csyntax.function) Cfrontend.Ctypes.type

abbrev ClightGlobdef :=
  Common.AST.globdef (Cfrontend.Ctypes.fundef Cfrontend.Clight.function) Cfrontend.Ctypes.type

/-- Whether a compiler result is a success. -/
def resOK {α : Type} : Common.Errors.res α → Bool
  | .OK _ => true
  | .Error _ => false

/-- A program from its parts, given that the composite environment builds. -/
def programOf (defs : List (positive × CGlobdef)) (pub : List positive) (main : positive)
    (types : List Cfrontend.Ctypes.composite_definition)
    (h : resOK (Cfrontend.Ctypes.build_composite_env types) = true) :
    Cfrontend.Csyntax.program :=
  match e : Cfrontend.Ctypes.build_composite_env types, h with
  | .OK env, _ =>
      { prog_defs := defs, prog_public := pub, prog_main := main,
        prog_types := types, prog_comp_env := env, prog_comp_env_eq := e }
  | .Error _, h => nomatch h

/-- The Clight program with `p`'s public names, main and composites and the given
definitions; this is the shape `SimplExpr.transl_program` produces. -/
def clightOf (p : Cfrontend.Csyntax.program) (defs : List (positive × ClightGlobdef)) :
    Cfrontend.Clight.program :=
  { prog_defs := defs, prog_public := p.prog_public, prog_main := p.prog_main,
    prog_types := p.prog_types, prog_comp_env := p.prog_comp_env,
    prog_comp_env_eq := p.prog_comp_env_eq }

/-- The identifier context the driver gives SimplExpr. -/
def freshContext (fresh : positive) : Cfrontend.SimplExpr.FreshIdentContext :=
  ⟨.sequential fresh⟩

def addDef (name : Name) (type value : Expr) : CommandElabM Unit :=
  liftCoreM <| addAndCompile <| .defnDecl
    { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }

/-- Add `name : type`, where `type` is `∀ xs, lhs = rhs`, proved by `Eq.refl lhs`
and checked by the kernel alone. (Elaborator `rfl` would unfold the compiler
passes with `whnfR` and exhaust its recursion budget.) -/
def addKernelRfl (name : Name) (type : Expr) : CommandElabM Unit := do
  let value ← liftTermElabM <| forallTelescope type fun xs body => do
    let some (α, lhs, _) := body.eq? | throwError "addKernelRfl: not an equation"
    let u ← getLevel α
    mkLambdaFVars xs (mkApp2 (mkConst ``_root_.Eq.refl [u]) α lhs)
  liftCoreM <| addDecl <| .thmDecl { name, levelParams := [], type, value }

def elabType (stx : Term) : CommandElabM Expr := liftTermElabM do
  let e ← Term.elabType stx
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- An identifier term for a fully qualified constant. -/
def rootIdent (n : Name) : Ident := mkIdent (`_root_ ++ n)

/-- Add `base ++ sub ++ <c_name>` for each definition and the list `base ++ listName`
of `(identifier, definition)` pairs referring to them. -/
def emitDefs {α : Type} [ToExpr α] (base sub listName : Name) (nameOf : positive → Name)
    (defs : List (positive × α)) : CommandElabM Unit := do
  let ty := toTypeExpr α
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (toTypeExpr positive) ty
  let mut entries : Array Expr := #[]
  for (ident, d) in defs do
    let n := base ++ sub ++ nameOf ident
    addDef n ty (toExpr d)
    entries := entries.push (mkApp4 (mkConst ``Prod.mk [0, 0]) (toTypeExpr positive) ty
      (toExpr ident) (mkConst n))
  addDef (base ++ listName) (mkApp (mkConst ``List [0]) pairTy)
    (entries.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) pairTy e acc)
      (mkApp (mkConst ``List.nil [0]) pairTy))

/-- Add `base.id.<name>` for each identifier name. -/
def emitNames (base : Name) (names : List (Nat × String)) : CommandElabM Unit := do
  for (i, str) in names do
    addDef (base ++ `id ++ Name.mkSimple str) (toTypeExpr positive)
      (toExpr (PArith.BinPos.Pos.of_nat i))

def nameLookup (names : List (Nat × String)) (p : positive) : Name :=
  match names.lookup (posToNat p) with
  | some s => Name.mkSimple s
  | none => Name.mkSimple s!"_{posToNat p}"

/-- Add `base.program` and its parts. -/
def emitProgram (base : Name) (nameOf : positive → Name) (p : Cfrontend.Csyntax.program)
    (fresh : positive) : CommandElabM Unit := do
  emitDefs base `program `defs nameOf p.prog_defs
  addDef (base ++ `pub) (toTypeExpr (List positive)) (toExpr p.prog_public)
  addDef (base ++ `main) (toTypeExpr positive) (toExpr p.prog_main)
  addDef (base ++ `types) (toTypeExpr (List Cfrontend.Ctypes.composite_definition))
    (toExpr p.prog_types)
  addDef (base ++ `fresh) (toTypeExpr positive) (toExpr fresh)
  let mk (n : Name) : Ident := rootIdent (base ++ n)
  elabCommand (← `(command|
    def $(mk `program) : Cfrontend.Csyntax.program :=
      programOf $(mk `defs) $(mk `pub) $(mk `main) $(mk `types) (by decide)))

/-- Add `base.clight` and `base.locals` with their kernel-checked equations. -/
def emitPasses (base : Name) (nameOf : positive → Name) (p : Cfrontend.Csyntax.program)
    (fresh : positive) : CommandElabM Unit := do
  let mk (n : Name) : Ident := rootIdent (base ++ n)
  let clight ← match Cfrontend.SimplExpr.transl_program (freshContext fresh) p with
    | .OK c => pure c
    | .Error _ => throwError "{base}: SimplExpr failed"
  emitDefs base `clight `clightDefs nameOf clight.prog_defs
  elabCommand (← `(command|
    def $(mk `clight) : Cfrontend.Clight.program := clightOf $(mk `program) $(mk `clightDefs)))
  addKernelRfl (base ++ `clight_eq) (← elabType (← `(
    Cfrontend.SimplExpr.transl_program (freshContext $(mk `fresh)) $(mk `program) =
      .OK $(mk `clight))))
  -- SimplLocals reads the configuration only through `Compopts.debug`.
  let locals ← match Cfrontend.SimplLocals.transf_program Prototype.cfg clight with
    | .OK c => pure c
    | .Error _ => throwError "{base}: SimplLocals failed"
  emitDefs base `locals `localsDefs nameOf locals.prog_defs
  elabCommand (← `(command|
    def $(mk `locals) : Cfrontend.Clight.program := clightOf $(mk `program) $(mk `localsDefs)))
  addKernelRfl (base ++ `locals_eq) (← elabType (← `(
    ∀ (o : Config.CompilerOptions) (abi : Config.X86_64ABI) (r : Config.RelocationContext),
      Cfrontend.SimplLocals.transf_program
        { options := { o with debug := false }, x86_64ABI := abi, relocation := r }
        $(mk `clight) = .OK $(mk `locals))))

/-- The parts of an interchange file that `c_unit` uses. -/
structure UnitFile where
  program : Cfrontend.Csyntax.program
  fresh : positive
  names : List (Nat × String)
  /-- Identifiers of globals with `static` storage. -/
  statics : List Nat

def readUnitFile (path : System.FilePath) : CommandElabM UnitFile := do
  let text ← IO.FS.readFile path
  let json ← match Json.parse text with
    | .ok json => pure json
    | .error e => throwError "{path}: invalid JSON: {e}"
  let (program, ctx) ← match Prototype.decodeSource json with
    | .ok r => pure r
    | .error e => throwError "{path}: {e}"
  let parsed : Except String (List (Nat × String) × List Nat) := do
    let names ← (← json.getObjVal? "names").getArr?
    let names ← names.toList.mapM fun entry => do
      let pair ← entry.getArr?
      unless pair.size == 2 do throw "bad name entry"
      return (posToNat (← Prototype.dec_pos 0 pair[0]!), ← pair[1]!.getStr?)
    let symbols ← (← (← json.getObjVal? "configuration").getObjVal? "symbols").getArr?
    let statics ← symbols.toList.filterMapM fun entry => do
      let pair ← entry.getArr?
      unless pair.size == 2 do throw "bad symbol entry"
      let storage ← (← pair[1]!.getObjVal? "storage").getStr?
      if storage == "static" then
        return some (posToNat (← Prototype.dec_pos 0 pair[0]!))
      else return none
    return (names, statics)
  let (names, statics) ← match parsed with
    | .ok r => pure r
    | .error e => throwError "{path}: {e}"
  return { program, fresh := Cfrontend.SimplExpr.first_unused_ident ctx (), names, statics }

elab "c_unit " id:ident " from " path:str : command => do
  let base := (← getCurrNamespace) ++ id.getId
  let u ← readUnitFile path.getString
  let nameOf := nameLookup u.names
  emitNames base u.names
  emitProgram base nameOf u.program u.fresh
  emitPasses base nameOf u.program u.fresh

end NautyVerified.Source
