import NautyVerified.Source.Unit

/-!
# Renaming identifiers in a CompCert C program

Each translation unit is read by a separate run of the frontend, which numbers
identifiers by first occurrence, so the same C name gets different numbers in
different units. Before linking, every unit is renamed into one shared
numbering by `rename σ`, where `σ` maps each identifier of the unit to the
shared number of its C name (file-local statics get a unit-qualified name; see
`NautyVerified.Source.Link`).

The frontend uses one identifier per C name, whatever the name denotes, so a
file-local static can share its identifier with a member, a tag or a local
variable of the same name. Renaming is therefore by position. Global symbol
positions (definitions, public names, `main`, address-of initialisers, and
variables not bound by the enclosing function) are mapped through `σg`; all
other identifiers (members, tags, labels, debug annotations, and the function's
own parameters and locals) through `σ`. Nothing but identifiers is touched.
-/

namespace NautyVerified.Source.Rename

open CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open Cfrontend.Ctypes Cfrontend.Csyntax Common.AST

variable (σ σg : positive → positive)

def type : Cfrontend.Ctypes.type → Cfrontend.Ctypes.type
  | .Tvoid => .Tvoid
  | .Tint sz sg a => .Tint sz sg a
  | .Tlong sg a => .Tlong sg a
  | .Tfloat sz a => .Tfloat sz a
  | .Tpointer t a => .Tpointer (type t) a
  | .Tarray t n a => .Tarray (type t) n a
  | .Tfunction args res cc => .Tfunction (types args) (type res) cc
  | .Tstruct id a => .Tstruct (σ id) a
  | .Tunion id a => .Tunion (σ id) a
where
  types : List Cfrontend.Ctypes.type → List Cfrontend.Ctypes.type
    | [] => []
    | t :: ts => type t :: types ts

def member : Cfrontend.Ctypes.member → Cfrontend.Ctypes.member
  | .Member_plain id t => .Member_plain (σ id) (type σ t)
  | .Member_bitfield id sz sg a w p => .Member_bitfield (σ id) sz sg a w p

def composite : composite_definition → composite_definition
  | .Composite id su ms a => .Composite (σ id) su ((show List _ from ms).map (member σ)) a

def externalFunction : external_function → external_function
  | .EF_debug kind text targs => .EF_debug kind (σ text) targs
  | ef => ef

section
variable (ν : positive → positive)

mutual
  /-- Rename an expression; `ν` renames variables. -/
  def expr : Cfrontend.Csyntax.expr → Cfrontend.Csyntax.expr
    | .Eval v ty => .Eval v (type σ ty)
    | .Evar x ty => .Evar (ν x) (type σ ty)
    | .Efield l f ty => .Efield (expr l) (σ f) (type σ ty)
    | .Evalof l ty => .Evalof (expr l) (type σ ty)
    | .Ederef r ty => .Ederef (expr r) (type σ ty)
    | .Eaddrof l ty => .Eaddrof (expr l) (type σ ty)
    | .Eunop op r ty => .Eunop op (expr r) (type σ ty)
    | .Ebinop op r1 r2 ty => .Ebinop op (expr r1) (expr r2) (type σ ty)
    | .Ecast r ty => .Ecast (expr r) (type σ ty)
    | .Eseqand r1 r2 ty => .Eseqand (expr r1) (expr r2) (type σ ty)
    | .Eseqor r1 r2 ty => .Eseqor (expr r1) (expr r2) (type σ ty)
    | .Econdition r1 r2 r3 ty => .Econdition (expr r1) (expr r2) (expr r3) (type σ ty)
    | .Esizeof ty' ty => .Esizeof (type σ ty') (type σ ty)
    | .Ealignof ty' ty => .Ealignof (type σ ty') (type σ ty)
    | .Eassign l r ty => .Eassign (expr l) (expr r) (type σ ty)
    | .Eassignop op l r tyres ty => .Eassignop op (expr l) (expr r) (type σ tyres) (type σ ty)
    | .Epostincr id l ty => .Epostincr id (expr l) (type σ ty)
    | .Ecomma r1 r2 ty => .Ecomma (expr r1) (expr r2) (type σ ty)
    | .Ecall r1 rargs ty => .Ecall (expr r1) (exprs rargs) (type σ ty)
    | .Ebuiltin ef tyargs rargs ty =>
        .Ebuiltin (externalFunction σ ef) (type.types σ tyargs) (exprs rargs) (type σ ty)
    | .Eloc b ofs bf ty => .Eloc b ofs bf (type σ ty)
    | .Eparen r tycast ty => .Eparen (expr r) (type σ tycast) (type σ ty)

  def exprs : Cfrontend.Csyntax.exprlist → Cfrontend.Csyntax.exprlist
    | .Enil => .Enil
    | .Econs r rl => .Econs (expr r) (exprs rl)
end

def optExpr : Option Cfrontend.Csyntax.expr → Option Cfrontend.Csyntax.expr
  | none => none
  | some e => some (expr σ ν e)

mutual
  def stmt : Cfrontend.Csyntax.statement → Cfrontend.Csyntax.statement
    | .Sskip => .Sskip
    | .Sdo r => .Sdo (expr σ ν r)
    | .Ssequence s1 s2 => .Ssequence (stmt s1) (stmt s2)
    | .Sifthenelse r s1 s2 => .Sifthenelse (expr σ ν r) (stmt s1) (stmt s2)
    | .Swhile r body => .Swhile (expr σ ν r) (stmt body)
    | .Sdowhile r body => .Sdowhile (expr σ ν r) (stmt body)
    | .Sfor init cond iter body => .Sfor (stmt init) (expr σ ν cond) (stmt iter) (stmt body)
    | .Sbreak => .Sbreak
    | .Scontinue => .Scontinue
    | .Sreturn r => .Sreturn (optExpr σ ν r)
    | .Sswitch r cases => .Sswitch (expr σ ν r) (lstmt cases)
    | .Slabel lbl body => .Slabel (σ lbl) (stmt body)
    | .Sgoto lbl => .Sgoto (σ lbl)

  def lstmt : Cfrontend.Csyntax.labeled_statements → Cfrontend.Csyntax.labeled_statements
    | .LSnil => .LSnil
    | .LScons lbl s rest => .LScons lbl (stmt s) (lstmt rest)
end

end

def binding : positive × Cfrontend.Ctypes.type → positive × Cfrontend.Ctypes.type
  | (id, t) => (σ id, type σ t)

/-- Variables bound by the function are renamed as locals, the rest as globals. -/
def function (f : Cfrontend.Csyntax.function) : Cfrontend.Csyntax.function :=
  let bound := f.fn_params.map Prod.fst ++ f.fn_vars.map Prod.fst
  { fn_return := type σ f.fn_return, fn_callconv := f.fn_callconv,
    fn_params := f.fn_params.map (binding σ), fn_vars := f.fn_vars.map (binding σ),
    fn_body := stmt σ (fun x => if bound.contains x then σ x else σg x) f.fn_body }

def fundef : Cfrontend.Ctypes.fundef Cfrontend.Csyntax.function →
    Cfrontend.Ctypes.fundef Cfrontend.Csyntax.function
  | .Internal f => .Internal (function σ σg f)
  | .External ef args res cc => .External (externalFunction σ ef) (type.types σ args) (type σ res) cc

def initData : init_data → init_data
  | .Init_addrof sym ofs => .Init_addrof (σg sym) ofs
  | d => d

def globdef : CGlobdef → CGlobdef
  | .Gfun f => .Gfun (fundef σ σg f)
  | .Gvar v => .Gvar { gvar_info := type σ v.gvar_info, gvar_init := v.gvar_init.map (initData σg),
                       gvar_readonly := v.gvar_readonly, gvar_volatile := v.gvar_volatile }

def defs (ds : List (positive × CGlobdef)) : List (positive × CGlobdef) :=
  ds.map fun (id, d) => (σg id, globdef σ σg d)

end NautyVerified.Source.Rename
