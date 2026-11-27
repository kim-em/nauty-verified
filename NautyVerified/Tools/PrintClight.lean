import NautyVerified.Source.Dense

/-!
# Printing Clight as Lean source

`printFn names f` renders a Clight function body as a Lean term over the
abbreviations of `NautyVerified.Proofs.Syntax` (`tint`, `tulong`, `tptr`,
`ci`, `cl`, `idOf`), with identifiers named by `names`. Proofs about a
function factor its body into named pieces this way and pin them to the
generated term by `rfl`. A development tool; nothing depends on it.
-/

namespace NautyVerified.Tools

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop CompCert4Lean.Foundation.Numbers.Rocq.Coq

variable (nm : Nat → Option String)

def idS (p : positive) : String :=
  match nm (posToNat p) with
  | some s => s!"id.«{s}»"
  | none => s!"(idOf {posToNat p})"

def attrDefault (a : attr) : Bool := !a.attr_volatile && a.attr_alignas.isNone

partial def tyS : type → String
  | .Tvoid => "Tvoid"
  | .Tint .I32 .Signed a => if attrDefault a then "tint" else "(Tint .I32 .Signed vattr)"
  | .Tint .I32 .Unsigned a => if attrDefault a then "tuint" else "(Tint .I32 .Unsigned vattr)"
  | .Tint .I8 .Signed _ => "tschar" | .Tint .I8 .Unsigned _ => "tuchar"
  | .Tint .I16 .Signed _ => "tshort" | .Tint .I16 .Unsigned _ => "tushort"
  | .Tint .IBool .Signed a => if attrDefault a then "tbool" else "(Tint .IBool .Signed vattr)"
  | .Tint .IBool .Unsigned _ => "(Tint .IBool .Unsigned at0)"
  | .Tlong .Signed _ => "tlong" | .Tlong .Unsigned _ => "tulong"
  | .Tfloat .F64 _ => "tdouble" | .Tfloat .F32 _ => "tfloat"
  | .Tpointer t _ => s!"(tptr {tyS t})"
  | .Tarray t n _ => s!"(tarray {tyS t} {intOfZ n})"
  | .Tfunction args r _ => s!"(tfun [{", ".intercalate (args.map tyS)}] {tyS r})"
  | .Tstruct i _ => s!"(Tstruct {idS nm i} noattr)"
  | .Tunion i _ => s!"(Tunion {idS nm i} noattr)"

def binS : binary_operation → String
  | .Oadd => ".Oadd" | .Osub => ".Osub" | .Omul => ".Omul" | .Odiv => ".Odiv" | .Omod => ".Omod"
  | .Oand => ".Oand" | .Oor => ".Oor" | .Oxor => ".Oxor" | .Oshl => ".Oshl" | .Oshr => ".Oshr"
  | .Oeq => ".Oeq" | .One => ".One" | .Olt => ".Olt" | .Ogt => ".Ogt" | .Ole => ".Ole" | .Oge => ".Oge"

def unS : unary_operation → String
  | .Onotbool => ".Onotbool" | .Onotint => ".Onotint" | .Oneg => ".Oneg" | .Oabsfloat => ".Oabsfloat"

partial def exS : expr → String
  | .Econst_int i t => s!"(ci {intOfZ i.intval} {tyS nm t})"
  | .Econst_long i t => s!"(cl {intOfZ i.intval} {tyS nm t})"
  | .Econst_float f t =>
      s!"(.Econst_float (CompCert4Lean.Lib.Floats.Float.of_bits (NautyVerified.Word.lr {intOfZ (Lib.Integers.Int64.unsigned (CompCert4Lean.Lib.Floats.Float.to_bits f))})) {tyS nm t})"
  | .Econst_single _ _ => "(csingle)"
  | .Evar i t => s!"(.Evar {idS nm i} {tyS nm t})"
  | .Etempvar i t => s!"(.Etempvar {idS nm i} {tyS nm t})"
  | .Ederef a t => s!"(.Ederef {exS a} {tyS nm t})"
  | .Eaddrof a t => s!"(.Eaddrof {exS a} {tyS nm t})"
  | .Eunop op a t => s!"(.Eunop {unS op} {exS a} {tyS nm t})"
  | .Ebinop op a b t => s!"(.Ebinop {binS op} {exS a} {exS b} {tyS nm t})"
  | .Ecast a t => s!"(.Ecast {exS a} {tyS nm t})"
  | .Efield a i t => s!"(.Efield {exS a} {idS nm i} {tyS nm t})"
  | .Esizeof t t' => s!"(.Esizeof {tyS nm t} {tyS nm t'})"
  | .Ealignof t t' => s!"(.Ealignof {tyS nm t} {tyS nm t'})"

def chunkS : Common.AST.memory_chunk → String
  | .Mint8signed => ".Mint8signed" | .Mint8unsigned => ".Mint8unsigned"
  | .Mint16signed => ".Mint16signed" | .Mint16unsigned => ".Mint16unsigned"
  | .Mint32 => ".Mint32" | .Mint64 => ".Mint64" | .Mfloat32 => ".Mfloat32"
  | .Mfloat64 => ".Mfloat64" | .Many32 => ".Many32" | .Many64 => ".Many64" | .Mbool => ".Mbool"

def efS : Common.AST.external_function → String
  | .EF_vload c => s!"(.EF_vload {chunkS c})"
  | .EF_vstore c => s!"(.EF_vstore {chunkS c})"
  | _ => "_"

def ind (n : Nat) : String := "".pushn ' ' n

mutual
partial def stS (d : Nat) : statement → String
  | .Sskip => ".Sskip"
  | .Sassign a b => s!"(.Sassign {exS nm a} {exS nm b})"
  | .Sset i a => s!"(.Sset {idS nm i} {exS nm a})"
  | .Scall r a l =>
      let r := match r with | some i => s!"(some {idS nm i})" | none => "none"
      s!"(.Scall {r} {exS nm a} [{", ".intercalate (l.map (exS nm))}])"
  | .Sbuiltin r ef tl l =>
      let r := match r with | some i => s!"(some {idS nm i})" | none => "none"
      s!"(.Sbuiltin {r} {efS ef} [{", ".intercalate (tl.map (tyS nm))}] [{", ".intercalate (l.map (exS nm))}])"
  | .Ssequence a b => s!"(.Ssequence\n{ind (d+2)}{stS (d+2) a}\n{ind (d+2)}{stS (d+2) b})"
  | .Sifthenelse c a b =>
      s!"(.Sifthenelse {exS nm c}\n{ind (d+2)}{stS (d+2) a}\n{ind (d+2)}{stS (d+2) b})"
  | .Sloop a b => s!"(.Sloop\n{ind (d+2)}{stS (d+2) a}\n{ind (d+2)}{stS (d+2) b})"
  | .Sbreak => ".Sbreak"
  | .Scontinue => ".Scontinue"
  | .Sreturn none => "(.Sreturn none)"
  | .Sreturn (some a) => s!"(.Sreturn (some {exS nm a}))"
  | .Sswitch a sl => s!"(.Sswitch {exS nm a}\n{ind (d+2)}{lsS (d+2) sl})"
  | .Slabel _ s => s!"(.Slabel _ {stS d s})"
  | .Sgoto _ => "(.Sgoto _)"

partial def lsS (d : Nat) : labeled_statements → String
  | .LSnil => ".LSnil"
  | .LScons c st rest =>
      let c := match c with
        | some z => s!"(some (zOfInt {CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z}))"
        | none => "none"
      s!"(.LScons {c}\n{ind (d+2)}{stS (d+2) st}\n{ind (d+2)}{lsS (d+2) rest})"
end

def names : Nat → Option String := fun i =>
  NautyVerified.Source.dense.keys[i - 1]?

end NautyVerified.Tools
