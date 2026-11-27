import CompCert4Lean.Cfrontend.Clight

/-!
# Abbreviations for writing Clight in proofs

The vocabulary `NautyVerified.Tools.printFn` prints Clight in, so that a
function body can be factored into named pieces and pinned to the generated
term by `rfl`.
-/

namespace NautyVerified.Proofs

open CompCert4Lean CompCert4Lean.Cfrontend.Ctypes CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

abbrev at0 : attr := { attr_volatile := false, attr_alignas := none }
abbrev vattr : attr := { attr_volatile := true, attr_alignas := none }
abbrev tint : type := .Tint .I32 .Signed at0
abbrev tuint : type := .Tint .I32 .Unsigned at0
abbrev tschar : type := .Tint .I8 .Signed at0
abbrev tuchar : type := .Tint .I8 .Unsigned at0
abbrev tshort : type := .Tint .I16 .Signed at0
abbrev tushort : type := .Tint .I16 .Unsigned at0
abbrev tbool : type := .Tint .IBool .Signed at0
abbrev tlong : type := .Tlong .Signed at0
abbrev tulong : type := .Tlong .Unsigned at0
abbrev tdouble : type := .Tfloat .F64 at0
abbrev tptr (t : type) : type := .Tpointer t at0
abbrev tarray (t : type) (n : Int) : type := .Tarray t (zOfInt n) at0

/-- A function type with the default calling convention. -/
abbrev tfun (args : List type) (res : type) : type := .Tfunction args res Common.AST.cc_default

/-- A literal identifier. -/
abbrev idOf (n : Nat) : Common.AST.ident := PArith.BinPos.Pos.of_nat n

/-- An `int` constant. -/
abbrev ci (z : Int) (t : type) : expr := .Econst_int (Lib.Integers.Int.repr (zOfInt z)) t
/-- A `long` constant. -/
abbrev cl (z : Int) (t : type) : expr := .Econst_long (Lib.Integers.Int64.repr (zOfInt z)) t

end NautyVerified.Proofs
