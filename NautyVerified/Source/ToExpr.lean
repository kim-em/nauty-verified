import CompCert4Lean.Cfrontend.Csyntax
import CompCert4Lean.Cfrontend.Clight
import CompCert4Lean.Lib.Floats

/-!
# Reflecting CompCert C syntax into Lean terms

`ToExpr` instances for the CompCert4Lean types that occur in a `Csyntax`
program. Machine integers and floats carry range proofs, so they are rebuilt
from their canonical integer contents through `Int.repr`, `Int64.repr`,
`Ptrofs.repr` and `Float.of_bits`; everything else is the derived constructor term.
-/

namespace NautyVerified.Source

open Lean
open CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

deriving instance ToExpr for Numbers.BinNums.positive
deriving instance ToExpr for Numbers.BinNums.Z
deriving instance ToExpr for Numbers.BinNums.N

instance : ToExpr Common.AST.ident := inferInstanceAs (ToExpr positive)
instance : ToExpr Common.Values.block := inferInstanceAs (ToExpr positive)
deriving instance ToExpr for
  Foundation.RocqString.Rocq.Coq.Strings.String.string

/- One instance per word type, so that each literal has exactly the type its
position expects (`Int.int`, `Int64.int`, `Ptrofs.int` are `Word` of three
distinct `wordsize` constants, equal only after unfolding). -/
instance : ToExpr Lib.Integers.int where
  toTypeExpr := mkConst ``Lib.Integers.int
  toExpr w := mkApp (mkConst ``Lib.Integers.Int.repr) (toExpr w.intval)

instance : ToExpr Lib.Integers.int64 where
  toTypeExpr := mkConst ``Lib.Integers.int64
  toExpr w := mkApp (mkConst ``Lib.Integers.Int64.repr) (toExpr w.intval)

instance : ToExpr Lib.Integers.ptrofs where
  toTypeExpr := mkConst ``Lib.Integers.ptrofs
  toExpr w := mkApp (mkConst ``Lib.Integers.Ptrofs.repr) (toExpr w.intval)

instance : ToExpr Lib.Floats.float where
  toTypeExpr := mkConst ``Lib.Floats.float
  toExpr f := mkApp (mkConst ``Lib.Floats.Float.of_bits)
    (mkApp (mkConst ``Lib.Integers.Int64.repr) (toExpr (Lib.Floats.Float.to_bits f).intval))

instance : ToExpr Lib.Floats.float32 where
  toTypeExpr := mkConst ``Lib.Floats.float32
  toExpr f := mkApp (mkConst ``Lib.Floats.Float32.of_bits)
    (mkApp (mkConst ``Lib.Integers.Int.repr) (toExpr (Lib.Floats.Float32.to_bits f).intval))

deriving instance ToExpr for Common.AST.typ
deriving instance ToExpr for Common.AST.xtype
deriving instance ToExpr for Common.AST.calling_convention
deriving instance ToExpr for Common.AST.signature
deriving instance ToExpr for Common.AST.memory_chunk
deriving instance ToExpr for Common.AST.init_data
deriving instance ToExpr for Common.AST.external_function
deriving instance ToExpr for Cfrontend.Ctypes.signedness
deriving instance ToExpr for Cfrontend.Ctypes.intsize
deriving instance ToExpr for Cfrontend.Ctypes.floatsize
deriving instance ToExpr for Cfrontend.Ctypes.attr
deriving instance ToExpr for Cfrontend.Ctypes.type
deriving instance ToExpr for Cfrontend.Ctypes.struct_or_union
deriving instance ToExpr for Cfrontend.Ctypes.member
instance : ToExpr Cfrontend.Ctypes.members :=
  inferInstanceAs (ToExpr (List Cfrontend.Ctypes.member))
deriving instance ToExpr for Cfrontend.Ctypes.composite_definition
deriving instance ToExpr for Cfrontend.Ctypes.bitfield
deriving instance ToExpr for Cfrontend.Cop.unary_operation
deriving instance ToExpr for Cfrontend.Cop.binary_operation
deriving instance ToExpr for Cfrontend.Cop.incr_or_decr
deriving instance ToExpr for Common.Values.val
deriving instance ToExpr for Cfrontend.Csyntax.expr
instance : ToExpr Cfrontend.Csyntax.label := inferInstanceAs (ToExpr positive)
deriving instance ToExpr for Cfrontend.Csyntax.statement
deriving instance ToExpr for Cfrontend.Csyntax.function
deriving instance ToExpr for Cfrontend.Ctypes.fundef
deriving instance ToExpr for Common.AST.globvar
deriving instance ToExpr for Common.AST.globdef

end NautyVerified.Source

namespace NautyVerified.Source

open Lean CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

instance : ToExpr Cfrontend.Clight.label := inferInstanceAs (ToExpr positive)
deriving instance ToExpr for Cfrontend.Clight.expr
deriving instance ToExpr for Cfrontend.Clight.statement
deriving instance ToExpr for Cfrontend.Clight.function

end NautyVerified.Source
