import NautyVerified.Source.Dense

/-!
# The linked dense program's global environment

The global environment `ge` of `dense.locals`, the blocks of the globals the
proofs use, and the functions at those blocks, each fact checked by the kernel.
-/

namespace NautyVerified.Program

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Source

/-- The global environment of the linked dense program. -/
abbrev ge : genv := globalenv dense.locals

namespace Block
def nextelement : Common.Values.block := PArith.BinPos.Pos.of_nat 13
def leftbit : Common.Values.block := PArith.BinPos.Pos.of_nat 284
end Block

kernel_rfl find_nextelement :
  Genv.find_symbol ge.genv_genv dense.id.nextelement = some Block.nextelement

kernel_rfl find_leftbit :
  Genv.find_symbol ge.genv_genv dense.id.«nautil:leftbit» = some Block.leftbit

kernel_rfl funct_nextelement :
  Genv.find_funct_ptr ge.genv_genv Block.nextelement = some (.Internal dense.fn.nextelement)

end NautyVerified.Program
