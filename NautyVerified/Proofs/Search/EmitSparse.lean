import NautyVerified.Proofs.Search.Emit
import NautyVerified.Program.Sparse

/-!
# The sparse harness's automorphism callback

`sparse_main.c`'s `emit_generator` has the Clight of `dense_main.c`'s, and the
sparse program links `nv_write` as the same external call, so
`automCb_emitAt` gives `AutomCb` for its block in `sparseGe`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.AST CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified NautyVerified.Program NautyVerified.Source

namespace SparseBlock
/-- `sparse_main.c`'s `emit_generator`. -/
def emitGenerator : Common.Values.block := PArith.BinPos.Pos.of_nat 215
/-- The harness's `nv_write`. -/
def nvWrite : Common.Values.block := PArith.BinPos.Pos.of_nat 1
end SparseBlock

kernel_rfl sparse_find_nvWrite :
  Genv.find_symbol sparseGe.genv_genv dense.id.nv_write = some SparseBlock.nvWrite
kernel_rfl sparse_funct_nvWrite : Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.nvWrite =
  some (.External (.EF_external Statement.nameWrite Statement.sigWrite) [tlong] .Tvoid cc_default)
kernel_rfl sparse_find_emitGenerator :
  Genv.find_symbol sparseGe.genv_genv sparse.id.«sparse_main:emit_generator» =
    some SparseBlock.emitGenerator
kernel_rfl sparse_funct_emitGenerator :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.emitGenerator =
    some (.Internal dense.fn.«dense_main:emit_generator»)

attribute [local instance] NautyEnv.sparse in
theorem automCb_emit_sparse : AutomCb Statement.xi SparseBlock.emitGenerator :=
  automCb_emitAt sparse_find_nvWrite sparse_funct_nvWrite sparse_funct_emitGenerator

end NautyVerified.Proofs.Search
