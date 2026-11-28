import NautyVerified.Proofs.Sparse.Blocks

/-!
# The blocks `refine_sg` uses

The blocks of the nausparse.c globals and functions `refine_sg` reaches
besides those of `Proofs/Sparse/Blocks.lean`: the work arrays `work2`,
`work3`, `work4` with their capacities, the second mark array `vmark2`
with its capacity and stamp, `preparemarks2`, nausparse.c's `bit` table,
`distvals`, `sortints`, `sortindirect` and `refine_sg` itself, each fact
checked by the kernel.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Source

namespace Block
def work2 : Common.Values.block := PArith.BinPos.Pos.of_nat 262
def work2Sz : Common.Values.block := PArith.BinPos.Pos.of_nat 339
def work3 : Common.Values.block := PArith.BinPos.Pos.of_nat 210
def work3Sz : Common.Values.block := PArith.BinPos.Pos.of_nat 289
def work4 : Common.Values.block := PArith.BinPos.Pos.of_nat 252
def work4Sz : Common.Values.block := PArith.BinPos.Pos.of_nat 333
def vmark2 : Common.Values.block := PArith.BinPos.Pos.of_nat 240
def vmark2Sz : Common.Values.block := PArith.BinPos.Pos.of_nat 322
def vmark2Val : Common.Values.block := PArith.BinPos.Pos.of_nat 352
def preparemarks2 : Common.Values.block := PArith.BinPos.Pos.of_nat 147
def bit : Common.Values.block := PArith.BinPos.Pos.of_nat 204
def distvals : Common.Values.block := PArith.BinPos.Pos.of_nat 307
def sortints : Common.Values.block := PArith.BinPos.Pos.of_nat 296
def sortindirect : Common.Values.block := PArith.BinPos.Pos.of_nat 216
def refine : Common.Values.block := PArith.BinPos.Pos.of_nat 90
end Block

kernel_rfl find_work2 :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work2» = some Block.work2
kernel_rfl find_work2Sz :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work2_sz» = some Block.work2Sz
kernel_rfl find_work3 :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work3» = some Block.work3
kernel_rfl find_work3Sz :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work3_sz» = some Block.work3Sz
kernel_rfl find_work4 :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work4» = some Block.work4
kernel_rfl find_work4Sz :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work4_sz» = some Block.work4Sz
kernel_rfl find_vmark2 :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:vmark2» = some Block.vmark2
kernel_rfl find_vmark2Sz :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:vmark2_sz» = some Block.vmark2Sz
kernel_rfl find_vmark2Val :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:vmark2_val» = some Block.vmark2Val
kernel_rfl find_preparemarks2 :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:preparemarks2» = some Block.preparemarks2
kernel_rfl find_bit : Genv.find_symbol sge.genv_genv sparse.id.«nausparse:bit» = some Block.bit
kernel_rfl find_distvals : Genv.find_symbol sge.genv_genv sparse.id.distvals = some Block.distvals
kernel_rfl find_sortints :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:sortints» = some Block.sortints
kernel_rfl find_sortindirect :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:sortindirect» = some Block.sortindirect
kernel_rfl find_refine : Genv.find_symbol sge.genv_genv sparse.id.refine_sg = some Block.refine

kernel_rfl funct_preparemarks2 : Genv.find_funct_ptr sge.genv_genv Block.preparemarks2 =
  some (.Internal sparse.fn.«nausparse:preparemarks2»)
kernel_rfl funct_distvals : Genv.find_funct_ptr sge.genv_genv Block.distvals =
  some (.Internal sparse.fn.distvals)
kernel_rfl funct_sortints : Genv.find_funct_ptr sge.genv_genv Block.sortints =
  some (.Internal sparse.fn.«nausparse:sortints»)
kernel_rfl funct_sortindirect : Genv.find_funct_ptr sge.genv_genv Block.sortindirect =
  some (.Internal sparse.fn.«nausparse:sortindirect»)
kernel_rfl funct_refine : Genv.find_funct_ptr sge.genv_genv Block.refine =
  some (.Internal sparse.fn.refine_sg)

end NautyVerified.Proofs.Sparse.Refine
