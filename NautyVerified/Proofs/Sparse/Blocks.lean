import NautyVerified.Source.Sparse
import NautyVerified.Proofs.Syntax

/-!
# The sparse program's global environment

`sge`, the global environment of `sparse.locals`, and the blocks of the
nausparse.c globals and functions the proofs of `isautom_sg`,
`testcanlab_sg`, `updatecan_sg` and `init_sg` use, each fact checked by the
kernel. The sparse program puts shared identifiers at other blocks than the
dense one, so these are separate from `Program.Block`.
-/

namespace NautyVerified.Proofs.Sparse

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Source

/-- The global environment of the linked sparse program. -/
abbrev sge : genv := globalenv sparse.locals

namespace Block
def vmark1 : Common.Values.block := PArith.BinPos.Pos.of_nat 200
def vmark1Sz : Common.Values.block := PArith.BinPos.Pos.of_nat 279
def vmark1Val : Common.Values.block := PArith.BinPos.Pos.of_nat 272
def preparemarks1 : Common.Values.block := PArith.BinPos.Pos.of_nat 46
def work1 : Common.Values.block := PArith.BinPos.Pos.of_nat 221
def work1Sz : Common.Values.block := PArith.BinPos.Pos.of_nat 300
def free : Common.Values.block := PArith.BinPos.Pos.of_nat 244
def zalloc : Common.Values.block := PArith.BinPos.Pos.of_nat 146
def malloc : Common.Values.block := PArith.BinPos.Pos.of_nat 270
def allocError : Common.Values.block := PArith.BinPos.Pos.of_nat 39
def isautom : Common.Values.block := PArith.BinPos.Pos.of_nat 346
def testcanlab : Common.Values.block := PArith.BinPos.Pos.of_nat 189
def updatecan : Common.Values.block := PArith.BinPos.Pos.of_nat 267
def init : Common.Values.block := PArith.BinPos.Pos.of_nat 327
end Block

kernel_rfl find_vmark1 :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:vmark1» = some Block.vmark1
kernel_rfl find_vmark1Sz :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:vmark1_sz» = some Block.vmark1Sz
kernel_rfl find_vmark1Val :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:vmark1_val» = some Block.vmark1Val
kernel_rfl find_preparemarks1 :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:preparemarks1» = some Block.preparemarks1
kernel_rfl find_work1 :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work1» = some Block.work1
kernel_rfl find_work1Sz :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work1_sz» = some Block.work1Sz
kernel_rfl find_free : Genv.find_symbol sge.genv_genv sparse.id.free = some Block.free
kernel_rfl find_zalloc : Genv.find_symbol sge.genv_genv sparse.id.nauty_zalloc = some Block.zalloc
kernel_rfl find_malloc : Genv.find_symbol sge.genv_genv sparse.id.malloc = some Block.malloc
kernel_rfl find_isautom : Genv.find_symbol sge.genv_genv sparse.id.isautom_sg = some Block.isautom
kernel_rfl find_testcanlab :
  Genv.find_symbol sge.genv_genv sparse.id.testcanlab_sg = some Block.testcanlab
kernel_rfl find_updatecan :
  Genv.find_symbol sge.genv_genv sparse.id.updatecan_sg = some Block.updatecan
kernel_rfl find_init : Genv.find_symbol sge.genv_genv sparse.id.init_sg = some Block.init

kernel_rfl funct_preparemarks1 : Genv.find_funct_ptr sge.genv_genv Block.preparemarks1 =
  some (.Internal sparse.fn.«nausparse:preparemarks1»)
kernel_rfl funct_free : Genv.find_funct_ptr sge.genv_genv Block.free =
  some (.External .EF_free [tptr .Tvoid] .Tvoid Common.AST.cc_default)
kernel_rfl funct_malloc : Genv.find_funct_ptr sge.genv_genv Block.malloc =
  some (.External .EF_malloc [tulong] (tptr .Tvoid) Common.AST.cc_default)
kernel_rfl funct_zalloc : Genv.find_funct_ptr sge.genv_genv Block.zalloc =
  some (.Internal sparse.fn.nauty_zalloc)
kernel_rfl funct_isautom : Genv.find_funct_ptr sge.genv_genv Block.isautom =
  some (.Internal sparse.fn.isautom_sg)
kernel_rfl funct_testcanlab : Genv.find_funct_ptr sge.genv_genv Block.testcanlab =
  some (.Internal sparse.fn.testcanlab_sg)
kernel_rfl funct_updatecan : Genv.find_funct_ptr sge.genv_genv Block.updatecan =
  some (.Internal sparse.fn.updatecan_sg)
kernel_rfl funct_init : Genv.find_funct_ptr sge.genv_genv Block.init =
  some (.Internal sparse.fn.init_sg)

end NautyVerified.Proofs.Sparse
