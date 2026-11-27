import NautyVerified.Program.Dense
import NautyVerified.Proofs.Syntax

/-!
# The allocator's globals

The blocks of `malloc`, `free` and the harness's `nauty_zalloc`, and the
functions at them, checked by the kernel.
-/

namespace NautyVerified.Program

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Source NautyVerified.Proofs

namespace Block
def malloc : Common.Values.block := PArith.BinPos.Pos.of_nat 242
def free : Common.Values.block := PArith.BinPos.Pos.of_nat 221
def zalloc : Common.Values.block := PArith.BinPos.Pos.of_nat 132
/-- nautil.c's `static int *workperm`. -/
def nautilWorkperm : Common.Values.block := PArith.BinPos.Pos.of_nat 29
/-- nautil.c's `static size_t workperm_sz`. -/
def nautilWorkpermSz : Common.Values.block := PArith.BinPos.Pos.of_nat 199
/-- naugraph.c's `static int *workperm`. -/
def naugraphWorkperm : Common.Values.block := PArith.BinPos.Pos.of_nat 1
/-- naugraph.c's `static size_t workperm_sz`. -/
def naugraphWorkpermSz : Common.Values.block := PArith.BinPos.Pos.of_nat 176
/-- naugraph.c's `static set *workset`. -/
def naugraphWorkset : Common.Values.block := PArith.BinPos.Pos.of_nat 245
/-- naugraph.c's `static size_t workset_sz`. -/
def naugraphWorksetSz : Common.Values.block := PArith.BinPos.Pos.of_nat 312
/-- `permset`'s block. -/
def permset : Common.Values.block := PArith.BinPos.Pos.of_nat 300
/-- naugraph.c's static `bit[64]`. -/
def naugraphBit : Common.Values.block := PArith.BinPos.Pos.of_nat 295
end Block

kernel_rfl find_malloc : Genv.find_symbol ge.genv_genv dense.id.malloc = some Block.malloc
kernel_rfl find_free : Genv.find_symbol ge.genv_genv dense.id.free = some Block.free
kernel_rfl find_zalloc : Genv.find_symbol ge.genv_genv dense.id.nauty_zalloc = some Block.zalloc

kernel_rfl find_nautilWorkperm :
  Genv.find_symbol ge.genv_genv dense.id.«nautil:workperm» = some Block.nautilWorkperm
kernel_rfl find_nautilWorkpermSz :
  Genv.find_symbol ge.genv_genv dense.id.«nautil:workperm_sz» = some Block.nautilWorkpermSz

kernel_rfl find_naugraphBit :
  Genv.find_symbol ge.genv_genv dense.id.«naugraph:bit» = some Block.naugraphBit

kernel_rfl find_naugraphWorkperm :
  Genv.find_symbol ge.genv_genv dense.id.«naugraph:workperm» = some Block.naugraphWorkperm
kernel_rfl find_naugraphWorkpermSz :
  Genv.find_symbol ge.genv_genv dense.id.«naugraph:workperm_sz» = some Block.naugraphWorkpermSz
kernel_rfl find_naugraphWorkset :
  Genv.find_symbol ge.genv_genv dense.id.«naugraph:workset» = some Block.naugraphWorkset
kernel_rfl find_naugraphWorksetSz :
  Genv.find_symbol ge.genv_genv dense.id.«naugraph:workset_sz» = some Block.naugraphWorksetSz
kernel_rfl find_permset : Genv.find_symbol ge.genv_genv dense.id.permset = some Block.permset
kernel_rfl funct_permset :
  Genv.find_funct_ptr ge.genv_genv Block.permset = some (.Internal dense.fn.permset)

kernel_rfl funct_malloc : Genv.find_funct_ptr ge.genv_genv Block.malloc =
  some (.External .EF_malloc [tulong] (tptr .Tvoid) Common.AST.cc_default)
kernel_rfl funct_free : Genv.find_funct_ptr ge.genv_genv Block.free =
  some (.External .EF_free [tptr .Tvoid] .Tvoid Common.AST.cc_default)
kernel_rfl funct_zalloc : Genv.find_funct_ptr ge.genv_genv Block.zalloc =
  some (.Internal dense.fn.nauty_zalloc)

end NautyVerified.Program
