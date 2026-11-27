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

namespace Block
/-- naugraph.c's `static int *bucket`. -/
def naugraphBucket : Common.Values.block := PArith.BinPos.Pos.of_nat 246
/-- naugraph.c's `static size_t bucket_sz`. -/
def naugraphBucketSz : Common.Values.block := PArith.BinPos.Pos.of_nat 211
/-- naugraph.c's `static set *dnwork`. -/
def naugraphDnwork : Common.Values.block := PArith.BinPos.Pos.of_nat 278
/-- naugraph.c's `static size_t dnwork_sz`. -/
def naugraphDnworkSz : Common.Values.block := PArith.BinPos.Pos.of_nat 193
/-- naugraph.c's static `bytecount[256]`. -/
def naugraphBytecount : Common.Values.block := PArith.BinPos.Pos.of_nat 210
/-- nauty.c's static `bit[64]`. -/
def nautyBit : Common.Values.block := PArith.BinPos.Pos.of_nat 289
/-- dense_main.c's static `bit[64]`. -/
def denseMainBit : Common.Values.block := PArith.BinPos.Pos.of_nat 87
/-- nauty.c's `canonlab` (DYNALLSTAT pointer). -/
def nautyCanonlab : Common.Values.block := PArith.BinPos.Pos.of_nat 6
/-- nauty.c's `canonlab_sz` (static size_t). -/
def nautyCanonlabSz : Common.Values.block := PArith.BinPos.Pos.of_nat 92
/-- nauty.c's `defltwork` (DYNALLSTAT pointer). -/
def nautyDefltwork : Common.Values.block := PArith.BinPos.Pos.of_nat 14
/-- nauty.c's `defltwork_sz` (static size_t). -/
def nautyDefltworkSz : Common.Values.block := PArith.BinPos.Pos.of_nat 98
/-- nauty.c's `active` (DYNALLSTAT pointer). -/
def nautyActive : Common.Values.block := PArith.BinPos.Pos.of_nat 17
/-- nauty.c's `active_sz` (static size_t). -/
def nautyActiveSz : Common.Values.block := PArith.BinPos.Pos.of_nat 104
/-- nauty.c's `canoncode` (DYNALLSTAT pointer). -/
def nautyCanoncode : Common.Values.block := PArith.BinPos.Pos.of_nat 26
/-- nauty.c's `canoncode_sz` (static size_t). -/
def nautyCanoncodeSz : Common.Values.block := PArith.BinPos.Pos.of_nat 115
/-- nauty.c's `fixedpts` (DYNALLSTAT pointer). -/
def nautyFixedpts : Common.Values.block := PArith.BinPos.Pos.of_nat 33
/-- nauty.c's `fixedpts_sz` (static size_t). -/
def nautyFixedptsSz : Common.Values.block := PArith.BinPos.Pos.of_nat 121
/-- nauty.c's `firstcode` (DYNALLSTAT pointer). -/
def nautyFirstcode : Common.Values.block := PArith.BinPos.Pos.of_nat 46
/-- nauty.c's `firstcode_sz` (static size_t). -/
def nautyFirstcodeSz : Common.Values.block := PArith.BinPos.Pos.of_nat 137
/-- nauty.c's `workperm` (DYNALLSTAT pointer). -/
def nautyWorkperm : Common.Values.block := PArith.BinPos.Pos.of_nat 53
/-- nauty.c's `workperm_sz` (static size_t). -/
def nautyWorkpermSz : Common.Values.block := PArith.BinPos.Pos.of_nat 142
/-- nauty.c's `firsttc` (DYNALLSTAT pointer). -/
def nautyFirsttc : Common.Values.block := PArith.BinPos.Pos.of_nat 71
/-- nauty.c's `firsttc_sz` (static size_t). -/
def nautyFirsttcSz : Common.Values.block := PArith.BinPos.Pos.of_nat 159
/-- nauty.c's `firstlab` (DYNALLSTAT pointer). -/
def nautyFirstlab : Common.Values.block := PArith.BinPos.Pos.of_nat 76
/-- nauty.c's `firstlab_sz` (static size_t). -/
def nautyFirstlabSz : Common.Values.block := PArith.BinPos.Pos.of_nat 165
end Block

kernel_rfl find_naugraphBucket :
  Genv.find_symbol ge.genv_genv dense.id.«naugraph:bucket» = some Block.naugraphBucket
kernel_rfl find_naugraphBucketSz :
  Genv.find_symbol ge.genv_genv dense.id.«naugraph:bucket_sz» = some Block.naugraphBucketSz
kernel_rfl find_naugraphDnwork :
  Genv.find_symbol ge.genv_genv dense.id.«naugraph:dnwork» = some Block.naugraphDnwork
kernel_rfl find_naugraphDnworkSz :
  Genv.find_symbol ge.genv_genv dense.id.«naugraph:dnwork_sz» = some Block.naugraphDnworkSz
kernel_rfl find_naugraphBytecount :
  Genv.find_symbol ge.genv_genv dense.id.«naugraph:bytecount» = some Block.naugraphBytecount
kernel_rfl find_nautyBit :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:bit» = some Block.nautyBit
kernel_rfl find_denseMainBit :
  Genv.find_symbol ge.genv_genv dense.id.«dense_main:bit» = some Block.denseMainBit
kernel_rfl find_nautyCanonlab :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:canonlab» = some Block.nautyCanonlab
kernel_rfl find_nautyCanonlabSz :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:canonlab_sz» = some Block.nautyCanonlabSz
kernel_rfl find_nautyDefltwork :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:defltwork» = some Block.nautyDefltwork
kernel_rfl find_nautyDefltworkSz :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:defltwork_sz» = some Block.nautyDefltworkSz
kernel_rfl find_nautyActive :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:active» = some Block.nautyActive
kernel_rfl find_nautyActiveSz :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:active_sz» = some Block.nautyActiveSz
kernel_rfl find_nautyCanoncode :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:canoncode» = some Block.nautyCanoncode
kernel_rfl find_nautyCanoncodeSz :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:canoncode_sz» = some Block.nautyCanoncodeSz
kernel_rfl find_nautyFixedpts :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:fixedpts» = some Block.nautyFixedpts
kernel_rfl find_nautyFixedptsSz :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:fixedpts_sz» = some Block.nautyFixedptsSz
kernel_rfl find_nautyFirstcode :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:firstcode» = some Block.nautyFirstcode
kernel_rfl find_nautyFirstcodeSz :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:firstcode_sz» = some Block.nautyFirstcodeSz
kernel_rfl find_nautyWorkperm :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:workperm» = some Block.nautyWorkperm
kernel_rfl find_nautyWorkpermSz :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:workperm_sz» = some Block.nautyWorkpermSz
kernel_rfl find_nautyFirsttc :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:firsttc» = some Block.nautyFirsttc
kernel_rfl find_nautyFirsttcSz :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:firsttc_sz» = some Block.nautyFirsttcSz
kernel_rfl find_nautyFirstlab :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:firstlab» = some Block.nautyFirstlab
kernel_rfl find_nautyFirstlabSz :
  Genv.find_symbol ge.genv_genv dense.id.«nauty:firstlab_sz» = some Block.nautyFirstlabSz

end NautyVerified.Program
