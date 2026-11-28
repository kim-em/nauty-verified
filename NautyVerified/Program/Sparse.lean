import NautyVerified.Program.Env
import NautyVerified.Source.Shared

/-!
# The linked sparse program's global environment

`sparseGe`, the global environment of `sparse.locals`, the blocks the sparse
program gives the globals of `NautyEnv`, and `NautyEnv.sparse`, each fact
checked by the kernel. The functions at these blocks are `dense.fn.*`, the
sparse program's Clight being the dense program's (`Source/Shared.lean`).

`NautyEnv.sparse` is not a global instance (the environment is an `outParam`,
so two global instances would compete); proofs about the sparse program
activate it with `attribute [local instance] NautyEnv.sparse`.
-/

namespace NautyVerified.Program

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Source NautyVerified.Proofs

/-- The global environment of the linked sparse program. -/
abbrev sparseGe : genv := globalenv sparse.locals

namespace SparseBlock
def nextelement : block := PArith.BinPos.Pos.of_nat 13
def leftbit : block := PArith.BinPos.Pos.of_nat 319
def nautilBit : block := PArith.BinPos.Pos.of_nat 236
def malloc : block := PArith.BinPos.Pos.of_nat 270
def free : block := PArith.BinPos.Pos.of_nat 244
def zalloc : block := PArith.BinPos.Pos.of_nat 146
def nautilWorkperm : block := PArith.BinPos.Pos.of_nat 30
def nautilWorkpermSz : block := PArith.BinPos.Pos.of_nat 218
def permset : block := PArith.BinPos.Pos.of_nat 337
def nautyBit : block := PArith.BinPos.Pos.of_nat 326
def nautyCanonlab : block := PArith.BinPos.Pos.of_nat 5
def nautyCanonlabSz : block := PArith.BinPos.Pos.of_nat 101
def nautyDefltwork : block := PArith.BinPos.Pos.of_nat 14
def nautyDefltworkSz : block := PArith.BinPos.Pos.of_nat 107
def nautyActive : block := PArith.BinPos.Pos.of_nat 19
def nautyActiveSz : block := PArith.BinPos.Pos.of_nat 116
def nautyCanoncode : block := PArith.BinPos.Pos.of_nat 27
def nautyCanoncodeSz : block := PArith.BinPos.Pos.of_nat 128
def nautyFixedpts : block := PArith.BinPos.Pos.of_nat 34
def nautyFixedptsSz : block := PArith.BinPos.Pos.of_nat 134
def nautyFirstcode : block := PArith.BinPos.Pos.of_nat 49
def nautyFirstcodeSz : block := PArith.BinPos.Pos.of_nat 150
def nautyWorkperm : block := PArith.BinPos.Pos.of_nat 58
def nautyWorkpermSz : block := PArith.BinPos.Pos.of_nat 157
def nautyFirsttc : block := PArith.BinPos.Pos.of_nat 78
def nautyFirsttcSz : block := PArith.BinPos.Pos.of_nat 175
def nautyFirstlab : block := PArith.BinPos.Pos.of_nat 84
def nautyFirstlabSz : block := PArith.BinPos.Pos.of_nat 181
def getcanon : block := PArith.BinPos.Pos.of_nat 285
def digraph : block := PArith.BinPos.Pos.of_nat 68
def writeautoms : block := PArith.BinPos.Pos.of_nat 246
def cartesian : block := PArith.BinPos.Pos.of_nat 165
def linelength : block := PArith.BinPos.Pos.of_nat 328
def outfile : block := PArith.BinPos.Pos.of_nat 43
def userautomproc : block := PArith.BinPos.Pos.of_nat 228
def userlevelproc : block := PArith.BinPos.Pos.of_nat 144
def usernodeproc : block := PArith.BinPos.Pos.of_nat 308
def usercanonproc : block := PArith.BinPos.Pos.of_nat 93
def invarproc : block := PArith.BinPos.Pos.of_nat 269
def tcLevel : block := PArith.BinPos.Pos.of_nat 192
def mininvarlevel : block := PArith.BinPos.Pos.of_nat 348
def maxinvarlevel : block := PArith.BinPos.Pos.of_nat 4
def invararg : block := PArith.BinPos.Pos.of_nat 194
def dispatch : block := PArith.BinPos.Pos.of_nat 100
def orbits : block := PArith.BinPos.Pos.of_nat 173
def domarkers : block := PArith.BinPos.Pos.of_nat 24
def doschreier : block := PArith.BinPos.Pos.of_nat 121
def m : block := PArith.BinPos.Pos.of_nat 288
def n : block := PArith.BinPos.Pos.of_nat 72
def g : block := PArith.BinPos.Pos.of_nat 251
def canong : block := PArith.BinPos.Pos.of_nat 168
def stats : block := PArith.BinPos.Pos.of_nat 332
def gcaFirst : block := PArith.BinPos.Pos.of_nat 231
def gcaCanon : block := PArith.BinPos.Pos.of_nat 311
def noncheaplevel : block := PArith.BinPos.Pos.of_nat 271
def allsamelevel : block := PArith.BinPos.Pos.of_nat 351
def eqlevFirst : block := PArith.BinPos.Pos.of_nat 193
def eqlevCanon : block := PArith.BinPos.Pos.of_nat 273
def compCanon : block := PArith.BinPos.Pos.of_nat 233
def samerows : block := PArith.BinPos.Pos.of_nat 313
def canonlevel : block := PArith.BinPos.Pos.of_nat 212
def stabvertex : block := PArith.BinPos.Pos.of_nat 123
def cosetindex : block := PArith.BinPos.Pos.of_nat 74
def needshortprune : block := PArith.BinPos.Pos.of_nat 170
def tcnode0 : block := PArith.BinPos.Pos.of_nat 66
def allocM : block := PArith.BinPos.Pos.of_nat 164
def workspace : block := PArith.BinPos.Pos.of_nat 42
def worktop : block := PArith.BinPos.Pos.of_nat 142
def fmptr : block := PArith.BinPos.Pos.of_nat 92
def invapplics : block := PArith.BinPos.Pos.of_nat 20
def invsuccesses : block := PArith.BinPos.Pos.of_nat 206
def invarsuclevel : block := PArith.BinPos.Pos.of_nat 117
def killRequest : block := PArith.BinPos.Pos.of_nat 33
def firstpathnodeFn : block := PArith.BinPos.Pos.of_nat 11
def othernodeFn : block := PArith.BinPos.Pos.of_nat 249
def firstterminalFn : block := PArith.BinPos.Pos.of_nat 287
def processnodeFn : block := PArith.BinPos.Pos.of_nat 97
def recoverFn : block := PArith.BinPos.Pos.of_nat 330
def nautyFn : block := PArith.BinPos.Pos.of_nat 105
def maketargetcellFn : block := PArith.BinPos.Pos.of_nat 345
def breakoutFn : block := PArith.BinPos.Pos.of_nat 226
def fmpermFn : block := PArith.BinPos.Pos.of_nat 89
def fmptnFn : block := PArith.BinPos.Pos.of_nat 266
def orbjoinFn : block := PArith.BinPos.Pos.of_nat 199
def shortpruneFn : block := PArith.BinPos.Pos.of_nat 278
def longpruneFn : block := PArith.BinPos.Pos.of_nat 188
def dorefFn : block := PArith.BinPos.Pos.of_nat 139
def nautilCheck : block := PArith.BinPos.Pos.of_nat 239
def nautilFreedyn : block := PArith.BinPos.Pos.of_nat 156
def nautyFreedyn : block := PArith.BinPos.Pos.of_nat 198
end SparseBlock

namespace SparseEnv

kernel_rfl find_nextelement :
  Genv.find_symbol sparseGe.genv_genv dense.id.nextelement = some SparseBlock.nextelement
kernel_rfl find_leftbit :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nautil:leftbit» = some SparseBlock.leftbit
kernel_rfl find_nautilBit :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nautil:bit» = some SparseBlock.nautilBit
kernel_rfl find_malloc :
  Genv.find_symbol sparseGe.genv_genv dense.id.malloc = some SparseBlock.malloc
kernel_rfl find_free :
  Genv.find_symbol sparseGe.genv_genv dense.id.free = some SparseBlock.free
kernel_rfl find_zalloc :
  Genv.find_symbol sparseGe.genv_genv dense.id.nauty_zalloc = some SparseBlock.zalloc
kernel_rfl find_nautilWorkperm :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nautil:workperm» = some SparseBlock.nautilWorkperm
kernel_rfl find_nautilWorkpermSz :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nautil:workperm_sz» = some SparseBlock.nautilWorkpermSz
kernel_rfl find_permset :
  Genv.find_symbol sparseGe.genv_genv dense.id.permset = some SparseBlock.permset
kernel_rfl find_nautyBit :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:bit» = some SparseBlock.nautyBit
kernel_rfl find_nautyCanonlab :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:canonlab» = some SparseBlock.nautyCanonlab
kernel_rfl find_nautyCanonlabSz :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:canonlab_sz» = some SparseBlock.nautyCanonlabSz
kernel_rfl find_nautyDefltwork :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:defltwork» = some SparseBlock.nautyDefltwork
kernel_rfl find_nautyDefltworkSz :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:defltwork_sz» = some SparseBlock.nautyDefltworkSz
kernel_rfl find_nautyActive :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:active» = some SparseBlock.nautyActive
kernel_rfl find_nautyActiveSz :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:active_sz» = some SparseBlock.nautyActiveSz
kernel_rfl find_nautyCanoncode :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:canoncode» = some SparseBlock.nautyCanoncode
kernel_rfl find_nautyCanoncodeSz :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:canoncode_sz» = some SparseBlock.nautyCanoncodeSz
kernel_rfl find_nautyFixedpts :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:fixedpts» = some SparseBlock.nautyFixedpts
kernel_rfl find_nautyFixedptsSz :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:fixedpts_sz» = some SparseBlock.nautyFixedptsSz
kernel_rfl find_nautyFirstcode :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:firstcode» = some SparseBlock.nautyFirstcode
kernel_rfl find_nautyFirstcodeSz :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:firstcode_sz» = some SparseBlock.nautyFirstcodeSz
kernel_rfl find_nautyWorkperm :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:workperm» = some SparseBlock.nautyWorkperm
kernel_rfl find_nautyWorkpermSz :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:workperm_sz» = some SparseBlock.nautyWorkpermSz
kernel_rfl find_nautyFirsttc :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:firsttc» = some SparseBlock.nautyFirsttc
kernel_rfl find_nautyFirsttcSz :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:firsttc_sz» = some SparseBlock.nautyFirsttcSz
kernel_rfl find_nautyFirstlab :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:firstlab» = some SparseBlock.nautyFirstlab
kernel_rfl find_nautyFirstlabSz :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:firstlab_sz» = some SparseBlock.nautyFirstlabSz
kernel_rfl find_getcanon :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:getcanon» = some SparseBlock.getcanon
kernel_rfl find_digraph :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:digraph» = some SparseBlock.digraph
kernel_rfl find_writeautoms :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:writeautoms» = some SparseBlock.writeautoms
kernel_rfl find_cartesian :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:cartesian» = some SparseBlock.cartesian
kernel_rfl find_linelength :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:linelength» = some SparseBlock.linelength
kernel_rfl find_outfile :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:outfile» = some SparseBlock.outfile
kernel_rfl find_userautomproc :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:userautomproc» = some SparseBlock.userautomproc
kernel_rfl find_userlevelproc :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:userlevelproc» = some SparseBlock.userlevelproc
kernel_rfl find_usernodeproc :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:usernodeproc» = some SparseBlock.usernodeproc
kernel_rfl find_usercanonproc :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:usercanonproc» = some SparseBlock.usercanonproc
kernel_rfl find_invarproc :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:invarproc» = some SparseBlock.invarproc
kernel_rfl find_tcLevel :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:tc_level» = some SparseBlock.tcLevel
kernel_rfl find_mininvarlevel :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:mininvarlevel» = some SparseBlock.mininvarlevel
kernel_rfl find_maxinvarlevel :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:maxinvarlevel» = some SparseBlock.maxinvarlevel
kernel_rfl find_invararg :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:invararg» = some SparseBlock.invararg
kernel_rfl find_dispatch :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:dispatch» = some SparseBlock.dispatch
kernel_rfl find_orbits :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:orbits» = some SparseBlock.orbits
kernel_rfl find_domarkers :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:domarkers» = some SparseBlock.domarkers
kernel_rfl find_doschreier :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:doschreier» = some SparseBlock.doschreier
kernel_rfl find_m :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:m» = some SparseBlock.m
kernel_rfl find_n :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:n» = some SparseBlock.n
kernel_rfl find_g :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:g» = some SparseBlock.g
kernel_rfl find_canong :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:canong» = some SparseBlock.canong
kernel_rfl find_stats :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:stats» = some SparseBlock.stats
kernel_rfl find_gcaFirst :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:gca_first» = some SparseBlock.gcaFirst
kernel_rfl find_gcaCanon :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:gca_canon» = some SparseBlock.gcaCanon
kernel_rfl find_noncheaplevel :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:noncheaplevel» = some SparseBlock.noncheaplevel
kernel_rfl find_allsamelevel :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:allsamelevel» = some SparseBlock.allsamelevel
kernel_rfl find_eqlevFirst :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:eqlev_first» = some SparseBlock.eqlevFirst
kernel_rfl find_eqlevCanon :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:eqlev_canon» = some SparseBlock.eqlevCanon
kernel_rfl find_compCanon :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:comp_canon» = some SparseBlock.compCanon
kernel_rfl find_samerows :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:samerows» = some SparseBlock.samerows
kernel_rfl find_canonlevel :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:canonlevel» = some SparseBlock.canonlevel
kernel_rfl find_stabvertex :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:stabvertex» = some SparseBlock.stabvertex
kernel_rfl find_cosetindex :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:cosetindex» = some SparseBlock.cosetindex
kernel_rfl find_needshortprune :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:needshortprune» = some SparseBlock.needshortprune
kernel_rfl find_tcnode0 :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:tcnode0» = some SparseBlock.tcnode0
kernel_rfl find_allocM :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:alloc_m» = some SparseBlock.allocM
kernel_rfl find_workspace :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:workspace» = some SparseBlock.workspace
kernel_rfl find_worktop :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:worktop» = some SparseBlock.worktop
kernel_rfl find_fmptr :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:fmptr» = some SparseBlock.fmptr
kernel_rfl find_invapplics :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:invapplics» = some SparseBlock.invapplics
kernel_rfl find_invsuccesses :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:invsuccesses» = some SparseBlock.invsuccesses
kernel_rfl find_invarsuclevel :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:invarsuclevel» = some SparseBlock.invarsuclevel
kernel_rfl find_killRequest :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty_kill_request» = some SparseBlock.killRequest
kernel_rfl find_firstpathnodeFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:firstpathnode0» = some SparseBlock.firstpathnodeFn
kernel_rfl find_othernodeFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:othernode0» = some SparseBlock.othernodeFn
kernel_rfl find_firstterminalFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:firstterminal» = some SparseBlock.firstterminalFn
kernel_rfl find_processnodeFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:processnode» = some SparseBlock.processnodeFn
kernel_rfl find_recoverFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty:recover» = some SparseBlock.recoverFn
kernel_rfl find_nautyFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«nauty» = some SparseBlock.nautyFn
kernel_rfl find_maketargetcellFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«maketargetcell» = some SparseBlock.maketargetcellFn
kernel_rfl find_breakoutFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«breakout» = some SparseBlock.breakoutFn
kernel_rfl find_fmpermFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«fmperm» = some SparseBlock.fmpermFn
kernel_rfl find_fmptnFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«fmptn» = some SparseBlock.fmptnFn
kernel_rfl find_orbjoinFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«orbjoin» = some SparseBlock.orbjoinFn
kernel_rfl find_shortpruneFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«shortprune» = some SparseBlock.shortpruneFn
kernel_rfl find_longpruneFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«longprune» = some SparseBlock.longpruneFn
kernel_rfl find_dorefFn :
  Genv.find_symbol sparseGe.genv_genv dense.id.«doref» = some SparseBlock.dorefFn
kernel_rfl find_nautilCheck :
  Genv.find_symbol sparseGe.genv_genv dense.id.nautil_check = some SparseBlock.nautilCheck
kernel_rfl find_nautilFreedyn :
  Genv.find_symbol sparseGe.genv_genv dense.id.nautil_freedyn = some SparseBlock.nautilFreedyn
kernel_rfl find_nautyFreedyn :
  Genv.find_symbol sparseGe.genv_genv dense.id.nauty_freedyn = some SparseBlock.nautyFreedyn
kernel_rfl funct_nextelement :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.nextelement = some (.Internal dense.fn.nextelement)
kernel_rfl funct_malloc :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.malloc = some (.External .EF_malloc [tulong] (tptr .Tvoid) Common.AST.cc_default)
kernel_rfl funct_free :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.free = some (.External .EF_free [tptr .Tvoid] .Tvoid Common.AST.cc_default)
kernel_rfl funct_zalloc :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.zalloc = some (.Internal dense.fn.nauty_zalloc)
kernel_rfl funct_permset :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.permset = some (.Internal dense.fn.permset)
kernel_rfl funct_firstpathnodeFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.firstpathnodeFn = some (.Internal dense.fn.«nauty:firstpathnode0»)
kernel_rfl funct_othernodeFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.othernodeFn = some (.Internal dense.fn.«nauty:othernode0»)
kernel_rfl funct_firstterminalFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.firstterminalFn = some (.Internal dense.fn.«nauty:firstterminal»)
kernel_rfl funct_processnodeFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.processnodeFn = some (.Internal dense.fn.«nauty:processnode»)
kernel_rfl funct_recoverFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.recoverFn = some (.Internal dense.fn.«nauty:recover»)
kernel_rfl funct_nautyFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.nautyFn = some (.Internal dense.fn.«nauty»)
kernel_rfl funct_maketargetcellFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.maketargetcellFn = some (.Internal dense.fn.«maketargetcell»)
kernel_rfl funct_breakoutFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.breakoutFn = some (.Internal dense.fn.«breakout»)
kernel_rfl funct_fmpermFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.fmpermFn = some (.Internal dense.fn.«fmperm»)
kernel_rfl funct_fmptnFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.fmptnFn = some (.Internal dense.fn.«fmptn»)
kernel_rfl funct_orbjoinFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.orbjoinFn = some (.Internal dense.fn.«orbjoin»)
kernel_rfl funct_shortpruneFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.shortpruneFn = some (.Internal dense.fn.«shortprune»)
kernel_rfl funct_longpruneFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.longpruneFn = some (.Internal dense.fn.«longprune»)
kernel_rfl funct_dorefFn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.dorefFn = some (.Internal dense.fn.«doref»)
kernel_rfl funct_nautilCheck :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.nautilCheck = some (.Internal dense.fn.nautil_check)
kernel_rfl funct_nautilFreedyn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.nautilFreedyn = some (.Internal dense.fn.nautil_freedyn)
kernel_rfl funct_nautyFreedyn :
  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.nautyFreedyn = some (.Internal dense.fn.nauty_freedyn)
kernel_rfl var_leftbit : Genv.find_var_info sparseGe.genv_genv SparseBlock.leftbit =
  Genv.find_var_info ge.genv_genv Block.leftbit
kernel_rfl var_nautilBit : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautilBit =
  Genv.find_var_info ge.genv_genv Block.nautilBit
kernel_rfl var_nautilWorkperm : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautilWorkperm =
  Genv.find_var_info ge.genv_genv Block.nautilWorkperm
kernel_rfl var_nautilWorkpermSz : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautilWorkpermSz =
  Genv.find_var_info ge.genv_genv Block.nautilWorkpermSz
kernel_rfl var_nautyBit : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyBit =
  Genv.find_var_info ge.genv_genv Block.nautyBit
kernel_rfl var_nautyCanonlab : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyCanonlab =
  Genv.find_var_info ge.genv_genv Block.nautyCanonlab
kernel_rfl var_nautyCanonlabSz : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyCanonlabSz =
  Genv.find_var_info ge.genv_genv Block.nautyCanonlabSz
kernel_rfl var_nautyDefltwork : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyDefltwork =
  Genv.find_var_info ge.genv_genv Block.nautyDefltwork
kernel_rfl var_nautyDefltworkSz : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyDefltworkSz =
  Genv.find_var_info ge.genv_genv Block.nautyDefltworkSz
kernel_rfl var_nautyActive : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyActive =
  Genv.find_var_info ge.genv_genv Block.nautyActive
kernel_rfl var_nautyActiveSz : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyActiveSz =
  Genv.find_var_info ge.genv_genv Block.nautyActiveSz
kernel_rfl var_nautyCanoncode : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyCanoncode =
  Genv.find_var_info ge.genv_genv Block.nautyCanoncode
kernel_rfl var_nautyCanoncodeSz : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyCanoncodeSz =
  Genv.find_var_info ge.genv_genv Block.nautyCanoncodeSz
kernel_rfl var_nautyFixedpts : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyFixedpts =
  Genv.find_var_info ge.genv_genv Block.nautyFixedpts
kernel_rfl var_nautyFixedptsSz : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyFixedptsSz =
  Genv.find_var_info ge.genv_genv Block.nautyFixedptsSz
kernel_rfl var_nautyFirstcode : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyFirstcode =
  Genv.find_var_info ge.genv_genv Block.nautyFirstcode
kernel_rfl var_nautyFirstcodeSz : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyFirstcodeSz =
  Genv.find_var_info ge.genv_genv Block.nautyFirstcodeSz
kernel_rfl var_nautyWorkperm : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyWorkperm =
  Genv.find_var_info ge.genv_genv Block.nautyWorkperm
kernel_rfl var_nautyWorkpermSz : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyWorkpermSz =
  Genv.find_var_info ge.genv_genv Block.nautyWorkpermSz
kernel_rfl var_nautyFirsttc : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyFirsttc =
  Genv.find_var_info ge.genv_genv Block.nautyFirsttc
kernel_rfl var_nautyFirsttcSz : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyFirsttcSz =
  Genv.find_var_info ge.genv_genv Block.nautyFirsttcSz
kernel_rfl var_nautyFirstlab : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyFirstlab =
  Genv.find_var_info ge.genv_genv Block.nautyFirstlab
kernel_rfl var_nautyFirstlabSz : Genv.find_var_info sparseGe.genv_genv SparseBlock.nautyFirstlabSz =
  Genv.find_var_info ge.genv_genv Block.nautyFirstlabSz
kernel_rfl var_getcanon : Genv.find_var_info sparseGe.genv_genv SparseBlock.getcanon =
  Genv.find_var_info ge.genv_genv Search.Block.getcanon
kernel_rfl var_digraph : Genv.find_var_info sparseGe.genv_genv SparseBlock.digraph =
  Genv.find_var_info ge.genv_genv Search.Block.digraph
kernel_rfl var_writeautoms : Genv.find_var_info sparseGe.genv_genv SparseBlock.writeautoms =
  Genv.find_var_info ge.genv_genv Search.Block.writeautoms
kernel_rfl var_cartesian : Genv.find_var_info sparseGe.genv_genv SparseBlock.cartesian =
  Genv.find_var_info ge.genv_genv Search.Block.cartesian
kernel_rfl var_linelength : Genv.find_var_info sparseGe.genv_genv SparseBlock.linelength =
  Genv.find_var_info ge.genv_genv Search.Block.linelength
kernel_rfl var_outfile : Genv.find_var_info sparseGe.genv_genv SparseBlock.outfile =
  Genv.find_var_info ge.genv_genv Search.Block.outfile
kernel_rfl var_userautomproc : Genv.find_var_info sparseGe.genv_genv SparseBlock.userautomproc =
  Genv.find_var_info ge.genv_genv Search.Block.userautomproc
kernel_rfl var_userlevelproc : Genv.find_var_info sparseGe.genv_genv SparseBlock.userlevelproc =
  Genv.find_var_info ge.genv_genv Search.Block.userlevelproc
kernel_rfl var_usernodeproc : Genv.find_var_info sparseGe.genv_genv SparseBlock.usernodeproc =
  Genv.find_var_info ge.genv_genv Search.Block.usernodeproc
kernel_rfl var_usercanonproc : Genv.find_var_info sparseGe.genv_genv SparseBlock.usercanonproc =
  Genv.find_var_info ge.genv_genv Search.Block.usercanonproc
kernel_rfl var_invarproc : Genv.find_var_info sparseGe.genv_genv SparseBlock.invarproc =
  Genv.find_var_info ge.genv_genv Search.Block.invarproc
kernel_rfl var_tcLevel : Genv.find_var_info sparseGe.genv_genv SparseBlock.tcLevel =
  Genv.find_var_info ge.genv_genv Search.Block.tcLevel
kernel_rfl var_mininvarlevel : Genv.find_var_info sparseGe.genv_genv SparseBlock.mininvarlevel =
  Genv.find_var_info ge.genv_genv Search.Block.mininvarlevel
kernel_rfl var_maxinvarlevel : Genv.find_var_info sparseGe.genv_genv SparseBlock.maxinvarlevel =
  Genv.find_var_info ge.genv_genv Search.Block.maxinvarlevel
kernel_rfl var_invararg : Genv.find_var_info sparseGe.genv_genv SparseBlock.invararg =
  Genv.find_var_info ge.genv_genv Search.Block.invararg
kernel_rfl var_dispatch : Genv.find_var_info sparseGe.genv_genv SparseBlock.dispatch =
  Genv.find_var_info ge.genv_genv Search.Block.dispatch
kernel_rfl var_orbits : Genv.find_var_info sparseGe.genv_genv SparseBlock.orbits =
  Genv.find_var_info ge.genv_genv Search.Block.orbits
kernel_rfl var_domarkers : Genv.find_var_info sparseGe.genv_genv SparseBlock.domarkers =
  Genv.find_var_info ge.genv_genv Search.Block.domarkers
kernel_rfl var_doschreier : Genv.find_var_info sparseGe.genv_genv SparseBlock.doschreier =
  Genv.find_var_info ge.genv_genv Search.Block.doschreier
kernel_rfl var_m : Genv.find_var_info sparseGe.genv_genv SparseBlock.m =
  Genv.find_var_info ge.genv_genv Search.Block.m
kernel_rfl var_n : Genv.find_var_info sparseGe.genv_genv SparseBlock.n =
  Genv.find_var_info ge.genv_genv Search.Block.n
kernel_rfl var_g : Genv.find_var_info sparseGe.genv_genv SparseBlock.g =
  Genv.find_var_info ge.genv_genv Search.Block.g
kernel_rfl var_canong : Genv.find_var_info sparseGe.genv_genv SparseBlock.canong =
  Genv.find_var_info ge.genv_genv Search.Block.canong
kernel_rfl var_stats : Genv.find_var_info sparseGe.genv_genv SparseBlock.stats =
  Genv.find_var_info ge.genv_genv Search.Block.stats
kernel_rfl var_gcaFirst : Genv.find_var_info sparseGe.genv_genv SparseBlock.gcaFirst =
  Genv.find_var_info ge.genv_genv Search.Block.gcaFirst
kernel_rfl var_gcaCanon : Genv.find_var_info sparseGe.genv_genv SparseBlock.gcaCanon =
  Genv.find_var_info ge.genv_genv Search.Block.gcaCanon
kernel_rfl var_noncheaplevel : Genv.find_var_info sparseGe.genv_genv SparseBlock.noncheaplevel =
  Genv.find_var_info ge.genv_genv Search.Block.noncheaplevel
kernel_rfl var_allsamelevel : Genv.find_var_info sparseGe.genv_genv SparseBlock.allsamelevel =
  Genv.find_var_info ge.genv_genv Search.Block.allsamelevel
kernel_rfl var_eqlevFirst : Genv.find_var_info sparseGe.genv_genv SparseBlock.eqlevFirst =
  Genv.find_var_info ge.genv_genv Search.Block.eqlevFirst
kernel_rfl var_eqlevCanon : Genv.find_var_info sparseGe.genv_genv SparseBlock.eqlevCanon =
  Genv.find_var_info ge.genv_genv Search.Block.eqlevCanon
kernel_rfl var_compCanon : Genv.find_var_info sparseGe.genv_genv SparseBlock.compCanon =
  Genv.find_var_info ge.genv_genv Search.Block.compCanon
kernel_rfl var_samerows : Genv.find_var_info sparseGe.genv_genv SparseBlock.samerows =
  Genv.find_var_info ge.genv_genv Search.Block.samerows
kernel_rfl var_canonlevel : Genv.find_var_info sparseGe.genv_genv SparseBlock.canonlevel =
  Genv.find_var_info ge.genv_genv Search.Block.canonlevel
kernel_rfl var_stabvertex : Genv.find_var_info sparseGe.genv_genv SparseBlock.stabvertex =
  Genv.find_var_info ge.genv_genv Search.Block.stabvertex
kernel_rfl var_cosetindex : Genv.find_var_info sparseGe.genv_genv SparseBlock.cosetindex =
  Genv.find_var_info ge.genv_genv Search.Block.cosetindex
kernel_rfl var_needshortprune : Genv.find_var_info sparseGe.genv_genv SparseBlock.needshortprune =
  Genv.find_var_info ge.genv_genv Search.Block.needshortprune
kernel_rfl var_tcnode0 : Genv.find_var_info sparseGe.genv_genv SparseBlock.tcnode0 =
  Genv.find_var_info ge.genv_genv Search.Block.tcnode0
kernel_rfl var_allocM : Genv.find_var_info sparseGe.genv_genv SparseBlock.allocM =
  Genv.find_var_info ge.genv_genv Search.Block.allocM
kernel_rfl var_workspace : Genv.find_var_info sparseGe.genv_genv SparseBlock.workspace =
  Genv.find_var_info ge.genv_genv Search.Block.workspace
kernel_rfl var_worktop : Genv.find_var_info sparseGe.genv_genv SparseBlock.worktop =
  Genv.find_var_info ge.genv_genv Search.Block.worktop
kernel_rfl var_fmptr : Genv.find_var_info sparseGe.genv_genv SparseBlock.fmptr =
  Genv.find_var_info ge.genv_genv Search.Block.fmptr
kernel_rfl var_invapplics : Genv.find_var_info sparseGe.genv_genv SparseBlock.invapplics =
  Genv.find_var_info ge.genv_genv Search.Block.invapplics
kernel_rfl var_invsuccesses : Genv.find_var_info sparseGe.genv_genv SparseBlock.invsuccesses =
  Genv.find_var_info ge.genv_genv Search.Block.invsuccesses
kernel_rfl var_invarsuclevel : Genv.find_var_info sparseGe.genv_genv SparseBlock.invarsuclevel =
  Genv.find_var_info ge.genv_genv Search.Block.invarsuclevel
kernel_rfl var_killRequest : Genv.find_var_info sparseGe.genv_genv SparseBlock.killRequest =
  Genv.find_var_info ge.genv_genv Search.Block.killRequest
kernel_rfl distinct : decide (List.Pairwise (· ≠ ·)
    [SparseBlock.nextelement, SparseBlock.leftbit, SparseBlock.nautilBit, SparseBlock.malloc, SparseBlock.free, SparseBlock.zalloc, SparseBlock.nautilWorkperm, SparseBlock.nautilWorkpermSz, SparseBlock.permset, SparseBlock.nautyBit, SparseBlock.nautyCanonlab, SparseBlock.nautyCanonlabSz, SparseBlock.nautyDefltwork, SparseBlock.nautyDefltworkSz, SparseBlock.nautyActive, SparseBlock.nautyActiveSz, SparseBlock.nautyCanoncode, SparseBlock.nautyCanoncodeSz, SparseBlock.nautyFixedpts, SparseBlock.nautyFixedptsSz, SparseBlock.nautyFirstcode, SparseBlock.nautyFirstcodeSz, SparseBlock.nautyWorkperm, SparseBlock.nautyWorkpermSz, SparseBlock.nautyFirsttc, SparseBlock.nautyFirsttcSz, SparseBlock.nautyFirstlab, SparseBlock.nautyFirstlabSz, SparseBlock.getcanon, SparseBlock.digraph, SparseBlock.writeautoms, SparseBlock.cartesian, SparseBlock.linelength, SparseBlock.outfile, SparseBlock.userautomproc, SparseBlock.userlevelproc, SparseBlock.usernodeproc, SparseBlock.usercanonproc, SparseBlock.invarproc, SparseBlock.tcLevel, SparseBlock.mininvarlevel, SparseBlock.maxinvarlevel, SparseBlock.invararg, SparseBlock.dispatch, SparseBlock.orbits, SparseBlock.domarkers, SparseBlock.doschreier, SparseBlock.m, SparseBlock.n, SparseBlock.g, SparseBlock.canong, SparseBlock.stats, SparseBlock.gcaFirst, SparseBlock.gcaCanon, SparseBlock.noncheaplevel, SparseBlock.allsamelevel, SparseBlock.eqlevFirst, SparseBlock.eqlevCanon, SparseBlock.compCanon, SparseBlock.samerows, SparseBlock.canonlevel, SparseBlock.stabvertex, SparseBlock.cosetindex, SparseBlock.needshortprune, SparseBlock.tcnode0, SparseBlock.allocM, SparseBlock.workspace, SparseBlock.worktop, SparseBlock.fmptr, SparseBlock.invapplics, SparseBlock.invsuccesses, SparseBlock.invarsuclevel, SparseBlock.killRequest, SparseBlock.firstpathnodeFn, SparseBlock.othernodeFn, SparseBlock.firstterminalFn, SparseBlock.processnodeFn, SparseBlock.recoverFn, SparseBlock.nautyFn, SparseBlock.maketargetcellFn, SparseBlock.breakoutFn, SparseBlock.fmpermFn, SparseBlock.fmptnFn, SparseBlock.orbjoinFn, SparseBlock.shortpruneFn, SparseBlock.longpruneFn, SparseBlock.dorefFn, SparseBlock.nautilCheck, SparseBlock.nautilFreedyn, SparseBlock.nautyFreedyn]) = true

end SparseEnv

/-- The sparse program's blocks. -/
@[reducible] def NautyEnv.sparse : NautyEnv sparseGe where
  nextelement := SparseBlock.nextelement
  leftbit := SparseBlock.leftbit
  nautilBit := SparseBlock.nautilBit
  malloc := SparseBlock.malloc
  free := SparseBlock.free
  zalloc := SparseBlock.zalloc
  nautilWorkperm := SparseBlock.nautilWorkperm
  nautilWorkpermSz := SparseBlock.nautilWorkpermSz
  permset := SparseBlock.permset
  nautyBit := SparseBlock.nautyBit
  nautyCanonlab := SparseBlock.nautyCanonlab
  nautyCanonlabSz := SparseBlock.nautyCanonlabSz
  nautyDefltwork := SparseBlock.nautyDefltwork
  nautyDefltworkSz := SparseBlock.nautyDefltworkSz
  nautyActive := SparseBlock.nautyActive
  nautyActiveSz := SparseBlock.nautyActiveSz
  nautyCanoncode := SparseBlock.nautyCanoncode
  nautyCanoncodeSz := SparseBlock.nautyCanoncodeSz
  nautyFixedpts := SparseBlock.nautyFixedpts
  nautyFixedptsSz := SparseBlock.nautyFixedptsSz
  nautyFirstcode := SparseBlock.nautyFirstcode
  nautyFirstcodeSz := SparseBlock.nautyFirstcodeSz
  nautyWorkperm := SparseBlock.nautyWorkperm
  nautyWorkpermSz := SparseBlock.nautyWorkpermSz
  nautyFirsttc := SparseBlock.nautyFirsttc
  nautyFirsttcSz := SparseBlock.nautyFirsttcSz
  nautyFirstlab := SparseBlock.nautyFirstlab
  nautyFirstlabSz := SparseBlock.nautyFirstlabSz
  getcanon := SparseBlock.getcanon
  digraph := SparseBlock.digraph
  writeautoms := SparseBlock.writeautoms
  cartesian := SparseBlock.cartesian
  linelength := SparseBlock.linelength
  outfile := SparseBlock.outfile
  userautomproc := SparseBlock.userautomproc
  userlevelproc := SparseBlock.userlevelproc
  usernodeproc := SparseBlock.usernodeproc
  usercanonproc := SparseBlock.usercanonproc
  invarproc := SparseBlock.invarproc
  tcLevel := SparseBlock.tcLevel
  mininvarlevel := SparseBlock.mininvarlevel
  maxinvarlevel := SparseBlock.maxinvarlevel
  invararg := SparseBlock.invararg
  dispatch := SparseBlock.dispatch
  orbits := SparseBlock.orbits
  domarkers := SparseBlock.domarkers
  doschreier := SparseBlock.doschreier
  m := SparseBlock.m
  n := SparseBlock.n
  g := SparseBlock.g
  canong := SparseBlock.canong
  stats := SparseBlock.stats
  gcaFirst := SparseBlock.gcaFirst
  gcaCanon := SparseBlock.gcaCanon
  noncheaplevel := SparseBlock.noncheaplevel
  allsamelevel := SparseBlock.allsamelevel
  eqlevFirst := SparseBlock.eqlevFirst
  eqlevCanon := SparseBlock.eqlevCanon
  compCanon := SparseBlock.compCanon
  samerows := SparseBlock.samerows
  canonlevel := SparseBlock.canonlevel
  stabvertex := SparseBlock.stabvertex
  cosetindex := SparseBlock.cosetindex
  needshortprune := SparseBlock.needshortprune
  tcnode0 := SparseBlock.tcnode0
  allocM := SparseBlock.allocM
  workspace := SparseBlock.workspace
  worktop := SparseBlock.worktop
  fmptr := SparseBlock.fmptr
  invapplics := SparseBlock.invapplics
  invsuccesses := SparseBlock.invsuccesses
  invarsuclevel := SparseBlock.invarsuclevel
  killRequest := SparseBlock.killRequest
  firstpathnodeFn := SparseBlock.firstpathnodeFn
  othernodeFn := SparseBlock.othernodeFn
  firstterminalFn := SparseBlock.firstterminalFn
  processnodeFn := SparseBlock.processnodeFn
  recoverFn := SparseBlock.recoverFn
  nautyFn := SparseBlock.nautyFn
  maketargetcellFn := SparseBlock.maketargetcellFn
  breakoutFn := SparseBlock.breakoutFn
  fmpermFn := SparseBlock.fmpermFn
  fmptnFn := SparseBlock.fmptnFn
  orbjoinFn := SparseBlock.orbjoinFn
  shortpruneFn := SparseBlock.shortpruneFn
  longpruneFn := SparseBlock.longpruneFn
  dorefFn := SparseBlock.dorefFn
  nautilCheck := SparseBlock.nautilCheck
  nautilFreedyn := SparseBlock.nautilFreedyn
  nautyFreedyn := SparseBlock.nautyFreedyn
  find_nextelement := SparseEnv.find_nextelement
  find_leftbit := SparseEnv.find_leftbit
  find_nautilBit := SparseEnv.find_nautilBit
  find_malloc := SparseEnv.find_malloc
  find_free := SparseEnv.find_free
  find_zalloc := SparseEnv.find_zalloc
  find_nautilWorkperm := SparseEnv.find_nautilWorkperm
  find_nautilWorkpermSz := SparseEnv.find_nautilWorkpermSz
  find_permset := SparseEnv.find_permset
  find_nautyBit := SparseEnv.find_nautyBit
  find_nautyCanonlab := SparseEnv.find_nautyCanonlab
  find_nautyCanonlabSz := SparseEnv.find_nautyCanonlabSz
  find_nautyDefltwork := SparseEnv.find_nautyDefltwork
  find_nautyDefltworkSz := SparseEnv.find_nautyDefltworkSz
  find_nautyActive := SparseEnv.find_nautyActive
  find_nautyActiveSz := SparseEnv.find_nautyActiveSz
  find_nautyCanoncode := SparseEnv.find_nautyCanoncode
  find_nautyCanoncodeSz := SparseEnv.find_nautyCanoncodeSz
  find_nautyFixedpts := SparseEnv.find_nautyFixedpts
  find_nautyFixedptsSz := SparseEnv.find_nautyFixedptsSz
  find_nautyFirstcode := SparseEnv.find_nautyFirstcode
  find_nautyFirstcodeSz := SparseEnv.find_nautyFirstcodeSz
  find_nautyWorkperm := SparseEnv.find_nautyWorkperm
  find_nautyWorkpermSz := SparseEnv.find_nautyWorkpermSz
  find_nautyFirsttc := SparseEnv.find_nautyFirsttc
  find_nautyFirsttcSz := SparseEnv.find_nautyFirsttcSz
  find_nautyFirstlab := SparseEnv.find_nautyFirstlab
  find_nautyFirstlabSz := SparseEnv.find_nautyFirstlabSz
  find_getcanon := SparseEnv.find_getcanon
  find_digraph := SparseEnv.find_digraph
  find_writeautoms := SparseEnv.find_writeautoms
  find_cartesian := SparseEnv.find_cartesian
  find_linelength := SparseEnv.find_linelength
  find_outfile := SparseEnv.find_outfile
  find_userautomproc := SparseEnv.find_userautomproc
  find_userlevelproc := SparseEnv.find_userlevelproc
  find_usernodeproc := SparseEnv.find_usernodeproc
  find_usercanonproc := SparseEnv.find_usercanonproc
  find_invarproc := SparseEnv.find_invarproc
  find_tcLevel := SparseEnv.find_tcLevel
  find_mininvarlevel := SparseEnv.find_mininvarlevel
  find_maxinvarlevel := SparseEnv.find_maxinvarlevel
  find_invararg := SparseEnv.find_invararg
  find_dispatch := SparseEnv.find_dispatch
  find_orbits := SparseEnv.find_orbits
  find_domarkers := SparseEnv.find_domarkers
  find_doschreier := SparseEnv.find_doschreier
  find_m := SparseEnv.find_m
  find_n := SparseEnv.find_n
  find_g := SparseEnv.find_g
  find_canong := SparseEnv.find_canong
  find_stats := SparseEnv.find_stats
  find_gcaFirst := SparseEnv.find_gcaFirst
  find_gcaCanon := SparseEnv.find_gcaCanon
  find_noncheaplevel := SparseEnv.find_noncheaplevel
  find_allsamelevel := SparseEnv.find_allsamelevel
  find_eqlevFirst := SparseEnv.find_eqlevFirst
  find_eqlevCanon := SparseEnv.find_eqlevCanon
  find_compCanon := SparseEnv.find_compCanon
  find_samerows := SparseEnv.find_samerows
  find_canonlevel := SparseEnv.find_canonlevel
  find_stabvertex := SparseEnv.find_stabvertex
  find_cosetindex := SparseEnv.find_cosetindex
  find_needshortprune := SparseEnv.find_needshortprune
  find_tcnode0 := SparseEnv.find_tcnode0
  find_allocM := SparseEnv.find_allocM
  find_workspace := SparseEnv.find_workspace
  find_worktop := SparseEnv.find_worktop
  find_fmptr := SparseEnv.find_fmptr
  find_invapplics := SparseEnv.find_invapplics
  find_invsuccesses := SparseEnv.find_invsuccesses
  find_invarsuclevel := SparseEnv.find_invarsuclevel
  find_killRequest := SparseEnv.find_killRequest
  find_firstpathnodeFn := SparseEnv.find_firstpathnodeFn
  find_othernodeFn := SparseEnv.find_othernodeFn
  find_firstterminalFn := SparseEnv.find_firstterminalFn
  find_processnodeFn := SparseEnv.find_processnodeFn
  find_recoverFn := SparseEnv.find_recoverFn
  find_nautyFn := SparseEnv.find_nautyFn
  find_maketargetcellFn := SparseEnv.find_maketargetcellFn
  find_breakoutFn := SparseEnv.find_breakoutFn
  find_fmpermFn := SparseEnv.find_fmpermFn
  find_fmptnFn := SparseEnv.find_fmptnFn
  find_orbjoinFn := SparseEnv.find_orbjoinFn
  find_shortpruneFn := SparseEnv.find_shortpruneFn
  find_longpruneFn := SparseEnv.find_longpruneFn
  find_dorefFn := SparseEnv.find_dorefFn
  find_nautilCheck := SparseEnv.find_nautilCheck
  find_nautilFreedyn := SparseEnv.find_nautilFreedyn
  find_nautyFreedyn := SparseEnv.find_nautyFreedyn
  funct_nextelement := SparseEnv.funct_nextelement
  funct_malloc := SparseEnv.funct_malloc
  funct_free := SparseEnv.funct_free
  funct_zalloc := SparseEnv.funct_zalloc
  funct_permset := SparseEnv.funct_permset
  funct_firstpathnodeFn := SparseEnv.funct_firstpathnodeFn
  funct_othernodeFn := SparseEnv.funct_othernodeFn
  funct_firstterminalFn := SparseEnv.funct_firstterminalFn
  funct_processnodeFn := SparseEnv.funct_processnodeFn
  funct_recoverFn := SparseEnv.funct_recoverFn
  funct_nautyFn := SparseEnv.funct_nautyFn
  funct_maketargetcellFn := SparseEnv.funct_maketargetcellFn
  funct_breakoutFn := SparseEnv.funct_breakoutFn
  funct_fmpermFn := SparseEnv.funct_fmpermFn
  funct_fmptnFn := SparseEnv.funct_fmptnFn
  funct_orbjoinFn := SparseEnv.funct_orbjoinFn
  funct_shortpruneFn := SparseEnv.funct_shortpruneFn
  funct_longpruneFn := SparseEnv.funct_longpruneFn
  funct_dorefFn := SparseEnv.funct_dorefFn
  funct_nautilCheck := SparseEnv.funct_nautilCheck
  funct_nautilFreedyn := SparseEnv.funct_nautilFreedyn
  funct_nautyFreedyn := SparseEnv.funct_nautyFreedyn
  var_leftbit := SparseEnv.var_leftbit
  var_nautilBit := SparseEnv.var_nautilBit
  var_nautilWorkperm := SparseEnv.var_nautilWorkperm
  var_nautilWorkpermSz := SparseEnv.var_nautilWorkpermSz
  var_nautyBit := SparseEnv.var_nautyBit
  var_nautyCanonlab := SparseEnv.var_nautyCanonlab
  var_nautyCanonlabSz := SparseEnv.var_nautyCanonlabSz
  var_nautyDefltwork := SparseEnv.var_nautyDefltwork
  var_nautyDefltworkSz := SparseEnv.var_nautyDefltworkSz
  var_nautyActive := SparseEnv.var_nautyActive
  var_nautyActiveSz := SparseEnv.var_nautyActiveSz
  var_nautyCanoncode := SparseEnv.var_nautyCanoncode
  var_nautyCanoncodeSz := SparseEnv.var_nautyCanoncodeSz
  var_nautyFixedpts := SparseEnv.var_nautyFixedpts
  var_nautyFixedptsSz := SparseEnv.var_nautyFixedptsSz
  var_nautyFirstcode := SparseEnv.var_nautyFirstcode
  var_nautyFirstcodeSz := SparseEnv.var_nautyFirstcodeSz
  var_nautyWorkperm := SparseEnv.var_nautyWorkperm
  var_nautyWorkpermSz := SparseEnv.var_nautyWorkpermSz
  var_nautyFirsttc := SparseEnv.var_nautyFirsttc
  var_nautyFirsttcSz := SparseEnv.var_nautyFirsttcSz
  var_nautyFirstlab := SparseEnv.var_nautyFirstlab
  var_nautyFirstlabSz := SparseEnv.var_nautyFirstlabSz
  var_getcanon := SparseEnv.var_getcanon
  var_digraph := SparseEnv.var_digraph
  var_writeautoms := SparseEnv.var_writeautoms
  var_cartesian := SparseEnv.var_cartesian
  var_linelength := SparseEnv.var_linelength
  var_outfile := SparseEnv.var_outfile
  var_userautomproc := SparseEnv.var_userautomproc
  var_userlevelproc := SparseEnv.var_userlevelproc
  var_usernodeproc := SparseEnv.var_usernodeproc
  var_usercanonproc := SparseEnv.var_usercanonproc
  var_invarproc := SparseEnv.var_invarproc
  var_tcLevel := SparseEnv.var_tcLevel
  var_mininvarlevel := SparseEnv.var_mininvarlevel
  var_maxinvarlevel := SparseEnv.var_maxinvarlevel
  var_invararg := SparseEnv.var_invararg
  var_dispatch := SparseEnv.var_dispatch
  var_orbits := SparseEnv.var_orbits
  var_domarkers := SparseEnv.var_domarkers
  var_doschreier := SparseEnv.var_doschreier
  var_m := SparseEnv.var_m
  var_n := SparseEnv.var_n
  var_g := SparseEnv.var_g
  var_canong := SparseEnv.var_canong
  var_stats := SparseEnv.var_stats
  var_gcaFirst := SparseEnv.var_gcaFirst
  var_gcaCanon := SparseEnv.var_gcaCanon
  var_noncheaplevel := SparseEnv.var_noncheaplevel
  var_allsamelevel := SparseEnv.var_allsamelevel
  var_eqlevFirst := SparseEnv.var_eqlevFirst
  var_eqlevCanon := SparseEnv.var_eqlevCanon
  var_compCanon := SparseEnv.var_compCanon
  var_samerows := SparseEnv.var_samerows
  var_canonlevel := SparseEnv.var_canonlevel
  var_stabvertex := SparseEnv.var_stabvertex
  var_cosetindex := SparseEnv.var_cosetindex
  var_needshortprune := SparseEnv.var_needshortprune
  var_tcnode0 := SparseEnv.var_tcnode0
  var_allocM := SparseEnv.var_allocM
  var_workspace := SparseEnv.var_workspace
  var_worktop := SparseEnv.var_worktop
  var_fmptr := SparseEnv.var_fmptr
  var_invapplics := SparseEnv.var_invapplics
  var_invsuccesses := SparseEnv.var_invsuccesses
  var_invarsuclevel := SparseEnv.var_invarsuclevel
  var_killRequest := SparseEnv.var_killRequest
  distinct := of_decide_eq_true SparseEnv.distinct

end NautyVerified.Program
