import NautyVerified.Program.Dense

/-!
# The blocks of nauty.c's globals and of the functions the search calls

Generated from the dense program's symbol table; each `find_*` lemma is
checked by the kernel.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Program NautyVerified.Source

namespace Block

def getcanon : Common.Values.block := PArith.BinPos.Pos.of_nat 256
def digraph : Common.Values.block := PArith.BinPos.Pos.of_nat 61
def writeautoms : Common.Values.block := PArith.BinPos.Pos.of_nat 223
def cartesian : Common.Values.block := PArith.BinPos.Pos.of_nat 150
def linelength : Common.Values.block := PArith.BinPos.Pos.of_nat 291
def outfile : Common.Values.block := PArith.BinPos.Pos.of_nat 41
def userautomproc : Common.Values.block := PArith.BinPos.Pos.of_nat 206
def userlevelproc : Common.Values.block := PArith.BinPos.Pos.of_nat 130
def usernodeproc : Common.Values.block := PArith.BinPos.Pos.of_nat 273
def usercanonproc : Common.Values.block := PArith.BinPos.Pos.of_nat 84
def invarproc : Common.Values.block := PArith.BinPos.Pos.of_nat 241
def tcLevel : Common.Values.block := PArith.BinPos.Pos.of_nat 174
def mininvarlevel : Common.Values.block := PArith.BinPos.Pos.of_nat 308
def maxinvarlevel : Common.Values.block := PArith.BinPos.Pos.of_nat 5
def invararg : Common.Values.block := PArith.BinPos.Pos.of_nat 178
def dispatch : Common.Values.block := PArith.BinPos.Pos.of_nat 91
def orbits : Common.Values.block := PArith.BinPos.Pos.of_nat 157
def domarkers : Common.Values.block := PArith.BinPos.Pos.of_nat 22
def doschreier : Common.Values.block := PArith.BinPos.Pos.of_nat 108
def m : Common.Values.block := PArith.BinPos.Pos.of_nat 259
def n : Common.Values.block := PArith.BinPos.Pos.of_nat 64
def g : Common.Values.block := PArith.BinPos.Pos.of_nat 227
def canong : Common.Values.block := PArith.BinPos.Pos.of_nat 152
def stats : Common.Values.block := PArith.BinPos.Pos.of_nat 294
def gcaFirst : Common.Values.block := PArith.BinPos.Pos.of_nat 209
def gcaCanon : Common.Values.block := PArith.BinPos.Pos.of_nat 276
def noncheaplevel : Common.Values.block := PArith.BinPos.Pos.of_nat 244
def allsamelevel : Common.Values.block := PArith.BinPos.Pos.of_nat 311
def eqlevFirst : Common.Values.block := PArith.BinPos.Pos.of_nat 177
def eqlevCanon : Common.Values.block := PArith.BinPos.Pos.of_nat 247
def compCanon : Common.Values.block := PArith.BinPos.Pos.of_nat 212
def samerows : Common.Values.block := PArith.BinPos.Pos.of_nat 279
def canonlevel : Common.Values.block := PArith.BinPos.Pos.of_nat 194
def stabvertex : Common.Values.block := PArith.BinPos.Pos.of_nat 110
def cosetindex : Common.Values.block := PArith.BinPos.Pos.of_nat 66
def needshortprune : Common.Values.block := PArith.BinPos.Pos.of_nat 155
def tcnode0 : Common.Values.block := PArith.BinPos.Pos.of_nat 60
def allocM : Common.Values.block := PArith.BinPos.Pos.of_nat 149
def workspace : Common.Values.block := PArith.BinPos.Pos.of_nat 40
def worktop : Common.Values.block := PArith.BinPos.Pos.of_nat 129
def fmptr : Common.Values.block := PArith.BinPos.Pos.of_nat 83
def invapplics : Common.Values.block := PArith.BinPos.Pos.of_nat 18
def invsuccesses : Common.Values.block := PArith.BinPos.Pos.of_nat 189
def invarsuclevel : Common.Values.block := PArith.BinPos.Pos.of_nat 105
def killRequest : Common.Values.block := PArith.BinPos.Pos.of_nat 32
def firstpathnodeFn : Common.Values.block := PArith.BinPos.Pos.of_nat 12
def othernodeFn : Common.Values.block := PArith.BinPos.Pos.of_nat 226
def firstterminalFn : Common.Values.block := PArith.BinPos.Pos.of_nat 258
def processnodeFn : Common.Values.block := PArith.BinPos.Pos.of_nat 89
def recoverFn : Common.Values.block := PArith.BinPos.Pos.of_nat 293
def nautyFn : Common.Values.block := PArith.BinPos.Pos.of_nat 96
def densenautyFn : Common.Values.block := PArith.BinPos.Pos.of_nat 175
def isautomFn : Common.Values.block := PArith.BinPos.Pos.of_nat 58
def testcanlabFn : Common.Values.block := PArith.BinPos.Pos.of_nat 222
def updatecanFn : Common.Values.block := PArith.BinPos.Pos.of_nat 147
def cheapautomFn : Common.Values.block := PArith.BinPos.Pos.of_nat 205
def targetcellFn : Common.Values.block := PArith.BinPos.Pos.of_nat 127
def maketargetcellFn : Common.Values.block := PArith.BinPos.Pos.of_nat 306
def breakoutFn : Common.Values.block := PArith.BinPos.Pos.of_nat 204
def fmpermFn : Common.Values.block := PArith.BinPos.Pos.of_nat 81
def fmptnFn : Common.Values.block := PArith.BinPos.Pos.of_nat 239
def orbjoinFn : Common.Values.block := PArith.BinPos.Pos.of_nat 184
def shortpruneFn : Common.Values.block := PArith.BinPos.Pos.of_nat 252
def longpruneFn : Common.Values.block := PArith.BinPos.Pos.of_nat 171
def dorefFn : Common.Values.block := PArith.BinPos.Pos.of_nat 126
def permsetFn : Common.Values.block := PArith.BinPos.Pos.of_nat 300
def dispatchGraph : Common.Values.block := PArith.BinPos.Pos.of_nat 243
/-- naugraph.c's `naugraph_freedyn` (the dispatch table's `freedyn`). -/
def naugraphFreedyn : Common.Values.block := PArith.BinPos.Pos.of_nat 277
end Block

kernel_rfl find_getcanon : Genv.find_symbol ge.genv_genv dense.id.«nauty:getcanon» = some Block.getcanon
kernel_rfl find_digraph : Genv.find_symbol ge.genv_genv dense.id.«nauty:digraph» = some Block.digraph
kernel_rfl find_writeautoms : Genv.find_symbol ge.genv_genv dense.id.«nauty:writeautoms» = some Block.writeautoms
kernel_rfl find_cartesian : Genv.find_symbol ge.genv_genv dense.id.«nauty:cartesian» = some Block.cartesian
kernel_rfl find_linelength : Genv.find_symbol ge.genv_genv dense.id.«nauty:linelength» = some Block.linelength
kernel_rfl find_outfile : Genv.find_symbol ge.genv_genv dense.id.«nauty:outfile» = some Block.outfile
kernel_rfl find_userautomproc : Genv.find_symbol ge.genv_genv dense.id.«nauty:userautomproc» = some Block.userautomproc
kernel_rfl find_userlevelproc : Genv.find_symbol ge.genv_genv dense.id.«nauty:userlevelproc» = some Block.userlevelproc
kernel_rfl find_usernodeproc : Genv.find_symbol ge.genv_genv dense.id.«nauty:usernodeproc» = some Block.usernodeproc
kernel_rfl find_usercanonproc : Genv.find_symbol ge.genv_genv dense.id.«nauty:usercanonproc» = some Block.usercanonproc
kernel_rfl find_invarproc : Genv.find_symbol ge.genv_genv dense.id.«nauty:invarproc» = some Block.invarproc
kernel_rfl find_tcLevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:tc_level» = some Block.tcLevel
kernel_rfl find_mininvarlevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:mininvarlevel» = some Block.mininvarlevel
kernel_rfl find_maxinvarlevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:maxinvarlevel» = some Block.maxinvarlevel
kernel_rfl find_invararg : Genv.find_symbol ge.genv_genv dense.id.«nauty:invararg» = some Block.invararg
kernel_rfl find_dispatch : Genv.find_symbol ge.genv_genv dense.id.«nauty:dispatch» = some Block.dispatch
kernel_rfl find_orbits : Genv.find_symbol ge.genv_genv dense.id.«nauty:orbits» = some Block.orbits
kernel_rfl find_domarkers : Genv.find_symbol ge.genv_genv dense.id.«nauty:domarkers» = some Block.domarkers
kernel_rfl find_doschreier : Genv.find_symbol ge.genv_genv dense.id.«nauty:doschreier» = some Block.doschreier
kernel_rfl find_m : Genv.find_symbol ge.genv_genv dense.id.«nauty:m» = some Block.m
kernel_rfl find_n : Genv.find_symbol ge.genv_genv dense.id.«nauty:n» = some Block.n
kernel_rfl find_g : Genv.find_symbol ge.genv_genv dense.id.«nauty:g» = some Block.g
kernel_rfl find_canong : Genv.find_symbol ge.genv_genv dense.id.«nauty:canong» = some Block.canong
kernel_rfl find_stats : Genv.find_symbol ge.genv_genv dense.id.«nauty:stats» = some Block.stats
kernel_rfl find_gcaFirst : Genv.find_symbol ge.genv_genv dense.id.«nauty:gca_first» = some Block.gcaFirst
kernel_rfl find_gcaCanon : Genv.find_symbol ge.genv_genv dense.id.«nauty:gca_canon» = some Block.gcaCanon
kernel_rfl find_noncheaplevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:noncheaplevel» = some Block.noncheaplevel
kernel_rfl find_allsamelevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:allsamelevel» = some Block.allsamelevel
kernel_rfl find_eqlevFirst : Genv.find_symbol ge.genv_genv dense.id.«nauty:eqlev_first» = some Block.eqlevFirst
kernel_rfl find_eqlevCanon : Genv.find_symbol ge.genv_genv dense.id.«nauty:eqlev_canon» = some Block.eqlevCanon
kernel_rfl find_compCanon : Genv.find_symbol ge.genv_genv dense.id.«nauty:comp_canon» = some Block.compCanon
kernel_rfl find_samerows : Genv.find_symbol ge.genv_genv dense.id.«nauty:samerows» = some Block.samerows
kernel_rfl find_canonlevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:canonlevel» = some Block.canonlevel
kernel_rfl find_stabvertex : Genv.find_symbol ge.genv_genv dense.id.«nauty:stabvertex» = some Block.stabvertex
kernel_rfl find_cosetindex : Genv.find_symbol ge.genv_genv dense.id.«nauty:cosetindex» = some Block.cosetindex
kernel_rfl find_needshortprune : Genv.find_symbol ge.genv_genv dense.id.«nauty:needshortprune» = some Block.needshortprune
kernel_rfl find_tcnode0 : Genv.find_symbol ge.genv_genv dense.id.«nauty:tcnode0» = some Block.tcnode0
kernel_rfl find_allocM : Genv.find_symbol ge.genv_genv dense.id.«nauty:alloc_m» = some Block.allocM
kernel_rfl find_workspace : Genv.find_symbol ge.genv_genv dense.id.«nauty:workspace» = some Block.workspace
kernel_rfl find_worktop : Genv.find_symbol ge.genv_genv dense.id.«nauty:worktop» = some Block.worktop
kernel_rfl find_fmptr : Genv.find_symbol ge.genv_genv dense.id.«nauty:fmptr» = some Block.fmptr
kernel_rfl find_invapplics : Genv.find_symbol ge.genv_genv dense.id.«nauty:invapplics» = some Block.invapplics
kernel_rfl find_invsuccesses : Genv.find_symbol ge.genv_genv dense.id.«nauty:invsuccesses» = some Block.invsuccesses
kernel_rfl find_invarsuclevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:invarsuclevel» = some Block.invarsuclevel
kernel_rfl find_killRequest : Genv.find_symbol ge.genv_genv dense.id.«nauty_kill_request» = some Block.killRequest
kernel_rfl find_firstpathnodeFn : Genv.find_symbol ge.genv_genv dense.id.«nauty:firstpathnode0» = some Block.firstpathnodeFn
kernel_rfl find_othernodeFn : Genv.find_symbol ge.genv_genv dense.id.«nauty:othernode0» = some Block.othernodeFn
kernel_rfl find_firstterminalFn : Genv.find_symbol ge.genv_genv dense.id.«nauty:firstterminal» = some Block.firstterminalFn
kernel_rfl find_processnodeFn : Genv.find_symbol ge.genv_genv dense.id.«nauty:processnode» = some Block.processnodeFn
kernel_rfl find_recoverFn : Genv.find_symbol ge.genv_genv dense.id.«nauty:recover» = some Block.recoverFn
kernel_rfl find_nautyFn : Genv.find_symbol ge.genv_genv dense.id.«nauty» = some Block.nautyFn
kernel_rfl find_densenautyFn : Genv.find_symbol ge.genv_genv dense.id.«densenauty» = some Block.densenautyFn
kernel_rfl find_isautomFn : Genv.find_symbol ge.genv_genv dense.id.«isautom» = some Block.isautomFn
kernel_rfl find_testcanlabFn : Genv.find_symbol ge.genv_genv dense.id.«testcanlab» = some Block.testcanlabFn
kernel_rfl find_updatecanFn : Genv.find_symbol ge.genv_genv dense.id.«updatecan» = some Block.updatecanFn
kernel_rfl find_cheapautomFn : Genv.find_symbol ge.genv_genv dense.id.«cheapautom» = some Block.cheapautomFn
kernel_rfl find_targetcellFn : Genv.find_symbol ge.genv_genv dense.id.«targetcell» = some Block.targetcellFn
kernel_rfl find_maketargetcellFn : Genv.find_symbol ge.genv_genv dense.id.«maketargetcell» = some Block.maketargetcellFn
kernel_rfl find_breakoutFn : Genv.find_symbol ge.genv_genv dense.id.«breakout» = some Block.breakoutFn
kernel_rfl find_fmpermFn : Genv.find_symbol ge.genv_genv dense.id.«fmperm» = some Block.fmpermFn
kernel_rfl find_fmptnFn : Genv.find_symbol ge.genv_genv dense.id.«fmptn» = some Block.fmptnFn
kernel_rfl find_orbjoinFn : Genv.find_symbol ge.genv_genv dense.id.«orbjoin» = some Block.orbjoinFn
kernel_rfl find_shortpruneFn : Genv.find_symbol ge.genv_genv dense.id.«shortprune» = some Block.shortpruneFn
kernel_rfl find_longpruneFn : Genv.find_symbol ge.genv_genv dense.id.«longprune» = some Block.longpruneFn
kernel_rfl find_dorefFn : Genv.find_symbol ge.genv_genv dense.id.«doref» = some Block.dorefFn
kernel_rfl find_permsetFn : Genv.find_symbol ge.genv_genv dense.id.«permset» = some Block.permsetFn
kernel_rfl find_dispatchGraph : Genv.find_symbol ge.genv_genv dense.id.«dispatch_graph» = some Block.dispatchGraph

kernel_rfl funct_firstpathnodeFn :
  Genv.find_funct_ptr ge.genv_genv Block.firstpathnodeFn = some (.Internal dense.fn.«nauty:firstpathnode0»)
kernel_rfl funct_othernodeFn :
  Genv.find_funct_ptr ge.genv_genv Block.othernodeFn = some (.Internal dense.fn.«nauty:othernode0»)
kernel_rfl funct_firstterminalFn :
  Genv.find_funct_ptr ge.genv_genv Block.firstterminalFn = some (.Internal dense.fn.«nauty:firstterminal»)
kernel_rfl funct_processnodeFn :
  Genv.find_funct_ptr ge.genv_genv Block.processnodeFn = some (.Internal dense.fn.«nauty:processnode»)
kernel_rfl funct_recoverFn :
  Genv.find_funct_ptr ge.genv_genv Block.recoverFn = some (.Internal dense.fn.«nauty:recover»)
kernel_rfl funct_nautyFn :
  Genv.find_funct_ptr ge.genv_genv Block.nautyFn = some (.Internal dense.fn.«nauty»)
kernel_rfl funct_densenautyFn :
  Genv.find_funct_ptr ge.genv_genv Block.densenautyFn = some (.Internal dense.fn.«densenauty»)
kernel_rfl funct_isautomFn :
  Genv.find_funct_ptr ge.genv_genv Block.isautomFn = some (.Internal dense.fn.«isautom»)
kernel_rfl funct_testcanlabFn :
  Genv.find_funct_ptr ge.genv_genv Block.testcanlabFn = some (.Internal dense.fn.«testcanlab»)
kernel_rfl find_naugraphFreedyn :
  Genv.find_symbol ge.genv_genv dense.id.naugraph_freedyn = some Block.naugraphFreedyn
kernel_rfl funct_naugraphFreedyn :
  Genv.find_funct_ptr ge.genv_genv Block.naugraphFreedyn = some (.Internal dense.fn.naugraph_freedyn)
kernel_rfl funct_updatecanFn :
  Genv.find_funct_ptr ge.genv_genv Block.updatecanFn = some (.Internal dense.fn.«updatecan»)
kernel_rfl funct_cheapautomFn :
  Genv.find_funct_ptr ge.genv_genv Block.cheapautomFn = some (.Internal dense.fn.«cheapautom»)
kernel_rfl funct_targetcellFn :
  Genv.find_funct_ptr ge.genv_genv Block.targetcellFn = some (.Internal dense.fn.«targetcell»)
kernel_rfl funct_maketargetcellFn :
  Genv.find_funct_ptr ge.genv_genv Block.maketargetcellFn = some (.Internal dense.fn.«maketargetcell»)
kernel_rfl funct_breakoutFn :
  Genv.find_funct_ptr ge.genv_genv Block.breakoutFn = some (.Internal dense.fn.«breakout»)
kernel_rfl funct_fmpermFn :
  Genv.find_funct_ptr ge.genv_genv Block.fmpermFn = some (.Internal dense.fn.«fmperm»)
kernel_rfl funct_fmptnFn :
  Genv.find_funct_ptr ge.genv_genv Block.fmptnFn = some (.Internal dense.fn.«fmptn»)
kernel_rfl funct_orbjoinFn :
  Genv.find_funct_ptr ge.genv_genv Block.orbjoinFn = some (.Internal dense.fn.«orbjoin»)
kernel_rfl funct_shortpruneFn :
  Genv.find_funct_ptr ge.genv_genv Block.shortpruneFn = some (.Internal dense.fn.«shortprune»)
kernel_rfl funct_longpruneFn :
  Genv.find_funct_ptr ge.genv_genv Block.longpruneFn = some (.Internal dense.fn.«longprune»)
kernel_rfl funct_dorefFn :
  Genv.find_funct_ptr ge.genv_genv Block.dorefFn = some (.Internal dense.fn.«doref»)
kernel_rfl funct_permsetFn :
  Genv.find_funct_ptr ge.genv_genv Block.permsetFn = some (.Internal dense.fn.«permset»)

end NautyVerified.Proofs.Search

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Program NautyVerified.Source

namespace Block
def nautilCheck : Common.Values.block := PArith.BinPos.Pos.of_nat 217
def nautilFreedyn : Common.Values.block := PArith.BinPos.Pos.of_nat 141
def nautyFreedyn : Common.Values.block := PArith.BinPos.Pos.of_nat 183
end Block

kernel_rfl find_nautilCheck :
  Genv.find_symbol ge.genv_genv dense.id.nautil_check = some Block.nautilCheck
kernel_rfl funct_nautilCheck :
  Genv.find_funct_ptr ge.genv_genv Block.nautilCheck = some (.Internal dense.fn.nautil_check)
kernel_rfl find_nautilFreedyn :
  Genv.find_symbol ge.genv_genv dense.id.nautil_freedyn = some Block.nautilFreedyn
kernel_rfl funct_nautilFreedyn :
  Genv.find_funct_ptr ge.genv_genv Block.nautilFreedyn = some (.Internal dense.fn.nautil_freedyn)
kernel_rfl find_nautyFreedyn :
  Genv.find_symbol ge.genv_genv dense.id.nauty_freedyn = some Block.nautyFreedyn
kernel_rfl funct_nautyFreedyn :
  Genv.find_funct_ptr ge.genv_genv Block.nautyFreedyn = some (.Internal dense.fn.nauty_freedyn)

end NautyVerified.Proofs.Top
