import NautyVerified.Proofs.Alloc.Blocks
import NautyVerified.Proofs.Search.Blocks
import NautyVerified.Exec.Expr

/-!
# The globals the shared proofs use, for any linked program

`NautyEnv ge`: the block of every global and function of `nauty.c`, `nautil.c`
and the allocator that the proofs of those files mention, with
`Genv.find_symbol` of its identifier (the identifiers are `dense.id.*` in every
program linked extending `dense`), `Genv.find_funct_ptr` of each function block
(the bodies are `dense.fn.*`, the same Clight in the sparse program by
`Source/Shared.lean`), the variable information of each variable block (equal
to the dense program's, so the initial-memory facts transfer), and the
pairwise distinctness of all of them (for `sep_ne`).

Proofs about these functions take `[E : NautyEnv ge]` and write `E.x` for the
block of `x`. The global environment is an `outParam`, so a specification that
mentions only `E.x` still determines `ge`. `NautyEnv.dense` is the dense
program's instance, made of the kernel-checked facts in `Program/Dense.lean`,
`Proofs/Alloc/Blocks.lean` and `Proofs/Search/Blocks.lean`.
-/

namespace NautyVerified.Program

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open NautyVerified.Source NautyVerified.Proofs

/-- The blocks of the shared globals and functions in `ge`, with their facts. -/
class NautyEnv (ge : outParam genv) where
  nextelement : block
  leftbit : block
  nautilBit : block
  malloc : block
  free : block
  zalloc : block
  nautilWorkperm : block
  nautilWorkpermSz : block
  permset : block
  nautyBit : block
  nautyCanonlab : block
  nautyCanonlabSz : block
  nautyDefltwork : block
  nautyDefltworkSz : block
  nautyActive : block
  nautyActiveSz : block
  nautyCanoncode : block
  nautyCanoncodeSz : block
  nautyFixedpts : block
  nautyFixedptsSz : block
  nautyFirstcode : block
  nautyFirstcodeSz : block
  nautyWorkperm : block
  nautyWorkpermSz : block
  nautyFirsttc : block
  nautyFirsttcSz : block
  nautyFirstlab : block
  nautyFirstlabSz : block
  getcanon : block
  digraph : block
  writeautoms : block
  cartesian : block
  linelength : block
  outfile : block
  userautomproc : block
  userlevelproc : block
  usernodeproc : block
  usercanonproc : block
  invarproc : block
  tcLevel : block
  mininvarlevel : block
  maxinvarlevel : block
  invararg : block
  dispatch : block
  orbits : block
  domarkers : block
  doschreier : block
  m : block
  n : block
  g : block
  canong : block
  stats : block
  gcaFirst : block
  gcaCanon : block
  noncheaplevel : block
  allsamelevel : block
  eqlevFirst : block
  eqlevCanon : block
  compCanon : block
  samerows : block
  canonlevel : block
  stabvertex : block
  cosetindex : block
  needshortprune : block
  tcnode0 : block
  allocM : block
  workspace : block
  worktop : block
  fmptr : block
  invapplics : block
  invsuccesses : block
  invarsuclevel : block
  killRequest : block
  firstpathnodeFn : block
  othernodeFn : block
  firstterminalFn : block
  processnodeFn : block
  recoverFn : block
  nautyFn : block
  maketargetcellFn : block
  breakoutFn : block
  fmpermFn : block
  fmptnFn : block
  orbjoinFn : block
  shortpruneFn : block
  longpruneFn : block
  dorefFn : block
  nautilCheck : block
  nautilFreedyn : block
  nautyFreedyn : block
  find_nextelement : Genv.find_symbol ge.genv_genv dense.id.nextelement = some nextelement
  find_leftbit : Genv.find_symbol ge.genv_genv dense.id.«nautil:leftbit» = some leftbit
  find_nautilBit : Genv.find_symbol ge.genv_genv dense.id.«nautil:bit» = some nautilBit
  find_malloc : Genv.find_symbol ge.genv_genv dense.id.malloc = some malloc
  find_free : Genv.find_symbol ge.genv_genv dense.id.free = some free
  find_zalloc : Genv.find_symbol ge.genv_genv dense.id.nauty_zalloc = some zalloc
  find_nautilWorkperm : Genv.find_symbol ge.genv_genv dense.id.«nautil:workperm» = some nautilWorkperm
  find_nautilWorkpermSz : Genv.find_symbol ge.genv_genv dense.id.«nautil:workperm_sz» = some nautilWorkpermSz
  find_permset : Genv.find_symbol ge.genv_genv dense.id.permset = some permset
  find_nautyBit : Genv.find_symbol ge.genv_genv dense.id.«nauty:bit» = some nautyBit
  find_nautyCanonlab : Genv.find_symbol ge.genv_genv dense.id.«nauty:canonlab» = some nautyCanonlab
  find_nautyCanonlabSz : Genv.find_symbol ge.genv_genv dense.id.«nauty:canonlab_sz» = some nautyCanonlabSz
  find_nautyDefltwork : Genv.find_symbol ge.genv_genv dense.id.«nauty:defltwork» = some nautyDefltwork
  find_nautyDefltworkSz : Genv.find_symbol ge.genv_genv dense.id.«nauty:defltwork_sz» = some nautyDefltworkSz
  find_nautyActive : Genv.find_symbol ge.genv_genv dense.id.«nauty:active» = some nautyActive
  find_nautyActiveSz : Genv.find_symbol ge.genv_genv dense.id.«nauty:active_sz» = some nautyActiveSz
  find_nautyCanoncode : Genv.find_symbol ge.genv_genv dense.id.«nauty:canoncode» = some nautyCanoncode
  find_nautyCanoncodeSz : Genv.find_symbol ge.genv_genv dense.id.«nauty:canoncode_sz» = some nautyCanoncodeSz
  find_nautyFixedpts : Genv.find_symbol ge.genv_genv dense.id.«nauty:fixedpts» = some nautyFixedpts
  find_nautyFixedptsSz : Genv.find_symbol ge.genv_genv dense.id.«nauty:fixedpts_sz» = some nautyFixedptsSz
  find_nautyFirstcode : Genv.find_symbol ge.genv_genv dense.id.«nauty:firstcode» = some nautyFirstcode
  find_nautyFirstcodeSz : Genv.find_symbol ge.genv_genv dense.id.«nauty:firstcode_sz» = some nautyFirstcodeSz
  find_nautyWorkperm : Genv.find_symbol ge.genv_genv dense.id.«nauty:workperm» = some nautyWorkperm
  find_nautyWorkpermSz : Genv.find_symbol ge.genv_genv dense.id.«nauty:workperm_sz» = some nautyWorkpermSz
  find_nautyFirsttc : Genv.find_symbol ge.genv_genv dense.id.«nauty:firsttc» = some nautyFirsttc
  find_nautyFirsttcSz : Genv.find_symbol ge.genv_genv dense.id.«nauty:firsttc_sz» = some nautyFirsttcSz
  find_nautyFirstlab : Genv.find_symbol ge.genv_genv dense.id.«nauty:firstlab» = some nautyFirstlab
  find_nautyFirstlabSz : Genv.find_symbol ge.genv_genv dense.id.«nauty:firstlab_sz» = some nautyFirstlabSz
  find_getcanon : Genv.find_symbol ge.genv_genv dense.id.«nauty:getcanon» = some getcanon
  find_digraph : Genv.find_symbol ge.genv_genv dense.id.«nauty:digraph» = some digraph
  find_writeautoms : Genv.find_symbol ge.genv_genv dense.id.«nauty:writeautoms» = some writeautoms
  find_cartesian : Genv.find_symbol ge.genv_genv dense.id.«nauty:cartesian» = some cartesian
  find_linelength : Genv.find_symbol ge.genv_genv dense.id.«nauty:linelength» = some linelength
  find_outfile : Genv.find_symbol ge.genv_genv dense.id.«nauty:outfile» = some outfile
  find_userautomproc : Genv.find_symbol ge.genv_genv dense.id.«nauty:userautomproc» = some userautomproc
  find_userlevelproc : Genv.find_symbol ge.genv_genv dense.id.«nauty:userlevelproc» = some userlevelproc
  find_usernodeproc : Genv.find_symbol ge.genv_genv dense.id.«nauty:usernodeproc» = some usernodeproc
  find_usercanonproc : Genv.find_symbol ge.genv_genv dense.id.«nauty:usercanonproc» = some usercanonproc
  find_invarproc : Genv.find_symbol ge.genv_genv dense.id.«nauty:invarproc» = some invarproc
  find_tcLevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:tc_level» = some tcLevel
  find_mininvarlevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:mininvarlevel» = some mininvarlevel
  find_maxinvarlevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:maxinvarlevel» = some maxinvarlevel
  find_invararg : Genv.find_symbol ge.genv_genv dense.id.«nauty:invararg» = some invararg
  find_dispatch : Genv.find_symbol ge.genv_genv dense.id.«nauty:dispatch» = some dispatch
  find_orbits : Genv.find_symbol ge.genv_genv dense.id.«nauty:orbits» = some orbits
  find_domarkers : Genv.find_symbol ge.genv_genv dense.id.«nauty:domarkers» = some domarkers
  find_doschreier : Genv.find_symbol ge.genv_genv dense.id.«nauty:doschreier» = some doschreier
  find_m : Genv.find_symbol ge.genv_genv dense.id.«nauty:m» = some m
  find_n : Genv.find_symbol ge.genv_genv dense.id.«nauty:n» = some n
  find_g : Genv.find_symbol ge.genv_genv dense.id.«nauty:g» = some g
  find_canong : Genv.find_symbol ge.genv_genv dense.id.«nauty:canong» = some canong
  find_stats : Genv.find_symbol ge.genv_genv dense.id.«nauty:stats» = some stats
  find_gcaFirst : Genv.find_symbol ge.genv_genv dense.id.«nauty:gca_first» = some gcaFirst
  find_gcaCanon : Genv.find_symbol ge.genv_genv dense.id.«nauty:gca_canon» = some gcaCanon
  find_noncheaplevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:noncheaplevel» = some noncheaplevel
  find_allsamelevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:allsamelevel» = some allsamelevel
  find_eqlevFirst : Genv.find_symbol ge.genv_genv dense.id.«nauty:eqlev_first» = some eqlevFirst
  find_eqlevCanon : Genv.find_symbol ge.genv_genv dense.id.«nauty:eqlev_canon» = some eqlevCanon
  find_compCanon : Genv.find_symbol ge.genv_genv dense.id.«nauty:comp_canon» = some compCanon
  find_samerows : Genv.find_symbol ge.genv_genv dense.id.«nauty:samerows» = some samerows
  find_canonlevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:canonlevel» = some canonlevel
  find_stabvertex : Genv.find_symbol ge.genv_genv dense.id.«nauty:stabvertex» = some stabvertex
  find_cosetindex : Genv.find_symbol ge.genv_genv dense.id.«nauty:cosetindex» = some cosetindex
  find_needshortprune : Genv.find_symbol ge.genv_genv dense.id.«nauty:needshortprune» = some needshortprune
  find_tcnode0 : Genv.find_symbol ge.genv_genv dense.id.«nauty:tcnode0» = some tcnode0
  find_allocM : Genv.find_symbol ge.genv_genv dense.id.«nauty:alloc_m» = some allocM
  find_workspace : Genv.find_symbol ge.genv_genv dense.id.«nauty:workspace» = some workspace
  find_worktop : Genv.find_symbol ge.genv_genv dense.id.«nauty:worktop» = some worktop
  find_fmptr : Genv.find_symbol ge.genv_genv dense.id.«nauty:fmptr» = some fmptr
  find_invapplics : Genv.find_symbol ge.genv_genv dense.id.«nauty:invapplics» = some invapplics
  find_invsuccesses : Genv.find_symbol ge.genv_genv dense.id.«nauty:invsuccesses» = some invsuccesses
  find_invarsuclevel : Genv.find_symbol ge.genv_genv dense.id.«nauty:invarsuclevel» = some invarsuclevel
  find_killRequest : Genv.find_symbol ge.genv_genv dense.id.«nauty_kill_request» = some killRequest
  find_firstpathnodeFn : Genv.find_symbol ge.genv_genv dense.id.«nauty:firstpathnode0» = some firstpathnodeFn
  find_othernodeFn : Genv.find_symbol ge.genv_genv dense.id.«nauty:othernode0» = some othernodeFn
  find_firstterminalFn : Genv.find_symbol ge.genv_genv dense.id.«nauty:firstterminal» = some firstterminalFn
  find_processnodeFn : Genv.find_symbol ge.genv_genv dense.id.«nauty:processnode» = some processnodeFn
  find_recoverFn : Genv.find_symbol ge.genv_genv dense.id.«nauty:recover» = some recoverFn
  find_nautyFn : Genv.find_symbol ge.genv_genv dense.id.«nauty» = some nautyFn
  find_maketargetcellFn : Genv.find_symbol ge.genv_genv dense.id.«maketargetcell» = some maketargetcellFn
  find_breakoutFn : Genv.find_symbol ge.genv_genv dense.id.«breakout» = some breakoutFn
  find_fmpermFn : Genv.find_symbol ge.genv_genv dense.id.«fmperm» = some fmpermFn
  find_fmptnFn : Genv.find_symbol ge.genv_genv dense.id.«fmptn» = some fmptnFn
  find_orbjoinFn : Genv.find_symbol ge.genv_genv dense.id.«orbjoin» = some orbjoinFn
  find_shortpruneFn : Genv.find_symbol ge.genv_genv dense.id.«shortprune» = some shortpruneFn
  find_longpruneFn : Genv.find_symbol ge.genv_genv dense.id.«longprune» = some longpruneFn
  find_dorefFn : Genv.find_symbol ge.genv_genv dense.id.«doref» = some dorefFn
  find_nautilCheck : Genv.find_symbol ge.genv_genv dense.id.nautil_check = some nautilCheck
  find_nautilFreedyn : Genv.find_symbol ge.genv_genv dense.id.nautil_freedyn = some nautilFreedyn
  find_nautyFreedyn : Genv.find_symbol ge.genv_genv dense.id.nauty_freedyn = some nautyFreedyn
  funct_nextelement : Genv.find_funct_ptr ge.genv_genv nextelement =
    some (.Internal dense.fn.nextelement)
  funct_malloc : Genv.find_funct_ptr ge.genv_genv malloc =
    some (.External .EF_malloc [tulong] (tptr .Tvoid) Common.AST.cc_default)
  funct_free : Genv.find_funct_ptr ge.genv_genv free =
    some (.External .EF_free [tptr .Tvoid] .Tvoid Common.AST.cc_default)
  funct_zalloc : Genv.find_funct_ptr ge.genv_genv zalloc =
    some (.Internal dense.fn.nauty_zalloc)
  funct_permset : Genv.find_funct_ptr ge.genv_genv permset =
    some (.Internal dense.fn.permset)
  funct_firstpathnodeFn : Genv.find_funct_ptr ge.genv_genv firstpathnodeFn =
    some (.Internal dense.fn.«nauty:firstpathnode0»)
  funct_othernodeFn : Genv.find_funct_ptr ge.genv_genv othernodeFn =
    some (.Internal dense.fn.«nauty:othernode0»)
  funct_firstterminalFn : Genv.find_funct_ptr ge.genv_genv firstterminalFn =
    some (.Internal dense.fn.«nauty:firstterminal»)
  funct_processnodeFn : Genv.find_funct_ptr ge.genv_genv processnodeFn =
    some (.Internal dense.fn.«nauty:processnode»)
  funct_recoverFn : Genv.find_funct_ptr ge.genv_genv recoverFn =
    some (.Internal dense.fn.«nauty:recover»)
  funct_nautyFn : Genv.find_funct_ptr ge.genv_genv nautyFn =
    some (.Internal dense.fn.«nauty»)
  funct_maketargetcellFn : Genv.find_funct_ptr ge.genv_genv maketargetcellFn =
    some (.Internal dense.fn.«maketargetcell»)
  funct_breakoutFn : Genv.find_funct_ptr ge.genv_genv breakoutFn =
    some (.Internal dense.fn.«breakout»)
  funct_fmpermFn : Genv.find_funct_ptr ge.genv_genv fmpermFn =
    some (.Internal dense.fn.«fmperm»)
  funct_fmptnFn : Genv.find_funct_ptr ge.genv_genv fmptnFn =
    some (.Internal dense.fn.«fmptn»)
  funct_orbjoinFn : Genv.find_funct_ptr ge.genv_genv orbjoinFn =
    some (.Internal dense.fn.«orbjoin»)
  funct_shortpruneFn : Genv.find_funct_ptr ge.genv_genv shortpruneFn =
    some (.Internal dense.fn.«shortprune»)
  funct_longpruneFn : Genv.find_funct_ptr ge.genv_genv longpruneFn =
    some (.Internal dense.fn.«longprune»)
  funct_dorefFn : Genv.find_funct_ptr ge.genv_genv dorefFn =
    some (.Internal dense.fn.«doref»)
  funct_nautilCheck : Genv.find_funct_ptr ge.genv_genv nautilCheck =
    some (.Internal dense.fn.nautil_check)
  funct_nautilFreedyn : Genv.find_funct_ptr ge.genv_genv nautilFreedyn =
    some (.Internal dense.fn.nautil_freedyn)
  funct_nautyFreedyn : Genv.find_funct_ptr ge.genv_genv nautyFreedyn =
    some (.Internal dense.fn.nauty_freedyn)
  var_leftbit : Genv.find_var_info ge.genv_genv leftbit =
    Genv.find_var_info Program.ge.genv_genv Block.leftbit
  var_nautilBit : Genv.find_var_info ge.genv_genv nautilBit =
    Genv.find_var_info Program.ge.genv_genv Block.nautilBit
  var_nautilWorkperm : Genv.find_var_info ge.genv_genv nautilWorkperm =
    Genv.find_var_info Program.ge.genv_genv Block.nautilWorkperm
  var_nautilWorkpermSz : Genv.find_var_info ge.genv_genv nautilWorkpermSz =
    Genv.find_var_info Program.ge.genv_genv Block.nautilWorkpermSz
  var_nautyBit : Genv.find_var_info ge.genv_genv nautyBit =
    Genv.find_var_info Program.ge.genv_genv Block.nautyBit
  var_nautyCanonlab : Genv.find_var_info ge.genv_genv nautyCanonlab =
    Genv.find_var_info Program.ge.genv_genv Block.nautyCanonlab
  var_nautyCanonlabSz : Genv.find_var_info ge.genv_genv nautyCanonlabSz =
    Genv.find_var_info Program.ge.genv_genv Block.nautyCanonlabSz
  var_nautyDefltwork : Genv.find_var_info ge.genv_genv nautyDefltwork =
    Genv.find_var_info Program.ge.genv_genv Block.nautyDefltwork
  var_nautyDefltworkSz : Genv.find_var_info ge.genv_genv nautyDefltworkSz =
    Genv.find_var_info Program.ge.genv_genv Block.nautyDefltworkSz
  var_nautyActive : Genv.find_var_info ge.genv_genv nautyActive =
    Genv.find_var_info Program.ge.genv_genv Block.nautyActive
  var_nautyActiveSz : Genv.find_var_info ge.genv_genv nautyActiveSz =
    Genv.find_var_info Program.ge.genv_genv Block.nautyActiveSz
  var_nautyCanoncode : Genv.find_var_info ge.genv_genv nautyCanoncode =
    Genv.find_var_info Program.ge.genv_genv Block.nautyCanoncode
  var_nautyCanoncodeSz : Genv.find_var_info ge.genv_genv nautyCanoncodeSz =
    Genv.find_var_info Program.ge.genv_genv Block.nautyCanoncodeSz
  var_nautyFixedpts : Genv.find_var_info ge.genv_genv nautyFixedpts =
    Genv.find_var_info Program.ge.genv_genv Block.nautyFixedpts
  var_nautyFixedptsSz : Genv.find_var_info ge.genv_genv nautyFixedptsSz =
    Genv.find_var_info Program.ge.genv_genv Block.nautyFixedptsSz
  var_nautyFirstcode : Genv.find_var_info ge.genv_genv nautyFirstcode =
    Genv.find_var_info Program.ge.genv_genv Block.nautyFirstcode
  var_nautyFirstcodeSz : Genv.find_var_info ge.genv_genv nautyFirstcodeSz =
    Genv.find_var_info Program.ge.genv_genv Block.nautyFirstcodeSz
  var_nautyWorkperm : Genv.find_var_info ge.genv_genv nautyWorkperm =
    Genv.find_var_info Program.ge.genv_genv Block.nautyWorkperm
  var_nautyWorkpermSz : Genv.find_var_info ge.genv_genv nautyWorkpermSz =
    Genv.find_var_info Program.ge.genv_genv Block.nautyWorkpermSz
  var_nautyFirsttc : Genv.find_var_info ge.genv_genv nautyFirsttc =
    Genv.find_var_info Program.ge.genv_genv Block.nautyFirsttc
  var_nautyFirsttcSz : Genv.find_var_info ge.genv_genv nautyFirsttcSz =
    Genv.find_var_info Program.ge.genv_genv Block.nautyFirsttcSz
  var_nautyFirstlab : Genv.find_var_info ge.genv_genv nautyFirstlab =
    Genv.find_var_info Program.ge.genv_genv Block.nautyFirstlab
  var_nautyFirstlabSz : Genv.find_var_info ge.genv_genv nautyFirstlabSz =
    Genv.find_var_info Program.ge.genv_genv Block.nautyFirstlabSz
  var_getcanon : Genv.find_var_info ge.genv_genv getcanon =
    Genv.find_var_info Program.ge.genv_genv Search.Block.getcanon
  var_digraph : Genv.find_var_info ge.genv_genv digraph =
    Genv.find_var_info Program.ge.genv_genv Search.Block.digraph
  var_writeautoms : Genv.find_var_info ge.genv_genv writeautoms =
    Genv.find_var_info Program.ge.genv_genv Search.Block.writeautoms
  var_cartesian : Genv.find_var_info ge.genv_genv cartesian =
    Genv.find_var_info Program.ge.genv_genv Search.Block.cartesian
  var_linelength : Genv.find_var_info ge.genv_genv linelength =
    Genv.find_var_info Program.ge.genv_genv Search.Block.linelength
  var_outfile : Genv.find_var_info ge.genv_genv outfile =
    Genv.find_var_info Program.ge.genv_genv Search.Block.outfile
  var_userautomproc : Genv.find_var_info ge.genv_genv userautomproc =
    Genv.find_var_info Program.ge.genv_genv Search.Block.userautomproc
  var_userlevelproc : Genv.find_var_info ge.genv_genv userlevelproc =
    Genv.find_var_info Program.ge.genv_genv Search.Block.userlevelproc
  var_usernodeproc : Genv.find_var_info ge.genv_genv usernodeproc =
    Genv.find_var_info Program.ge.genv_genv Search.Block.usernodeproc
  var_usercanonproc : Genv.find_var_info ge.genv_genv usercanonproc =
    Genv.find_var_info Program.ge.genv_genv Search.Block.usercanonproc
  var_invarproc : Genv.find_var_info ge.genv_genv invarproc =
    Genv.find_var_info Program.ge.genv_genv Search.Block.invarproc
  var_tcLevel : Genv.find_var_info ge.genv_genv tcLevel =
    Genv.find_var_info Program.ge.genv_genv Search.Block.tcLevel
  var_mininvarlevel : Genv.find_var_info ge.genv_genv mininvarlevel =
    Genv.find_var_info Program.ge.genv_genv Search.Block.mininvarlevel
  var_maxinvarlevel : Genv.find_var_info ge.genv_genv maxinvarlevel =
    Genv.find_var_info Program.ge.genv_genv Search.Block.maxinvarlevel
  var_invararg : Genv.find_var_info ge.genv_genv invararg =
    Genv.find_var_info Program.ge.genv_genv Search.Block.invararg
  var_dispatch : Genv.find_var_info ge.genv_genv dispatch =
    Genv.find_var_info Program.ge.genv_genv Search.Block.dispatch
  var_orbits : Genv.find_var_info ge.genv_genv orbits =
    Genv.find_var_info Program.ge.genv_genv Search.Block.orbits
  var_domarkers : Genv.find_var_info ge.genv_genv domarkers =
    Genv.find_var_info Program.ge.genv_genv Search.Block.domarkers
  var_doschreier : Genv.find_var_info ge.genv_genv doschreier =
    Genv.find_var_info Program.ge.genv_genv Search.Block.doschreier
  var_m : Genv.find_var_info ge.genv_genv m =
    Genv.find_var_info Program.ge.genv_genv Search.Block.m
  var_n : Genv.find_var_info ge.genv_genv n =
    Genv.find_var_info Program.ge.genv_genv Search.Block.n
  var_g : Genv.find_var_info ge.genv_genv g =
    Genv.find_var_info Program.ge.genv_genv Search.Block.g
  var_canong : Genv.find_var_info ge.genv_genv canong =
    Genv.find_var_info Program.ge.genv_genv Search.Block.canong
  var_stats : Genv.find_var_info ge.genv_genv stats =
    Genv.find_var_info Program.ge.genv_genv Search.Block.stats
  var_gcaFirst : Genv.find_var_info ge.genv_genv gcaFirst =
    Genv.find_var_info Program.ge.genv_genv Search.Block.gcaFirst
  var_gcaCanon : Genv.find_var_info ge.genv_genv gcaCanon =
    Genv.find_var_info Program.ge.genv_genv Search.Block.gcaCanon
  var_noncheaplevel : Genv.find_var_info ge.genv_genv noncheaplevel =
    Genv.find_var_info Program.ge.genv_genv Search.Block.noncheaplevel
  var_allsamelevel : Genv.find_var_info ge.genv_genv allsamelevel =
    Genv.find_var_info Program.ge.genv_genv Search.Block.allsamelevel
  var_eqlevFirst : Genv.find_var_info ge.genv_genv eqlevFirst =
    Genv.find_var_info Program.ge.genv_genv Search.Block.eqlevFirst
  var_eqlevCanon : Genv.find_var_info ge.genv_genv eqlevCanon =
    Genv.find_var_info Program.ge.genv_genv Search.Block.eqlevCanon
  var_compCanon : Genv.find_var_info ge.genv_genv compCanon =
    Genv.find_var_info Program.ge.genv_genv Search.Block.compCanon
  var_samerows : Genv.find_var_info ge.genv_genv samerows =
    Genv.find_var_info Program.ge.genv_genv Search.Block.samerows
  var_canonlevel : Genv.find_var_info ge.genv_genv canonlevel =
    Genv.find_var_info Program.ge.genv_genv Search.Block.canonlevel
  var_stabvertex : Genv.find_var_info ge.genv_genv stabvertex =
    Genv.find_var_info Program.ge.genv_genv Search.Block.stabvertex
  var_cosetindex : Genv.find_var_info ge.genv_genv cosetindex =
    Genv.find_var_info Program.ge.genv_genv Search.Block.cosetindex
  var_needshortprune : Genv.find_var_info ge.genv_genv needshortprune =
    Genv.find_var_info Program.ge.genv_genv Search.Block.needshortprune
  var_tcnode0 : Genv.find_var_info ge.genv_genv tcnode0 =
    Genv.find_var_info Program.ge.genv_genv Search.Block.tcnode0
  var_allocM : Genv.find_var_info ge.genv_genv allocM =
    Genv.find_var_info Program.ge.genv_genv Search.Block.allocM
  var_workspace : Genv.find_var_info ge.genv_genv workspace =
    Genv.find_var_info Program.ge.genv_genv Search.Block.workspace
  var_worktop : Genv.find_var_info ge.genv_genv worktop =
    Genv.find_var_info Program.ge.genv_genv Search.Block.worktop
  var_fmptr : Genv.find_var_info ge.genv_genv fmptr =
    Genv.find_var_info Program.ge.genv_genv Search.Block.fmptr
  var_invapplics : Genv.find_var_info ge.genv_genv invapplics =
    Genv.find_var_info Program.ge.genv_genv Search.Block.invapplics
  var_invsuccesses : Genv.find_var_info ge.genv_genv invsuccesses =
    Genv.find_var_info Program.ge.genv_genv Search.Block.invsuccesses
  var_invarsuclevel : Genv.find_var_info ge.genv_genv invarsuclevel =
    Genv.find_var_info Program.ge.genv_genv Search.Block.invarsuclevel
  var_killRequest : Genv.find_var_info ge.genv_genv killRequest =
    Genv.find_var_info Program.ge.genv_genv Search.Block.killRequest
  /-- The blocks are pairwise distinct. -/
  distinct : List.Pairwise (· ≠ ·)
    [nextelement, leftbit, nautilBit, malloc, free, zalloc, nautilWorkperm, nautilWorkpermSz, permset, nautyBit, nautyCanonlab, nautyCanonlabSz, nautyDefltwork, nautyDefltworkSz, nautyActive, nautyActiveSz, nautyCanoncode, nautyCanoncodeSz, nautyFixedpts, nautyFixedptsSz, nautyFirstcode, nautyFirstcodeSz, nautyWorkperm, nautyWorkpermSz, nautyFirsttc, nautyFirsttcSz, nautyFirstlab, nautyFirstlabSz, getcanon, digraph, writeautoms, cartesian, linelength, outfile, userautomproc, userlevelproc, usernodeproc, usercanonproc, invarproc, tcLevel, mininvarlevel, maxinvarlevel, invararg, dispatch, orbits, domarkers, doschreier, m, n, g, canong, stats, gcaFirst, gcaCanon, noncheaplevel, allsamelevel, eqlevFirst, eqlevCanon, compCanon, samerows, canonlevel, stabvertex, cosetindex, needshortprune, tcnode0, allocM, workspace, worktop, fmptr, invapplics, invsuccesses, invarsuclevel, killRequest, firstpathnodeFn, othernodeFn, firstterminalFn, processnodeFn, recoverFn, nautyFn, maketargetcellFn, breakoutFn, fmpermFn, fmptnFn, orbjoinFn, shortpruneFn, longpruneFn, dorefFn, nautilCheck, nautilFreedyn, nautyFreedyn]
  /-- The member offsets of `tcnode`, `statsblk` (`_1024`) and `dispatchvec`
  (`_1027`) in the program's composite environment. -/
  field_tcnodeNext : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«tcnode_struct» Cfrontend.Ctypes.noattr) dense.id.«next» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 0)), .Full)
  field_tcnodeTcell : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«tcnode_struct» Cfrontend.Ctypes.noattr) dense.id.«tcellptr» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 8)), .Full)
  field_statsGrpsize1 : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«grpsize1» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 0)), .Full)
  field_statsGrpsize2 : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«grpsize2» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 8)), .Full)
  field_statsNumorbits : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«numorbits» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 12)), .Full)
  field_statsNumgenerators : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«numgenerators» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 16)), .Full)
  field_statsErrstatus : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«errstatus» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 20)), .Full)
  field_statsNumnodes : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«numnodes» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 24)), .Full)
  field_statsNumbadleaves : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«numbadleaves» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 32)), .Full)
  field_statsMaxlevel : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«maxlevel» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 40)), .Full)
  field_statsTctotal : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«tctotal» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 48)), .Full)
  field_statsCanupdates : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«canupdates» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 56)), .Full)
  field_dIsautom : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«isautom» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 0)), .Full)
  field_dTestcanlab : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«testcanlab» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 8)), .Full)
  field_dUpdatecan : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«updatecan» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 16)), .Full)
  field_dRefine : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«refine» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 24)), .Full)
  field_dRefine1 : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«refine1» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 32)), .Full)
  field_dCheapautom : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«cheapautom» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 40)), .Full)
  field_dTargetcell : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«targetcell» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 48)), .Full)
  /-- `sizeof(struct tcnode_struct)`, which a node's `malloc` of a new list entry asks for. -/
  sizeof_tcnode : Cfrontend.Ctypes.sizeof ge.genv_cenv
    (Cfrontend.Ctypes.Tstruct dense.id.«tcnode_struct» Cfrontend.Ctypes.noattr) =
      Foundation.Numbers.Rocq.Coq.zOfInt 16

namespace NautyEnv

variable {ge : genv} (E : NautyEnv ge)

/-- `permset`'s block, under the name the search proofs use. -/
abbrev permsetFn : block := E.permset

theorem find_permsetFn : Genv.find_symbol ge.genv_genv dense.id.permset = some E.permsetFn :=
  E.find_permset

theorem funct_permsetFn :
    Genv.find_funct_ptr ge.genv_genv E.permsetFn = some (.Internal dense.fn.permset) :=
  E.funct_permset

theorem ne_of_pairwise {l : List block} (h : l.Pairwise (· ≠ ·)) (i j : Nat) (hij : i < j)
    (hj : j < l.length) : l[i]'(Nat.lt_trans hij hj) ≠ l[j] := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons a l ih =>
    rw [List.pairwise_cons] at h
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => exact h.1 _ (List.getElem_mem _)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact ih h.2 i j (by omega) (by simpa using hj)

/-- Every block of `E`, in the order of `distinct`. -/
def blocks : List block :=
  [E.nextelement, E.leftbit, E.nautilBit, E.malloc, E.free, E.zalloc, E.nautilWorkperm, E.nautilWorkpermSz, E.permset, E.nautyBit, E.nautyCanonlab, E.nautyCanonlabSz, E.nautyDefltwork, E.nautyDefltworkSz, E.nautyActive, E.nautyActiveSz, E.nautyCanoncode, E.nautyCanoncodeSz, E.nautyFixedpts, E.nautyFixedptsSz, E.nautyFirstcode, E.nautyFirstcodeSz, E.nautyWorkperm, E.nautyWorkpermSz, E.nautyFirsttc, E.nautyFirsttcSz, E.nautyFirstlab, E.nautyFirstlabSz, E.getcanon, E.digraph, E.writeautoms, E.cartesian, E.linelength, E.outfile, E.userautomproc, E.userlevelproc, E.usernodeproc, E.usercanonproc, E.invarproc, E.tcLevel, E.mininvarlevel, E.maxinvarlevel, E.invararg, E.dispatch, E.orbits, E.domarkers, E.doschreier, E.m, E.n, E.g, E.canong, E.stats, E.gcaFirst, E.gcaCanon, E.noncheaplevel, E.allsamelevel, E.eqlevFirst, E.eqlevCanon, E.compCanon, E.samerows, E.canonlevel, E.stabvertex, E.cosetindex, E.needshortprune, E.tcnode0, E.allocM, E.workspace, E.worktop, E.fmptr, E.invapplics, E.invsuccesses, E.invarsuclevel, E.killRequest, E.firstpathnodeFn, E.othernodeFn, E.firstterminalFn, E.processnodeFn, E.recoverFn, E.nautyFn, E.maketargetcellFn, E.breakoutFn, E.fmpermFn, E.fmptnFn, E.orbjoinFn, E.shortpruneFn, E.longpruneFn, E.dorefFn, E.nautilCheck, E.nautilFreedyn, E.nautyFreedyn]

end NautyEnv

open Lean Meta in
/-- The entries of a list literal, after unfolding. -/
partial def listEntriesD (e : Expr) : MetaM (Array Expr) := do
  let e ← whnfD e
  match e.getAppFnArgs with
  | (``List.cons, #[_, x, rest]) => return #[x] ++ (← listEntriesD rest)
  | _ => return #[]

open Lean Meta Elab Tactic in
/-- `env_ne`: closes `a ≠ b` for two distinct blocks of a `NautyEnv` (`E.x ≠ E.y`),
from `NautyEnv.distinct`. -/
elab "env_ne" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (_, a, b) := (← whnfR ty).not?.bind (·.eq?) |>.orElse fun _ =>
      (ty.app3? ``Ne).map fun (α, a, b) => (α, a, b)
    | throwError "env_ne: goal is not a disequality"
  let instOf (x : Expr) : MetaM (Option Expr) := do
    let x ← instantiateMVars x
    let fn := x.getAppFn
    let args := x.getAppArgs
    if let .const n _ := fn then
      if (`NautyVerified.Program.NautyEnv).isPrefixOf n && args.size == 2 then
        return some args[1]!
    return none
  let some inst ← (do if let some i ← instOf a then pure (some i) else instOf b)
    | throwError "env_ne: neither side is a block of a NautyEnv"
  let dist ← mkAppOptM ``NautyEnv.distinct #[none, inst]
  let dT ← whnf (← inferType dist)
  let l := dT.appArg!
  let es ← listEntriesD l
  let idx (x : Expr) : MetaM (Option Nat) := do
    for i in [0:es.size] do
      if ← withReducible (isDefEq es[i]! x) then return some i
    return none
  let some i ← idx a | throwError "env_ne: {a} is not a block of the environment"
  let some j ← idx b | throwError "env_ne: {b} is not a block of the environment"
  let distStx ← Term.exprToSyntax dist
  if i < j then
    evalTactic (← `(tactic| exact NautyVerified.Program.NautyEnv.ne_of_pairwise $distStx
      $(Syntax.mkNumLit (toString i)) $(Syntax.mkNumLit (toString j)) (by decide) (by simp)))
  else if j < i then
    evalTactic (← `(tactic| exact Ne.symm (NautyVerified.Program.NautyEnv.ne_of_pairwise $distStx
      $(Syntax.mkNumLit (toString j)) $(Syntax.mkNumLit (toString i)) (by decide) (by simp))))
  else throwError "env_ne: both sides are the same block"

kernel_rfl dense_distinct : decide (List.Pairwise (· ≠ ·)
    [Block.nextelement, Block.leftbit, Block.nautilBit, Block.malloc, Block.free, Block.zalloc, Block.nautilWorkperm, Block.nautilWorkpermSz, Block.permset, Block.nautyBit, Block.nautyCanonlab, Block.nautyCanonlabSz, Block.nautyDefltwork, Block.nautyDefltworkSz, Block.nautyActive, Block.nautyActiveSz, Block.nautyCanoncode, Block.nautyCanoncodeSz, Block.nautyFixedpts, Block.nautyFixedptsSz, Block.nautyFirstcode, Block.nautyFirstcodeSz, Block.nautyWorkperm, Block.nautyWorkpermSz, Block.nautyFirsttc, Block.nautyFirsttcSz, Block.nautyFirstlab, Block.nautyFirstlabSz, Search.Block.getcanon, Search.Block.digraph, Search.Block.writeautoms, Search.Block.cartesian, Search.Block.linelength, Search.Block.outfile, Search.Block.userautomproc, Search.Block.userlevelproc, Search.Block.usernodeproc, Search.Block.usercanonproc, Search.Block.invarproc, Search.Block.tcLevel, Search.Block.mininvarlevel, Search.Block.maxinvarlevel, Search.Block.invararg, Search.Block.dispatch, Search.Block.orbits, Search.Block.domarkers, Search.Block.doschreier, Search.Block.m, Search.Block.n, Search.Block.g, Search.Block.canong, Search.Block.stats, Search.Block.gcaFirst, Search.Block.gcaCanon, Search.Block.noncheaplevel, Search.Block.allsamelevel, Search.Block.eqlevFirst, Search.Block.eqlevCanon, Search.Block.compCanon, Search.Block.samerows, Search.Block.canonlevel, Search.Block.stabvertex, Search.Block.cosetindex, Search.Block.needshortprune, Search.Block.tcnode0, Search.Block.allocM, Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr, Search.Block.invapplics, Search.Block.invsuccesses, Search.Block.invarsuclevel, Search.Block.killRequest, Search.Block.firstpathnodeFn, Search.Block.othernodeFn, Search.Block.firstterminalFn, Search.Block.processnodeFn, Search.Block.recoverFn, Search.Block.nautyFn, Search.Block.maketargetcellFn, Search.Block.breakoutFn, Search.Block.fmpermFn, Search.Block.fmptnFn, Search.Block.orbjoinFn, Search.Block.shortpruneFn, Search.Block.longpruneFn, Search.Block.dorefFn, Top.Block.nautilCheck, Top.Block.nautilFreedyn, Top.Block.nautyFreedyn]) = true

namespace DenseLayout

kernel_rfl field_tcnodeNext : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«tcnode_struct» Cfrontend.Ctypes.noattr) dense.id.«next» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 0)), .Full)

kernel_rfl field_tcnodeTcell : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«tcnode_struct» Cfrontend.Ctypes.noattr) dense.id.«tcellptr» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 8)), .Full)

kernel_rfl field_statsGrpsize1 : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«grpsize1» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 0)), .Full)

kernel_rfl field_statsGrpsize2 : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«grpsize2» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 8)), .Full)

kernel_rfl field_statsNumorbits : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«numorbits» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 12)), .Full)

kernel_rfl field_statsNumgenerators : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«numgenerators» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 16)), .Full)

kernel_rfl field_statsErrstatus : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«errstatus» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 20)), .Full)

kernel_rfl field_statsNumnodes : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«numnodes» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 24)), .Full)

kernel_rfl field_statsNumbadleaves : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«numbadleaves» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 32)), .Full)

kernel_rfl field_statsMaxlevel : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«maxlevel» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 40)), .Full)

kernel_rfl field_statsTctotal : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«tctotal» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 48)), .Full)

kernel_rfl field_statsCanupdates : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«canupdates» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 56)), .Full)

kernel_rfl field_dIsautom : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«isautom» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 0)), .Full)

kernel_rfl field_dTestcanlab : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«testcanlab» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 8)), .Full)

kernel_rfl field_dUpdatecan : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«updatecan» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 16)), .Full)

kernel_rfl field_dRefine : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«refine» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 24)), .Full)

kernel_rfl field_dRefine1 : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«refine1» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 32)), .Full)

kernel_rfl field_dCheapautom : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«cheapautom» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 40)), .Full)

kernel_rfl field_dTargetcell : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField Program.ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«targetcell» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 48)), .Full)

kernel_rfl sizeof_tcnode : Cfrontend.Ctypes.sizeof Program.ge.genv_cenv
    (Cfrontend.Ctypes.Tstruct dense.id.«tcnode_struct» Cfrontend.Ctypes.noattr) =
      Foundation.Numbers.Rocq.Coq.zOfInt 16

end DenseLayout

/-- The dense program's blocks (reducible, so `E.x` unfolds to `Block.x` at
reducible transparency). -/
@[reducible] instance NautyEnv.dense : NautyEnv ge where
  nextelement := Block.nextelement
  leftbit := Block.leftbit
  nautilBit := Block.nautilBit
  malloc := Block.malloc
  free := Block.free
  zalloc := Block.zalloc
  nautilWorkperm := Block.nautilWorkperm
  nautilWorkpermSz := Block.nautilWorkpermSz
  permset := Block.permset
  nautyBit := Block.nautyBit
  nautyCanonlab := Block.nautyCanonlab
  nautyCanonlabSz := Block.nautyCanonlabSz
  nautyDefltwork := Block.nautyDefltwork
  nautyDefltworkSz := Block.nautyDefltworkSz
  nautyActive := Block.nautyActive
  nautyActiveSz := Block.nautyActiveSz
  nautyCanoncode := Block.nautyCanoncode
  nautyCanoncodeSz := Block.nautyCanoncodeSz
  nautyFixedpts := Block.nautyFixedpts
  nautyFixedptsSz := Block.nautyFixedptsSz
  nautyFirstcode := Block.nautyFirstcode
  nautyFirstcodeSz := Block.nautyFirstcodeSz
  nautyWorkperm := Block.nautyWorkperm
  nautyWorkpermSz := Block.nautyWorkpermSz
  nautyFirsttc := Block.nautyFirsttc
  nautyFirsttcSz := Block.nautyFirsttcSz
  nautyFirstlab := Block.nautyFirstlab
  nautyFirstlabSz := Block.nautyFirstlabSz
  getcanon := Search.Block.getcanon
  digraph := Search.Block.digraph
  writeautoms := Search.Block.writeautoms
  cartesian := Search.Block.cartesian
  linelength := Search.Block.linelength
  outfile := Search.Block.outfile
  userautomproc := Search.Block.userautomproc
  userlevelproc := Search.Block.userlevelproc
  usernodeproc := Search.Block.usernodeproc
  usercanonproc := Search.Block.usercanonproc
  invarproc := Search.Block.invarproc
  tcLevel := Search.Block.tcLevel
  mininvarlevel := Search.Block.mininvarlevel
  maxinvarlevel := Search.Block.maxinvarlevel
  invararg := Search.Block.invararg
  dispatch := Search.Block.dispatch
  orbits := Search.Block.orbits
  domarkers := Search.Block.domarkers
  doschreier := Search.Block.doschreier
  m := Search.Block.m
  n := Search.Block.n
  g := Search.Block.g
  canong := Search.Block.canong
  stats := Search.Block.stats
  gcaFirst := Search.Block.gcaFirst
  gcaCanon := Search.Block.gcaCanon
  noncheaplevel := Search.Block.noncheaplevel
  allsamelevel := Search.Block.allsamelevel
  eqlevFirst := Search.Block.eqlevFirst
  eqlevCanon := Search.Block.eqlevCanon
  compCanon := Search.Block.compCanon
  samerows := Search.Block.samerows
  canonlevel := Search.Block.canonlevel
  stabvertex := Search.Block.stabvertex
  cosetindex := Search.Block.cosetindex
  needshortprune := Search.Block.needshortprune
  tcnode0 := Search.Block.tcnode0
  allocM := Search.Block.allocM
  workspace := Search.Block.workspace
  worktop := Search.Block.worktop
  fmptr := Search.Block.fmptr
  invapplics := Search.Block.invapplics
  invsuccesses := Search.Block.invsuccesses
  invarsuclevel := Search.Block.invarsuclevel
  killRequest := Search.Block.killRequest
  firstpathnodeFn := Search.Block.firstpathnodeFn
  othernodeFn := Search.Block.othernodeFn
  firstterminalFn := Search.Block.firstterminalFn
  processnodeFn := Search.Block.processnodeFn
  recoverFn := Search.Block.recoverFn
  nautyFn := Search.Block.nautyFn
  maketargetcellFn := Search.Block.maketargetcellFn
  breakoutFn := Search.Block.breakoutFn
  fmpermFn := Search.Block.fmpermFn
  fmptnFn := Search.Block.fmptnFn
  orbjoinFn := Search.Block.orbjoinFn
  shortpruneFn := Search.Block.shortpruneFn
  longpruneFn := Search.Block.longpruneFn
  dorefFn := Search.Block.dorefFn
  nautilCheck := Top.Block.nautilCheck
  nautilFreedyn := Top.Block.nautilFreedyn
  nautyFreedyn := Top.Block.nautyFreedyn
  find_nextelement := Program.find_nextelement
  find_leftbit := Program.find_leftbit
  find_nautilBit := Program.find_nautilBit
  find_malloc := Program.find_malloc
  find_free := Program.find_free
  find_zalloc := Program.find_zalloc
  find_nautilWorkperm := Program.find_nautilWorkperm
  find_nautilWorkpermSz := Program.find_nautilWorkpermSz
  find_permset := Program.find_permset
  find_nautyBit := Program.find_nautyBit
  find_nautyCanonlab := Program.find_nautyCanonlab
  find_nautyCanonlabSz := Program.find_nautyCanonlabSz
  find_nautyDefltwork := Program.find_nautyDefltwork
  find_nautyDefltworkSz := Program.find_nautyDefltworkSz
  find_nautyActive := Program.find_nautyActive
  find_nautyActiveSz := Program.find_nautyActiveSz
  find_nautyCanoncode := Program.find_nautyCanoncode
  find_nautyCanoncodeSz := Program.find_nautyCanoncodeSz
  find_nautyFixedpts := Program.find_nautyFixedpts
  find_nautyFixedptsSz := Program.find_nautyFixedptsSz
  find_nautyFirstcode := Program.find_nautyFirstcode
  find_nautyFirstcodeSz := Program.find_nautyFirstcodeSz
  find_nautyWorkperm := Program.find_nautyWorkperm
  find_nautyWorkpermSz := Program.find_nautyWorkpermSz
  find_nautyFirsttc := Program.find_nautyFirsttc
  find_nautyFirsttcSz := Program.find_nautyFirsttcSz
  find_nautyFirstlab := Program.find_nautyFirstlab
  find_nautyFirstlabSz := Program.find_nautyFirstlabSz
  find_getcanon := Search.find_getcanon
  find_digraph := Search.find_digraph
  find_writeautoms := Search.find_writeautoms
  find_cartesian := Search.find_cartesian
  find_linelength := Search.find_linelength
  find_outfile := Search.find_outfile
  find_userautomproc := Search.find_userautomproc
  find_userlevelproc := Search.find_userlevelproc
  find_usernodeproc := Search.find_usernodeproc
  find_usercanonproc := Search.find_usercanonproc
  find_invarproc := Search.find_invarproc
  find_tcLevel := Search.find_tcLevel
  find_mininvarlevel := Search.find_mininvarlevel
  find_maxinvarlevel := Search.find_maxinvarlevel
  find_invararg := Search.find_invararg
  find_dispatch := Search.find_dispatch
  find_orbits := Search.find_orbits
  find_domarkers := Search.find_domarkers
  find_doschreier := Search.find_doschreier
  find_m := Search.find_m
  find_n := Search.find_n
  find_g := Search.find_g
  find_canong := Search.find_canong
  find_stats := Search.find_stats
  find_gcaFirst := Search.find_gcaFirst
  find_gcaCanon := Search.find_gcaCanon
  find_noncheaplevel := Search.find_noncheaplevel
  find_allsamelevel := Search.find_allsamelevel
  find_eqlevFirst := Search.find_eqlevFirst
  find_eqlevCanon := Search.find_eqlevCanon
  find_compCanon := Search.find_compCanon
  find_samerows := Search.find_samerows
  find_canonlevel := Search.find_canonlevel
  find_stabvertex := Search.find_stabvertex
  find_cosetindex := Search.find_cosetindex
  find_needshortprune := Search.find_needshortprune
  find_tcnode0 := Search.find_tcnode0
  find_allocM := Search.find_allocM
  find_workspace := Search.find_workspace
  find_worktop := Search.find_worktop
  find_fmptr := Search.find_fmptr
  find_invapplics := Search.find_invapplics
  find_invsuccesses := Search.find_invsuccesses
  find_invarsuclevel := Search.find_invarsuclevel
  find_killRequest := Search.find_killRequest
  find_firstpathnodeFn := Search.find_firstpathnodeFn
  find_othernodeFn := Search.find_othernodeFn
  find_firstterminalFn := Search.find_firstterminalFn
  find_processnodeFn := Search.find_processnodeFn
  find_recoverFn := Search.find_recoverFn
  find_nautyFn := Search.find_nautyFn
  find_maketargetcellFn := Search.find_maketargetcellFn
  find_breakoutFn := Search.find_breakoutFn
  find_fmpermFn := Search.find_fmpermFn
  find_fmptnFn := Search.find_fmptnFn
  find_orbjoinFn := Search.find_orbjoinFn
  find_shortpruneFn := Search.find_shortpruneFn
  find_longpruneFn := Search.find_longpruneFn
  find_dorefFn := Search.find_dorefFn
  find_nautilCheck := Top.find_nautilCheck
  find_nautilFreedyn := Top.find_nautilFreedyn
  find_nautyFreedyn := Top.find_nautyFreedyn
  funct_nextelement := Program.funct_nextelement
  funct_malloc := Program.funct_malloc
  funct_free := Program.funct_free
  funct_zalloc := Program.funct_zalloc
  funct_permset := Program.funct_permset
  funct_firstpathnodeFn := Search.funct_firstpathnodeFn
  funct_othernodeFn := Search.funct_othernodeFn
  funct_firstterminalFn := Search.funct_firstterminalFn
  funct_processnodeFn := Search.funct_processnodeFn
  funct_recoverFn := Search.funct_recoverFn
  funct_nautyFn := Search.funct_nautyFn
  funct_maketargetcellFn := Search.funct_maketargetcellFn
  funct_breakoutFn := Search.funct_breakoutFn
  funct_fmpermFn := Search.funct_fmpermFn
  funct_fmptnFn := Search.funct_fmptnFn
  funct_orbjoinFn := Search.funct_orbjoinFn
  funct_shortpruneFn := Search.funct_shortpruneFn
  funct_longpruneFn := Search.funct_longpruneFn
  funct_dorefFn := Search.funct_dorefFn
  funct_nautilCheck := Top.funct_nautilCheck
  funct_nautilFreedyn := Top.funct_nautilFreedyn
  funct_nautyFreedyn := Top.funct_nautyFreedyn
  var_leftbit := rfl
  var_nautilBit := rfl
  var_nautilWorkperm := rfl
  var_nautilWorkpermSz := rfl
  var_nautyBit := rfl
  var_nautyCanonlab := rfl
  var_nautyCanonlabSz := rfl
  var_nautyDefltwork := rfl
  var_nautyDefltworkSz := rfl
  var_nautyActive := rfl
  var_nautyActiveSz := rfl
  var_nautyCanoncode := rfl
  var_nautyCanoncodeSz := rfl
  var_nautyFixedpts := rfl
  var_nautyFixedptsSz := rfl
  var_nautyFirstcode := rfl
  var_nautyFirstcodeSz := rfl
  var_nautyWorkperm := rfl
  var_nautyWorkpermSz := rfl
  var_nautyFirsttc := rfl
  var_nautyFirsttcSz := rfl
  var_nautyFirstlab := rfl
  var_nautyFirstlabSz := rfl
  var_getcanon := rfl
  var_digraph := rfl
  var_writeautoms := rfl
  var_cartesian := rfl
  var_linelength := rfl
  var_outfile := rfl
  var_userautomproc := rfl
  var_userlevelproc := rfl
  var_usernodeproc := rfl
  var_usercanonproc := rfl
  var_invarproc := rfl
  var_tcLevel := rfl
  var_mininvarlevel := rfl
  var_maxinvarlevel := rfl
  var_invararg := rfl
  var_dispatch := rfl
  var_orbits := rfl
  var_domarkers := rfl
  var_doschreier := rfl
  var_m := rfl
  var_n := rfl
  var_g := rfl
  var_canong := rfl
  var_stats := rfl
  var_gcaFirst := rfl
  var_gcaCanon := rfl
  var_noncheaplevel := rfl
  var_allsamelevel := rfl
  var_eqlevFirst := rfl
  var_eqlevCanon := rfl
  var_compCanon := rfl
  var_samerows := rfl
  var_canonlevel := rfl
  var_stabvertex := rfl
  var_cosetindex := rfl
  var_needshortprune := rfl
  var_tcnode0 := rfl
  var_allocM := rfl
  var_workspace := rfl
  var_worktop := rfl
  var_fmptr := rfl
  var_invapplics := rfl
  var_invsuccesses := rfl
  var_invarsuclevel := rfl
  var_killRequest := rfl
  distinct := of_decide_eq_true dense_distinct
  field_tcnodeNext := DenseLayout.field_tcnodeNext
  field_tcnodeTcell := DenseLayout.field_tcnodeTcell
  field_statsGrpsize1 := DenseLayout.field_statsGrpsize1
  field_statsGrpsize2 := DenseLayout.field_statsGrpsize2
  field_statsNumorbits := DenseLayout.field_statsNumorbits
  field_statsNumgenerators := DenseLayout.field_statsNumgenerators
  field_statsErrstatus := DenseLayout.field_statsErrstatus
  field_statsNumnodes := DenseLayout.field_statsNumnodes
  field_statsNumbadleaves := DenseLayout.field_statsNumbadleaves
  field_statsMaxlevel := DenseLayout.field_statsMaxlevel
  field_statsTctotal := DenseLayout.field_statsTctotal
  field_statsCanupdates := DenseLayout.field_statsCanupdates
  field_dIsautom := DenseLayout.field_dIsautom
  field_dTestcanlab := DenseLayout.field_dTestcanlab
  field_dUpdatecan := DenseLayout.field_dUpdatecan
  field_dRefine := DenseLayout.field_dRefine
  field_dRefine1 := DenseLayout.field_dRefine1
  field_dCheapautom := DenseLayout.field_dCheapautom
  field_dTargetcell := DenseLayout.field_dTargetcell
  sizeof_tcnode := DenseLayout.sizeof_tcnode

/-! The dense instance's blocks are the dense `Block` constants. -/

@[simp] theorem NautyEnv.dense_nextelement : (NautyEnv.nextelement : block) = Block.nextelement := rfl
@[simp] theorem NautyEnv.dense_leftbit : (NautyEnv.leftbit : block) = Block.leftbit := rfl
@[simp] theorem NautyEnv.dense_nautilBit : (NautyEnv.nautilBit : block) = Block.nautilBit := rfl
@[simp] theorem NautyEnv.dense_malloc : (NautyEnv.malloc : block) = Block.malloc := rfl
@[simp] theorem NautyEnv.dense_free : (NautyEnv.free : block) = Block.free := rfl
@[simp] theorem NautyEnv.dense_zalloc : (NautyEnv.zalloc : block) = Block.zalloc := rfl
@[simp] theorem NautyEnv.dense_nautilWorkperm : (NautyEnv.nautilWorkperm : block) = Block.nautilWorkperm := rfl
@[simp] theorem NautyEnv.dense_nautilWorkpermSz : (NautyEnv.nautilWorkpermSz : block) = Block.nautilWorkpermSz := rfl
@[simp] theorem NautyEnv.dense_permset : (NautyEnv.permset : block) = Block.permset := rfl
@[simp] theorem NautyEnv.dense_nautyBit : (NautyEnv.nautyBit : block) = Block.nautyBit := rfl
@[simp] theorem NautyEnv.dense_nautyCanonlab : (NautyEnv.nautyCanonlab : block) = Block.nautyCanonlab := rfl
@[simp] theorem NautyEnv.dense_nautyCanonlabSz : (NautyEnv.nautyCanonlabSz : block) = Block.nautyCanonlabSz := rfl
@[simp] theorem NautyEnv.dense_nautyDefltwork : (NautyEnv.nautyDefltwork : block) = Block.nautyDefltwork := rfl
@[simp] theorem NautyEnv.dense_nautyDefltworkSz : (NautyEnv.nautyDefltworkSz : block) = Block.nautyDefltworkSz := rfl
@[simp] theorem NautyEnv.dense_nautyActive : (NautyEnv.nautyActive : block) = Block.nautyActive := rfl
@[simp] theorem NautyEnv.dense_nautyActiveSz : (NautyEnv.nautyActiveSz : block) = Block.nautyActiveSz := rfl
@[simp] theorem NautyEnv.dense_nautyCanoncode : (NautyEnv.nautyCanoncode : block) = Block.nautyCanoncode := rfl
@[simp] theorem NautyEnv.dense_nautyCanoncodeSz : (NautyEnv.nautyCanoncodeSz : block) = Block.nautyCanoncodeSz := rfl
@[simp] theorem NautyEnv.dense_nautyFixedpts : (NautyEnv.nautyFixedpts : block) = Block.nautyFixedpts := rfl
@[simp] theorem NautyEnv.dense_nautyFixedptsSz : (NautyEnv.nautyFixedptsSz : block) = Block.nautyFixedptsSz := rfl
@[simp] theorem NautyEnv.dense_nautyFirstcode : (NautyEnv.nautyFirstcode : block) = Block.nautyFirstcode := rfl
@[simp] theorem NautyEnv.dense_nautyFirstcodeSz : (NautyEnv.nautyFirstcodeSz : block) = Block.nautyFirstcodeSz := rfl
@[simp] theorem NautyEnv.dense_nautyWorkperm : (NautyEnv.nautyWorkperm : block) = Block.nautyWorkperm := rfl
@[simp] theorem NautyEnv.dense_nautyWorkpermSz : (NautyEnv.nautyWorkpermSz : block) = Block.nautyWorkpermSz := rfl
@[simp] theorem NautyEnv.dense_nautyFirsttc : (NautyEnv.nautyFirsttc : block) = Block.nautyFirsttc := rfl
@[simp] theorem NautyEnv.dense_nautyFirsttcSz : (NautyEnv.nautyFirsttcSz : block) = Block.nautyFirsttcSz := rfl
@[simp] theorem NautyEnv.dense_nautyFirstlab : (NautyEnv.nautyFirstlab : block) = Block.nautyFirstlab := rfl
@[simp] theorem NautyEnv.dense_nautyFirstlabSz : (NautyEnv.nautyFirstlabSz : block) = Block.nautyFirstlabSz := rfl
@[simp] theorem NautyEnv.dense_getcanon : (NautyEnv.getcanon : block) = Search.Block.getcanon := rfl
@[simp] theorem NautyEnv.dense_digraph : (NautyEnv.digraph : block) = Search.Block.digraph := rfl
@[simp] theorem NautyEnv.dense_writeautoms : (NautyEnv.writeautoms : block) = Search.Block.writeautoms := rfl
@[simp] theorem NautyEnv.dense_cartesian : (NautyEnv.cartesian : block) = Search.Block.cartesian := rfl
@[simp] theorem NautyEnv.dense_linelength : (NautyEnv.linelength : block) = Search.Block.linelength := rfl
@[simp] theorem NautyEnv.dense_outfile : (NautyEnv.outfile : block) = Search.Block.outfile := rfl
@[simp] theorem NautyEnv.dense_userautomproc : (NautyEnv.userautomproc : block) = Search.Block.userautomproc := rfl
@[simp] theorem NautyEnv.dense_userlevelproc : (NautyEnv.userlevelproc : block) = Search.Block.userlevelproc := rfl
@[simp] theorem NautyEnv.dense_usernodeproc : (NautyEnv.usernodeproc : block) = Search.Block.usernodeproc := rfl
@[simp] theorem NautyEnv.dense_usercanonproc : (NautyEnv.usercanonproc : block) = Search.Block.usercanonproc := rfl
@[simp] theorem NautyEnv.dense_invarproc : (NautyEnv.invarproc : block) = Search.Block.invarproc := rfl
@[simp] theorem NautyEnv.dense_tcLevel : (NautyEnv.tcLevel : block) = Search.Block.tcLevel := rfl
@[simp] theorem NautyEnv.dense_mininvarlevel : (NautyEnv.mininvarlevel : block) = Search.Block.mininvarlevel := rfl
@[simp] theorem NautyEnv.dense_maxinvarlevel : (NautyEnv.maxinvarlevel : block) = Search.Block.maxinvarlevel := rfl
@[simp] theorem NautyEnv.dense_invararg : (NautyEnv.invararg : block) = Search.Block.invararg := rfl
@[simp] theorem NautyEnv.dense_dispatch : (NautyEnv.dispatch : block) = Search.Block.dispatch := rfl
@[simp] theorem NautyEnv.dense_orbits : (NautyEnv.orbits : block) = Search.Block.orbits := rfl
@[simp] theorem NautyEnv.dense_domarkers : (NautyEnv.domarkers : block) = Search.Block.domarkers := rfl
@[simp] theorem NautyEnv.dense_doschreier : (NautyEnv.doschreier : block) = Search.Block.doschreier := rfl
@[simp] theorem NautyEnv.dense_m : (NautyEnv.m : block) = Search.Block.m := rfl
@[simp] theorem NautyEnv.dense_n : (NautyEnv.n : block) = Search.Block.n := rfl
@[simp] theorem NautyEnv.dense_g : (NautyEnv.g : block) = Search.Block.g := rfl
@[simp] theorem NautyEnv.dense_canong : (NautyEnv.canong : block) = Search.Block.canong := rfl
@[simp] theorem NautyEnv.dense_stats : (NautyEnv.stats : block) = Search.Block.stats := rfl
@[simp] theorem NautyEnv.dense_gcaFirst : (NautyEnv.gcaFirst : block) = Search.Block.gcaFirst := rfl
@[simp] theorem NautyEnv.dense_gcaCanon : (NautyEnv.gcaCanon : block) = Search.Block.gcaCanon := rfl
@[simp] theorem NautyEnv.dense_noncheaplevel : (NautyEnv.noncheaplevel : block) = Search.Block.noncheaplevel := rfl
@[simp] theorem NautyEnv.dense_allsamelevel : (NautyEnv.allsamelevel : block) = Search.Block.allsamelevel := rfl
@[simp] theorem NautyEnv.dense_eqlevFirst : (NautyEnv.eqlevFirst : block) = Search.Block.eqlevFirst := rfl
@[simp] theorem NautyEnv.dense_eqlevCanon : (NautyEnv.eqlevCanon : block) = Search.Block.eqlevCanon := rfl
@[simp] theorem NautyEnv.dense_compCanon : (NautyEnv.compCanon : block) = Search.Block.compCanon := rfl
@[simp] theorem NautyEnv.dense_samerows : (NautyEnv.samerows : block) = Search.Block.samerows := rfl
@[simp] theorem NautyEnv.dense_canonlevel : (NautyEnv.canonlevel : block) = Search.Block.canonlevel := rfl
@[simp] theorem NautyEnv.dense_stabvertex : (NautyEnv.stabvertex : block) = Search.Block.stabvertex := rfl
@[simp] theorem NautyEnv.dense_cosetindex : (NautyEnv.cosetindex : block) = Search.Block.cosetindex := rfl
@[simp] theorem NautyEnv.dense_needshortprune : (NautyEnv.needshortprune : block) = Search.Block.needshortprune := rfl
@[simp] theorem NautyEnv.dense_tcnode0 : (NautyEnv.tcnode0 : block) = Search.Block.tcnode0 := rfl
@[simp] theorem NautyEnv.dense_allocM : (NautyEnv.allocM : block) = Search.Block.allocM := rfl
@[simp] theorem NautyEnv.dense_workspace : (NautyEnv.workspace : block) = Search.Block.workspace := rfl
@[simp] theorem NautyEnv.dense_worktop : (NautyEnv.worktop : block) = Search.Block.worktop := rfl
@[simp] theorem NautyEnv.dense_fmptr : (NautyEnv.fmptr : block) = Search.Block.fmptr := rfl
@[simp] theorem NautyEnv.dense_invapplics : (NautyEnv.invapplics : block) = Search.Block.invapplics := rfl
@[simp] theorem NautyEnv.dense_invsuccesses : (NautyEnv.invsuccesses : block) = Search.Block.invsuccesses := rfl
@[simp] theorem NautyEnv.dense_invarsuclevel : (NautyEnv.invarsuclevel : block) = Search.Block.invarsuclevel := rfl
@[simp] theorem NautyEnv.dense_killRequest : (NautyEnv.killRequest : block) = Search.Block.killRequest := rfl
@[simp] theorem NautyEnv.dense_firstpathnodeFn : (NautyEnv.firstpathnodeFn : block) = Search.Block.firstpathnodeFn := rfl
@[simp] theorem NautyEnv.dense_othernodeFn : (NautyEnv.othernodeFn : block) = Search.Block.othernodeFn := rfl
@[simp] theorem NautyEnv.dense_firstterminalFn : (NautyEnv.firstterminalFn : block) = Search.Block.firstterminalFn := rfl
@[simp] theorem NautyEnv.dense_processnodeFn : (NautyEnv.processnodeFn : block) = Search.Block.processnodeFn := rfl
@[simp] theorem NautyEnv.dense_recoverFn : (NautyEnv.recoverFn : block) = Search.Block.recoverFn := rfl
@[simp] theorem NautyEnv.dense_nautyFn : (NautyEnv.nautyFn : block) = Search.Block.nautyFn := rfl
@[simp] theorem NautyEnv.dense_maketargetcellFn : (NautyEnv.maketargetcellFn : block) = Search.Block.maketargetcellFn := rfl
@[simp] theorem NautyEnv.dense_breakoutFn : (NautyEnv.breakoutFn : block) = Search.Block.breakoutFn := rfl
@[simp] theorem NautyEnv.dense_fmpermFn : (NautyEnv.fmpermFn : block) = Search.Block.fmpermFn := rfl
@[simp] theorem NautyEnv.dense_fmptnFn : (NautyEnv.fmptnFn : block) = Search.Block.fmptnFn := rfl
@[simp] theorem NautyEnv.dense_orbjoinFn : (NautyEnv.orbjoinFn : block) = Search.Block.orbjoinFn := rfl
@[simp] theorem NautyEnv.dense_shortpruneFn : (NautyEnv.shortpruneFn : block) = Search.Block.shortpruneFn := rfl
@[simp] theorem NautyEnv.dense_longpruneFn : (NautyEnv.longpruneFn : block) = Search.Block.longpruneFn := rfl
@[simp] theorem NautyEnv.dense_dorefFn : (NautyEnv.dorefFn : block) = Search.Block.dorefFn := rfl
@[simp] theorem NautyEnv.dense_nautilCheck : (NautyEnv.nautilCheck : block) = Top.Block.nautilCheck := rfl
@[simp] theorem NautyEnv.dense_nautilFreedyn : (NautyEnv.nautilFreedyn : block) = Top.Block.nautilFreedyn := rfl
@[simp] theorem NautyEnv.dense_nautyFreedyn : (NautyEnv.nautyFreedyn : block) = Top.Block.nautyFreedyn := rfl

end NautyVerified.Program
