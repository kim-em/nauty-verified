import NautyVerified.Proofs.Search.Blocks
import NautyVerified.Proofs.Refine.Fn
import NautyVerified.Proofs.Alloc.Dyn3

/-!
# The state nauty.c's search works in

`SLoc`: where one `nauty()` call keeps its data: the caller's graph, `lab`,
`ptn`, `orbits`, `statsblk` and `canong`; the automorphism workspace; the
blocks of nauty.c's `DYNALLSTAT` arrays; the harness's automorphism
callback; `M`.

`SearchAt m S ctx st pre nsp`: memory holds HexGraphIso's search state `st` (a
`Search n`, run with `inf = NAUTY_INFINITY`, see `Spec/SearchInf.lean`):

- the pointer globals, the option copies and the dispatch table hold the
  values the pinned configuration gives them (`Fixed`);
- each static `int` of nauty.c holds the field of `st` it mirrors, and
  `needshortprune` holds `nsp` (`Scalars`): HexGraphIso carries the
  short-prune request in `Exit.unwind`, nauty in this global;
- the members of the caller's `statsblk` hold `st`'s counters (`Stats`);
  `maxlevel` only once the first leaf is reached (`pre = false`): before
  that the harness has not initialised it, and nothing reads it;
- the `DYNALLSTAT` arrays hold `st`'s arrays (`firstcode`/`canoncode` as
  `short`s, `firsttc` as signed `int`s), `canong`'s first `samerows` rows
  represent `st.canong`, and the workspace holds `st.autos` (`Arrays`);
- naugraph.c's and nautil.c's work arrays are allocated somewhere apart from
  everything else (`Work`), since the callees may reallocate them.

The target-cell list (`tcnode0`) is described separately (`TcAt`), since each
level owns one of its nodes.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt)
open NautyVerified.Proofs.Set (BitTable longs)
open NautyVerified.Proofs.Graph (GraphAt)
open NautyVerified.Proofs.Nextelement (LeftbitTable)
open NautyVerified.Proofs.Init (BytecountTable)
open Hex.GraphIso.Nauty

/-- `NAUTY_INFINITY` for `int`s of at least 32 bits. -/
abbrev nautyInf : Nat := 2000000002

/-- The automorphism workspace holds this many `(fix, mcr)` pairs. -/
abbrev wsPairs : Nat := 500

/-- A `short` array holding `o` (values below `2^15`). -/
def shorts (o : Array Nat) (i : Nat) : val := .Vint (ir (o[i]! : Int))

/-- An `int` array holding the signed values `o`. -/
def intsZ (o : Array Int) (i : Nat) : val := .Vint (ir o[i]!)

/-- `chunk` at byte `off` of block `b` holds `v` and is writable. -/
structure FieldAt (m : mem) (chunk : memory_chunk) (b : block) (off : Int) (v : val) : Prop where
  load : Mem.load chunk m b (zOfInt off) = some v
  writable : Mem.valid_access m chunk b (zOfInt off) .Writable

/-- Where one `nauty()` call keeps its data. -/
structure SLoc where
  bg : block
  gofs : ptrofs
  gw : Nat → Lib.Integers.int64
  bl : block
  lofs : ptrofs
  bp : block
  pofs : ptrofs
  bo : block
  oofs : ptrofs
  bst : block
  sofs : ptrofs
  bc : block
  cofs : ptrofs
  /-- The automorphism workspace: `2 * wsPairs * M` setwords. -/
  bws : block
  wofs : ptrofs
  /-- nauty.c's `DYNALLSTAT` arrays: blocks and capacities. -/
  bA : block
  capA : Nat
  bF : block
  capF : Nat
  bWP : block
  capWP : Nat
  bFL : block
  capFL : Nat
  bCL : block
  capCL : Nat
  bFC : block
  capFC : Nat
  bCC : block
  capCC : Nat
  bTC : block
  capTC : Nat
  /-- The harness's `userautomproc`. -/
  bUA : block
  M : Nat

namespace SLoc
variable (S : SLoc)
abbrev lb : Int := intOfZ (Ptrofs.unsigned S.lofs)
abbrev pb : Int := intOfZ (Ptrofs.unsigned S.pofs)
abbrev ob : Int := intOfZ (Ptrofs.unsigned S.oofs)
abbrev sb : Int := intOfZ (Ptrofs.unsigned S.sofs)
abbrev cb : Int := intOfZ (Ptrofs.unsigned S.cofs)
abbrev wb : Int := intOfZ (Ptrofs.unsigned S.wofs)

/-- The dispatch table's refinement procedure: `refine1` when `M = 1`. -/
def refineBlock : block := if S.M = 1 then Refine.Block.refine1 else Refine.Block.refine
end SLoc

/-- A pointer global holds `v`. -/
abbrev PtrAt (m : mem) (b : block) (v : val) : Prop := FieldAt m .Mint64 b 0 v

/-- An `int` global holds `v`. -/
abbrev IntAt (m : mem) (b : block) (v : Int) : Prop := FieldAt m .Mint32 b 0 (.Vint (ir v))

/-- The pointer globals, option copies and dispatch table, fixed for the whole
search by `nauty()` under the pinned configuration. -/
structure Fixed (n : Nat) (m : mem) (S : SLoc) : Prop where
  g : PtrAt m Block.g (.Vptr S.bg S.gofs)
  canong : PtrAt m Block.canong (.Vptr S.bc S.cofs)
  orbits : PtrAt m Block.orbits (.Vptr S.bo S.oofs)
  stats : PtrAt m Block.stats (.Vptr S.bst S.sofs)
  workspace : PtrAt m Block.workspace (.Vptr S.bws S.wofs)
  worktop : PtrAt m Block.worktop
    (.Vptr S.bws (Ptrofs.repr (zOfInt (S.wb + 8 * (2 * wsPairs * S.M)))))
  mm : IntAt m Block.m S.M
  nn : IntAt m Block.n n
  getcanon : IntAt m Block.getcanon 1
  digraph : IntAt m Block.digraph 0
  writeautoms : IntAt m Block.writeautoms 0
  domarkers : IntAt m Block.domarkers 0
  doschreier : IntAt m Block.doschreier 0
  tcLevel : IntAt m Block.tcLevel 100
  invarproc : PtrAt m Block.invarproc Vnullptr
  usernodeproc : PtrAt m Block.usernodeproc Vnullptr
  userlevelproc : PtrAt m Block.userlevelproc Vnullptr
  usercanonproc : PtrAt m Block.usercanonproc Vnullptr
  userautomproc : PtrAt m Block.userautomproc (.Vptr S.bUA Ptrofs.zero)
  /-- `dispatch.isautom`, `testcanlab`, `updatecan`, `refine`, `refine1`,
  `cheapautom`, `targetcell`. -/
  dIsautom : FieldAt m .Mint64 Block.dispatch 0 (.Vptr Block.isautomFn Ptrofs.zero)
  dTestcanlab : FieldAt m .Mint64 Block.dispatch 8 (.Vptr Block.testcanlabFn Ptrofs.zero)
  dUpdatecan : FieldAt m .Mint64 Block.dispatch 16 (.Vptr Block.updatecanFn Ptrofs.zero)
  dRefine : FieldAt m .Mint64 Block.dispatch 24 (.Vptr S.refineBlock Ptrofs.zero)
  dRefine1 : FieldAt m .Mint64 Block.dispatch 32 (.Vptr Refine.Block.refine1 Ptrofs.zero)
  dCheapautom : FieldAt m .Mint64 Block.dispatch 40 (.Vptr Block.cheapautomFn Ptrofs.zero)
  dTargetcell : FieldAt m .Mint64 Block.dispatch 48 (.Vptr Block.targetcellFn Ptrofs.zero)
  kill : IntAt m Block.killRequest 0
  allocM : IntAt m Block.allocM S.M

/-- nauty.c's static `int`s hold `st`'s fields. -/
structure Scalars {n : Nat} (m : mem) (st : Search n) (nsp : Bool) : Prop where
  gcaFirst : IntAt m Block.gcaFirst st.gcaFirst
  gcaCanon : IntAt m Block.gcaCanon st.gcaCanon
  noncheaplevel : IntAt m Block.noncheaplevel st.noncheaplevel
  allsamelevel : IntAt m Block.allsamelevel st.allsamelevel
  eqlevFirst : IntAt m Block.eqlevFirst st.eqlevFirst
  eqlevCanon : IntAt m Block.eqlevCanon st.eqlevCanon
  compCanon : IntAt m Block.compCanon st.compCanon
  samerows : IntAt m Block.samerows st.samerows
  canonlevel : IntAt m Block.canonlevel st.canonlevel
  stabvertex : IntAt m Block.stabvertex st.stabvertex
  cosetindex : IntAt m Block.cosetindex st.cosetindex
  needshortprune : IntAt m Block.needshortprune (if nsp then 1 else 0)

/-- The `statsblk` members (x86-64 layout) hold `st`'s counters; `maxlevel`
only once the first leaf is reached. -/
structure Stats {n : Nat} (m : mem) (S : SLoc) (st : Search n) (pre : Bool) : Prop where
  numorbits : FieldAt m .Mint32 S.bst (S.sb + 12) (.Vint (ir st.numorbits))
  numgenerators : FieldAt m .Mint32 S.bst (S.sb + 16) (.Vint (ir st.numgenerators))
  numnodes : FieldAt m .Mint64 S.bst (S.sb + 24) (.Vlong (lr st.numnodes))
  numbadleaves : FieldAt m .Mint64 S.bst (S.sb + 32) (.Vlong (lr st.numbadleaves))
  maxlevel : pre = false → FieldAt m .Mint32 S.bst (S.sb + 40) (.Vint (ir st.maxlevel))
  maxlevelW : Mem.valid_access m .Mint32 S.bst (zOfInt (S.sb + 40)) .Writable
  tctotal : FieldAt m .Mint64 S.bst (S.sb + 48) (.Vlong (lr st.tctotal))
  canupdates : FieldAt m .Mint64 S.bst (S.sb + 56) (.Vlong (lr st.canupdates))
  /-- The `statsblk` (88 bytes) lies inside the address space. -/
  fits : S.sb + 88 < 2 ^ 64

/-- `canong`'s first `samerows` rows represent `st.canong`. -/
structure CanongAt {n : Nat} (m : mem) (S : SLoc) (rows : Array (VSet n)) (samerows : Nat) :
    Prop where
  arr : ∃ cw, ArrayAt m .Mint64 S.bc S.cb (longs cw) (S.M * n) ∧
    ∀ v < samerows, SetRep (fun w => bv64 (cw (S.M * v + w))) S.M rows[v]!

/-- The workspace holds the stored `(fix, mcr)` pairs. -/
structure AutosAt {n : Nat} (m : mem) (S : SLoc) (autos : Array (VSet n × VSet n)) : Prop where
  size : autos.size ≤ wsPairs
  arr : ∃ ww, ArrayAt m .Mint64 S.bws S.wb (longs ww) (2 * wsPairs * S.M) ∧
    ∀ i < autos.size,
      SetRep (fun w => bv64 (ww (2 * S.M * i + w))) S.M autos[i]!.1 ∧
      SetRep (fun w => bv64 (ww (2 * S.M * i + S.M + w))) S.M autos[i]!.2
  fmptr : PtrAt m Block.fmptr
    (.Vptr S.bws (Ptrofs.repr (zOfInt (S.wb + 8 * (2 * S.M * autos.size)))))

/-- nauty.c's arrays hold `st`'s. -/
structure Arrays {n : Nat} (m : mem) (S : SLoc) (ctx : Ctx n) (st : Search n) : Prop where
  lab : ArrayAt m .Mint32 S.bl S.lb (ints st.lab) n
  ptn : ArrayAt m .Mint32 S.bp S.pb (ints st.ptn) n
  orbits : ArrayAt m .Mint32 S.bo S.ob (ints st.orbits) n
  active : ∃ aw, ArrayAt m .Mint64 S.bA 0 (longs aw) S.M ∧
    SetRep (fun w => bv64 (aw w)) S.M st.active
  fixedpts : ∃ fw, ArrayAt m .Mint64 S.bF 0 (longs fw) S.M ∧
    SetRep (fun w => bv64 (fw w)) S.M st.fixedpts
  /-- `workperm` is scratch: `doref` passes it to `refine` as the count array,
  and every reader refills it first, so its contents are not related to `st`. -/
  workperm : ∃ v, ArrayAt m .Mint32 S.bWP 0 v n
  firstlab : ArrayAt m .Mint32 S.bFL 0 (ints st.firstlab) n
  canonlab : ArrayAt m .Mint32 S.bCL 0 (ints st.canonlab) n
  firstcode : ArrayAt m .Mint16signed S.bFC 0 (shorts st.firstcode) (n + 2)
  canoncode : ArrayAt m .Mint16signed S.bCC 0 (shorts st.canoncode) (n + 2)
  firsttc : ArrayAt m .Mint32 S.bTC 0 (intsZ st.firsttc) (n + 2)
  canong : CanongAt m S st.canong st.samerows
  autos : AutosAt m S st.autos
  graph : GraphAt m S.bg S.gofs S.gw ctx.g S.M

/-- naugraph.c's and nautil.c's work arrays, wherever their last allocation put
them: each in use is valid, and none of them is a block of `S`. -/
structure WorkAt (n : Nat) (m : mem) (S : SLoc) (fixedBlocks : List block) : Prop where
  arr : ∃ (capW : Nat) (bW : block) (capS : Nat) (bS : block) (capB : Nat) (bB : block)
      (capN : Nat) (bN : block),
    DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 capW bW ∧
    DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 capS bS ∧
    DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 capB bB ∧
    DynAt m Block.nautilWorkperm Block.nautilWorkpermSz 4 capN bN ∧
    (0 < capW → bW ∉ fixedBlocks) ∧ (0 < capS → bS ∉ fixedBlocks) ∧
    (0 < capB → bB ∉ fixedBlocks) ∧ (0 < capN → bN ∉ fixedBlocks) ∧
    (0 < capW → 0 < capS → bW ≠ bS) ∧ (0 < capW → 0 < capB → bW ≠ bB) ∧
    (0 < capS → 0 < capB → bS ≠ bB) ∧ (0 < capN → 0 < capW → bN ≠ bW) ∧
    (0 < capN → 0 < capS → bN ≠ bS) ∧ (0 < capN → 0 < capB → bN ≠ bB)

/-- The target-cell list from `tcnode0`: node `i` (a `tcnode`, `next` at 0 and
`tcellptr` at 8) owns the `M`-word target cell of level `i + 1`. -/
def TcChain (m : mem) (M : Nat) (prev : block) : List (block × block) → Prop
  | [] => FieldAt m .Mint64 prev 0 Vnullptr
  | (nd, tc) :: rest => FieldAt m .Mint64 prev 0 (.Vptr nd Ptrofs.zero) ∧
      FieldAt m .Mint64 nd 8 (.Vptr tc Ptrofs.zero) ∧
      (∃ vals, ArrayAt m .Mint64 tc 0 vals M) ∧ TcChain m M nd rest

/-- The blocks the search may not confuse: the caller's, nauty.c's arrays, and
the globals and tables it reads. -/
def SLoc.blocks (S : SLoc) : List block :=
  [S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC,
   S.bTC, S.bUA,
   Block.getcanon, Block.digraph, Block.writeautoms, Block.domarkers, Block.doschreier,
   Block.tcLevel, Block.invarproc, Block.usernodeproc, Block.userlevelproc, Block.usercanonproc,
   Block.userautomproc, Block.dispatch, Block.orbits, Block.m, Block.n, Block.g, Block.canong,
   Block.stats, Block.gcaFirst, Block.gcaCanon, Block.noncheaplevel, Block.allsamelevel,
   Block.eqlevFirst, Block.eqlevCanon, Block.compCanon, Block.samerows, Block.canonlevel,
   Block.stabvertex, Block.cosetindex, Block.needshortprune, Block.tcnode0, Block.allocM,
   Block.workspace, Block.worktop, Block.fmptr, Block.killRequest,
   Program.Block.nautyActive, Program.Block.nautyActiveSz, Program.Block.nautyFixedpts,
   Program.Block.nautyFixedptsSz, Program.Block.nautyWorkperm, Program.Block.nautyWorkpermSz,
   Program.Block.nautyFirstlab, Program.Block.nautyFirstlabSz, Program.Block.nautyCanonlab,
   Program.Block.nautyCanonlabSz, Program.Block.nautyFirstcode, Program.Block.nautyFirstcodeSz,
   Program.Block.nautyCanoncode, Program.Block.nautyCanoncodeSz, Program.Block.nautyFirsttc,
   Program.Block.nautyFirsttcSz,
   Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
   Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
   Block.nautilWorkperm, Block.nautilWorkpermSz,
   Program.Block.nautyBit, Block.naugraphBit, Block.nautilBit, Block.naugraphBytecount,
   Block.leftbit]

/-- nauty.c's `DYNALLSTAT` pairs, with the capacities the search needs. -/
structure Dyns (n : Nat) (m : mem) (S : SLoc) : Prop where
  active : DynAt m Program.Block.nautyActive Program.Block.nautyActiveSz 8 S.capA S.bA
  fixedpts : DynAt m Program.Block.nautyFixedpts Program.Block.nautyFixedptsSz 8 S.capF S.bF
  workperm : DynAt m Program.Block.nautyWorkperm Program.Block.nautyWorkpermSz 4 S.capWP S.bWP
  firstlab : DynAt m Program.Block.nautyFirstlab Program.Block.nautyFirstlabSz 4 S.capFL S.bFL
  canonlab : DynAt m Program.Block.nautyCanonlab Program.Block.nautyCanonlabSz 4 S.capCL S.bCL
  firstcode : DynAt m Program.Block.nautyFirstcode Program.Block.nautyFirstcodeSz 2 S.capFC S.bFC
  canoncode : DynAt m Program.Block.nautyCanoncode Program.Block.nautyCanoncodeSz 2 S.capCC S.bCC
  firsttc : DynAt m Program.Block.nautyFirsttc Program.Block.nautyFirsttcSz 4 S.capTC S.bTC
  capA : S.M ≤ S.capA
  capF : S.M ≤ S.capF
  capWP : n ≤ S.capWP
  capFL : n ≤ S.capFL
  capCL : n ≤ S.capCL
  capFC : n + 2 ≤ S.capFC
  capCC : n + 2 ≤ S.capCC
  capTC : n + 2 ≤ S.capTC

/-- The tables nauty reads. -/
structure Tables (m : mem) : Prop where
  nautyBit : BitTable m Program.Block.nautyBit
  naugraphBit : BitTable m Block.naugraphBit
  nautilBit : BitTable m Block.nautilBit
  left : LeftbitTable m
  bytes : BytecountTable m

/-- HexGraphIso's invariants of the search state that the C needs. -/
structure SInv {n : Nat} (st : Search n) : Prop where
  labSize : st.lab.size = n
  labSmall : ∀ i < n, st.lab[i]! < n
  labSurj : ∀ v < n, ∃ i < n, st.lab[i]! = v
  ptnSize : st.ptn.size = n
  ptnVals : ∀ i < n, st.ptn[i]! ≤ n + 1 ∨ st.ptn[i]! = nautyInf
  ptnLast : st.ptn[n - 1]! = 0
  orbitsSmall : ∀ i < n, st.orbits[i]! < n
  codesSmall : ∀ i < n + 2, st.firstcode[i]! < 32768 ∧ st.canoncode[i]! < 32768
  firsttcRange : ∀ i < n + 2, -1 ≤ st.firsttc[i]! ∧ st.firsttc[i]! < n
  workpermSmall : ∀ i < n, st.workperm[i]! < n
  samerows : st.samerows ≤ n
  orbitsSize : st.orbits.size = n
  workpermSize : st.workperm.size = n
  firstlabSize : st.firstlab.size = n
  canonlabSize : st.canonlab.size = n
  firstcodeSize : st.firstcode.size = n + 2
  canoncodeSize : st.canoncode.size = n + 2
  firsttcSize : st.firsttc.size = n + 2
  canongSize : st.canong.size = n
  /-- The level-valued statics fit nauty.c's `int`s. -/
  scalars : st.gcaFirst < 2147483648 ∧ st.gcaCanon < 2147483648 ∧
    st.noncheaplevel < 2147483648 ∧ st.allsamelevel < 2147483648 ∧
    st.eqlevFirst < 2147483648 ∧ -1 ≤ st.eqlevCanon ∧ st.eqlevCanon < 2147483648 ∧
    -1 ≤ st.compCanon ∧ st.compCanon ≤ 1 ∧ st.canonlevel < 2147483648 ∧
    st.stabvertex < 2147483648 ∧ st.cosetindex < 2147483648

/-- Memory holds HexGraphIso's search state `st` for the graph `ctx`. -/
structure SearchAt {n : Nat} (m : mem) (S : SLoc) (ctx : Ctx n) (st : Search n) (pre nsp : Bool) :
    Prop where
  fixed : Fixed n m S
  scalars : Scalars m st nsp
  stats : Stats m S st pre
  arrays : Arrays m S ctx st
  dyns : Dyns n m S
  work : WorkAt n m S S.blocks
  tables : Tables m
  distinct : S.blocks.Pairwise (· ≠ ·)
  inv : SInv st
  n0 : 0 < n
  nlt : n < 1073741824
  nM : n ≤ 64 * S.M
  M1 : 0 < S.M
  Mlt : S.M < 33554432

end NautyVerified.Proofs.Search
