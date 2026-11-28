import NautyVerified.Proofs.Search.Blocks
import NautyVerified.Proofs.Refine.Fn
import NautyVerified.Proofs.Alloc.Dyn3
import NautyVerified.Proofs.Dispatch.DenseRep
import NautyVerified.Logic.PermLit

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
  /-- The capacity of naugraph.c's `dnwork` pair, whose block is the workspace. -/
  capD : Nat

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
  /-- `nauty_kill_request` is a volatile global: nauty's reads of it are volatile
  loads (trace events), so only its block's existence matters here. -/
  kill : Mem.valid_access m .Mint32 Block.killRequest (zOfInt 0) .Nonempty
  allocM : IntAt m Block.allocM S.M
  /-- `mininvarlevel`, `maxinvarlevel`, `invararg`: some `int`s, passed to
  `doref` and unused there since `invarproc` is `NULL`. -/
  mininv : ∃ v, FieldAt m .Mint32 Block.mininvarlevel 0 (.Vint v)
  maxinv : ∃ v, FieldAt m .Mint32 Block.maxinvarlevel 0 (.Vint v)
  invarg : ∃ v, FieldAt m .Mint32 Block.invararg 0 (.Vint v)
  /-- `dispatch.freedyn` (`naugraph_freedyn`) and `dispatch.cleanup` (`NULL`), read by
  `nauty()` after the search. -/
  dFreedyn : FieldAt m .Mint64 Block.dispatch 56 (.Vptr Block.naugraphFreedyn Ptrofs.zero)
  dCleanup : FieldAt m .Mint64 Block.dispatch 80 Vnullptr

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
  /-- The members no search function writes, and the block's permissions
  (`StatsFix`). -/
  perm : Mem.range_perm m S.bst (zOfInt S.sb) (zOfInt (S.sb + 88)) .Cur .Freeable
  errstatus : FieldAt m .Mint32 S.bst (S.sb + 20) (.Vint (ir 0))
  grpsize1 : ∃ x, FieldAt m .Mfloat64 S.bst S.sb (.Vfloat x)
  grpsize2 : ∃ i, FieldAt m .Mint32 S.bst (S.sb + 8) (.Vint i)

/-- The part of `Stats` that the search's own stores to `statsblk` (all at
offsets from 12 to 20 or from 24 on) leave alone: the block's permissions,
`errstatus = 0`, and some `grpsize1`/`grpsize2`. -/
structure StatsFix (m : mem) (S : SLoc) : Prop where
  perm : Mem.range_perm m S.bst (zOfInt S.sb) (zOfInt (S.sb + 88)) .Cur .Freeable
  errstatus : FieldAt m .Mint32 S.bst (S.sb + 20) (.Vint (ir 0))
  grpsize1 : ∃ x, FieldAt m .Mfloat64 S.bst S.sb (.Vfloat x)
  grpsize2 : ∃ i, FieldAt m .Mint32 S.bst (S.sb + 8) (.Vint i)

theorem Stats.fix {n : Nat} {m : mem} {S : SLoc} {st : Search n} {pre : Bool}
    (h : Stats m S st pre) : StatsFix m S :=
  ⟨h.perm, h.errstatus, h.grpsize1, h.grpsize2⟩

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
`tcellptr` at 8) owns the `M`-word target cell of level `i + 1`. Both blocks
are as `malloc` made them (16 and `8 * M` bytes), so nauty's final `free`s
succeed. -/
def TcChain (m : mem) (M : Nat) (prev : block) : List (block × block) → Prop
  | [] => FieldAt m .Mint64 prev 0 Vnullptr
  | (nd, tc) :: rest => FieldAt m .Mint64 prev 0 (.Vptr nd Ptrofs.zero) ∧
      FieldAt m .Mint64 nd 8 (.Vptr tc Ptrofs.zero) ∧
      (∃ vals, ArrayAt m .Mint64 tc 0 vals M) ∧
      (Alloc.Malloced m nd 16 ∧ Alloc.Malloced m tc (8 * M)) ∧ TcChain m M nd rest

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
   Block.leftbit, Block.mininvarlevel, Block.maxinvarlevel, Block.invararg,
   Block.naugraphDnwork, Block.naugraphDnworkSz]

/-- The blocks of `S` a search function may change: all but the harness
callback's block and the target-cell list's head `tcnode0`, which no callee writes
(the list itself is framed separately, `TcChain`). -/
abbrev SLoc.Chg (S : SLoc) (z : block) : Prop :=
  z ∈ S.blocks ∧ z ≠ S.bUA ∧ z ≠ Block.tcnode0

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
  /-- The workspace is naugraph.c's `dnwork` (`densenauty` allocates it). -/
  workspace : DynAt m Block.naugraphDnwork Block.naugraphDnworkSz 8 S.capD S.bws
  capWs : 2 * wsPairs * S.M ≤ S.capD

/-- The workspace is as `malloc` made it. -/
theorem Dyns.wsMal {n : Nat} {m : mem} {S : SLoc} (h : Dyns n m S) (hM : 0 < S.M) :
    Alloc.Malloced m S.bws (8 * S.capD) :=
  h.workspace.mal (Nat.lt_of_lt_of_le (Nat.mul_pos (by decide) hM) h.capWs)

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
  ptnLast : st.ptn[n - 1]! ≤ 1
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
  /-- The workspace holds `wsPairs` pairs. -/
  wsCap : st.wsCap = wsPairs
  maxlevelLe : st.maxlevel ≤ n
  numorbitsLe : st.numorbits ≤ n
  orbitsDesc : Hex.GraphIso.Nauty.Orbit.Descending st.orbits n

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

/-! ### The search state for any dispatch representation

The definitions above are the dense program's. Below, the same state for a
linked program with shared globals `E : NautyEnv ge` and dispatch
representation `D : DispatchRep ge O`: the HexGraphIso state is a
`SearchState n (O.Canon n)` over the graph `G : O.Gr n`; the graph and the
canonical store are `D.GraphRep`/`D.CanonRep` on the blocks
`D.graphBlocks gl S.bg` and `D.canonBlocks cl S.bc`; the dispatch table
holds `D`'s procedures; the workspace is `D`'s pair `wsP`/`wsS`; the
procedures' scratch state is `D.Work`, besides nautil.c's `workperm` pair
(`WorkG`); the tables are nautil.c's and nauty.c's (`ETables`) and `D`'s.
`SInvG` and the procedures' graph condition `O.GraphOk` are carried too.
`SearchAtG.dense`/`SearchAt.toG` relate the dense instance to `SearchAt`. -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep ETables envAvoid)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} (D : DispatchRep ge O)

/-- `Fixed` for `D`. -/
structure FixedG (n : Nat) (m : mem) (S : SLoc) : Prop where
  g : PtrAt m E.g (.Vptr S.bg S.gofs)
  canong : PtrAt m E.canong (.Vptr S.bc S.cofs)
  orbits : PtrAt m E.orbits (.Vptr S.bo S.oofs)
  stats : PtrAt m E.stats (.Vptr S.bst S.sofs)
  workspace : PtrAt m E.workspace (.Vptr S.bws S.wofs)
  worktop : PtrAt m E.worktop
    (.Vptr S.bws (Ptrofs.repr (zOfInt (S.wb + 8 * (2 * wsPairs * S.M)))))
  mm : IntAt m E.m S.M
  nn : IntAt m E.n n
  getcanon : IntAt m E.getcanon 1
  digraph : IntAt m E.digraph 0
  writeautoms : IntAt m E.writeautoms 0
  domarkers : IntAt m E.domarkers 0
  doschreier : IntAt m E.doschreier 0
  tcLevel : IntAt m E.tcLevel 100
  invarproc : PtrAt m E.invarproc Vnullptr
  usernodeproc : PtrAt m E.usernodeproc Vnullptr
  userlevelproc : PtrAt m E.userlevelproc Vnullptr
  usercanonproc : PtrAt m E.usercanonproc Vnullptr
  userautomproc : PtrAt m E.userautomproc (.Vptr S.bUA Ptrofs.zero)
  dIsautom : FieldAt m .Mint64 E.dispatch 0 (.Vptr D.isautom Ptrofs.zero)
  dTestcanlab : FieldAt m .Mint64 E.dispatch 8 (.Vptr D.testcanlab Ptrofs.zero)
  dUpdatecan : FieldAt m .Mint64 E.dispatch 16 (.Vptr D.updatecan Ptrofs.zero)
  dRefine : FieldAt m .Mint64 E.dispatch 24 (.Vptr (D.refineAt S.M) Ptrofs.zero)
  dRefine1 : FieldAt m .Mint64 E.dispatch 32 (.Vptr D.refine1 Ptrofs.zero)
  dCheapautom : FieldAt m .Mint64 E.dispatch 40 (.Vptr D.cheapautom Ptrofs.zero)
  dTargetcell : FieldAt m .Mint64 E.dispatch 48 (.Vptr D.targetcell Ptrofs.zero)
  kill : Mem.valid_access m .Mint32 E.killRequest (zOfInt 0) .Nonempty
  allocM : IntAt m E.allocM S.M
  mininv : ∃ v, FieldAt m .Mint32 E.mininvarlevel 0 (.Vint v)
  maxinv : ∃ v, FieldAt m .Mint32 E.maxinvarlevel 0 (.Vint v)
  invarg : ∃ v, FieldAt m .Mint32 E.invararg 0 (.Vint v)
  dFreedyn : FieldAt m .Mint64 E.dispatch 56 (.Vptr D.freedyn Ptrofs.zero)
  dCleanup : FieldAt m .Mint64 E.dispatch 80 Vnullptr

/-- `Scalars` for any canonical store. -/
structure ScalarsG {n : Nat} {κ : Type} (m : mem) (st : SearchState n κ) (nsp : Bool) : Prop where
  gcaFirst : IntAt m E.gcaFirst st.gcaFirst
  gcaCanon : IntAt m E.gcaCanon st.gcaCanon
  noncheaplevel : IntAt m E.noncheaplevel st.noncheaplevel
  allsamelevel : IntAt m E.allsamelevel st.allsamelevel
  eqlevFirst : IntAt m E.eqlevFirst st.eqlevFirst
  eqlevCanon : IntAt m E.eqlevCanon st.eqlevCanon
  compCanon : IntAt m E.compCanon st.compCanon
  samerows : IntAt m E.samerows st.samerows
  canonlevel : IntAt m E.canonlevel st.canonlevel
  stabvertex : IntAt m E.stabvertex st.stabvertex
  cosetindex : IntAt m E.cosetindex st.cosetindex
  needshortprune : IntAt m E.needshortprune (if nsp then 1 else 0)

/-- `Stats` for any canonical store. -/
structure StatsG {n : Nat} {κ : Type} (m : mem) (S : SLoc) (st : SearchState n κ) (pre : Bool) :
    Prop where
  numorbits : FieldAt m .Mint32 S.bst (S.sb + 12) (.Vint (ir st.numorbits))
  numgenerators : FieldAt m .Mint32 S.bst (S.sb + 16) (.Vint (ir st.numgenerators))
  numnodes : FieldAt m .Mint64 S.bst (S.sb + 24) (.Vlong (lr st.numnodes))
  numbadleaves : FieldAt m .Mint64 S.bst (S.sb + 32) (.Vlong (lr st.numbadleaves))
  maxlevel : pre = false → FieldAt m .Mint32 S.bst (S.sb + 40) (.Vint (ir st.maxlevel))
  maxlevelW : Mem.valid_access m .Mint32 S.bst (zOfInt (S.sb + 40)) .Writable
  tctotal : FieldAt m .Mint64 S.bst (S.sb + 48) (.Vlong (lr st.tctotal))
  canupdates : FieldAt m .Mint64 S.bst (S.sb + 56) (.Vlong (lr st.canupdates))
  fits : S.sb + 88 < 2 ^ 64
  perm : Mem.range_perm m S.bst (zOfInt S.sb) (zOfInt (S.sb + 88)) .Cur .Freeable
  errstatus : FieldAt m .Mint32 S.bst (S.sb + 20) (.Vint (ir 0))
  grpsize1 : ∃ x, FieldAt m .Mfloat64 S.bst S.sb (.Vfloat x)
  grpsize2 : ∃ i, FieldAt m .Mint32 S.bst (S.sb + 8) (.Vint i)

theorem StatsG.fix {n : Nat} {κ : Type} {m : mem} {S : SLoc} {st : SearchState n κ} {pre : Bool}
    (h : StatsG m S st pre) : StatsFix m S :=
  ⟨h.perm, h.errstatus, h.grpsize1, h.grpsize2⟩

/-- `AutosAt` with `fmptr` at `E.fmptr`. -/
structure AutosAtG {n : Nat} (m : mem) (S : SLoc) (autos : Array (VSet n × VSet n)) : Prop where
  size : autos.size ≤ wsPairs
  arr : ∃ ww, ArrayAt m .Mint64 S.bws S.wb (longs ww) (2 * wsPairs * S.M) ∧
    ∀ i < autos.size,
      SetRep (fun w => bv64 (ww (2 * S.M * i + w))) S.M autos[i]!.1 ∧
      SetRep (fun w => bv64 (ww (2 * S.M * i + S.M + w))) S.M autos[i]!.2
  fmptr : PtrAt m E.fmptr
    (.Vptr S.bws (Ptrofs.repr (zOfInt (S.wb + 8 * (2 * S.M * autos.size)))))

/-- `Arrays` for `D`: the graph and the canonical store through `D`'s representations. -/
structure ArraysG {n : Nat} (m : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) (G : O.Gr n)
    (st : SearchState n (O.Canon n)) : Prop where
  lab : ArrayAt m .Mint32 S.bl S.lb (ints st.lab) n
  ptn : ArrayAt m .Mint32 S.bp S.pb (ints st.ptn) n
  orbits : ArrayAt m .Mint32 S.bo S.ob (ints st.orbits) n
  active : ∃ aw, ArrayAt m .Mint64 S.bA 0 (longs aw) S.M ∧
    SetRep (fun w => bv64 (aw w)) S.M st.active
  fixedpts : ∃ fw, ArrayAt m .Mint64 S.bF 0 (longs fw) S.M ∧
    SetRep (fun w => bv64 (fw w)) S.M st.fixedpts
  workperm : ∃ v, ArrayAt m .Mint32 S.bWP 0 v n
  firstlab : ArrayAt m .Mint32 S.bFL 0 (ints st.firstlab) n
  canonlab : ArrayAt m .Mint32 S.bCL 0 (ints st.canonlab) n
  firstcode : ArrayAt m .Mint16signed S.bFC 0 (shorts st.firstcode) (n + 2)
  canoncode : ArrayAt m .Mint16signed S.bCC 0 (shorts st.canoncode) (n + 2)
  firsttc : ArrayAt m .Mint32 S.bTC 0 (intsZ st.firsttc) (n + 2)
  canong : D.CanonRep m cl S.bc S.cofs S.M (O.rows st.canong) st.samerows
  autos : AutosAtG m S st.autos
  graph : D.GraphRep m gl S.bg S.gofs G S.M

/-- `z` is one of the dispatch procedures' scratch blocks or nautil.c's `workperm` block, in use. -/
def IsWorkG (m : mem) (z : block) : Prop :=
  D.IsWork m z ∨ ∃ cap, 0 < cap ∧ DynAt m E.nautilWorkperm E.nautilWorkpermSz 4 cap z

/-- The procedures' scratch state and nautil.c's `workperm` pair, their blocks in use
apart from `L` and from each other. -/
structure WorkG (m : mem) (L : List block) : Prop where
  disp : D.Work m
  nautil : ∃ cN bN, DynAt m E.nautilWorkperm E.nautilWorkpermSz 4 cN bN ∧ (0 < cN → bN ∉ L) ∧
    (0 < cN → ¬ D.IsWork m bN)
  notin : ∀ z, D.IsWork m z → z ∉ L

theorem WorkG.sub {m : mem} {L L' : List block} (h : WorkG D m L) (hL : ∀ z ∈ L', z ∈ L) :
    WorkG D m L' :=
  let ⟨cN, bN, dN, nN, uN⟩ := h.nautil
  ⟨h.disp, ⟨cN, bN, dN, fun hc hm => nN hc (hL _ hm), uN⟩, fun z hz hm => h.notin z hz (hL _ hm)⟩

/-- `Dyns` for `D`: the workspace is `D`'s pair. -/
structure DynsG (n : Nat) (m : mem) (S : SLoc) : Prop where
  active : DynAt m E.nautyActive E.nautyActiveSz 8 S.capA S.bA
  fixedpts : DynAt m E.nautyFixedpts E.nautyFixedptsSz 8 S.capF S.bF
  workperm : DynAt m E.nautyWorkperm E.nautyWorkpermSz 4 S.capWP S.bWP
  firstlab : DynAt m E.nautyFirstlab E.nautyFirstlabSz 4 S.capFL S.bFL
  canonlab : DynAt m E.nautyCanonlab E.nautyCanonlabSz 4 S.capCL S.bCL
  firstcode : DynAt m E.nautyFirstcode E.nautyFirstcodeSz 2 S.capFC S.bFC
  canoncode : DynAt m E.nautyCanoncode E.nautyCanoncodeSz 2 S.capCC S.bCC
  firsttc : DynAt m E.nautyFirsttc E.nautyFirsttcSz 4 S.capTC S.bTC
  capA : S.M ≤ S.capA
  capF : S.M ≤ S.capF
  capWP : n ≤ S.capWP
  capFL : n ≤ S.capFL
  capCL : n ≤ S.capCL
  capFC : n + 2 ≤ S.capFC
  capCC : n + 2 ≤ S.capCC
  capTC : n + 2 ≤ S.capTC
  workspace : DynAt m D.wsP D.wsS 8 S.capD S.bws
  capWs : 2 * wsPairs * S.M ≤ S.capD

/-- The tables: nautil.c's and nauty.c's, and the procedures'. -/
structure TablesG (m : mem) : Prop where
  env : ETables m
  disp : D.Tables m

/-- `SInv` for `O`: the store's rows are what the procedures need (`O.StoreOk`). -/
structure SInvG {n : Nat} (O : Ops) (G : O.Gr n) (st : SearchState n (O.Canon n)) : Prop where
  labSize : st.lab.size = n
  labSmall : ∀ i < n, st.lab[i]! < n
  labSurj : ∀ v < n, ∃ i < n, st.lab[i]! = v
  ptnSize : st.ptn.size = n
  ptnVals : ∀ i < n, st.ptn[i]! ≤ n + 1 ∨ st.ptn[i]! = nautyInf
  ptnLast : st.ptn[n - 1]! ≤ 1
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
  canong : O.StoreOk G (O.rows st.canong)
  scalars : st.gcaFirst < 2147483648 ∧ st.gcaCanon < 2147483648 ∧
    st.noncheaplevel < 2147483648 ∧ st.allsamelevel < 2147483648 ∧
    st.eqlevFirst < 2147483648 ∧ -1 ≤ st.eqlevCanon ∧ st.eqlevCanon < 2147483648 ∧
    -1 ≤ st.compCanon ∧ st.compCanon ≤ 1 ∧ st.canonlevel < 2147483648 ∧
    st.stabvertex < 2147483648 ∧ st.cosetindex < 2147483648
  wsCap : st.wsCap = wsPairs
  maxlevelLe : st.maxlevel ≤ n
  numorbitsLe : st.numorbits ≤ n
  orbitsDesc : Hex.GraphIso.Nauty.Orbit.Descending st.orbits n

/-- The shared globals among the search's blocks (the dense `SLoc.blocks` order,
without naugraph.c's globals). -/
abbrev envSearch : List block :=
  [E.getcanon, E.digraph, E.writeautoms, E.domarkers, E.doschreier,
   E.tcLevel, E.invarproc, E.usernodeproc, E.userlevelproc, E.usercanonproc,
   E.userautomproc, E.dispatch, E.orbits, E.m, E.n, E.g, E.canong,
   E.stats, E.gcaFirst, E.gcaCanon, E.noncheaplevel, E.allsamelevel,
   E.eqlevFirst, E.eqlevCanon, E.compCanon, E.samerows, E.canonlevel,
   E.stabvertex, E.cosetindex, E.needshortprune, E.tcnode0, E.allocM,
   E.workspace, E.worktop, E.fmptr, E.killRequest,
   E.nautyActive, E.nautyActiveSz, E.nautyFixedpts, E.nautyFixedptsSz, E.nautyWorkperm,
   E.nautyWorkpermSz, E.nautyFirstlab, E.nautyFirstlabSz, E.nautyCanonlab, E.nautyCanonlabSz,
   E.nautyFirstcode, E.nautyFirstcodeSz, E.nautyCanoncode, E.nautyCanoncodeSz, E.nautyFirsttc,
   E.nautyFirsttcSz, E.nautilWorkperm, E.nautilWorkpermSz, E.nautyBit, E.nautilBit, E.leftbit,
   E.mininvarlevel, E.maxinvarlevel, E.invararg]

/-- The blocks the search may not confuse: the caller's (the graph's and the
canonical store's through `D`), nauty.c's arrays, the shared globals and tables
it reads, and `D`'s globals. -/
def SLoc.blocksG (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) : List block :=
  D.graphBlocks gl S.bg ++ [S.bl, S.bp, S.bo, S.bst] ++ D.canonBlocks cl S.bc ++
    [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ++ envSearch ++ D.globs

/-- The blocks of `S` a search function may change. -/
abbrev SLoc.ChgG (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) (z : block) : Prop :=
  z ∈ S.blocksG D gl cl ∧ z ≠ S.bUA ∧ z ≠ E.tcnode0

/-- The blocks of `S.blocksG` given as list entries: `S`'s own blocks (with the
first blocks of the graph's and the store's representations) and the shared
globals, in the dense `SLoc.blocks` order. A sublist of `S.blocksG`
(`SLoc.litG_sub`), so `sep_ne` decides their distinctness from
`SearchAtG.lit`. -/
def SLoc.litG (S : SLoc) : List block :=
  [S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC,
   S.bTC, S.bUA] ++ envSearch

theorem SLoc.litG_sub (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) :
    S.litG.Sublist (S.blocksG D gl cl) := by
  have hg : [S.bg].Sublist (D.graphBlocks gl S.bg) :=
    List.singleton_sublist.2 (D.graphBlocks_head gl S.bg)
  have hc : [S.bc].Sublist (D.canonBlocks cl S.bc) :=
    List.singleton_sublist.2 (D.canonBlocks_head cl S.bc)
  exact ((((hg.append (List.Sublist.refl [S.bl, S.bp, S.bo, S.bst])).append hc).append
    (List.Sublist.refl [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA])).append
    (List.Sublist.refl envSearch)).trans (List.sublist_append_left _ _)

/-- Memory holds HexGraphIso's search state `st` for the graph `G`, through `D`. -/
structure SearchAtG {n : Nat} (m : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) (G : O.Gr n)
    (st : SearchState n (O.Canon n)) (pre nsp : Bool) : Prop where
  fixed : FixedG D n m S
  scalars : ScalarsG m st nsp
  stats : StatsG m S st pre
  arrays : ArraysG D m S gl cl G st
  dyns : DynsG D n m S
  work : WorkG D m (S.blocksG D gl cl)
  tables : TablesG D m
  distinct : (S.blocksG D gl cl).Pairwise (· ≠ ·)
  inv : SInvG O G st
  graphOk : O.GraphOk G
  n0 : 0 < n
  nlt : n < 1073741824
  nM : n ≤ 64 * S.M
  M1 : 0 < S.M
  Mlt : S.M < 33554432

end Generic

/-! ### The dense instance

`SearchAt` is `SearchAtG denseRep` (with `GLoc = CLoc = Unit`): `SearchAt.toG`
and `SearchAtG.dense` convert between them. The way back needs the graph's
words `S.gw`, which the dense `SLoc` fixes and `denseRep` leaves existential;
they are memory-independent, so the caller passes them from an earlier
`SearchAt` (`SearchAt.gw`). -/

section Dense

open NautyVerified.Proofs.Dispatch
open NautyVerified.Proofs.Alloc (Slot InUse SlotsOk)
open NautyVerified.Proofs.Graph (RowsAt)

theorem SLoc.blocksG_perm (S : SLoc) : (S.blocksG denseRep () ()).Perm S.blocks := by perm_lit

theorem SLoc.mem_blocksG {S : SLoc} {z : block} : z ∈ S.blocksG denseRep () () ↔ z ∈ S.blocks :=
  S.blocksG_perm.mem_iff

theorem SLoc.distinctG {S : SLoc} (h : S.blocks.Pairwise (· ≠ ·)) :
    (S.blocksG denseRep () ()).Pairwise (· ≠ ·) :=
  (S.blocksG_perm.pairwise_iff (fun h => Ne.symm h)).2 h

theorem SLoc.distinct_ofG {S : SLoc} (h : (S.blocksG denseRep () ()).Pairwise (· ≠ ·)) :
    S.blocks.Pairwise (· ≠ ·) :=
  (S.blocksG_perm.pairwise_iff (fun h => Ne.symm h)).1 h

/-- Two words representing the same set are equal. -/
theorem setRep_words {n M : Nat} {ws wt : Nat → BitVec 64} {s : VSet n} (hs : SetRep ws M s)
    (ht : SetRep wt M s) : ∀ i < M, ws i = wt i := by
  intro i hi
  apply BitVec.eq_of_getMsbD_eq
  intro j hj
  have hv : 64 * i + j < 64 * M := by omega
  have e1 : (64 * i + j) / 64 = i := by omega
  have e2 : (64 * i + j) % 64 = j := by omega
  have h1 := hs.2 _ hv
  have h2 := ht.2 _ hv
  simp only [SetwordsMem, e1, e2] at h1 h2
  rw [h1, h2]

/-- The graph's rows in other words `gw'` are the same words. -/
theorem graphAt_words {n : Nat} {m : mem} {bg : block} {gofs : ptrofs}
    {gw gw' : Nat → Lib.Integers.int64} {rows : Array (VSet n)} {M : Nat}
    (h : GraphAt m bg gofs gw' rows M)
    (hgw : ∀ v < n, SetRep (fun w => bv64 (gw (M * v + w))) M rows[v]!) :
    GraphAt m bg gofs gw rows M := by
  refine ⟨⟨h.arr.base_nonneg, h.arr.fits, fun i hi => ?_, h.arr.writable⟩, hgw⟩
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have hv : i / M < n := by
    rw [Nat.div_lt_iff_lt_mul hM]; rw [Nat.mul_comm] at hi; exact hi
  have e : M * (i / M) + i % M = i := Nat.div_add_mod i M
  have hw := setRep_words (h.rep _ hv) (hgw _ hv) (i % M) (Nat.mod_lt _ hM)
  rw [e] at hw
  rw [h.arr.load i hi]
  simp only [longs, bv64_inj.1 hw]

/-- The words of `S`'s graph represent `ctx`'s rows. -/
theorem SearchAt.gw {n : Nat} {m : mem} {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    (h : SearchAt m S ctx st pre nsp) :
    ∀ v < n, SetRep (fun w => bv64 (S.gw (S.M * v + w))) S.M ctx.g[v]! :=
  h.arrays.graph.rep

theorem inUse_dense {m : mem} {z : block} :
    InUse m denseSlots z ↔
      (∃ cap, 0 < cap ∧ DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cap z) ∨
      (∃ cap, 0 < cap ∧ DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 cap z) ∨
      (∃ cap, 0 < cap ∧ DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 cap z) := by
  constructor
  · rintro ⟨p, hp, c, hc, d⟩
    simp only [denseSlots, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact .inl ⟨c, hc, d⟩
    · exact .inr (.inl ⟨c, hc, d⟩)
    · exact .inr (.inr ⟨c, hc, d⟩)
  · rintro (⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩)
    · exact ⟨(Block.naugraphWorkperm, Block.naugraphWorkpermSz, 4), by simp [denseSlots], c, hc, d⟩
    · exact ⟨(Block.naugraphWorkset, Block.naugraphWorksetSz, 8), by simp [denseSlots], c, hc, d⟩
    · exact ⟨(Block.naugraphBucket, Block.naugraphBucketSz, 4), by simp [denseSlots], c, hc, d⟩

private theorem dyn_vp {m : mem} {bp bs : block} {c cap : Nat} {b : block}
    (h : DynAt m bp bs c cap b) : Mem.valid_block m bp := Alloc.valid_of_access h.bpW

private theorem dyn_vs {m : mem} {bp bs : block} {c cap : Nat} {b : block}
    (h : DynAt m bp bs c cap b) : Mem.valid_block m bs := Alloc.valid_of_access h.bsW

private theorem load_v {m : mem} {chunk : memory_chunk} {b : block} {ofs : Z} {v : val}
    (h : Mem.load chunk m b ofs = some v) : Mem.valid_block m b :=
  Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h)

/-- A positive-capacity block of a pair is the pair's block in any `DynAt` of it. -/
private theorem dyn_eq {m : mem} {bp bs : block} {k c c' : Nat} {b b' : block}
    (d : DynAt m bp bs k c b) (d' : DynAt m bp bs k c' b') (hc' : 0 < c') : b' = b ∧ 0 < c := by
  have := d.same_cap d'
  subst this
  exact ⟨d.same_block d' hc', hc'⟩

private theorem dyn_sep {m : mem} {bp bs bp' bs' : block} {k k' cX cY c c' : Nat}
    {bX bY z : block} (dX : DynAt m bp bs k cX bX) (dY : DynAt m bp' bs' k' cY bY)
    (pXY : 0 < cX → 0 < cY → bX ≠ bY) (dp : DynAt m bp bs k c z) (dq : DynAt m bp' bs' k' c' z)
    (hc : 0 < c) (hc' : 0 < c') : False :=
  pXY (dyn_eq dX dp hc).2 (dyn_eq dY dq hc').2 ((dyn_eq dX dp hc).1.symm.trans (dyn_eq dY dq hc').1)

theorem WorkAt.toG {n : Nat} {m : mem} {S : SLoc} {L : List block} (h : WorkAt n m S L)
    (hL : ∀ z ∈ denseL, z ∈ L) (hv : ∀ z ∈ denseL, Mem.valid_block m z) : WorkG denseRep m L := by
  obtain ⟨cW, bW, cS, bS, cB, bB, cN, bN, dW, dS, dB, dN, nW, nS, nB, nN, pWS, pWB, pSB, pNW,
    pNS, pNB⟩ := h.arr
  have notL : ∀ z, InUse m denseSlots z → z ∉ L := by
    intro z hz
    rcases inUse_dense.1 hz with ⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩
    · obtain ⟨rfl, h1⟩ := dyn_eq dW d hc; exact nW h1
    · obtain ⟨rfl, h1⟩ := dyn_eq dS d hc; exact nS h1
    · obtain ⟨rfl, h1⟩ := dyn_eq dB d hc; exact nB h1
  refine ⟨⟨⟨fun p hp => ?_, fun z hz hzL => notL z hz (hL z hzL), ?_⟩, hv⟩,
    ⟨cN, bN, dN, nN, fun hc hu => ?_⟩, fun z hz => notL z hz⟩
  · simp only [denseSlots, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨_, _, dW⟩
    · exact ⟨_, _, dS⟩
    · exact ⟨_, _, dB⟩
  · intro p hp q hq c c' z hc hc' dp dq
    simp only [denseSlots, List.mem_cons, List.mem_nil_iff, or_false] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    all_goals first
      | rfl
      | exact (dyn_sep dW dS pWS dp dq hc hc').elim
      | exact (dyn_sep dW dB pWB dp dq hc hc').elim
      | exact (dyn_sep dS dB pSB dp dq hc hc').elim
      | exact (dyn_sep dS dW (fun a b e => pWS b a e.symm) dp dq hc hc').elim
      | exact (dyn_sep dB dW (fun a b e => pWB b a e.symm) dp dq hc hc').elim
      | exact (dyn_sep dB dS (fun a b e => pSB b a e.symm) dp dq hc hc').elim
  · rcases inUse_dense.1 hu with ⟨c, hc', d⟩ | ⟨c, hc', d⟩ | ⟨c, hc', d⟩
    · obtain ⟨e, h1⟩ := dyn_eq dW d hc'; exact pNW hc h1 e
    · obtain ⟨e, h1⟩ := dyn_eq dS d hc'; exact pNS hc h1 e
    · obtain ⟨e, h1⟩ := dyn_eq dB d hc'; exact pNB hc h1 e

theorem WorkG.dense {n : Nat} {m : mem} {S : SLoc} {L : List block} (h : WorkG denseRep m L) :
    WorkAt n m S L := by
  obtain ⟨⟨hs, -⟩, ⟨cN, bN, dN, nN, uN⟩, hn⟩ := h
  obtain ⟨cW, bW, dW⟩ := hs.dyn (Block.naugraphWorkperm, Block.naugraphWorkpermSz, 4)
    (by simp [denseSlots])
  obtain ⟨cS, bS, dS⟩ := hs.dyn (Block.naugraphWorkset, Block.naugraphWorksetSz, 8)
    (by simp [denseSlots])
  obtain ⟨cB, bB, dB⟩ := hs.dyn (Block.naugraphBucket, Block.naugraphBucketSz, 4)
    (by simp [denseSlots])
  have uW : 0 < cW → InUse m denseSlots bW := fun hc => inUse_dense.2 (.inl ⟨_, hc, dW⟩)
  have uS : 0 < cS → InUse m denseSlots bS := fun hc => inUse_dense.2 (.inr (.inl ⟨_, hc, dS⟩))
  have uB : 0 < cB → InUse m denseSlots bB := fun hc => inUse_dense.2 (.inr (.inr ⟨_, hc, dB⟩))
  have sep : ∀ {p q : Slot}, p ∈ denseSlots → q ∈ denseSlots → p ≠ q → ∀ {c c' b b'}, 0 < c →
      0 < c' → p.At m c b → q.At m c' b' → b ≠ b' := by
    intro p q hp hq hpq c c' b b' hc hc' dp dq e
    subst e
    exact hpq (hs.sep p hp q hq c c' b hc hc' dp dq)
  exact ⟨⟨cW, bW, cS, bS, cB, bB, cN, bN, dW, dS, dB, dN,
    fun hc => hn _ (uW hc), fun hc => hn _ (uS hc), fun hc => hn _ (uB hc), nN,
    fun h1 h2 => sep (by simp [denseSlots]) (by simp [denseSlots]) (by decide) h1 h2 dW dS,
    fun h1 h2 => sep (by simp [denseSlots]) (by simp [denseSlots]) (by decide) h1 h2 dW dB,
    fun h1 h2 => sep (by simp [denseSlots]) (by simp [denseSlots]) (by decide) h1 h2 dS dB,
    fun h1 h2 e => uN h1 (e ▸ uW h2), fun h1 h2 e => uN h1 (e ▸ uS h2),
    fun h1 h2 e => uN h1 (e ▸ uB h2)⟩⟩

/-- `SInv` as `SInvG` for dense nauty's operations. -/
theorem SInv.toG {n : Nat} {ctx : Ctx n} {st : Search n} (h : SInv st) : SInvG denseOps ctx st :=
  { h with canong := h.canongSize }

theorem SInvG.dense {n : Nat} {ctx : Ctx n} {st : Search n} (h : SInvG denseOps ctx st) : SInv st :=
  { h with canongSize := h.canong }

/-- The dense search state as the generic one. -/
theorem SearchAt.toG {n : Nat} {m : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) :
    SearchAtG denseRep m S () () ctx st pre nsp := by
  have hA := h.arrays
  have hD := h.dyns
  have hB := h.tables
  obtain ⟨_, _, _, _, _, _, _, _, dW, dS, dB, dN, -⟩ := h.work.arr
  have hv : ∀ z ∈ denseL, Mem.valid_block m z := by
    intro z hz
    simp only [denseL, denseGlobs, denseWGlobs, envAvoid, List.cons_append, List.nil_append,
      List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact dyn_vp dW
    · exact dyn_vs dW
    · exact dyn_vp dS
    · exact dyn_vs dS
    · exact dyn_vp dB
    · exact dyn_vs dB
    · exact load_v (hB.naugraphBit 0 (by decide))
    · exact load_v (hB.bytes 0 (by decide))
    · exact dyn_vp hD.workspace
    · exact dyn_vs hD.workspace
    · exact load_v (hB.nautyBit 0 (by decide))
    · exact load_v (hB.nautilBit 0 (by decide))
    · exact load_v (hB.left 0 (by decide))
    · exact dyn_vp dN
    · exact dyn_vs dN
  exact
    { fixed := { h.fixed with }
      scalars := { h.scalars with }
      stats := { h.stats with }
      arrays := { hA with
        canong := let ⟨cw, ha, hr⟩ := hA.canong.arr; ⟨cw, ha, hr⟩
        autos := { hA.autos with }
        graph := ⟨S.gw, hA.graph⟩ }
      dyns := { hD with }
      work := (h.work.toG (by simp [denseL, denseGlobs, denseWGlobs, envAvoid, SLoc.blocks])
        hv).sub _ fun z hz => SLoc.mem_blocksG.1 hz
      tables := ⟨⟨hB.nautyBit, hB.nautilBit, hB.left⟩, hB.naugraphBit, hB.bytes⟩
      distinct := SLoc.distinctG h.distinct
      inv := { h.inv with canong := h.inv.canongSize }
      graphOk := trivial
      n0 := h.n0, nlt := h.nlt, nM := h.nM, M1 := h.M1, Mlt := h.Mlt }

/-- The generic search state at `denseRep` as the dense one, given the graph's
words `S.gw` (`SearchAt.gw`). -/
theorem SearchAtG.dense {n : Nat} {m : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAtG denseRep m S () () ctx st pre nsp)
    (hgw : ∀ v < n, SetRep (fun w => bv64 (S.gw (S.M * v + w))) S.M ctx.g[v]!) :
    SearchAt m S ctx st pre nsp := by
  have hA := h.arrays
  exact
    { fixed := { h.fixed with }
      scalars := { h.scalars with }
      stats := { h.stats with }
      arrays := { hA with
        canong := ⟨let ⟨cw, hr⟩ := hA.canong; ⟨cw, hr.arr, hr.rep⟩⟩
        autos := { hA.autos with }
        graph := let ⟨_, hg⟩ := hA.graph; graphAt_words hg hgw }
      dyns := { h.dyns with }
      work := (h.work.sub _ fun z hz => SLoc.mem_blocksG.2 hz).dense
      tables := ⟨h.tables.env.nautyBit, h.tables.disp.1, h.tables.env.nautilBit, h.tables.env.left,
        h.tables.disp.2⟩
      distinct := SLoc.distinct_ofG h.distinct
      inv := { h.inv with canongSize := h.inv.canong }
      n0 := h.n0, nlt := h.nlt, nM := h.nM, M1 := h.M1, Mlt := h.Mlt }

end Dense

end NautyVerified.Proofs.Search
