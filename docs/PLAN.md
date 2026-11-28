# Plan: machine-checked refinement from nauty's C to HexGraphIso, down to x86-64

Paths under `/tmp` refer to the experiment directories described in
[feasibility-2026-11.md](feasibility-2026-11.md); they are not part of this
repository.

## Context

Hex's `HexGraphIso` reimplements nauty 2.9.3 in Lean and proves it correct
(canonical form is a complete invariant, emitted generators generate Aut,
orbits are correct). Agreement with the C is currently established only by
conformance testing and source review (`reports/nauty-translation-audit.md`,
"Proof boundary"). Kim wants a theorem about the actual blob of `.c` sources:
the C, and the machine code compiled from it, behaves like Hex's Lean code,
so Hex's correctness theorems hold of the binary.

Experiments on 2026-11-27 (`/tmp/nauty-verif/REPORT.md`) showed every stage
is feasible: CLean's `clightgen -lean` exports unmodified nauty to Lean
Clight; CLean's interpreter reproduces native results (CFI-120, 25M steps);
CompCert4Lean compiles nauty to a correct x86-64 binary and its
`transf_c_program_correct` is axiom-clean; a CLean `FunSpec` for
`nextelement` was proved (1,258 lines, `/tmp/nauty-verif/lean/NautyC/NextElement.lean`).
One blocker was found: `firstcode[0]` is read uninitialised (`nauty.c:884`),
undefined behaviour under CompCert semantics.

Decisions (Kim, 2026-11-27): new repo under `kim-em` (not part of Hex);
proofs written against **CompCert4Lean's** Clight (port CLean's logic onto
it); `firstcode` handled by a **zero-filling allocator** with nauty's `.c`
byte-identical; **dense first, then sparse**.

## Final theorem (target shape)

In repo `kim-em/nauty-verified` (working name):

```
theorem densenauty_binary_correct (G : HexGraphIso.Colored n k) (hn : n ≤ maxN) :
  transf_c_program cfg … dense.program = .OK tp →       -- the binary of scripts/build_binary.sh
  ∀ beh, program_behaves (Asm.semantics cfg xi tp) beh →
    Inputs.consistent G beh →                         -- nv_read calls return encode G,
                                                      -- nauty_kill_request reads return 0
    beh = Terminates (Out.trace (HexGraphIso.Nauty.runColoredTraced G) ...) _
```

where `dense.program` is the linked program of Phase 1 and the harness reads
the graph through calls to the external function `nv_read` and writes results
through `nv_write` (CompCert records both as trace events, which is what its
whole-program backward simulation preserves). Outputs: canonical labelling, canonical graph rows, emitted
generators in order, orbits, the seven statistics. Corollaries restate
`canon_invariant`, `iso_iff_canon_eq`, `Aut.complete`, orbit correctness for
the binary (the Mathlib-facing ones via `hex-graph-iso-theory`). Group order
is out of scope (nauty's is a rounded double; Hex computes its own).

Explicit assumptions in the trusted base: Lean kernel; CompCert's OCaml
frontend (preprocessor, parser, elaboration to Csyntax); CompCert4Lean's
x86-64 Asm semantics, Asmexpand, printer, assembler and linker; the
renaming and C linking of Phase 1 as a model of the system linker; CompCert's
infinite-memory model (allocation never fails, no stack overflow); the
input/kill-flag environment assumption; `maxN` from `int` overflow bounds.

## Repository layout and pins (Phase 0)

- `kim-em/nauty-verified`, one Lake package, Lean toolchain = the one the
  released `leanprover/hex-graph-iso` tag uses (hex-dev is on
  `v4.35.0-rc3`). Licence: the compiler layer is INRIA non-commercial, so the
  repo is research-only; keep upstream licence notices and sidecars.
- `c/nauty-2.9.3/`: `nauty.c nautil.c naugraph.c nausparse.c nauty.h
  nausparse.h naututil.h schreier.h naurng.h sorttemplates.c` copied from
  hex-dev `vendor/nauty-2.9.3/` with its SHA-256 table (`vendor/nauty-2.9.3/README.md`).
  Never edited.
- `c/harness/`: `zalloc.c` (7 lines, zero-fill), `dense_main.c`,
  `sparse_main.c` (volatile-I/O harnesses), `config.h` documenting flags
  `-DWORDSIZE=64 -DHAVE_HWLZCNT=0 -DHAVE_HWPOPCNT=0 -Dmalloc=nauty_zalloc`
  (zalloc.c compiled without the `-D`), `options.outfile` set to a dummy.
- Lake requires: a `kim-em` fork of `fanlong/compcert4lean` (bumped to our
  toolchain; upstream the bump), `leanprover/hex-graph-iso` at a release
  tag, `leanprover/hex-graph-iso-theory` only in a separate `Corollaries` lib.
- CI: one ubuntu job. Steps: build CompCert at the pin (cached), regenerate
  the C exports and diff against committed Lean, `lake build`, run the
  differential tests (below), compile the harnesses with CompCert4Lean and
  run them on fixtures. Mirror hex's bans: no `axiom`, no `native_decide`,
  `sorry` only on a tracked list that must shrink.

## Phase 1: C to CompCert4Lean terms (done)

1. **Csyntax files.** `scripts/export_csyntax.sh` runs CompCert4Lean's
   frontend bridge on each translation unit and writes
   `c/csyntax/<unit>.json`, the interchange file the compiler driver itself
   consumes, extended (in the `kim-em/compcert4lean` branch `nauty-verified`)
   with the C name of every identifier. The files are committed; regeneration
   is byte-identical.
2. **Units as Lean definitions.** `c_unit u from "c/csyntax/u.json"`
   (`NautyVerified/Source/Unit.lean`) decodes the file at elaboration time with
   the driver's own decoder (`Prototype.decodeSource`) and adds the program as
   closed constructor terms via derived `ToExpr` (`u.program`, one constant per
   global definition, `u.id.<c_name>`). Because the decoder is the one the
   driver runs, no separate printer or agreement test is needed.
3. **Clight by CompCert4Lean's own passes.** `u.clight` and `u.locals` are the
   outputs of `SimplExpr.transl_program` and `SimplLocals.transf_program`
   (for every configuration with debug information off), pinned by
   `u.clight_eq` and `u.locals_eq`, which are `Eq.refl` checked by the kernel
   alone (elaborator `rfl` exhausts its recursion budget). Kernel cost is small:
   1 to 2 seconds per equation even for `nauty.c`.
4. **Linking.** CompCert4Lean proves only whole-program preservation, so the
   binary is one whole-program compile of the linked program rather than
   per-unit objects joined by the system linker. `c_link dense := dense_main
   nauty nautil naugraph schreier naurng zalloc` (`Source/Link.lean`):
   - gives every C name one shared identifier; a global with `static` storage
     is keyed `unit:name` (file-local), every other name by itself;
   - renames each unit by position (`Source/Rename.lean`): global symbol
     positions (definitions, public names, `main`, address-of initialisers,
     variables not bound by the enclosing function) take the global key,
     other identifiers (members, tags, labels, parameters, locals) the plain
     name, since the frontend uses one identifier per name whatever it denotes;
   - links the renamed units left to right with CompCert's
     `Ctypes.link_program`; `dense.link_eq : linkUnits [...] = some
     dense.program` is kernel-checked (on the program's parts, the composite
     environment following by `eq_of_parts`);
   - pins `dense.clight` and `dense.locals` as for a unit.
5. **Binary.** `scripts/build_binary.sh` compiles `dense.program` with
   `transf_c_program` at the driver's O0 configuration (`nvCompile`,
   `NautyVerified/Build/Compile.lean`), prints it with the bridge's
   `print_named` operation (supplied names, printer defaults for sections and
   alignment, every symbol global; static `name` of `unit` printed
   `name.unit`), and links it with `io_stdio.c` and CompCert's runtime
   library. It reproduces all 52 fixtures.

Trust added by this phase: the renaming and `link_program` model what the
system linker does with the units (file-local statics distinct, everything
else shared by name).

## Phase 2: program logic on CompCert4Lean's Clight

The logic is written directly against CompCert4Lean's Clight `step` (with
`function_entry2`), following the design of CLean's `CCLib.Hoare` rather than
porting CCLib wholesale: CCLib's separation-logic layer is built on its own
copy of the semantics, and nauty's data (dynamically allocated arrays in
distinct blocks, a few statics) does not need a frame rule.

- **Executable evaluation** (`NautyVerified/Exec/Expr.lean`, done): `evalExpr`,
  `evalLvalue`, `evalExprlist`, `derefLoc`, `assignLoc` (scalar stores and
  structure copies), proved sound against `eval_expr`, `eval_lvalue`,
  `eval_exprlist`, `deref_loc`, `assign_loc`. On a concrete expression `simp`
  unfolds them to the memory operations performed.
- **Interpreter** (`Exec/Interp.lean`, `nvInterp`, done): runs
  `dense.locals` on every fixture and reproduces the native output (CFI-120:
  28 million steps); run in CI by `scripts/run_interp.sh`.
- **Triples** (`Logic/Triple.lean`, done): total, existential, trace-carrying:
  from every state satisfying the precondition some execution finishes
  normally, by `break`, by `continue` or by `return`, with the emitted trace
  passed to the postcondition. Rules: consequence, skip, break, continue,
  sequence, set, assign, if, return, loop (invariant indexed by a decreasing
  variant and the trace so far).
- **Calls** (`Logic/Call.lean`, done): `FunSpec`, `Satisfies`, call rule,
  builtin rule, external functions, internal functions from a triple about
  the body. Recursive functions by induction on a measure.
- **Words** (`Word/BitVec.lean`): `toBV : Word bits → BitVec bits` with a
  rewrite lemma per operation, and Rocq `Z` to `Int`, so `bv_decide` and
  `omega` apply. Needs the public residue lemmas added to the fork's
  `Lib/Integers.lean`.
- **Memory**: array predicates over `Mem.load`/`Mem.store` (`int`, `setword`,
  pointer arrays), unchanged-outside-footprint postconditions
  (`Mem.unchanged_on`), initial memory of globals (including read-only tables
  `leftbit`, `bytecount`, `bit`).
- **Automation**: a stepping tactic that applies the rule for the next
  statement and evaluates its expressions with `simp`.
- **Determinism** (for Phase 6): Clight `step` is determinate given
  `extcall_properties.ec_determ`, so the execution the logic produces is the
  only one consistent with the inputs.

- **Fork changes for symbolic execution** (`kim-em/compcert4lean`, branch
  `nauty-verified`): public residue and comparison lemmas in
  `Lib/Integers.lean`; `ident`, `block`, `PTree.t`, `env` and `temp_env` made
  abbreviations, because terms mixing them with `positive` or `PTree.tree`
  are type-correct only after unfolding, and `simp` refuses to rewrite such
  goals. Literal words are emitted at their exact type (`Int.repr`,
  `Int64.repr`, `Ptrofs.repr`) for the same reason.

Acceptance (done): `nextelement_satisfies` (`Proofs/Nextelement/`) proves
nauty's `nextelement`, from its pinned Clight, against `NextSpec`, and
`nextElem_of_nextSpec` derives HexGraphIso's `VSet.nextElem` from it;
interpreter agreement. The proof pattern for every function: factor the body
(`Tools/PrintClight`, pinned by `kernel_rfl`), state lookups of the
temporaries as hypotheses, run `wp_step` and evaluate with the `cop` simp set
and the `ir`/`bv64` lemmas, split on tests, and close leaves with the pure
specification lemmas. `bv_decide` is not used (it adds `Lean.ofReduceBool`).

## Phase 3: Clight to Asm theorem (done)

`CompCert4Lean/Driver/ClightCompiler.lean` (fork branch `nauty-verified`):
`Clight.semantics2_receptive`, and `transf_c_program_clight_correct`: if
`transf_c_program … p = .OK tp`, `SimplExpr.transl_program ctx p = .OK c1` and
`SimplLocals.transf_program cfg c1 = .OK c2`, then `backward_simulation
(Clight.semantics2 xi c2) (Asm.semantics cfg xi tp)`. It chains each pass's
`transf_program_match` into that pass's correctness theorem from Cshmgen on, so
no linking certificates are involved. `Statement/Compiler.lean` instantiates
it for the dense program (`dense_backward`) with `dense.clight_eq` and
`dense.locals_eq`. Upstreaming to CompCert4Lean needs approval.

## Phase 4: statements first (written; awaiting review)

Before bulk proofs, commit the final statements with `sorry`:
- encodings: `Inputs.events G`, `Out.trace r` for the harness protocol;
- representation predicates: `SetwordsRep p m (s : VSet n)` (64-bit,
  MSB-first, against Hex's 63-bit LSB-first limbs; membership-level relation),
  `PartitionRep lab ptn`, `GraphRep g m n rows`, `WorkspaceRep` (nauty's
  `workspace`/`fmptr` ring of 500 pairs against `SearchState.autos` +
  `pushAuto`), `GlobalsRep` (nauty.c statics against `SearchState` fields:
  codes, levels, `firstlab`, `canonlab`, stats; `firstcode[0]` = 0 by zalloc);
- `maxN` from the overflow bounds (audit "Arithmetic": `2*500*m < 2^31`,
  `64m < 2^31`, refine hash sums; `nextelement` already needed `64n < 2^31`);
- the top theorem and corollaries.
Review these with Kim before Phase 5.

Written: `Statement/Harness.lean` (the environment `xi`, `Encodes`,
`Consistent`, `reads`/`writes`, `expected`), `Statement/Dense.lean`
(`canonWords_eq_iff`, `generators_correct`, `orbits_correct`,
`maxN = 65536`) and `Statement/Final.lean` (`densenauty_binary_correct`,
above `main_ok` in the import graph).
`expected G`, evaluated in Lean, equals the native binary's output on the
fixtures checked (Petersen, coloured Petersen, an edgeless graph, five random
graphs). The representation predicates are written per function during Phase
5 (as `WordsAt`, `LeftbitTable`, `LoopInv` for `nextelement`).

Input bounds (decision taken with Kim): `Encodes` lists each edge of `G`
exactly once, in one orientation, without loops (`es.Nodup`, no reversed
pair), so the edge count is at most `n (n - 1) / 2 < 2^31` for `n ≤ maxN` and
fits the harness's `int`; `densenauty_binary_correct` also assumes `k ≤ maxN`,
so the colours and the `c <= maxc` loop stay within `int`. No other numeric
hypotheses on the input.

## Phase 5: dense specs (the bulk)

Pattern per C function: a CompCert4Lean-logic `FunSpec` whose pre/post are
the Rep predicates applied to a Hex state, postcondition = Rep of Hex's
corresponding function applied to it. Where representations differ at bit
level, both sides meet a shared mathematical spec (as `nextelement`: Hex's
`nextElem_some`/`nextElem_none`, `firstFrom_some`), rather than lockstep.
Correspondence map (from `HexGraphIso/Nauty/Search/Search.lean:33-130`,
`Refine.lean`, `State.lean`, `VSet/Basic.lean`):

1. `nautil.c` primitives and macros: `FIRSTBITNZ`/`POPCOUNT` table macros
   (`lowBit`, `popCount`), `nextelement` (`VSet.nextElem`), `permset`,
   `breakout`, `fmperm`, `fmptn`, `orbjoin`, `shortprune`, `longprune`,
   `doref`, `maketargetcell`. Reuse `fmperm_fix`, `orbjoin_orbSound`,
   `longprune_subset`, `maketargetcell_eq_spec`, VSet `toNat` bitset lemmas.
2. `naugraph.c`: `isautom`, `testcanlab`, `updatecan`, `cheapautom`,
   `bestcell`, `targetcell`, `refine`/`refine1` (largest; `MASH`/`CLEANUP`
   hash; Hex `refine`/`refineLoop`/`refineStep`, `@[csimp]` fast variants).
3. `nauty.c` search: `firstpathnode`/`othernode` (Hex `node`/`sweep`, via
   `node_eq_generic`), `firstterminal`, `processnode` (`classify`,
   `leafExit`, …), `recover`, `nauty` (`runState`/`finish`). Recursion by
   CompCert4Lean-logic measures matching Hex fuel `n+2`/`n+1`; discharge
   fuel with `runState_noFuel`. Function pointers through `dispatch_graph`.
   Callback `userautomproc` = harness collector, so emitted generators =
   `TraceRun.emitted`.
4. `densenauty`, `zalloc.c`, `dense_main.c`.

Each item is an issue; items in 1 and 2 parallelise once Phase 2 and the
Rep definitions exist. Expected size: 25-40 Lean lines per C line on set
code; total C-side 100k-200k lines (estimate from one function).

Status: proved against HexGraphIso (`*_satisfies`, axiom-clean):
`nextelement`, `orbjoin`, `breakout`, `fmptn`, `shortprune`, `longprune`,
`fmperm`, `permset` (nautil.c); `cheapautom`, `isautom`, `updatecan`
(naugraph.c; `isautom` calls `nextelement` and `updatecan` calls `permset`
through their proved specifications); and the allocator layer:
`malloc`, `free`, `nauty_zalloc`, `DYNALLOC1` (`wp_dynalloc1`). Graphs in
memory are `GraphAt` (row `v` at word `M * v`, each row `SetRep` of the Hex
row).

`bestcell` (naugraph.c, `Proofs/Bestcell/`) is proved against HexGraphIso's
`bestcell`: the start loop against `startsOf` over `cells`, the joined-cell
counts against `bestcellRows` unrolled into `rowsStep`/`rowStep` folds
(`Spec/Bestcell.lean`, with `rows_bound` keeping every count below `nnt`), and
the argmax against `argmaxLoop`. Its spec (`bestcellSpec`, `Pre`, `Post`) is
shared with `targetcell`: the three `DYNALLSTAT` pairs may be replaced, and
only `dyn3Set` changes. Sets reached through a pointer global use
`Proofs/Set/Global.lean`; loops from a nonzero start use `wp_forLoopFrom`.
`targetcell` (`Proofs/Targetcell/`) is proved against HexGraphIso's
`targetcell` for any `digraph` argument and a hint below `n`, calling
`bestcell` through `bestcell_satisfies`; `targetcell_mem` (Hex level) gives the
start of a nontrivial cell when one exists. `maketargetcell` (nautil.c,
`Proofs/Maketargetcell/`) is proved against HexGraphIso's `maketargetcell`,
calling `targetcell` through its function-pointer argument (which must be
`Block.targetcell`), when some cell is nontrivial.

Conventions settled while doing these:

- An `int` array holding `o : Array Nat` is `ArrayAt … (ints o) n`; a set of
  `M` words `ws` is `ArrayAt … (longs ws) M` together with
  `SetRep (bv64 ∘ ws) M s`. Specs return the words existentially (or as a
  named function such as `Set.single`, `Set.addW`, `Set.andW`) plus the
  `SetRep` of the Hex result, so callers never see bit layouts.
- nauty's set macros are generic lemmas in `Proofs/Set/` (`EMPTYSET`,
  `ADDELEMENT`, word-wise `INTERSECT` loops, the `NOTSUBSET` scan),
  instantiated per function by the identifiers SimplExpr chose.
- Each function's frame (pointer temporaries, read-only arrays, block
  disjointness) is a structure with `temps` and `unch` transport lemmas.
- Hex functions written with `Id.run do` loops are unrolled once into folds
  (`orbjoin_eq`, `fmptn_eq`, `longprune_eq`) and the C loops are matched
  against the folds, iteration by iteration.
- Word offsets inside the workspace are carried as `Nat` atoms advanced by
  `M + M` (`PairsAt`), never as products, so `omega` closes the arithmetic.
- `longprune` is specified over an arbitrary contiguous run of pairs; how
  nauty's ring of `fmptr` pairs maps to `SearchState.autos` belongs to its
  callers.
- `DYNALLSTAT` pairs are `DynAt m bp bs c cap b`: the capacity global holds
  `cap` and, when `cap > 0`, the pointer global points to block `b` that
  `malloc` made for `c * cap` bytes (`Malloced`: header at `-8`, `Freeable`
  on `[-8, c*cap)`). `wp_dynalloc1` re-establishes it with capacity at least
  the size asked for and reports exactly what changed: the two globals, the
  old block (only when `cap > 0`), and a block not valid before. Writes into
  the array go through `wp_gstore`, which also gives `Keep` (header and
  permissions unchanged), so `DynAt` survives a function's own use of its
  array. Specs taking a `DYNALLSTAT` array take `DynAt` in their pre and
  return it in their post.
- Facts about the `workperm` block are needed only when `n > 0`: with
  capacity 0 the block is arbitrary and may coincide with a caller's array.
- `refineLoop`'s fuel `4 * n + 8` is never exhausted (`Spec/RefineFuel.lean`):
  `refineFuel st` (`|active| + (n - numcells)` while `numcells < n`, else 0)
  drops on every `refineStep`, because each insertion into `active` comes
  with a `numcells` increment (and `nontrivialFix` erases `maxpos`, which is
  `cell1` or already active). The C loop of `refine` carries
  `refineLoop … (4n+8) st₀ = refineLoop … F st ∧ refineFuel st < F`, using
  `refineFuel_lt_init`, `refineLoop_next` and `refineLoop_stop`; no invariant
  on `lab` or `ptn` is needed.
- A function writing into part of a caller's array (a row of `canong`, a
  slice of the workspace) also reports `Outside m m' b lo hi`: block `b`
  changed only in `[lo, hi)`. `ArrayAt.outside` and `GraphAt.setRow` rebuild
  the caller's whole array from it.

- `refine` is proved through one state predicate (`Proofs/Refine/State.lean`):
  `Loc` (argument blocks, the three naugraph work blocks), `Ok` (sizes and a
  pairwise-distinct list of every block it touches), `Mem` (memory holds a
  Hex `RefineSt`), `Tmp` (temporaries), `StInv`. Each pass goes from `Mem …
  st` to `Mem … st'` with `Unch` over the blocks it writes, and the
  `scripts/factor_clight.py` cut of the Clight names the pieces. The passes
  enter `wp_iter`/`wp_mainLoop` as the props `TrivialPass`/`NontrivialPass`.
  `refineSpec`'s post promises no workset capacity, because `refine1` (used
  when `m = 1`) never allocates the workset. Callers reach either routine
  through `RefineFn xi M vf` (`Proofs/Refine/Fn.lean`), as `doref` and
  nauty.c do through `dispatch.refine`.
- `ptn`'s "infinite" entries differ between C and Hex: `nauty()` and
  `recover` write `NAUTY_INFINITY = 2000000002`, HexGraphIso's search
  writes `inf = n + 2`. All readers compare `ptn[i] > level` with
  `level ≤ n + 1`, so the C proofs are stated against Hex's search run with
  `inf = 2000000002`, and `Spec/SearchInf.lean` proves the search's results
  independent of `inf > n + 1`.

- nauty.c's search is specified over `Proofs/Search/State.lean`:
  `SLoc` (the caller's arrays, the workspace, nauty.c's `DYNALLSTAT` arrays,
  the harness callback, `M`) and `SearchAt m S ctx st pre nsp` (pointer
  globals, option copies and dispatch table fixed by `nauty()`; static
  scalars = `st`'s fields; `statsblk` = `st`'s counters, `maxlevel` only once
  the first leaf is reached since the harness leaves it uninitialised; the
  arrays, `canong`'s first `samerows` rows, the workspace ring = `st.autos`;
  naugraph/nautil work arrays somewhere apart (`WorkAt`)). HexGraphIso
  carries the short-prune request in `Exit.unwind`, nauty in
  `needshortprune`, hence `nsp`. The `unsigned long` counters are related
  through `lr` (modular), so increments need no bound; bounds below `2^31`
  for the written outputs are a Phase 6 lemma. Generators found are written
  through the harness's `userautomproc` (`AutomCb`), so specs state the
  trace as `Writes t (gensWords …)`. Leaf functions' specs are in
  `Proofs/Search/Spec.lean`; the recursive nodes are specified against
  `node`/`sweep` with fuel `n + 3 - level` (sweep `n + 1`), and HexGraphIso's
  `node_noFuel` shows the fuel is never the reason a call returns.
- The C initial state differs from `Nauty.initial` in `ptn` (`NAUTY_INFINITY`
  for `n + 2`) and `firsttc` (zero-filled by the allocator, `-1` in Hex); both
  are absorbed by `Spec/SearchInf.lean`.

- nauty.c's leaf functions are proved over `SearchAt` (`Proofs/Search/State.lean`):
  `firstterminal_satisfies`, `recover_satisfies`, and `automCb_emit` (the
  harness's `emit_generator` as `AutomCb Statement.xi`). `Proofs/Search/Frame.lean`
  moves `SearchAt` across memory changes; `sep_ne hd` proves two blocks of
  `S.blocks` distinct by locating them in the list. Spec changes made for these
  proofs: `SInv` records the sizes of the search's arrays (stores match
  `Array.set!` only in range) and bounds the level-valued statics by `2^31`
  (the C compares them as `int`s); `Stats` records that the `statsblk` lies
  below `2^64`; `AutomCb` asks for the permutation's entries to be below `2^31`;
  `processnodeSpec`'s trace writes the leaf's permutation exactly when
  `numgenerators` goes up, because nauty does not report a code-2 automorphism
  that leaves the orbits unchanged, while HexGraphIso's `genTrace` records it.
  The last point also affects the final statement: `expected` writes
  `genTrace`, which is more than nauty emits.
- For `processnode`: `updatecanSpec` asks only that `canong`'s first
  `samerows` rows represent anything (`Graph.RowsAt`), since `updatecan`
  overwrites the rest and `CanongAt` says no more; `testcanlabSpec` states
  that its two reallocated work blocks differ; `SInv` adds `wsCap = 500`,
  `maxlevel ≤ n`, `numorbits ≤ n` and the orbit forest being descending
  (`orbjoin`'s precondition; the C compares `maxlevel` and `numorbits` as
  `int`s). `Proofs/Search/Step.lean` composes frames across calls that
  reallocate the work arrays (`SStep`, `WorkMono`, `WorkAt.next`,
  `SearchAt.rebuildW`); `Spec/Processnode.lean` restates `classify` in the
  C's order.
- `processnode_satisfies` (`Proofs/Search/Processnode/`): nauty.c's
  `processnode` is `classify` then `leafExit`. `processnodeSpec` asks for
  `LeafOk st` (first and best labellings are permutations, `0 ≤ eqlevCanon`,
  `1 ≤ noncheaplevel`, `cosetindex < n`), for the blocks of `S` to be valid
  (so the local `sr` is none of them) and for `userautomproc`'s block to have
  a permission at offset 0 (the C compares it with `NULL`); its postcondition
  adds that the work blocks in use afterwards were in use before or are new
  (`WorkMono`), which composing frames across calls needs. Callee
  specifications changed for it: `fmpermSpec` and `fmptnSpec` allow `fix` and
  `mcr` in one block at disjoint ranges (`Logic/Rest.lean`: `Apart`, `Rest`),
  since nauty passes `fmptr` and `fmptr + M` in the workspace;
  `testcanlabSpec` keeps the block holding `samerows` (`Keep`), so `sr` can
  be freed.

- `densenauty`, `nauty()` and `main` are proved. `densenauty_satisfies`
  (`Proofs/Top/Densenauty.lean`) proves the harness's `densenautySpec` from
  `nauty` against `nautySpec` (`Top/Spec.lean`: `densenautySpec`'s memory plus
  the reallocated `dnwork` pair; `options->digraph` stays writable for the
  write-back); the loop scan is `wp_scanLoop` (HexGraphIso's graphs are
  loopless). `nauty_satisfies` (`Proofs/Top/Nauty.lean`) composes `nauty()`'s
  stages (`Top/NautySyntax.lean`: `tSizes`, `tZero`, `tMain`, `tAlloc`, `tTc`,
  `tOpts`, `tPtn`, `tInit`, `tOrbits`, `tStats`, `tWork`, `tRoot`, `tPost`,
  `tFree`), each proved in its own `Top/` file, with the root call through
  `nodes_satisfies` (`Proofs/Search/Node/Nodes.lean`: `firstpathnode_body`
  and `othernode_body` by induction on the level) from `SearchAt …
  (initialC …)` (`SearchInf.nodeOk_root`). `main_ok` gives `main`'s
  `mainSpec` (`Proofs/Harness/Main.lean`: reads `ins`, writes `expected G`,
  returns 0) from `main_satisfies` and `densenauty_ok`.
- The search's output is stated as `Emits t (Em …)` for an abstract emission
  function `Em` obeying `EmLawOff` / `EmLawFirst` (`Search/Node/Em.lean`).
  `main_ok` and everything above it take `Em`, the laws, `Em`'s value at the
  root (`gensWords gens n`) and `gensWords gens n = autosWords G` as
  hypotheses. They are discharged for HexGraphIso's `TraceRun.emitted` after
  the re-pin of hex-graph-iso (Phase 6).

## Phase 6: dense end-to-end

Shape of the composition: `main`'s specification (`Proofs/Harness/`) is an
existence statement (some execution, the one whose `nv_read`s return `ins`,
terminates with `writes t = expected G`); every behaviour consistent with
`ins` is that one by determinism of Clight steps up to the results of
external calls (`nv_write`'s event result is arbitrary but does not affect
the state), and Phase 3's backward simulation carries the behaviour to the
binary. Decisions taken with Kim on the final statement (2026-11-27):

- The statistics in `expected` are compared modulo their C types
  (`Statement.asInt`, `Statement.asLong`): no bound on the search's counters
  holds for every graph with `n ≤ maxN`, and nauty never reads them back to
  decide anything, so the theorem stays unconditional.
- nauty does not report every admitted automorphism: in `processnode`'s
  code-2 case it skips `userautomproc` when `orbjoin` leaves the orbit count
  unchanged, while the pinned hex-graph-iso v0.10.0 pushes onto `genTrace`
  regardless. `expected` must write HexGraphIso's emitted sequence
  (`SearchState.emitted`, hex-dev PR #11048); nauty-verified re-pins
  hex-graph-iso to the release containing it and switches `expected` to
  `TraceRun.emitted`. The C-side specs state the trace through an abstract
  emission function (`processnode`: `genWords workperm n` exactly when
  `numgenerators` increases; the search: `Em` obeying `EmLawOff` /
  `EmLawFirst`), which holds for both versions.

Compose Phase 5 with Phase 3 into `densenauty_binary_correct`; derive the
corollaries from `HexGraphIso` (`canon_iso`, `canon_invariant`,
`iso_iff_canon_eq`, `Aut.complete`, `autos_sameOrbit`) and, in the
Corollaries lib, `hex-graph-iso-theory`'s Mathlib-facing forms.
`#print axioms` must show only `propext`, `Classical.choice`, `Quot.sound`.

Status: `densenauty_binary_correct_of` (`Statement/DenseOf.lean`) proves
`densenauty_binary_correct`'s statement from `main_ok`'s hypotheses on the
emitted words (an `Em` obeying `EmLawOff` and `EmLawFirst`, its root value
`gensWords gens n`, and `gensWords gens n = autosWords G`), axiom-clean.
`init_mem_some` gives the initial memory (CompCert's `init_mem_exists`, its
alignment and symbol conditions checked by the kernel as `initOk_prog`),
`exec_of_main` turns a `Satisfies` of `main` from it into an execution from
the initial state to `main`'s return, and `binary_of_execution`
(`Statement/Compose.lean`) carries that execution to every behaviour of the
binary. `densenauty_binary_correct` (`Statement/Final.lean`) is
`densenauty_binary_correct_of` with the emission hypotheses `sorry` until they are
discharged.

Remaining: re-pin hex-graph-iso to the release with `TraceRun.emitted`,
switch `expected` to it, and prove `EmLawOff`/`EmLawFirst`, the root value
and `hgens` for it, which closes `densenauty_binary_correct`; then Phase 7.

Initial memory (`Proofs/Init/Tables.lean`, done): `globals` turns Clight's
`initial_state` fact `Genv.init_mem prog = some m` into `Globals m`: the four
copies of `bit[64]` (`BitTable`), `leftbit` (`LeftbitTable`), naugraph.c's
`bytecount` (`BytecountTable`, entry `i` = HexGraphIso's `popCount i`), and
`DynAt m bp bs c 0 b` for every `DYNALLSTAT` pair of nautil.c, naugraph.c and
nauty.c (for any `c`, `b`); `valid_global` gives validity of every global's
block. The whole initial memory is never evaluated: CompCert's proved
`init_mem_characterization` reduces each global to its own initialiser,
which one `kernel_rfl` per global pins (`info b`: initialiser, read-only and
volatile flags), and `loads64`/`loads32` read an initialiser of integers back
as loads. The file checks in about 5 seconds. `ge.genv_genv = Genv.globalenv
prog` must be stated with `kernel_rfl` (`ge_eq`): the elaborator's `rfl`
unfolds `globalenv` and exceeds the recursion limit. Block numbers of all
these globals are pinned in `Proofs/Alloc/Blocks.lean`.

## Phase 7: sparse

Target: `sparsenauty_binary_correct` (`Statement/SparseFinal.lean`), the
dense theorem's shape for `sparse_main.c`: for a coloured sparse graph `G`
(`Hex.GraphIso.Sparse.Colored`, sorted symmetric loopless rows) with
`0 < n ≤ maxN`, `k ≤ maxN` and input `sparseInput G` (`n`, the colours, the
degrees, the rows in `G`'s order), every behaviour of the binary of
`scripts/build_binary.sh --sparse` consistent with the input terminates and
writes `expectedSparse G`: `sparseOutput` of
`Hex.GraphIso.Nauty.Sparse.runColored G` (generators, canonical labelling,
orbits, the canonical rows in nauty's unsorted order with `dispatch_sparse`'s
`cleanup = NULL`, the statistics). It is `binary_of_backward` (Compose.lean,
generic over the Clight program) through `sparse_backward`, with one `sorry`
for the execution of `main`. The generators block uses `genTrace` like the
dense statement and switches to `TraceRun.emitted` with the same re-pin
(CI checks nauty's generators are a subsequence of `genTrace`; on CFI-120
`genTrace` has seven more). `maxN` is the dense one: nausparse.c's `int`
arithmetic is on degrees, counts and cell positions below `n`, edge offsets
are `size_t`, and `2 * 500 * m` is shared with dense.

Trusted base: unchanged. `sparse` is linked by the same `c_link` model; the
`extending dense` numbering only chooses different identifiers, and
`sparse.fresh = dense.fresh` is a SimplExpr context, which Phase 3's theorem
quantifies over.

### Done

- `c_link sparse := sparse_main nauty nautil nausparse schreier naurng zalloc
  extending dense` (`Source/Sparse.lean`): every key of `dense` keeps its
  identifier, new keys are numbered from `dense.fresh + 65536` (clear of
  SimplExpr's temporaries, which start at `dense.fresh` in every function),
  so a function both programs link has the same Clight in both.
  `Source/Shared.lean` checks this by kernel `rfl` for all 60 functions of
  nauty.c, nautil.c, schreier.c, naurng.c and zalloc.c, and for
  `cheapautom_sg = dense.fn.cheapautom` (same source). Clight pinned by
  `sparse.clight_eq`/`sparse.locals_eq` as for dense; `sparse_backward`.
- `sparse_main.c`: offsets are the running sums of the degrees, the edge
  array has at least one entry, all other options as dense.
- CI: `run_native.sh` (both harnesses, `*.sparse.out`), `run_interp.sh`
  (`nvInterp --sparse` on `sparse.locals`), `run_expected.sh`
  (`nvSparseExpected`, HexGraphIso's sparse search, against the sparse
  fixtures: blocks 2 to 5 equal, generators as above). The CompCert4Lean
  binary (`build_binary.sh --sparse --check`) reproduces all 52 fixtures.
  Regenerating `c/csyntax/` needs a built CompCert and is not in CI for
  either program; regeneration is byte-identical locally.

### What is reused, and how

The shared functions have identical Clight, but every proof is stated over
`Program.ge = globalenv dense.locals` with concrete block numbers
(`Block.*`, pinned by `kernel_rfl`), and the sparse program puts the same
identifiers at other blocks (`malloc` 242 against 270, `firstpathnode` 12
against 11, because `prog_defs` differ). So the reuse is by generalising
once, not by copying:

1. **Environment record** (`Program/Env.lean`). A structure `NautyEnv ge`
   holding the block of every global and function the nautil.c, nauty.c,
   allocator and naugraph-independent proofs mention, with their
   `find_symbol`, `find_funct_ptr` (bodies `dense.fn.*`) and initial-memory
   facts and a `Nodup` of the block list for `sep_ne`. Rewrite the proofs to
   take `E : NautyEnv ge` and use `E.<x>` for `Block.<x>`. Instances: `dense`
   from today's `kernel_rfl` facts, `sparse` from new ones plus
   `Source/Shared.lean`. This covers, unchanged in substance: `nextelement`,
   `orbjoin`, `breakout`, `fmptn`, `shortprune`, `longprune`, `fmperm`,
   `permset`, `doref`, `maketargetcell` (its target-cell argument is already a
   function pointer), the allocator layer (`malloc`, `free`, `nauty_zalloc`,
   `DYNALLOC1`, `DynAt`), `cheapautom` (as `cheapautom_sg`) and
   `automCb_emit`.
2. **Dispatch record.** `SearchAt`'s `Fixed` pins `dispatch` to naugraph.c's
   seven procedures and their specs. Replace them by a record `DispatchC`:
   the blocks of `isautom`, `testcanlab`, `updatecan`, `refine`, `refine1`,
   `cheapautom`, `targetcell`, `freedyn`, `check`, `init` (`NULL` for dense)
   and the `FunSpec` each satisfies, stated against the policy's operations
   (below). nauty.c (`firstterminal`, `recover`, `processnode`,
   `firstpathnode`, `othernode`, `nodes`, `nauty()`) is proved once over
   `DispatchC`; dense instantiates it with the existing
   naugraph.c proofs, sparse with nausparse.c's.
3. **Canonical storage.** `SearchState n κ` is already generic in the
   canonical store; `SearchAt` fixes `κ = Array (VSet n)` and `CanongAt`
   (setword rows). Make the store's representation a field of `DispatchC`
   (`CanonRep m S c samerows`): dense, the first `samerows` setword rows;
   sparse, the `sparsegraph` struct `canong` (its `v`, `d`, `e` arrays and
   capacities, allocated by `init_sg`) holding `Rows` up to `samerows`.
4. **Search function.** The node proofs are stated against HexGraphIso's
   dense `node`/`sweep`; restate them against `Generic.node`/`Generic.sweep`
   (dense `node_eq_generic`) for any policy whose shared transitions are the
   dense ones (`recordFirst`, `compareCodes`, `firstterminal`, `leafExit`,
   `cheapCheck`, `afterChildFirst`, `orbit`, `shortprune`, `longprune`) and
   whose `child`, `recover`, `afterSweep` agree with dense on every field
   nauty.c stores. The policy-specific operations (`visit`, `chooseTarget`,
   `classify`, `updatecan` at the end) enter only through `DispatchC`'s specs.
   `Sparse.policy` differs from dense only in those, in `Storage.invalidate`
   (ghost: sets `scratch.indexed := false`) and in `order` (not written).
5. **Ghost scratch.** HexGraphIso's sparse state carries `Scratch` (cell
   indices, hit counts, marks with an unbounded stamp), reused across calls;
   nausparse.c keeps `work1`..`work4` and `vmark1`/`vmark2` with `short`
   stamps reset at 32000. The C specs are stated against the fresh
   functions (`Sparse.refine`, `Sparse.maketargetcell`), and the search
   proof connects them to the cached ones in the policy by two HexGraphIso lemmas:
   `maketargetCached_eq` (exists) and the analogue for `refineWith` (C-visible
   outputs `lab`, `ptn`, `active`, `numcells`, `longcode` equal `refine`'s for
   any `Scratch.Bounded` scratch; to be proved from `RefineSt.Equiv`), with
   `Scratch.Bounded` carried as an invariant of the search
   (`Storage.invalidate_valid`, `Storage.update_valid`, `splitCounts_bounded`).

### Making nauty.c's proofs generic (stage 3)

How the sparse procedures fit `DispatchC` (`Proofs/Dispatch/Spec.lean`): the
graph's and store's own conditions are `Ops.GraphOk G` (in every
specification taking `G`, carried by `SearchAtG.graphOk`) and
`Ops.StoreOk G c` (carried by `SInvG`); `initSpec` and `init_null` produce
`Ops.blank G` (sparse: `Graph.blank`) with no meaningful row; `testcanlab`
and `updatecan` get `lab` injective as well as onto. Facts about memory
belong to the instance's representations: offset bounds such as
`cofs + 48 < 2^64` in `CanonRep`/`CanonPre`, the `e = NULL` case of an
edgeless graph by leaving `e` out of `canonBlocks`, the separation of
`canong` from its arrays through `Sep` over `canonBlocks`, `work1` and the
other scratch pairs in `Work`, `snwork` as `wsP`/`wsS`.

Foundation (in place): `Proofs/Dispatch/DenseRep.lean` (`denseRep`, below the
search so the state can name it), and in `Proofs/Search/` the generic forms
next to the dense ones:

- `State.lean`: `SearchAtG D m S gl cl G st pre nsp` over `[E : NautyEnv ge]`,
  `D : DispatchRep ge O`, the representation locations `gl : D.GLoc`,
  `cl : D.CLoc`, `G : O.Gr n`, `st : SearchState n (O.Canon n)`; its parts
  `FixedG`, `ScalarsG`, `StatsG`, `ArraysG` (graph and store through
  `D.GraphRep`/`D.CanonRep`), `DynsG` (workspace pair `D.wsP`/`D.wsS`),
  `WorkG` (`D.Work`, nautil.c's `workperm` pair, both apart from the blocks),
  `TablesG`, `SInvG`; `IsWorkG`; `S.blocksG D gl cl` (caller blocks with the
  rep block lists, `envSearch`, `D.globs`), `S.ChgG`. Dense instance:
  `SearchAt.toG : SearchAt … → SearchAtG denseRep … () () …` and
  `SearchAtG.dense : SearchAtG denseRep … → (graph words, `SearchAt.gw`) →
  SearchAt …`; `SLoc.mem_blocksG`, `SLoc.distinctG`/`distinct_ofG`
  (`S.blocksG denseRep () ()` is a permutation of `S.blocks`, `perm_lit`).
- `Spec.lean`: `SFrameG`, `firstterminalSpecG`, `recoverSpecG`,
  `processnodeSpecG` (leaf step `O.classify`), `LeafOkG`; `isWork_dense`,
  `SFrameG.dense`/`SFrame.toG`, `workMonoG_dense`, and
  `firstterminalSpec_ofG`, `recoverSpec_ofG`, `processnodeSpec_ofG`
  (a `Satisfies` of the generic specification at `denseRep` gives the dense
  one).
- `Frame.lean`: the `.unch` lemmas for every part, `SearchAtG.work_not`,
  `SearchAtG.unch` (needs the step to keep valid blocks valid, for
  `D.work_unch`); dense `SearchAt.work_not` is derived.
- `Step.lean`: `WorkMonoG`, `SStepG` (`refl`, `trans`), `SValidG`,
  `IsWorkG.valid`, `SStepG.of_unch`, and `WorkG.step`: the scratch state and
  `WorkMonoG` after a dispatch call's `DispatchRep.Step`. This replaces the
  dense `afterWP`/`afterWPWS`/`WorkAt.next` family, which stays dense-only.
- `Valid.lean`: `SearchAtG.valid_blocks`, `valid_all`; dense
  `SearchAt.valid_blocks` is derived.

Recipe for converting a file (dense names and statements stay, so the files
after it build unchanged):

1. State each lemma over `SearchAtG D` (take `D : DispatchC ge O` and use
   `D.toDispatchRep` when the code calls a dispatch procedure, with
   `D.isautom_fn` and the others for the call). Replace `Block.x` by `E.x`,
   `S.blocks` by `S.blocksG D gl cl`, `IsWork`/`SFrame`/`SStep`/`WorkMono`/
   `SValid` by their `G` forms, `ctx : Ctx n` by `G : O.Gr n`, `Search n` by
   `SearchState n (O.Canon n)`, dense HexGraphIso steps by the `O` fields or
   the generic `SearchState` functions; naugraph.c's slots are not visible,
   so reason about dispatch calls with `DispatchRep.Step` and `WorkG.step`.
2. Re-derive the dense name below it: a `SearchAt` conclusion as
   `(L_G h.toG …).dense h.gw`, a specification through a `*_ofG` lemma (add
   one per new generic specification, as in `Search/Spec.lean`), frames
   through `SFrameG.dense` and `workMonoG_dense`, block membership through
   `SLoc.mem_blocksG`.
3. A dense-only lemma with no generic counterpart (naugraph.c's slots) stays
   as it is until its last user is converted, then goes.

Tools from batch 1, for the batches after it:

- Distinctness. `S.blocksG` has opaque parts (`D.graphBlocks`,
  `D.canonBlocks`, `D.globs`), so `sep_ne` cannot index it. Use
  `sep_ne h.lit` / `sep_all h.lit` / `sep_notin h.lit` (`SearchAtG.lit`:
  `S.litG`, `S`'s own blocks with `S.bg`, `S.bc` and `envSearch`, is pairwise
  distinct) for list entries; `h.graph_ne`, `h.canon_ne`, `h.globs_ne` for a
  block of the graph's or store's representation or a global of `D` against
  the other parts. Where the dense proofs decided `¬ z ∈ L` for many blocks by
  `decide`, prove one permutation of `S.litG` by `perm_lit` and read the
  disjointness off its `Pairwise` (`SLoc.keepG_perm`, `SLoc.scal_perm` in
  `Node/Rebuild.lean`). Inside `first | exact .inl (by simp) | …` the `by`
  is elaborated late, so a failing branch is not skipped: order the cases.
- Rebuilding. `SearchAtG.rebuild` (writes confined to `wrEnv`, `S.wrVG` and
  `D.canonBlocks cl S.bc`) and `SearchAtG.setScalars` need every valid block
  kept valid (for `D.work_unch`); the `wp_*` lemmas all supply it. The dense
  `SearchAt.rebuild`/`setScalars` do not take it, so they stay dense-only.
  Fields of a changed state go in as `{ h.scalars.unch hu … with }` (the
  structure-update form), not `h.scalars.unch hu …` directly.
- Struct members. `NautyEnv` carries the member offsets of `tcnode`,
  `statsblk` and `dispatchvec` (`E.field_*`, kernel-checked per program);
  `Node/Fields.lean`'s `field_*` and `Ops.lean`'s `fld_*` are generic.
- Nodes. `nodeSpecG D … first S gl cl G st level numcells chain` is stated
  against `Generic.node` for a policy instance
  `[Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]` taken as an
  argument (`hexNodeG`); the node proofs will need hypotheses tying that
  policy's `visit`, `chooseTarget`, `classify` and the shared transitions to
  `O` and to the dense ones. `nodeSpec_ofG` instantiates it with HexGraphIso's
  nauty policy (`node_eq_generic`). `firstChildG`, `otherChildG`,
  `node_true_succG`, `node_false_succG`, `sweep_*_someG` are the unfoldings at
  any policy; `cmpFirst`/`cmpCanon` and `compareCodes_eq` are over any store.
  `tcParent` is over any `NautyEnv`.
- `Node/GcaSteps.lean` stays dense: its users are `OkOff`/`OkFirst`, which
  feed `denseLaws`; for a general policy the level counters across a sweep
  step are part of `NodeLaws`' sweep invariants (`first_next`, `off_next`),
  so it has no generic counterpart. The dense HexGraphIso unfoldings
  (`FirstHex`, `OtherHex`) and the dense `UaFrame`/`Rebuild` lemmas keep their
  own proofs beside the generic ones.
- Firstterminal (batch 2 (a)): `firstterminal_satisfiesG D` meets
  `firstterminalSpecG D` for any `D : DispatchRep ge O` (no dispatch call;
  the final state by `SearchAtG.rebuild`, the frame by `SStepG.of_unch`), and
  `wp_copyIntsG` is the copy loop over any `NautyEnv`. The dense
  `firstterminal_satisfies` and `wp_copyInts` are their instances. A generic
  node body calls `firstterminal_satisfiesG` directly.
- Processnode (batch 2 (d)): `processnode_satisfiesG D C S gl cl G st level
  numcells` meets `processnodeSpecG D.toDispatchRep` for any
  `D : DispatchC ge O` and `C : Classifier O` (`Processnode/Classifier.lean`):
  `O.classify` is `classifyBy O (C.update G)`, `classify_eq`'s processnode-order
  restatement over `O.isautom`, `O.testcanlab` and the store update `C.update`
  (rows `O.updatecan`, `rows_update`), with `testcanlab_range`. The dense
  `processnode_satisfies` is its instance at `Dispatch.dense` and
  `denseClassifier` through `processnodeSpec_ofG`. A sparse instance needs a
  `Classifier` with `update` the store's own update and `classify_eq` proved as
  `Spec.classify_eq` is. `PCtx D`/`PAt D` (`Processnode/State.lean`) are over
  `SearchAtG`; `PAt.call` and `PAt.callSame` step across a dispatch call
  (`DispatchRep.Step`, outputs among the store's blocks and `sr`), `PAt.nautil`
  across a reallocation of nautil.c's `workperm` pair (`fmperm`), and
  `PAt.sepG`/`PAt.sepGC` and `SearchAtG.ctx` give a call's `Sep` and `Ctx`.
  The dispatch preconditions come from `SearchAtG` as it stands: `lab`
  injective from onto (`lab_inj`, by `surj_inj`), `O.StoreOk` from
  `SInvG.canong`, `O.GraphOk` from `SearchAtG.graphOk`. `Keeps`, `lxBody`,
  `leafExit_eq`, `leafWords` are over any store, and `Processnode/Set.lean`
  has the `ArraysG` updates (`set`, `setCanong`, `setAutos`, `wp`, `cast`).

Batch 2 group (b), the node leaf steps (generic names next to the dense ones):

- Over `SearchAtG D` with the dense lemma derived: `wp_nodeBreakoutG`,
  `wp_tctotalG`, `wp_hintG`, `wp_tcResetG`, `wp_prune0G`, `wp_nodeLongG`
  (`AutosAtG.pairs`), `TcOkG.mono`, `NSetG`/`nset_stepG`/`nset_childG`/
  `nset_ownG` (with `NodeFrameG.nset`/`grow`/`mk'`). Prologue's
  `wp_tcallocSkip`/`wp_tcallocNew` take any `NautyEnv`, which records
  `sizeof_tcnode`. `brokenSt`, `shortprune_last` are over any store.
- Dispatch calls: `wp_cheapG` (`DispatchC`'s `cheapautom`; hypothesis
  `O.cheapautom st.ptn level n = cheapautom st.ptn level n`, which the node
  policy's linking structure should supply), `wp_nodeVisitG` (`doref` with
  `D.refineAt M`, state `visitStG O G level numcells st`). Their frames are
  `D`'s (written globals, scratch blocks in use, new blocks), weaker than the
  dense ones, so the dense `wp_cheap`/`wp_nodeVisit` keep their own proofs.
- Shared tools: `SInv.toG`/`SInvG.dense`; `SearchAtG.dstep` (a dispatch
  call whose outputs avoid `S`: state unchanged, `WorkMonoG`);
  `SearchAtG.lit_globs`, `ChgD`, `SearchAtG.not_chgD` and
  `SearchAtG.rebuildD` (writes to `S`, a dispatch procedure's scratch and
  nautil.c's `workperm` pair in one step, the counterpart of `reallocW`);
  `DispatchRep.doref_refineT`; `dorefSpecR`'s post keeps validity across the
  `qinvar` store.
- Dense-only, replaced by the tools above: `LocDistinct`, `Realloc`,
  `ReallocW.reallocW`, `Doref.wp_nodeDoref` (naugraph.c's slots).
- Target and Choose: `wp_nodeTargetG` is the `maketargetcell` call with
  `D.targetcell` (`maketargetcell_satisfiesV`, which adds to
  `maketargetcellSpecT` that blocks valid after `targetcell` stay valid, by
  `wp_grow`), result `mtcOf n lab ptn level (O.targetcell …)`, state unchanged;
  `wp_chooseOffG` leaves `chooseTargetG O false`'s state, and
  `chooseTargetG_false_eq` gives its cases (the dense `chooseTarget_false_eq`
  is its instance). Both take `htc` (the target position starts a nontrivial
  cell), which a node body gets from `NodeLaws.target_lt`, and the policy's
  `chooseTarget` comes in through `PolicyLink.target_eq`/`target_same`. Their
  frames are `D`'s, so the dense `wp_nodeTarget`/`wp_chooseOff` keep their
  own proofs. The HexGraphIso-side
  files `InvSteps`, `OkOff`, `OkFirst`, `ProcFacts`, `Em` are about the dense
  `node`, `Colored` graphs and `SearchInf`; they stay dense. The generic node
  bodies need `SInvG` of each step's state, which comes from the policy
  structure (partition facts of `P.visit`, `P.child`, …) rather than from
  these files; `SRest` itself is store-independent except `canongSize`.

Batch 3, the policy side (generic names next to the dense ones):

- `Node/Policy.lean`: `PolicyLink O n` for a policy instance
  `[Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]`, a separate
  argument of the node proofs (like `Classifier O`): `visit` through
  `O.refine` (`visit_numcells`, `visit_code`, `visit_same` to `visitStG` of the
  counted state), `chooseTarget` through `O.targetcell` and `mtcOf`
  (`chooseTargetG`; `target_eq`, `target_same`), `classify_eq` to
  `O.classify`, the shared transitions equal to HexGraphIso's, `child`,
  `recover` and `afterSweep` equal up to `Same` (every field but the carried
  store, whose rows agree, and `order`), `cheapautom_eq` for `wp_cheapG`.
  `visit` and `chooseTarget` are conditional on the store invariant `Inv`
  (kept by `visit_inv`, `target_inv`, `classify_inv`, `child_inv`,
  `recover_inv`, `afterSweep_inv`; the other transitions keep the store) and
  on `VisitOk`/`TargetOk`. `SearchAtG.same`/`SInvG.same` move the C state
  along `Same`. Dense: `denseLink` (all three conditions `True`).
- `Node/Laws.lean`: `NodeLaws L G`, the HexGraphIso facts the node bodies
  read (`NodeOk`, `SweepFirst`, `SweepOff` and the laws `first_start`,
  `first_child`, `first_next`, `off_start`, `off_child`, `off_next`,
  `visit_inv`, `visit_part`, `target_lt`, `first_broken`, `off_broken`,
  `first_args`, `off_args`, `noFuel`, `unwind_lt`, `leaf_lt`, `leaf_done`,
  `leafOk`, `short_autos`, and `inv`, `visitOk`, `targetOk` for the link's
  conditions), stated against `Generic.node`, `firstChildG`, `otherChildG`
  and `SInvG`. They rest on HexGraphIso's soundness of the policy, so they
  are a structure rather than theorems; `denseLaws G ctx hn0 hn` is the
  dense instance from the dense lemmas (`Spec/NodeOk`, `NodeOkOff`,
  `NodeExit`, `NodeBound`, `PartOk`, `Node/OkOff`, `OkFirst`, `ProcFacts`),
  and a sparse instance comes from HexGraphIso's sparse soundness. The
  emitted words: `EmLawOffG`/`EmLawFirstG` (`sweepEmG`, `sweepEmFirstG`,
  `procExitG`, `procWordsG`), from the dense laws by `EmLawOff.toG`/
  `EmLawFirst.toG`. `PartFactsG`, `SRestG`, `SInvG.of`.

Remaining files (`Proofs/`), in dependency order; the files of one batch
depend only on earlier batches, so a batch's groups can go to parallel
agents:

- Batch 1 (shared node infrastructure, one agent): `Search/Ops.lean`,
  `Search/Node/{Spec, Rebuild, Tc, TcOps, UaFrame, Fields, Env, Steps,
  Fixed, GcaSteps, Compare, FirstHex, OtherHex}` (the `*Hex` files are the
  HexGraphIso-side node facts, to restate against `Generic.node`).
- Batch 2 (four independent groups): (a) `Search/Firstterminal/*`;
  (b) the node leaf steps `Search/Node/{Breakout, LocDistinct, InvSteps,
  OtherSteps, Prologue, OkOff, OkFirst, Doref, Prune, Realloc, ReallocW,
  Target, TcFrame, Choose, Visit, OtherFrame, Long, ProcFacts, Em}` (the
  dispatch calls are in `Doref`, `Target`, `Visit`, `Choose`, `Realloc*`);
  (c) `Search/Recover/*` and `Search/Node/LoopSteps` (after `Node/Prune`);
  (d) `Search/Processnode/*` (after `Node/{Fields, Env, Steps, InvSteps}`;
  `Processnode/Callback` imports `Top/NautyMain`, whose part it needs moves
  first).
- Batch 3 (two groups): the node bodies `Search/Node/{Process, Child,
  FirstLocal, FirstMisc, NodePrologue, FirstShape, FirstLoopAt, FirstCall,
  FirstHead, FirstEntry, FirstTail, FirstInit, FirstVertex, FirstLoop,
  FirstEnd, FirstBodySteps, FirstBody}` and `Search/Node/{LoopShape,
  OtherRest, OtherIter, OtherCarry, OtherLoop, OtherBodySteps, OtherEntry,
  OtherTail, OtherBody}`, then `Search/Node/Nodes`.
- Batch 4: `Top/*` for `nauty()` (`NautyAlloc`, `NautySizes`, `Spec`, `Init`,
  `Globals`, `Copy`, `Head`, `NautyEntry`, `NautyTc`, `Opts`, `Ptn`,
  `NautyInit` with the `init` call (`DispatchC.init_fn`, `init_null`),
  `NautyOrbits`, `NautyStats`, `NautyWork`, `NautyRoot`, `NautyPost`,
  `NautyFreedyn`, `NautyFree`, `Nauty`); `Top/Densenauty`, `Top/Check`,
  `Top/Freedyn`, `Search/Emit*` and `Harness/*` stay dense (the sparse
  program has its own `sparsenauty` and `sparse_main`).

### New specifications (nausparse.c), with their HexGraphIso counterparts

Each is a `*_satisfies` over `NautyEnv` for the sparse instance, with the
input graph as `SparseGraphAt` (the `sparsegraph` struct: `nv`, `nde`, `v`,
`d`, `e`, `w = NULL`, rows equal to `Sparse.Graph.ofGraph G` rows) and the
work arrays as `DynAt` pairs.

- Marks: `preparemarks1`/`preparemarks2` and `RESETMARKS1`/`RESETMARKS2`
  with the invariant every `vmarkK[i] ≤ vmarkK_val ≤ 32000`, so after a reset
  every entry is below the stamp (the wraparound branch zeroes the array and
  sets the stamp to 1). Specs are relative to "entry equals the stamp", which
  is how HexGraphIso's `marks`/`stamp` and its local stamps `i + 1` are read.
- `isautom_sg`: `Sparse.isautom` (undirected: fixed vertices skipped).
- `testcanlab_sg`: `Sparse.testcanlab`, writing `samerows`; uses `work1` as
  `INVLAB` (`Sparse.inverse`).
- `updatecan_sg`: `Sparse.updatecan` on `CanonRep`; `nv`, `nde` of `canong`
  set; `w = NULL` branch only.
- `init_sg`: `SG_ALLOC` of `canong` to `n` and `nde` entries, `*status = 0`;
  establishes the sparse `CanonRep` of `Graph.blank` (zero-filled).
- `distvals`: `Sparse.distvals` (`work4` as the queue, already allocated to
  `n` by `refine_sg`, so its `DYNALLOC1` does nothing).
- `sortindirect`: `Sort.indirect` (quicksort with insertion sort below the
  cutoff, the inclusive-cursor case at the array base from the audit);
  `sortints`: `sortCells` (on `HITCELL`). Both come from `sorttemplates.c`.
- `refine_sg`: `Sparse.refine`, i.e. `refineWith` with fresh scratch: the
  initial queue from `nextelement` over `active`, `CELLSTART` as
  `indexCells`, the distance split at `level ≤ 2` (`distvals`, then
  `splitCounts … true`), the main loop choosing a singleton splitter among the
  first ten queue entries, `splitSingleton` (trivial split, `HITS[--k]`
  order) and `splitNontrivial` (`splitCounts`, `minima`, `sortindirect`), the
  `MASH`/`CLEANUP` code (`mash`, `cleanup`). Loop variant as dense
  (`refineFuel`). Both `dispatch.refine` and `dispatch.refine1` are
  `refine_sg`.
- `bestcell_sg`, `targetcell_sg`: `Sparse.bestcell`, `Sparse.targetcell`;
  the target cell's set and size as `maketargetcell` (reused).
- `nausparse_check`, `nausparse_freedyn` (frees the seven pairs, including
  `snwork`, the search workspace, after its last use).
- `sparsenauty`: the `dispatch == &dispatch_sparse` test, the loop scan over
  the rows (none, rows are loopless), `DYNALLOC1(snwork, 2*500*m)`,
  `nauty()` through the generic proof, restoring `digraph`; spec as
  `densenautySpec` with `SparseGraphAt` and the sparse `CanonRep`.
- `sparse_main`: reading `sparseInput G` into `sg` (offsets as running sums,
  `Layout` gives `G.offsets`), the partition loops (the same C as
  `dense_main`'s; reuse `Proofs/Harness/Part*.lean` by stating them over the
  loop's factored Clight), output of block 4 from `CanonRep`; `mainSpec`
  writing `expectedSparse G`.

### Statement-side pieces

- Initial memory of `sparse.locals`: `initOk` by the kernel, `Globals` for
  nausparse.c's statics (`vmark1_val = vmark2_val = 32000`, `fuzz1`/`fuzz2`,
  `dispatch_sparse`, seven `DYNALLSTAT` pairs at capacity 0), block pinning.
- `exec_of_main` for the sparse program (generalise DenseOf's over the
  program as Compose's is), giving `sparsenauty_binary_correct` from the
  sparse `main_ok`.
- Emission: the same `Em` laws (`EmLawOff`, `EmLawFirst`) over
  `Generic.node` serve both programs; discharge them for `emitted` with the
  re-pin.
- Corollaries: HexGraphIso's sparse theorems (`Sparse.canon`, `Aut`,
  orbits) are about the sorted `G.relabel l`; the binary writes the same rows
  unsorted, so the invariant corollary needs "the written rows, sorted, are
  `G.relabel l`'s rows" (from `Sparse.updatecan`).

## Verification (continuous)

- Differential tests in CI: run the exported program in the ported Lean
  interpreter on hex's conformance fixtures (`conformance-fixtures/HexGraphIso/`,
  including `prune.json` CFI-120) and compare with `HexGraphIso` evaluated in
  Lean; catches wrong specs before proofs.
- `ccomp -interp` over the fixture corpus as an independent CompCert-semantics
  UB check (harness generator: `/tmp/nauty-verif/gen/mkharness.py`).
- Compile harnesses with CompCert4Lean's driver (`scripts/compile_c.py`)
  and compare outputs with the native gcc build and the hex oracle
  (`scripts/oracle/graphiso_nauty.py` protocol).
- Per-phase acceptance as listed; axiom audit and `sorry`-list shrinkage
  checked in CI.

## Side items

- Report the `firstcode[0]` read to Brendan McKay (draft for Kim's approval
  first); upstream the toolchain bump, Csyntax exporter and Clight-to-Asm
  theorem to CompCert4Lean; ask Certora about CCLib's licence for the ported
  logic.
- Main risks: kernel cost of pinning the Clight ASTs (Phase 1.3); keeping
  the CompCert4Lean fork on Hex's toolchain; spec effort for `nauty.c`'s
  globals and recursion; CompCert's infinite-memory model hiding allocation
  failure and stack depth (state them as assumptions).
