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

Acceptance: `nextelement` proved against Hex's `VSet.nextElem` specification
on this base; interpreter agreement (done).

## Phase 3: Clight to Asm theorem

`transf_clight_correct`: backward simulation from `Clight.semantics2` (the
SimplLocals output we reason about) to `Asm.semantics`, by copying the
composition in `CompCert4Lean/Driver/Compiler.lean`
(`cstrategy_semantic_preservation`, line 1494) from Cshmgen onwards, plus a
new `Clight.semantics_receptive` and the existing
`Asm.semantics_determinate_proof`. Show
`transf_c_program p = transf_clight_program (clight p)` by unfolding, so the
binary the driver emits is the one the theorem covers. Upstream to
CompCert4Lean.

## Phase 4: statements first

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

## Phase 6: dense end-to-end

Compose Phase 5 with Phase 3 into `densenauty_binary_correct`; derive the
corollaries from `HexGraphIso` (`canon_iso`, `canon_invariant`,
`iso_iff_canon_eq`, `Aut.complete`, `autos_sameOrbit`) and, in the
Corollaries lib, `hex-graph-iso-theory`'s Mathlib-facing forms.
`#print axioms` must show only `propext`, `Classical.choice`, `Quot.sound`.

## Phase 7: sparse

`nausparse.c`: `refine_sg` (`refineWith`, `splitCounts`), `distvals`,
`sortindirect` (`Sort.indirect`; the inclusive-cursor case at the array base
from the audit), `sortints`, `isautom_sg`, `testcanlab_sg`, `updatecan_sg`,
`bestcell_sg`/`targetcell_sg` (cached = fresh by `maketargetCached_eq`),
`init_sg` and stamps (C resets short stamps before wraparound; Hex's are
unbounded: invariant needed), `sparsenauty`, `sparse_main.c`. Harness
always supplies valid offsets and a non-null edge array, avoiding the
audit's out-of-range pointer findings. Reuse all Phase 2/4 infrastructure
and the generic search proofs (`Generic.node`).

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
