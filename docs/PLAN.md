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
  ∀ beh ∈ Asm.semantics xi (compiledDense),          -- CompCert4Lean output for the pinned C
    Inputs.consistent G beh →                         -- volatile input reads supply encode G,
                                                      -- nauty_kill_request reads return 0
    beh = Terminates (Out.trace (HexGraphIso.Nauty.runColoredTraced G) ...) _
```

where the harness reads the graph through volatile loads of a designated
input global and writes results through volatile stores (CompCert records
both as trace events, which is what its whole-program backward simulation
preserves). Outputs: canonical labelling, canonical graph rows, emitted
generators in order, orbits, the seven statistics. Corollaries restate
`canon_invariant`, `iso_iff_canon_eq`, `Aut.complete`, orbit correctness for
the binary (the Mathlib-facing ones via `hex-graph-iso-theory`). Group order
is out of scope (nauty's is a rounded double; Hex computes its own).

Explicit assumptions in the trusted base: Lean kernel; CompCert's OCaml
frontend (preprocessor, parser, elaboration to Csyntax); CompCert4Lean's
x86-64 Asm semantics, Asmexpand, printer, assembler and linker; CompCert's
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

## Phase 1: C to CompCert4Lean terms

1. **Csyntax exporter.** A `-lean` printer for CompCert's OCaml frontend
   that emits a Lean term of `CompCert4Lean.Cfrontend.Csyntax.program` plus
   its `SimplExpr.FreshIdentContext`. Templates: CLean's
   `/tmp/survey-clean/export/ExportLean{Base,Ctypes,Clight}.ml`; vocabulary
   from CompCert4Lean's generated codecs (`Prototype/Codecs.lean`,
   `bridge/codecs.ml`, `scripts/generate_codecs.py`). Literals as Rocq
   `Z`/`positive`/`RocqString`; `prog_comp_env_eq` by `decide`/`rfl`.
   One module per translation unit; namespaced; header records input SHA-256s
   and flags. Lives in the fork (upstreamable) or `tools/`.
2. **Agreement with the existing ingestion.** Lean test: the printed term
   equals `decodeSource` of the bridge's JSON for the same file (evaluated).
3. **Clight by CompCert4Lean's own passes.** Define
   `clight := SimplLocals (SimplExpr p)` per function; pin each function's
   Clight body with a kernel-checked equality. Risk: kernel cost on nauty's
   largest functions (`refine`, `othernode`). Measure first on `nautil.c`;
   fallback is per-function lemmas with `decide := true` unfolding, or
   printing the Clight from extracted OCaml and proving equality.
4. **Link** the translation units (CompCert4Lean `Common/Linking.lean`,
   `Ctypes.Linker_program`), resolving nauty's file-local statics
   (`workperm` appears in several files).

Acceptance: `lake build` elaborates all units; CI regeneration is
byte-identical; the term/JSON agreement test passes.

## Phase 2: program logic on CompCert4Lean's Clight

Port CLean's CCLib (from `/tmp/survey-clean/export/CCLib`, LGPL/INRIA dual)
onto CompCert4Lean definitions. Order and effort (from the survey):

- First a **transfer layer**: `Word bits ≃ BitVec bits` and Rocq `Z ≃ Int`
  with simp lemmas, so `omega`/`bv_decide` work through `intOfZ`/`zOfInt`;
  Prop-valued `perm`/`valid_access` with deciders.
- Mechanical: `SepLogic`, `FunPtr`, `Tactics`, most of `Funspec`, `Locals`.
- Heavy: `MemdataLemmas`, `SepHoare` (Ptrofs arithmetic), `Aggregate`,
  64-bit array support (replace CLean's `HoareArray`/`HoareLong` bridges).
- Re-validate kernel `decide` on canonical `PTree` and Rocq `positive`
  (`Temps`).
- Determinism from `ExternalCalls`' `extcall_properties.ec_determ` instead of
  CLean's axioms; external calls become the `xi` parameter.
- Port `ClightExec` + `ClightExecSound` (an executable step proved sound),
  with the volatile-read environment from `/tmp/nauty-verif/lean/NautyC/Run.lean`.
- Fill the gaps the `nextelement` proof hit: `arrayU64`, pointer + `long`
  offsets, signed comparison lemmas for negatives, `int ==`/`long != 0`/shift
  helpers, a forward-stepping tactic for `set`/`if`/`assign` chains, better
  `sep_cancel`, and **initial memory to owned fragments** (globals including
  read-only `dropPerm` ones like `leftbit`, `bytecount`, `bit`).

Acceptance: re-prove `nextelement` on the new base; run the interpreter on
the Petersen and CFI-120 harnesses and match native output (as in
`/tmp/nauty-verif/gen/`).

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
