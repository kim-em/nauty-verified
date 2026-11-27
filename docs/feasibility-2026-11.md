# Proving nauty's C refines HexGraphIso: options, experiments, findings

Target theorem: for the vendored nauty 2.9.3 sources (`nauty.c`, `nautil.c`,
`naugraph.c`, `nausparse.c`), in the pinned Hex configuration, the C (or the
machine code compiled from it) computes the same canonical labelling, orbits
and emitted generators as `HexGraphIso`'s Lean implementation; correctness of
graph isomorphism then follows from `HexGraphIsoTheory`.

Everything below was run on 2026-11-27 in `/tmp/nauty-verif` and the
`/tmp/survey-*` clones. No file in the hex-dev worktree was changed.

## Bottom line

A source-level route exists today, and every stage of it has now been exercised
on nauty itself:

1. `clightgen -lean` (Certora's CompCert fork, "CLean") exports the unmodified
   nauty sources to Lean as Clight ASTs. All four core files, and `schreier.c`
   and `naurng.c`, export and elaborate (46k lines of Lean for the core).
2. CLean's Lean Clight semantics executes them. Its interpreter is proved
   sound against the small-step relation, so each run is a witness of an
   execution in the semantics the theorem would be about. On the 120-vertex
   CFI pruning regression it reproduces the native result for dense (25.2M
   Clight steps, 36 s) and sparse (6.6M steps, 29 s) nauty.
3. CompCert4Lean compiles the same sources to x86-64 with its Lean backend,
   and the binary returns the native result. Its end-to-end theorem
   `transf_c_program_correct` (CompCert C to x86-64 assembly, backward
   simulation) builds, and `#print axioms` shows only `propext`,
   `Classical.choice`, `Quot.sound`. Its README's "proof completion is still in
   progress" is out of date with respect to that theorem.

What does not exist yet, and is ours to build: the refinement proof itself,
and the plumbing that makes the C-side proof and the compiler theorem talk
about the same Clight.

The machine-code route is also real but less ready: braid lowers 98% of
nauty's RISC-V code with soundness-proved lowerings, while the other tool's
proved lift (machine-checked) cannot take nauty at all today.

## A new C finding: nauty has no defined behaviour under CompCert semantics

With `MAXN=0` (dynamic allocation, the configuration Hex pins), every
`densenauty` or `sparsenauty` call reads an indeterminate value.
`firstterminal` copies `firstcode[0..level]` into `canoncode`
(`nauty.c:884`), but `firstcode` comes from `malloc` (`nauty.c:361`) and only
indices `1..` are ever written (`nauty.c:594` writes `firstcode[level]` with
`level ≥ 1`; `nauty.c:873` writes `level+1`). `canoncode[0]` is never read
afterwards, so the copy is harmless on real hardware, and MemorySanitizer
stays quiet (it reports uses, not copies). In ISO C the copied value is
indeterminate but, for `short` without trap representations, arguably only
unspecified; CompCert is stricter. In CompCert's semantics the copy
of an undefined `short` is a stuck state: both CompCert's own reference
interpreter (`ccomp -interp`) and CLean's Lean interpreter stop at exactly
this statement, on every input tried (Petersen, coloured Petersen, the
7-vertex empty graph, CFI-120; dense and sparse). With static allocation
(`MAXN > 0`) the arrays are zero-initialised globals and the issue
disappears.

Consequence: no theorem can be proved about the unmodified `MAXN=0` build in
CompCert C semantics. Options: (a) zero-filling allocation, which is what the
experiments use, via `-Dmalloc=nauty_zalloc` with a 7-line allocator in a
separate file (no nauty source change); (b) an upstream one-line fix
(`firstcode[0] = 0` after allocation, or start the copy at 1), worth
reporting to Brendan McKay alongside the existing audit findings; (c) pin
`MAXN`. It probably belongs in `reports/nauty-translation-audit.md` too.

Also needed, with no source change: `HAVE_HWLZCNT=0` and `HAVE_HWPOPCNT=0`
(nauty's portable table-based bit operations instead of compiler builtins),
and `options.outfile` set to a non-null dummy, since otherwise `nauty()`
reads glibc's `stdout` object, which is not part of the program. The single
volatile object, `nauty_kill_request`, is read 10 to 167 times per run; the
theorem has to assume the environment answers 0 (no asynchronous kill),
which matches the Lean side's pinned-out cancellation.

## The tools, as checked locally

| Tool | What it is | Status verified here |
| --- | --- | --- |
| CLean (`Certora/clean`, Sept 2026) | CompCert 3.17 fork: `clightgen -lean`, Lean port of Clight semantics and memory model, interpreter proved sound, determinism, separation logic with total-correctness triples, function specs, linking | Built (Coq 8.20, Lean 4.32.1). Exports and runs all of nauty. No `sorry` in its library per README; its axioms are the uninterpreted external-call semantics. |
| CompCert4Lean (`fanlong/compcert4lean`, arXiv 2611.21084) | Lean port of CompCert 3.17's compiler core, CompCert C to x86-64 assembly, plus driver | Built (Lean 4.33.0, 374 jobs). Top-level theorem axiom-clean. Compiles all nauty files; binary correct on the harness. Needed a stand-in for `opam` and a relaxed OCaml/yojson version check (this machine has OCaml 4.14.4 and yojson 3.0.0 under Nix). |
| braid (`dhsorens/braid`, Nov 2026) | Binary to MLIR dialect to separation logic, lowerings proved sound against riscv-zkvm (Sail-tied RV64), DeepMind's arm64-semantics, Kraken x86-64 | Built. Nauty core on RISC-V (gcc 16, `-march=rv64imfd`): 6,330 of 6,455 instructions lowered (98%), 39 functions. On x86-64: 6,115 of 6,347 (96%), gaps are SSE floating point plus some `lea`/`mov`/`call` forms Kraken's parser rejects. |
| machine-checked (`Verified-zkEVM/machine-checked`, Nov 2026) | ELF to Lprog lift proved (simulation) against SP1's RISC-V machine; Myreen-style decompilation | Built (needed a private toolchain copy, see below). Its `--proved` lift leaves out nearly every nauty function: SP1's machine does not execute RV64 `*W` instructions (`ADDW`, `SRAIW`), which gcc emits for all C `int` arithmetic. |
| Harmonic Aristotle for C (announced 2026-10-27) | Proprietary; public material describes memory-safety proofs | Not usable for a refinement theorem we can compose with hex. |

## Route A: source-level refinement, then compiler correctness

Theorem shape. With `P` the Clight program obtained by linking the exported
modules and a small harness, `enc` the encoding of a Lean graph into the
harness's memory, and `R` relating C memory to Hex's search state:

```
∀ g, valid g → g.n ≤ N →
  Triple / call-to-return on densenauty from (memory ⊨ enc g)
  terminates, without undefined behaviour, in memory ⊨ out (HexGraphIso.canon g)
```

Then compose with `HexGraphIsoTheory`. CompCert4Lean's backward simulation
transfers the same statement to the x86-64 assembly the Lean compiler emits,
provided the harness makes the inputs and outputs observable (external
calls), because CompCert's theorems are about whole-program traces.

Work items, in rough order of size:

1. **Function specs for the C, refinement to Hex.** This is the bulk.
   nauty's dense core is about 2,700 lines of C (nauty.c 1,256, nautil.c
   750, naugraph.c 732) and sparse adds nausparse.c (1,771). Hex already
   mirrors nauty function by function (the audit's source-coverage table and
   the correspondence table in `HexGraphIso/Nauty/Search/Search.lean`), so
   most specs are "this C function updates memory as Hex's corresponding
   function updates its state". The audit lists where the relation is
   non-trivial: 64-bit MSB-first setwords against 63-bit ascending limbs,
   C's short stamps with reset-before-wraparound against unbounded stamps,
   file-level globals against threaded state, cached cell indices, inclusive
   against exclusive sort cursors, and nauty's recursion (`firstpathnode`,
   `othernode`) against Hex's fuelled mutual recursion. For bit-level pieces
   the cheaper pattern is probably "both meet the same mathematical spec"
   (Hex already proves e.g. `firstFrom_some` for `nextElem`), rather than
   lockstep.
2. **One Clight.** CLean's semantics and CompCert4Lean's are independent
   ports of the same Rocq development with different representations
   (CLean: `BitVec`; CompCert4Lean: a `Word` structure over `Z`). Either
   port CLean's separation logic (about 15k lines, Mathlib-free) onto
   CompCert4Lean's `Clight`, or prove the two semantics equivalent. The first
   is cleaner. CompCert4Lean's theorem starts at CompCert C (`Csyntax`), so a
   Clight-level corollary has to be assembled from its pass lemmas
   (`SimplLocals` onwards), or the logic has to run on its `Clight` produced
   by its own verified `SimplExpr`.
3. **Pin the source to the AST.** The theorem is about the AST, not the
   bytes; the frontend (preprocessor, parser, elaboration to `Csyntax`) is
   CompCert's unverified OCaml in both projects. CLean's examples start each
   proof with an `rfl` check that the AST is what `clightgen` produced; a
   build step can regenerate and compare.
4. **Small semantic assumptions** to state explicitly: volatile reads of
   `nauty_kill_request` return 0; allocation zero-fills (or the upstream
   fix); a bound on `n` so that `int` arithmetic does not wrap (the audit's
   workspace-size and hash overflows set that bound).

Trusted base at the end: Lean's kernel; CompCert's frontend (OCaml);
CompCert's x86-64 assembly semantics, `Asmexpand` and printer; the assembler
and linker; the stated environment assumptions. The binary is the one
CompCert4Lean emits, not gcc's.

Licensing: the semantics files in both ports (Clight, Cop, Csem, Ctypes,
`common/`, `lib/`) are dual LGPL / INRIA non-commercial; CompCert4Lean's
compiler passes are INRIA non-commercial only; CLean ships under CompCert's
LICENSE. Fine for research, but a released Hex library depending on the
compiler theorem would inherit non-commercial terms. A theorem stopping at
Clight needs only the LGPL-able semantics plus CLean's logic, whose licence
should be clarified with Certora.

## Route B: machine code against an ISA model

Theorem shape: for the gcc-compiled RISC-V (or AArch64) image, from a machine
state whose memory encodes `g`, the machine reaches the return address with
memory encoding Hex's result. braid's lowerings are proved sound against the
models, so proofs are done once in braid's separation logic over its
dialect.

Advantages: no C semantics and no compiler in the trusted base; the theorem
is about the gcc output Hex actually benchmarks against; the `firstcode[0]`
issue is not undefined behaviour at the machine level. Costs: proofs are
about optimised machine code (register allocation, inlining, unrolling at
`-O2`), so the refinement relation is harder to state and maintain, and it
must be redone per compiler version and flag set. Gaps found: floating-point
group-size code (`fmul.d`, `fdiv.d`, `fcvt`, a few functions; avoidable by
soft-float or by excluding the group-size output from the theorem); the
`*W` instructions in machine-checked's proved lift; Kraken's parser coverage
on x86-64; no whole-program composition demonstrated by either project yet.

## Recommendation

Start with Route A at the Clight level using CLean as is, on one small
function, to measure cost (done for `nextelement`, see below). In parallel, decide whether to rebase CLean's logic onto
CompCert4Lean's Clight before investing in the bulk of the specs, because
that choice determines which definitions thousands of lines of proofs are
written against. Route B is worth keeping as a later second theorem for the
gcc build; braid's RISC-V coverage makes it plausible, and the refinement
relation from Route A largely carries over.

## First proof: `nextelement`

`/tmp/nauty-verif/lean/NautyC/NextElement.lean` (1,258 lines, no `sorry`,
no `native_decide`, no new axioms) proves a CLean `FunSpec` for nautil.c's
`nextelement`, both the `m == 1` branch and the multi-word loop, against the
exported AST (checked by `rfl`), plus a call-to-return corollary as a raw
`Star Step`. `#print axioms` gives the standard three plus CLean's two
uninterpreted external-call declarations, which enter through `Step`.

- Spec: given `n ≥ 1` readable 64-bit words `ws` (MSB-first vertex
  encoding) and the `leftbit` table, with `-1 ≤ pos < 64n`, the call
  terminates without undefined behaviour and returns the least member
  greater than `pos`, or `-1`; resources handed back unchanged.
- Extra hypotheses the proof surfaced: `64n < 2^31` (C `int` overflow in
  `TIMESWORDSIZE`), and the array must not wrap the address space.
- The `leftbit` global is lent as a heap fragment. Its contents are checked
  against the real program's initial memory by kernel `decide` (about 15 s),
  but CLean has no lemma turning initial memory into owned fragments, so
  that last step is open and is needed for a whole-program theorem.
- Link to Hex (stated, not proved): with `Enc s ws m := ∀ v, InSet ws m v ↔
  s.mem v`, `NextSpec` and Hex's `nextElem` characterise the same unique
  answer, with `-1` for `none`. The shared-spec pattern, not lockstep.
- Cost: about 25 minutes of agent time; roughly 800 function-specific lines
  and 400 reusable lines (a 64-bit array assertion, pointer-plus-`long`
  offsets, `FIRSTBITMAC` proved once for both inlined copies).
- CLean friction: no 64-bit array assertion; `omega` blocked by `CC.Z` until
  goals are restated over `Int`; signed comparison lemmas only for
  non-negative values; no frame inference or forward-stepping automation; a
  `temps_get` tactic bug (its `repeat` leaks into sibling goals; `focus`
  fixes it).
- Extrapolation (the agent's estimate, to be treated as a guess): 25 to 40
  Lean lines per C line on set-manipulation code; nauty.c's search, with
  globals, recursion, function pointers and partition invariants, costs
  more; 100k to 200k lines overall for the C-side proofs, dominated by
  specs and invariants. A forward-stepping tactic would cut the mechanical
  part.

## Environment notes

- Seven toolchains in `~/.elan` (v4.32.0, v4.33.0-rc2, v4.35.0, v4.35.0-rc2,
  v4.35.0-rc3, v4.36.0-rc1, v4.36.0-rc2) had a `bin/ld.lld` wrapper from the
  old NixOS elan that locates `nix-support/ld-wrapper.sh` through
  `/run/current-system/sw/bin/elan`; the current elan has no such directory
  (the system moved to nix-ld on 2026-11-16, and fresh installs are no longer
  wrapped). Fixed 2026-11-27: each wrapper is kept as `bin/ld.lld.nix-wrapper`
  and replaced by the real linker from `bin-unwrapped/`, matching freshly
  installed toolchains. The three v4.34 toolchains still use wrappers that
  point at an old elan store path or a private copy, and work for now.
- Nix hardening's `_FORTIFY_SOURCE` must be off for `ccomp`
  (`NIX_HARDENING_ENABLE=""`).

## Reproducing

- `/tmp/cverif-env/shell.nix`: Coq 8.20.1, OCaml 4.14.4, Menhir, gcc.
- `/tmp/nauty-verif/src`: copies of the vendored nauty files, `harness.c`
  (Petersen), `zalloc.c`.
- `/tmp/nauty-verif/gen/mkharness.py GRAPH.json dense|sparse OUT.c`
  generates a harness; `run-one.sh` runs `ccomp -interp`, `native-one.sh`
  runs gcc.
- `/tmp/nauty-verif/lean`: Lake project with the exported modules;
  `lake build && .lake/build/bin/runCfiDense` (and `runCfiSparse`,
  `runPetersen`). `NautyC/Run.lean` is the runner with the zero-kill-request
  environment; `NautyC/Diag.lean` prints stuck states.
- CompCert4Lean: `PATH=/tmp/fake-opam:$PATH python3 scripts/compile_c.py
  --compcert-root /tmp/CompCert-upstream …` inside the Nix shell, upstream
  CompCert at `7b1f02b0` built in `/tmp/CompCert-upstream`.
- braid: `/tmp/survey-braid/.lake/build/bin/braid-lower
  /tmp/nauty-verif/bin/h-rv --stats --fn …`.
