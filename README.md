# nauty-verified

A machine-checked proof, in Lean, that nauty's C code computes what
[HexGraphIso](https://github.com/leanprover/hex-graph-iso) computes, so that
HexGraphIso's correctness theorems (canonical form is a complete isomorphism
invariant; the emitted generators generate the automorphism group; orbits are
correct) hold of nauty itself and of the x86-64 program compiled from it.

**Status: Phases 1 and 2 done.** The C sources are Lean terms, linked into
one program whose Clight form is pinned by kernel-checked equations against
CompCert4Lean's own passes; the binary built from it reproduces every
fixture. A program logic over CompCert4Lean's Clight semantics is in place,
and the first nauty function, `nextelement`, is proved against HexGraphIso's
`VSet.nextElem`. The
plan is [docs/PLAN.md](docs/PLAN.md); the experiments that motivated it are in
[docs/feasibility-2026-11.md](docs/feasibility-2026-11.md).

## What is verified, and against what

- The C: the unmodified nauty 2.9.3 sources in `c/nauty-2.9.3/`
  (checksums in `SHA256SUMS`), built with the flags in `c/flags.sh`, with the
  harness in `c/harness/`.
- The semantics: CompCert's C semantics as ported to Lean by CompCert4Lean
  (fork: [kim-em/compcert4lean](https://github.com/kim-em/compcert4lean)).
- The compiler: CompCert4Lean's verified compiler core, whose correctness
  theorem carries the result to its x86-64 assembly.
- The reference: `Hex.GraphIso` in HexGraphIso v0.10.0.

Trusted, outside the proofs: Lean's kernel; CompCert's C frontend
(preprocessor, parser, elaboration); CompCert4Lean's x86-64 assembly semantics,
assembly expansion and printer; the assembler and linker; the identifier
renaming and C linking that combine the translation units into one program
(`NautyVerified/Source/Link.lean`), as a model of what the system linker does;
`io_stdio.c`; and
CompCert's memory model, in which allocation never fails and the stack is
unbounded.

nauty reads `firstcode[0]` without writing it (nauty.c:884), which CompCert's
semantics treats as undefined behaviour. All allocations therefore go through
the zero-filling `c/harness/zalloc.c`; nauty's sources are not modified.

## Layout

| Path | Contents |
| --- | --- |
| `c/nauty-2.9.3/` | pinned nauty sources |
| `c/harness/` | `dense_main.c` (the verified program's `main`), `zalloc.c`, `nv_io.h`; `io_stdio.c` for native runs only |
| `c/flags.sh` | the one build configuration |
| `c/csyntax/` | the CompCert frontend's output for each unit (generated, committed) |
| `NautyVerified/Source/` | the units as Lean terms, their linking, and the pinned Clight |
| `NautyVerified/Build/` | `nvCompile`, which compiles the linked program |
| `tests/fixtures/` | graphs (`.json`) and recorded harness output (`.out`) |
| `scripts/` | native test runner, fixture generators, trust check |

## Building and testing

```sh
lake build                    # Lean development
scripts/run_native.sh         # native harness against tests/fixtures
scripts/check_trust.sh        # no axiom, no native_decide, sorry only where listed
```

Regenerating `c/csyntax/` and building the verified binary need a prepared
CompCert checkout and OCaml, as for CompCert4Lean's `scripts/compile_c.py`:

```sh
scripts/export_csyntax.sh COMPCERT4LEAN_CHECKOUT COMPCERT_CHECKOUT
scripts/build_binary.sh COMPCERT4LEAN_CHECKOUT COMPCERT_CHECKOUT OUT_DIR --check
```

## Licence

Original work is Apache 2.0. The end-to-end theorems depend on
CompCert4Lean's compiler passes, which are under the INRIA Non-Commercial
License Agreement; see [NOTICE](NOTICE).
