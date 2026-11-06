# Búri

Búri is an attempt to prove, with machine-checked proofs, that real implementations of the
[Shen](https://shenlanguage.org) programming language run programs the way the language says they
should, all the way down to the machine code that actually executes.

It is not a test suite. Tests show that a program behaved correctly on the inputs someone tried. A proof
shows it behaves correctly on every input, and a proof checker, not a person, decides whether the proof
holds.

## Why now

Anthropic's research post [Formal verification](https://www.anthropic.com/research/formal-verification)
describes using Claude to write proofs about the compiled binaries of real open-source libraries, checked
by the [Rocq](https://rocq-prover.org) proof assistant. Proofs like these used to need a lot of
specialist time, so they were rare for real code. If they can now be written for existing code, it should
be possible to verify a whole programming language implementation, not only individual libraries.

Búri applies that idea to Shen. AI agents write the proofs, Rocq checks every one, and a second independent
checker (`coqchk` or `rocqchk`) replays them. Nothing counts because an AI says it is correct.

## What it aims for

The goal is a checked theorem that says: for every Shen program, running it on a specific, pinned
implementation produces exactly the behavior Shen's semantics allows, or stops with a named resource error
such as running out of memory.

That claim has to hold for the actual bytes that run, not for a simplified model of them. The
[end-to-end plan](docs/END-TO-END-PLAN.md) works towards it in three stages:

1. **Language and port:** Shen through a host language such as Scheme or Common Lisp, under stated
   assumptions about that host.
2. **Hosted process:** the exact executable, including its runtime and garbage collector, under a formal
   model of the operating system.
3. **Closed deployment:** everything the program depends on, down to a declared hardware interface.

Some things can never be proved, and stay as stated trust assumptions even at the end: the logic and proof
checker themselves, whether the specification says what people meant, the model of the processor, and
whether the physical chip matches that model.

Búri also supplies the language-level guarantees that [Vör](https://github.com/pyrex41/vor) needs, since a
proof that a business program meets its contract is only as good as the language it runs on.

## Where it is now

**No Shen implementation is verified yet.** What exists are checked proofs about pieces of three real
implementations, plus a formal model of what Shen means.

| Implementation | Checked so far | Not yet |
|---|---|---|
| Shen-Scheme, on Chez Scheme | Real compiler output for 12 arithmetic forms; one real compiler pass, for the programs it admits | The whole compiler, its primitives, Chez itself |
| Shen-CL, on SBCL | A restricted result about how it compiles boolean tests | Almost everything |
| [Shen/JIT](https://github.com/tizoc/shen-jit) 0.3, a small native JIT | A formal model of its bytecode, compared with the real binary on 732 cases; small pieces of the real RISC-V binary proved in a formal Linux model | The proof from Shen to bytecode is in progress; the code generator, runtime and collector |

**Shen/JIT is now the lead track.** It is far smaller than Chez Scheme or SBCL, which makes a proof about
its exact binary look reachable. Its proofs use the same formal model of a RISC-V Linux process that the
Anthropic work used, from [Theorem](https://github.com/theorem-labs/rocq-linux-process-semantics), and they
cover one specially built static RISC-V binary rather than the releases people download. See
[the Shen/JIT scope](docs/SHEN-JIT.md) and the [feasibility results](spikes/GATE.md), which estimate the
remaining cost and say where it is still unknown.

### The ledgers

As of commit `7b0eaaa` (6 November 2026):

| Ledger | Status |
|---|---|
| [Work packages](spec/end-to-end-plan.json) | 0 of 41 done: 17 in progress, 24 planned |
| [Six-stage plan](spec/six-stages.json) | 0 of 6 done: all partial |
| [Obligations](spec/obligations.json) | 194 total: 18 discharged, 45 partial, 93 open, 18 assumed, 11 refuted, 5 superseded, 4 foundation |
| [Semantics targets](spec/release-charter.json) | 27 total: 7 partial, 20 planned |
| [Release pins](spec/release-charter.json) | 20 total: 11 pinned, 2 identity-only, 7 unpinned |

### The last full check

`make report` passed on 6 November 2026, on the tree committed as `7b0eaaa`, in a Linux x86-64 container.
Reports are unsigned. GitHub Actions jobs now start, but they exceed the workflow's 20-minute limit, so
for current evidence run `make report` yourself.

| Gate | Result |
|---|---|
| Rocq audit | 995 audited theorems, replayed with `coqchk` |
| Proof mutations | 160 deliberately broken variants, all rejected |
| Shen test suites | 1,018 checks across 26 suites |
| Shen-Scheme comparisons | 108 cases (tests, not proof) |
| Orchestration checks | 27 |

### Bugs found upstream

Writing precise semantics turns up real bugs. Nine issues have been filed so far, and upstream has closed
eight as fixed. Búri's pinned sources may predate those fixes.

| Project | Fixed | Open |
|---|---|---|
| Shen-Scheme | [#46](https://github.com/tizoc/shen-scheme/issues/46), [#47](https://github.com/tizoc/shen-scheme/issues/47), [#48](https://github.com/tizoc/shen-scheme/issues/48) | None |
| Shen-CL | [#68](https://github.com/Shen-Language/shen-cl/issues/68), [#69](https://github.com/Shen-Language/shen-cl/issues/69) | [#70](https://github.com/Shen-Language/shen-cl/issues/70) |
| `shen-sources` | [#118](https://github.com/Shen-Language/shen-sources/issues/118) | None |
| Shen/JIT | [#1](https://github.com/tizoc/shen-jit/issues/1), [#12](https://github.com/tizoc/shen-jit/issues/12) | None |

## How it works

- **A precise meaning for Shen.** Shen compiles to a small core language, KLambda. Búri defines what KLambda
  programs mean as an executable semantics in Rocq, with the executable checking and certificate code in
  Shen.
- **Compare against the real thing.** Each implementation's actual compiler output is captured and checked
  against that meaning, instead of trusting a hand-written description of the compiler.
- **Machine-checked proofs.** Rocq checks every proof, an independent checker replays it, and an audit
  lists exactly which assumptions each theorem uses. No new axioms are allowed.
- **Proofs that can fail.** Deliberately broken compilers, captures and models are checked on every run, and
  each must be rejected. A gate that never fails proves nothing.
- **Honest reporting.** Proofs, tests, sampled agreement, open obligations and assumptions are kept
  apart in every report, and nothing is called verified without acceptance evidence.

## The tracks in more detail

The [complete end-to-end plan](docs/END-TO-END-PLAN.md) specifies 41 work packages, from Shen semantics
through each host runtime, exact machine code and deployment software, with dependencies and acceptance
criteria in the [planning ledger](spec/end-to-end-plan.json). These are planned obligations, not
completed proofs.

The [Scheme track](docs/SCHEME-PORT.md) proves preservation for arbitrary admitted binding tails through an
actual captured compiler pass. The [Common Lisp track](docs/CL-PORT.md) starts with source-bound strict
boolean admission and a restricted semantics proof. The [Shen/JIT track](docs/SHEN-JIT.md) has a Rocq model
of its bytecode and the results of six feasibility spikes. The [ARM foundation](docs/ARM-FOUNDATION.md)
has first theorems against the Sail model of Arm's
architecture specification. [Coalton](docs/COALTON-ASSESSMENT.md) is assessed
separately as optional typed tooling.

## What works now

- **Independent Rocq proofs:** generic arithmetic compiler preservation for
  every expression, continuation, and initial stack; no compiled stack faults;
  relational evaluation adequacy/determinism; equational certificate-checker
  soundness conditional on valid rules; lexical evaluator fuel monotonicity
  and determinism; and `let`-to-lambda observational equivalence.
- **Shen proof certificates:** an explicit structural-induction proof of the
  same arithmetic compiler theorem, replayed by a small sorted equational
  kernel. Search/normalization is outside its acceptance path.
- **Equation bridge:** all 18 executable arithmetic equations and both compiler
  theorem statements are exported from Shen and checked against Rocq definitions.
  The exporter/source correspondence remains an explicit trust assumption.
- **Executable KLambda reference fragment:** lexical closures, partial and
  higher-order application, closed recursive definitions, conditionals, exact
  integer operations, pairs, explicit exceptions, and freeze/thaw. Unknown
  resource exhaustion is distinct from a language error.
- **Actual compiler-output validation:** 12 source/output schemas are captured
  from Shen-Scheme's real compiler and proved equivalent by Rocq for every exact
  integer input. A new required raw-data path performs decoding and lexical
  resolution inside Rocq, with round-trip, exact-input, normalization, and full
  record-coverage proofs. Capture provenance and the lower runtime remain trusted.
  See [the capture boundary](docs/CAPTURE.md).
- **Source-linked encoder proof:** the exact loaded Shen file matches a formal
  program with universal termination, unique-output, and decoding round-trip
  proofs. Reader/compiler preservation, primitives, and native execution remain
  explicit obligations. See [the encoder boundary](docs/ENCODER.md).
- **Registered KLambda validation:** all three actual encoder definitions are
  captured from the loaded image and checked against that proved program. A
  generic theorem preserves named bindings, shadowing, and recursive calls.
  See [the front-end boundary](docs/FRONTEND.md).
- **Real Shen-Scheme comparisons:** 108 native cases, including evaluation
  order, lexical capture, lazy branches, currying, exceptions, large integers,
  and freeze/thaw. These are tests, not a preservation proof.
- **Adversarial gates:** Shen checks, Rocq regression examples, orchestration
  checks, and compiler, capture, encoder, and capsule mutations rejected by Rocq.
  Claim reports keep proofs, ground replay, tests, open obligations, and
  assumptions distinct.

Read [STATUS](docs/STATUS.md) and [TRUST](docs/TRUST.md) before interpreting any
result. A theorem about the arithmetic reference compiler does not verify the
Shen-Scheme compiler. A proved Rocq checker is not yet a proof of the Shen
checker's implementation.

## Run

On Linux x86_64 (tested with Ubuntu 24.04-compatible libraries):

```sh
make bootstrap
make check
make report
make demo
```

Bootstrap verifies pinned SHA-256 downloads and installs entirely under `.tools/`.
It uses Shen-Scheme v0.52, Shen 43.1, the exact PR #117 typechecker overlay, and
Coq 8.18.0 (the pre-rename Rocq release). No sudo is needed. The Rocq launcher
also supports an already installed `coqc`/`coqchk`; use version 8.18.0 for this
release. Shen bootstrap also supports macOS arm64, but that combination has not
been tested here. See [toolchain provenance](toolchain.lock.json).

`make test` runs the Shen tests. `make prove` regenerates the equation bridge,
checks all proofs, audits theorem dependencies for custom axioms, independently
replays compiled proof objects with `coqchk`, and rejects broken variants.
`make conformance` executes the Shen-Scheme comparison corpus.

`make check-shen-jit` runs the opt-in Shen/JIT lane: its Rocq 9 proofs and the comparison with the named
binary. It needs the Rocq 9 and `qemu-riscv64` container set up by `spikes/jit-in-model/setup.sh`, and the
binary built by `ports/shen-jit/build.sh`; its paths still assume that container.

`make report` reruns every gate and emits `_build/report.json`, exact source and
host hashes, theorem signatures, assumption inventories, and logs. This is an
unsigned evidence report, not a verified-port badge.

## The first compiler theorem

For every finite natural-number expression `e`, continuation `k`, and stack `s`:

```text
run(compile(e, k), s) = run(k, cons(eval(e), s))
```

The expression language has literals, addition, and multiplication. Naturals
are structural Peano values, so the theorem does not silently assume machine
integer overflow behavior. The arbitrary continuation includes code that can
fault: the theorem preserves its modeled outcome as well.

The [Shen certificate](proofs/compiler.shen) contains every case and rewrite.
The [Rocq proof](rocq/Arithmetic.v) is independently checked by an established
kernel. [The exact scope](docs/SEMANTICS.md) explains why this is a useful initial
preservation proof and not a claim about arbitrary Shen programs.

## Project map

| Path | Role |
|---|---|
| `spec/arithmetic.shen` | Closed sorted signature and executable defining equations |
| `shen/kernel.shen` | Shen equality/instantiation/structural-induction checker |
| `shen/equations.shen` | Term validation and reference normalization |
| `shen/klambda.shen` | Broader inert KLambda-like reference interpreter |
| `rocq/` | Independent semantic definitions, proofs, and assumption audit |
| `shen/export-rocq.shen` | Checked-equation bridge generator; currently trusted correspondence |
| `rocq/Wire.v`, `Resolve.v`, `Normalize.v`, `NativeValidation.v` | Checked raw-data validation and lexical/arithmetic preservation |
| `shen/wire.shen`, `rocq/Encoder.v`, `EncoderSource.v` | Source-linked encoder program, semantics, and correctness proof |
| `rocq/EncoderNames.v`, `EncoderFrontend.v`, `EncoderKLambda.v` | Named execution preservation and validation of registered KLambda |
| `shen/export-wire.shen` | Raw capture of the real compiler input/output |
| `ports/shen-scheme.shen` | Native test adapter; intentionally executes trusted fixtures |
| `tests/` | Hostile proofs, reference regressions, native conformance |
| `PLAN.md` | Dependency-ordered route to actual port preservation |

## Why Rocq alongside Shen

Shen remains the executable domain and port interface. Rocq gives the foundational
proofs an independent checker. That avoids relying solely on the very port being
investigated. Lean would also be viable; this repository chooses one external
foundation to keep the correspondence obligations tractable. See the
[decision record](docs/PROOF-FOUNDATION.md).

The [trust audit](docs/TRUST-AUDIT.md) records the remaining obligations, proven
typed transport protocol, reachable byte domain, and concrete counterexamples
to unrestricted native halving and metadata/executable identity.

The [observed compilation lane](docs/OBSERVED.md) now validates the three paired
KLambda/Scheme definitions captured during actual installation by a controlled
loader. It proves administrative binding preservation and canonical target
execution under the explicit primitive and runtime assumptions.

The [sealed encoder](docs/SEALED.md) runs the checked target bodies with seven
private helper procedures and a restricted Chez import environment. Its exact
capture is checked for lexical dependency closure and target linkage. It avoids
the legacy identity guard's rebinding race. Chez implementation refinement
remains an explicit obligation.

[Native execution proofs](docs/NATIVE.md) now cover the captured constructor,
exact shim bodies and an instruction-level lexical machine under arbitrary
ambient rebinding. The remaining native boundary is explicit: Chez/library
implementation and representation contracts, not an assumed correct shim.

The exact sealed encoder now has universal codec refinement in Rocq: all finite
supported datums terminate in the instruction model with canonical bytes and
roundtrip decoding. The captured pure Shen tagging functions have execution
proofs too. Independent source parsing and exact compiler-record identity bind
the codec artifacts together. See [CODEC-CORRESPONDENCE](docs/CODEC-CORRESPONDENCE.md)
for the admitted domains and remaining native provenance boundary.

[OBSERVER-PROVENANCE](docs/OBSERVER-PROVENANCE.md) adds the boolean-aware bootstrap
body proof, captured installer effect-order and failure proofs, checked source
snapshot data-flow, and a generic preservation step for the pinned upstream
`merge-nested-lets` compiler pass. Native effect/IO contracts and the rest of the
Shen compiler remain explicit obligations. The native syntax decoder also fixes
Scheme `and` to preserve its final operand value.

[CHECKED-IO](docs/CHECKED-IO.md) fixes a concrete observer assumption: Shen's
`write-to-file` can silently suppress text under `*hush*`. Controlled observers
now read each output back and reject mismatches. The captured wrapper's success
postcondition is proved against a truthful-read contract. Compiler preservation
also now covers arbitrary binding lists, including effects and shadowing, under
explicit syntax-admission premises.

[Implementation correctness ledger](docs/CORRECTNESS.md) records the exact
numeric-wrapper, fresh-name, call-ordering, three-definition loader and read
adapter proofs, their domains, and the remaining path to full preservation.

[Six-stage progress](docs/SIX-STAGES.md) now includes two-way pure instruction
refinement, general effect-preserving let insertion, changing-generator freshness,
all loader failure positions, and an executable private axiom-free congruence
kernel with checked raw admission and native rebinding regressions. The full
six-stage goal remains open; its scoped evidence ledger is machine checked.
