# Búri

Formal semantics and machine-checked implementation correctness for Shen.

Búri defines what a supported Shen/KLambda fragment means, checks proof
certificates, and compares real ports against that meaning. **The current
release has checked proofs about reference models; no Shen port is yet verified.**

Vör asks whether a business program satisfies its contract. Búri supplies the
language/runtime semantics and preservation obligations that such a claim
ultimately depends on.

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
- **Real Shen-Scheme comparisons:** 105 native cases, including evaluation
  order, lexical capture, lazy branches, currying, exceptions, large integers,
  and freeze/thaw. These are tests, not a preservation proof.
- **Adversarial gates:** 105 Shen kernel/evaluator/encoder/adapter checks, 51 Rocq adversarial examples,
  fourteen orchestration checks, and fifty-two compiler, capture, encoder, or capsule mutations rejected by Rocq. Claim reports keep proofs, ground replay,
  tests, open obligations, and assumptions distinct.

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
checks all proofs, audits 247 theorem dependencies for custom axioms, independently
replays compiled proof objects with `coqchk`, and rejects broken variants.
`make conformance` executes the Shen-Scheme comparison corpus.

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
