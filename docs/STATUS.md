# Current evidence boundary

This status describes the committed source, not a prediction of future work.
Run `make report` for evidence from your own image and toolchain.

| Claim | Evidence now | Important limit |
|---|---|---|
| Arithmetic compiler continuation preservation | Generic Rocq theorem and Shen induction certificate | Small reference compiler, not a Shen port |
| Compiled arithmetic cannot underflow at Halt | Rocq corollary for all expressions/stacks | No OS memory/stack/resource claim |
| Arithmetic relational semantics agrees with evaluator | Rocq soundness, completeness, determinism | Formal model only |
| Equational certificate checking preserves valid equations | Rocq theorem conditional on the supplied rules being valid | Not yet an implementation proof for `shen/kernel.shen` |
| Lexical evaluator results survive increased fuel | Rocq universal fuel monotonicity theorem | Narrow formal fragment; no termination theorem for arbitrary programs |
| Lexical terminating outcomes are unique | Rocq theorem across all fuel witnesses | Divergence and liveness remain separate |
| Let lowering to lambda application preserves outcomes | Rocq equivalence theorem | Formal pure lexical fragment |
| Shen arithmetic equations match Rocq equations | 18 generated universally quantified equality lemmas | Exporter and source correspondence are trusted |
| Exported compiler goals match proved goals | Two generated Rocq theorem applications | No proof of certificate serialization/exporter implementation |
| Actual Shen-Scheme compiler output preserves 12 arithmetic schemas | Raw-data validation in Rocq, with name-resolution and normalization preservation for every integer environment | Capture provenance and Scheme primitive/runtime semantics remain trusted; not universal compiler correctness |
| Canonical captured-data transport | Generic codec round-trip, exact decoding, and injectivity proofs | Native primitive and execution correspondence remains open |
| Exact Shen encoder source matches a correct program | Source equality plus generic termination, unique-output, and decoder round-trip proofs | Admitted first-order semantics; native reader/compiler, primitive, and representation preservation remain open |
| Registered KLambda for all three encoder functions preserves the proved program | Complete capture validation plus generic named-execution preservation, including recursion and shadowing | Source metadata/capture provenance and tagging, primitive contracts, and backend/runtime remain trusted; not a full compiler proof |
| Typed tagging protocol recovers the exact syntax tree | Generic Rocq roundtrip, injectivity, wire composition and exact-root validation | Captured pure tagging targets now proved; host execution, bootstrap tagging and IO remain trusted |
| Byte recursion stays in its finite character domain | Generic call-bound theorem plus exhaustive native checks of 256 codes × 9 counts | Unrestricted native halving has a concrete counterexample; sealed target now universally refined in the model; stock native counterexample remains |
| Every supplied capture record is checked in order | Generic record-coverage theorem and an exact 12-record release check | Cannot establish the provenance of the supplied data |
| Native Shen-Scheme agrees on selected cases | 105 actual execution comparisons | Sampled evidence only |
| Kernel/evaluator reject regressions and malformed evidence | 45 kernel, 36 evaluator, and 16 encoder and 8 capture-adapter checks | Tests do not establish checker soundness |
| Wrong compiler instructions and false equations rejected | Fifty-seven Rocq mutation cases, including eight altered native constructors | Tests of the gates, not a completeness claim |
| Full Shen-Scheme or any other port correct | OPEN | No verified-port claim |

The audit enumerates 347 theorems/corollaries/bridge goals and prints their exact
signatures and assumptions. It requires no custom axioms and independently
rechecks their compiled proof objects. The rule-validity premise of
`check_sound_under_rules` is an explicit theorem hypothesis, not a discharged
claim about arbitrary imported equations.

`buri.obligations` is a static inventory. `proof-available` means an artifact
exists; it is not acceptance of the current checkout. Only a fresh successful
gate run produces `_build/report.json`. Reports are unsigned and retain exact
source hashes, toolchain identity, theorem log, and remaining assumptions.

The native validation lane has 78 additional Rocq regression examples and eighteen
orchestration checks. The raw input string, decoded records, names, and arithmetic
normalization are covered by the new formal path described in [CAPTURE](CAPTURE.md).
[ENCODER](ENCODER.md) describes the source-linked program proof. The broader Shen
evaluator, Shen proof checker, and native execution of the encoder still require
implementation-correspondence proofs.

[FRONTEND](FRONTEND.md) specifies the registered-KLambda validation boundary.

[TRUST-AUDIT](TRUST-AUDIT.md) records every remaining trust obligation, the
large-integer halving and mutable-metadata counterexamples, and 260 native trust
regressions. The tagged protocol is proved; its Shen implementation is not.

[OBSERVED](OBSERVED.md) describes the new controlled load path: actual frontend
KLambda and actual backend Scheme are captured as the Scheme is installed.
All three pairs are validated, with generic administrative-let preservation and
proved successful source-to-target execution, encoder termination and unique
output in the admitted semantics. The observer, reader, primitives and Chez
remain trusted. This adds 12 native observer checks; it does not certify the
stock loader or a binary, or enforce immutable runtime bindings.

[BINDINGS](BINDINGS.md) documents the single-read source snapshot, explicit
runtime dependency inventory, and live procedure-identity guard. Eight native
checks exercise actual helper rebinding and fail-closed execution. Three new
abstract version-vector theorems are independently checked; native guard
refinement, full transitive closure and concurrent rebinding protection remain
open.

[SEALED](SEALED.md) adds a separate immutable execution lane: three checked target
bodies plus seven private helper lambdas, with complete syntactic dependency
coverage up to 27 named Chez primitives. Eight additional audited proof goals
cover closure, exact target linkage, dependency-resolution noninterference and
the exact capture. There are 271 sealed native checks, including a synchronized
concurrent global-rebinding regression. This lane does not use the legacy
identity guard. Captured constructor/shim execution is now proved in the model
below; Chez/library implementation, primitive internals and concurrent input-data
mutation are not proved.

[NATIVE](NATIVE.md) replaces the remaining constructor/shim assumptions with
code-linked execution proofs in an explicit pure Scheme model. The new observer
captures all ten generated constructor definitions, with typed booleans. Twelve
proof goals check exact decoding, all constructor components, assembly for
arbitrary supplied target bodies, failure cases and the authority/entry shapes.
The exact seven helper bodies are interpreted and proved, including all-natural
exact halving and specified boolean errors. An instruction machine proves that
arbitrary ambient rebinding steps cannot change a completed private result;
this is instantiated on the exact decoded capsule. There are 55 new audited
goals, 12 additional semantic regression examples, 19 new native checks, and
eight new rejected constructor mutations.

The new exact-rational sealed division avoids the pinned host's inexact-halving
counterexample. Unused `eq?` and `inexact` imports are removed. The stock lane is
unchanged. Chez implementation refinement, the 27 primitive/representation
contracts, observer/compiler
provenance, and concurrent input-object mutation remain open. The legacy
identity guard is still unverified and is not used by the sealed lane.

## Evaluator-to-instruction refinement

`NativeSimulation.v` now proves, for every private program, environment and
expression, that a non-exhausted functional evaluation has a finite instruction
execution with exactly the same result. This includes returned values, exact
raised owner/message payloads and unsupported operations. Recursive calls,
left-to-right argument evaluation and short-circuiting are covered universally.
The instruction budget is existential; it is not the evaluator's nesting fuel.
Any completed instruction execution interleaved with ambient rebindings must
have that same result, including failures. This assumes the modeled separation
of private cells and ambient state.

`NativeApplications.v` transfers the actual captured constructor's arbitrary
three-target assembly and arbitrary-program authority-request proofs to the
machine, plus both specified malformed-input errors. Sixteen additional audited
goals cover this bridge and its applications. These are model refinement proofs,
not additional native test cases or a Chez correctness claim. Both engines now
share an explicit external primitive/error dispatch definition; its mathematical
contracts are unchanged.

The next section closes universal codec refinement and the pure captured tagging
functions within the model. General source/reader/compiler correctness, observer
provenance, the broader Shen evaluator and proof checker remain open. That increment supplied only forward refinement; the later six-stage work below
adds reverse result and divergence correspondence for the existing pure core. Chez compiler/runtime verification
and primitive implementation internals are deferred at the user's direction.

## Universal codec and artifact correspondence

[CODEC-CORRESPONDENCE](CODEC-CORRESPONDENCE.md) records 23 additional audited
proof goals. The exact decoded sealed encoder now terminates for all finite
supported datums and returns precisely `Wire.capture`, with decoder roundtrip
and concurrent-output correctness. Byte encoding covers every natural input and
count; strings cover every byte string; integer datums cover all Rocq integers.
These proofs use the actual captured target bodies and their private helpers.

The captured Shen `buri.kl-bytes` and `buri.kl-node` functions now implement the
typed protocol in the fixed helper model, for all finite syntax nodes. Composition
with the sealed codec recovers the original admitted syntax tree. The protocol's
existing numeral bound of 256 applies to that decoding theorem, not to the
encoder's integer domain. Four new source-reader regression examples, twelve
native adapter checks, four rejected adapter mutations and a packaging/stale-data
gate supplement these proofs.

The exact source parses independently into the expected three bodies. Observed
KLambda/Scheme pairs and sealed records are checked equal, and successful source
model evaluations agree with the instruction result for every supported datum
and source fuel. This is translation validation of this encoder artifact chain,
not a universal compiler theorem. Native observer/reader/IO truthfulness, the
boolean-aware bootstrap capture adapter and host activation remain unverified.
The pure tagging proof fixes its helper table; it does not freeze the current
global exporter in a running Shen process. Chez internals remain deferred.

## Bootstrap, captured observer effects, and upstream compiler pass

[OBSERVER-PROVENANCE](OBSERVER-PROVENANCE.md) adds 26 audited goals. The actual
boolean-aware `buri.native-bytes`/`buri.native-node` targets now have universal
model execution proofs and typed decoding roundtrip for the admitted numeral
profile. Booleans remain distinct from symbols. This closes their pure target
algorithm obligation, not the truthfulness of the self-capture process.

The captured `buri.install-observed` body is now executed in explicit state/effect
semantics. For arbitrary valid definition names/arguments/bodies and arbitrary
successful compiler/activation responses, the exact compiled target is activated
before the source/target record is read and prepended. A failed compiler or
activation response preserves prior records and makes no publication. Other
side effects, including stored arity, are not rolled back. These are conditional
execution proofs against specified external operations, not verification of
native host effects or a refinement theorem for the entire observer.

The captured entry is checked structurally for one source-read token, one parse
token, and the same lexical source variable flowing to parsing and snapshot
writing. This is an IO-plan check, not a proof that file IO is truthful.

The pinned upstream Shen compiler source is vendored with its exact Git blob
identity and license. The extracted, package-qualified `merge-nested-lets` pass
is recompiled/captured. Both transformation cases preserve arbitrary supplied
bindings/bodies. For the two-binding case with admitted subexpression decoding,
all pure evaluator outcomes and modeled state/effect traces are unchanged.
General compiler correctness remains open beyond this pass and profile.

This work exposed and fixed a model decoder defect: Scheme `and` returns its
last operand, so `(and 1 2)` returns `2`, not true. Three new Rocq regressions
cover empty, single and multiple operands; existing boolean-only proofs are
rechecked. There are 25 additional native checks, five new rejected mutations,
and three new literal/stale packaging checks.

## Checked writes and full binding-list preservation

[CHECKED-IO](CHECKED-IO.md) adds sixteen audited goals and fixes a native
counterexample: `write-to-file` returns its requested text under `*hush*` while
writing an empty file. Controlled encoder/constructor observers now use
`buri.checked-write` for all outputs. It writes, reads back and raises an error
on mismatch. Thirteen native IO cases include this counterexample, mismatch
rejection, observer rejection, empty-file correctness and recovery.

`CheckedFileIO.v` proves the actual captured wrapper against an arbitrary writer
which may lie, corrupt the file world, partially mutate it or fail. A successful
return implies that the requested path looks up to the requested text in the
final modeled world. Corruption is rejected; writer failures do not read back.
This removes the assumption that the writer's success return proves persistence.
It retains truthful reads, correct native equality/execution and stable context
as explicit contracts. It does not prove atomicity, durability, cleanup or future
immunity from concurrent file mutation.

`ObserverIO.v` additionally checks the source variable is bound once and all
three entry writes call the checked wrapper. `ObserverEffects.eval_with` now
allows a supplied effect handler while preserving the existing installer proofs.
The captures were regenerated; changed generated names are validated again.

`CompilerBindings.v` closes the previously open many-binding preservation case
of the source-pinned `merge-nested-lets` pass. Arbitrary-length lists, empty lists
and repeated binding names retain their decoded expression, every pure outcome
and every modeled effect trace. Stable subexpression decoding is an explicit
admission relation, with literal/variable/conditional/let construction lemmas.
A theorem links actual captured pass execution to that preservation result.
Other compiler passes and general Shen frontend/backend correctness remain open.

Two new tampering fixtures must fail proof compilation: bypassing comparison or
replacing the read-back call. Literal-package checks include the checked wrapper.
Underlying native reads, activation, observer concurrency and Chez internals are
not relabelled as verified by these new component proofs.

## Source-linked numeric, ordering, loader, and read-wrapper proofs

[CORRECTNESS](CORRECTNESS.md) defines the full correctness target and the
remaining six-part implementation sequence. Thirty-five additional audited
claims bring the inventory to 282. New source pins include the actual primitive
and override files, not ideal replacements.

`StockDivision.v` proves the parsed upstream division wrapper's branch behavior
for the admitted exact inputs and arbitrary rounding results. The existing
private exact helper now has signed floor-division correctness for all integer
numerators and positive denominators. Stock precision loss remains a failure of
the encoder's exact-halving requirement; whether it violates Shen's allowed
numeric semantics is not established. Negative denominators remain outside the
formal ratio profile, despite passing native numeric tests.

`OrderCallCorrect.v` proves captured fresh-name acceptance, collision exhaustion,
success implies absence, and preservation of existing symbol bindings under its
specified occurrence and constant-generator contracts. It also checks an actual
captured two-computation transformation and proves generic two-nullary-call
preservation for arbitrary modeled effects/errors, with adjusted evaluator fuel.
This is not preservation for arbitrary call inputs or higher-order operators.

`ObserverPipeline.v` executes the captured three-form loader and installer
together: arbitrary valid frontend results compile, activate and publish in
order. First/second frontend failures and third backend failure retain exact
completed prefixes; no rollback is claimed. The complete observer entry and
native compiler/activation correspondence remain open.

`IOReadCorrect.v` proves that the actual captured Shen read override constructs
the home-directory prefix and forwards the exact native read outcome/state/trace.
The remaining foundation is the Chez reader, stable home lookup, and native
execution correspondence. The theorem does not establish IO truthfulness by
assuming that the entire Shen wrapper was truthful.

Thirty-nine new native assertions bring native checks to 868 across fifteen
suites. Five additional rejected mutations bring the total to 57. Eighteen
orchestration regressions check literal/stale/error handling. All native samples,
ground captured transformations and universal formal statements remain distinct.
Full Shen/port correctness is still OPEN; Chez internals remain deferred.


## Six-stage refinement and a private congruence kernel

[SIX-STAGES](SIX-STAGES.md) records 65 additional audited goals (347 total).
The first-order effect evaluator now has completed-result fuel monotonicity,
environment congruence and fresh-binding preservation. Fresh administrative let
insertion handles arbitrary operands/argument tails and every modeled completed
outcome, state and trace, in both directions. Stateful noncompletion includes
external exhaustion and is not relabelled divergence.

The pure evaluator is exactly the empty-trace specialization. Reverse instruction
refinement now covers every non-exhausted result, including errors/unsupported,
and pure-model divergence correspondence holds in both directions. This closes
the old formal-core reverse gap, not native Chez execution correspondence.

The captured fresh-name loop supports changing/erroring stateful generators and
finite-supply progress under explicit symbol/count contracts. The actual
three-form observer loader has one complete outcome summary covering all nine
failure positions. Native division wrapper behavior is proved for arbitrary
input values and named primitive responses, with signed denominator normalization;
underlying primitive/representation contracts remain explicit.

The new executable Shen axiom-free congruence deriver agrees universally with the
Rocq checker on typed certificates. Rejecting raw admission is canonical, complete
for its declared profile, and semantically sound. It does not admit artifact rules,
verify the original EQ-1 induction kernel, or establish arbitrary business logic.
A separate captured constructor assembles exactly that private table with one
private equality helper. Exact activation wiring, seventeen imports, raw Scheme
identifier closure, scoped authority and model rebinding soundness are checked.
The producer builds/activates from the same literal-checked core records.

Native regressions exercise the private capsule under sequential and synchronized
hostile rebinding, without native eval of certificate payloads. There are 914
native checks across seventeen suites, 96 additional Rocq regression examples,
71 rejected mutations and twenty-two orchestration regressions. Native capture,
construction-context stability, primitive/representation and Chez contracts are
not silently discharged. Full observer entry, general KLambda/compiler preservation
and the remaining six-stage acceptance conditions stay open in
`spec/six-stages.json`; all six stages are explicitly partial.

The report collector captures child output through a pipe and writes the complete
log only after child exit. Regressions cover replaced/truncated logs on success
and failure; missing markers and failed child status still prevent a report.

## Parallel Shen-Scheme and Shen-CL work

The shared semantic obligations now have two implementation tracks. See
[SCHEME-PORT](SCHEME-PORT.md), [CL-PORT](CL-PORT.md), and the optional
[Coalton assessment](COALTON-ASSESSMENT.md).

`SchemePortMerge.v` extends the actual captured Scheme merge pass to arbitrary
successfully decoded sequential binding tails. It proves that the captured pass
produces a target with the same decoded expression, preserving all modeled
outcomes, state and traces. It introduces no new primitive oracle or custom axiom.
Decoding depth and admissibility remain explicit premises.

`CLPortGuard.v` defines a deliberately restricted CL AST semantics and proves
strict boolean behavior for every modeled input of the exactly admitted guard
body. `CLPortCapture.v` checks the captured body against that syntax. Conditional
continuations preserve their modeled observations; the actual Shen-CL compiler's
IF lowering is not yet proved. Object identity, formatting/error behavior and
SBCL execution remain contracts. The inert Shen adapter is executable and tested,
but its correspondence with the Rocq admission checker is not proved.

The native `make check-cl-port` gate separately regenerates the capture from
Shen-CL revision `4844072dde0208c3e4b99dcbfea58e4fdfd812e8`, compares both Rocq
and Shen data, exercises SBCL, and rejects three altered guard captures. This
requires a separate pinned checkout and SBCL; the default proof gate checks the
stored inert capture and does not claim fresh CL source regeneration.

Ten additional statements join the assumption audit (357 total). Native tests,
source capture and universal model proofs remain separate evidence. Neither port
is fully verified, and Chez, SBCL, runtime and ARM execution refinement remain
open. Coalton adds no theorem and is not used in the acceptance path.

## Wave A: shared KLambda semantics and observations (E2E-04, 05, 06 in progress)

[KLAMBDA-SEMANTICS](KLAMBDA-SEMANTICS.md) and [VALUE-MODEL](VALUE-MODEL.md)
describe nine new Rocq modules. `Observation.v` defines the common observation
vocabulary (IO request/response events including partial and failed reads and
writes, signals and cancellation, outcomes with structured errors and modeled
resource failure, coinductive divergence and reaction, and evaluator verdicts
as a separate type). Its refinement relations provably cannot hide errors,
failed writes or silent loops. `KLSyntax.v`/`KLValue.v`/`KLSemantics.v` give a
small-step semantics with heap, global value/function namespaces and explicit
continuations for all 10 canonical special forms and all 36 primitives; each
primitive has a named rule, and inexact arithmetic, printing and system error
text are explicit profile slots quantified over by every theorem.
`KLMetatheory.v`, `KLWellFormed.v` and `KLTail.v` prove progress, the exact
stuck states, determinism (with a functional environment oracle), well-formed
state preservation, a fuel evaluator that is sound, monotone and complete for
terminating behaviors, that divergence exhausts every fuel bound while
exhaustion does not imply divergence, and bounded-continuation divergence of
tail-recursive loops. `KLBridge.v` embeds the `Lambda.v` lexical fragment.

Forty additional statements join the assumption audit (397 total), including
three ground derivations from `KLExamples.v`. These are theorems about the
formal semantics only: `shen/klambda.shen` is not yet related to it (E2E-07),
no port is related to it, inexact numerics are unpinned, and native probes
recorded in VALUE-MODEL.md (including a Shen-Scheme `cond` fall-through that
returns a host void value) are sampled observations, not proofs.

## Release charter and obligation ledger (E2E-01/02, seeding E2E-35)

[RELEASE-CHARTER](RELEASE-CHARTER.md) adds a versioned charter
(`spec/release-charter.json`, v1), an obligation graph (`spec/obligations.json`),
and a Shen coverage checker (`shen/ledger.shen`). Both data files are planning
and bookkeeping data, not proof evidence. The charter records the existing pins
(PR117 overlay hash, Shen-Scheme v0.52 archives and source, Shen-CL `4844072d`
capture source, Coq 8.18). It also marks what is **not** pinned: SBCL, the Chez
version inside the host archive (identity only), the kernel source tree, the
ARM architecture/ABI/CPU features, the OS profile, a Linux AArch64 host archive
and compiler modes. It names 74 required features (16 provisional exclusions
with registered enforcement tests) and seven separately defined property kinds,
each with a semantics target and an owning package.

The graph harvests TRUST, TRUST-AUDIT, SIX-STAGES, STATUS and the port documents
into 97 obligations. The status counts are 8 discharged, 24 partial, 46 open,
13 assumed, 2 refuted and 4 foundation. Each obligation has one of four kinds:
model proof, implementation correspondence, artifact correspondence or
deployment identity. Every discharged obligation is a dependency-free model
proof. No implementation, artifact or deployment obligation is discharged.
Two genuine cycles (heap/GC and checker bootstrap) are tagged joint invariants
and can never be counted as discharged. The older `buri.obligations` inventory
maps entry-by-entry into the graph, and superseded or refuted statements are
retained as history.

The checker reads ledger bytes through an inert JSON reader. It enforces:

- owner and dependency coverage;
- an acyclic package plan;
- justified obligation cycles;
- evidence-kind rules: sampled, exhaustive-host and ground evidence cannot
  discharge universal obligations, and cited theorems must be in the
  `rocq/Audit.v` inventory;
- closure over open premises;
- honest package completion;
- a frozen required-feature fingerprint, so features cannot be silently dropped.

`tests/ledger.shen` adds 56 regressions to `make test`: 7 exclusion-enforcement
tests, 6 inert-reader cases, and real-ledger and hostile variants. These are
bookkeeping checks. They add no theorem and leave the 357-statement audit
unchanged. The checker itself is unproved, and theorem-to-obligation fit is
checked by name only. E2E-01, E2E-02 and E2E-35 are in progress, not complete.

## ARM foundation research gate (E2E-20, first experiment)

[ARM-FOUNDATION](ARM-FOUNDATION.md) records the first ARM experiment. It adds
no Rocq module or theorem, so the proven boundary and the audited statement
count (357 total) are unchanged. `(define buri-arm-add X Y -> (+ X Y))` was
compiled through each port's real generated code: Shen-Scheme v0.52's form on
Chez 10.3.0 tarm64le (the shen-scheme pin, cross-built here), and Shen-CL
`4844072d` on aarch64 SBCL 2.6.8. Its exact machine-code bytes are stored in
`ports/arm/` and were executed under qemu-aarch64; those runs are emulated
samples, not model evidence. isla traced the exact opcode bytes against the
Sail Armv9.4-A model. That is unchecked symbolic execution, trusting isla, z3
and the Sail-to-IR step, so it is not a Rocq theorem. The sail-arm v9.4 Coq
model elaborates under a separate Coq 8.18.0 with stdpp 1.10.0 and
coq-sail-stdpp 0.19 (24 min, 6.4 GB). The first decode lemma is not yet
proved, because the Sail decoder is monadic over the `SEE` register. Islaris
was not built: it
requires Coq 8.19.0 and lithium dev pins, and its package sources were
unreachable. The runtime calls are inventoried: Chez library `+`, `event` and
`doargerr`; SBCL `TWO-ARG-+`, `%DOUBLE-FLOAT`, `ALLOC-TRAMP` and the `brk`
traps. Incompatibilities are listed there. Package 20 remains in progress: no
instruction is yet checked against the ISA model in Rocq.

## Pinned and reproducible build (E2E-03, in progress)

See [BUILD](BUILD.md). `flake.nix` pins nixpkgs (nixos-24.11 revision
`50ab793786d9de88ee30ec4e4c24fb4236fc2674`, narHash in `flake.lock`), the
Shen-Scheme v0.52 release archive, the PR 117 overlay and the six Coq/OCaml
Ubuntu snapshot debs. Each is pinned by the same sha256 as `scripts/bootstrap`
or `rocq-packages.lock`. `nix build .#gates` runs `make test` and `make prove`
in the Nix sandbox with no network. `make manifest` and `make manifest-compare`
record and compare build identity: sources, tool payloads, the loaded runtime
libraries, commands, flags, environment, and `.vo`/`.glob`/capture outputs.

A host bootstrap build and a sandboxed Nix build of the same commit produced
byte-identical `.vo` files (228), `.glob` files, generated proof inputs,
captures and Rocq logs. The differences that remain are explained: coqc `.aux`
files (absolute path and timings), Shen `run time` log lines, the launcher and
glibc on each route, and recorded environment variables. Earthly `+test` was
executed and matched the host Nix test manifest. Earthly `+gates`, `+host` and
`+compare` are written but not executed. This is identity evidence only. It adds no theorem and does not change the audited count (357).
Shen-Scheme is a prebuilt binary trusted by hash. Rebuilding Shen-Scheme and Chez
from source, rebuilding Coq from source, pinning `/bin/sh`, and producing ARM
artifacts all remain open. aarch64-linux is declared in the flake but not built.

## Shen-CL actual conditional lowering (E2E-16, in progress)

`CLLowering.v` admits an inert byte-level capture of Shen-CL
`4844072dde0208c3e4b99dcbfea58e4fdfd812e8` `src/compiler.shen` (`emit-if`,
`optimise-boolean-check`, `optimise-boolean-sequence`, `emit-boolean` and the
package header) and interprets the admitted clauses; the lowering is not
re-implemented. Universal theorems (`optimise_sound`, `emit_if_refines`) show,
for every input, every CL world and every `compile-expression` function, that
each emitted `IF` evaluates its condition once and selects branches with Shen
Boolean semantics, preserving results, raised conditions, Boolean errors and
state. They assume the named `primitive_contracts` (owned by E2E-17, shown
satisfiable by `model_contracts`) and `qsafe`, which excludes quoted non-symbol
comparands: for those the optimizer's `EQ` rewrite disagrees with Shen equality.
Boolean-error diagnostic text is quotiented. `compile-expression`,
`bind-accessor-chains`, `emit-cond-clauses`, SBCL execution, the CL reader and
printer, and the package system remain contracts. The 34 Rocq-checked agreements
with the actual compiler run on the Shen host are sampled evidence, and the SBCL
contract samples in the opt-in gate are native samples; neither is a theorem.
Three altered stored captures (dropped guard, CL truthiness, swapped branches)
join the default proof mutations (74 total); the opt-in gate also rejects an
`EQ`-for-equality capture after fresh regeneration. Twenty-two additional
statements join the assumption audit (379 total).

## Shen-Scheme argument ordering and fresh names (E2E-15, in progress)

[SCHEME-PORT](SCHEME-PORT.md) records the first E2E-15 item. Twenty-eight
additional audited statements bring the inventory to 385 on this branch's
baseline. The actual captured `order-call` pass is executed on the effect
evaluator together with the actual captured Shen kernel 43.1 `occurrences`,
`reverse` and `not` (new pinned `ports/upstream/sys.shen`, `kernel_list`
capture, regenerated and diffed by the proof gate); these are no longer Rocq
oracles. `gensym` is quantified as an arbitrary stateful generator.

Universal theorems: every successful pass run follows the exact keep/lift
structure with names whose captured occurrence count is zero
(`order_call_success`, `fresh_success`); the reader only produces variables
occurring in the syntax (`decode_vars`) and is budget-monotone
(`decode_monotone`); and the produced syntax has exactly the same completed
outcomes, error payloads, final state and event trace, and the same
non-completion, as the input call, for arbitrary programs and operations
(`order_call_preserves`, `order_call_noncompletion`). Admission: an
application head, no `lambda` argument (no closures in the first-order
model), and bound variable arguments. One ground sample and a twelve-check
sampled Shen regression are separate evidence; four new mutants are rejected.

Open: termination/progress with the real generator, the identity of the boot
image's precompiled kernel with this recompilation, `kl:=`/assert-boolean
primitive contracts, composition with the other compiler passes, and native
Chez execution. E2E-15 is not complete.

## EQ-1 induction-checker correspondence (E2E-09, in progress)

The original EQ-1 kernel (`shen/kernel.shen`) and every helper it calls are
captured from the pinned image, one provenance profile per source file
(`eq1_base`, `eq1_equations`, `eq1_theory`, `eq1_kernel`), regenerated and
diffed by `make prove`, and decoded completely in Rocq. `EqualityInductionOracle`
proves that every value the Native evaluator returns is the value of a
fuel-free oracle semantics of the same bodies. Universally, the captured
helpers (sorting, contexts, substitution, rule lookup, zip, induction
hypotheses, resolution, replacement assembly, theory data) compute their
reference functions over arbitrary raw input. `EqualityInductionKernel`
defines a reference kernel that mirrors `kernel.shen` and proves it sound for
the standard model of BURI/ARITH-1, including structural induction over
`expr`; stale theories are rejected and no accepted output contains a false
equation. Ground derivations on the captured program show that acceptance
cannot reach search, normalisation or `eval`, and that injected rules,
forged `accepted` labels and ill-sorted theorems are rejected; agreement with
the reference kernel on those samples is sampled evidence only.

Not proved: that the captured recursive drivers and `substitution?`,
`instantiate`, `replace`, `goal?` refine the reference kernel (EQ1-DRIVERS);
`guard` semantics; numeric `=` and budget-spelling contracts; termination of
the captured kernel. See [EQ1](EQ1.md). The soundness theorem is therefore
about the reference kernel, not yet about the captured one.

Forty-seven additional statements join the assumption audit (404 total).

## Primitive and helper wrappers (E2E-17, in progress)

[PRIMITIVES](PRIMITIVES.md) records the first E2E-17 increment.
`spec/primitives.json` is generated by an inert Shen capture of the vendored
pinned port sources and is checked by `shen/primitive-matrix.shen`. It covers
114 entries: all 36 KLSyntax primitives on both ports and every registered
port primitive. Each entry names its exact implementation, either a
definition byte span or the inlining compiler clause, and a computed closure
down to 252 individually named host operations, each owned by one of
E2E-21..27. The matrix also has 101 named contracts: every primitive contract
assumed in the repository, including all 17 `CLLowering.primitive_contracts`
fields, the 30 `Native.primitive` operations and the profile slots.

Universal theorems are proved over the actual pinned definition bytes,
admitted by computed equality with a reviewed AST and regenerated and diffed
by `make prove`, under individually named host operation contracts:

- **Shen-Scheme.** `kl:=` refines `rule_equal` on first-order data, and
  equals the sealed and EQ-1 replacement `equal?` there (bridging the
  `kl:=` part of EQ1-NUMERIC). `kl:_scm.assert-boolean` makes the guarded
  `if` the KLambda `if` rule.
- **Shen-CL.** The Boolean wrappers discharge eight `primitive_contracts`
  fields at the arity the optimizer emits. `absequal` is structural equality
  on data. The optimizer's `EQ` rewrite is exact iff the quoted comparand is
  a symbol or NIL, which is exactly `qsafe`. `shen-cl.add`, `subtract`,
  `multiply` and `divide` are exact on all integers, and `divide` never lets
  a ratio escape.

Two divergences are now refuted obligations:

- Shen-Scheme's compiled literal `=` (`eqv?`) disagrees with `kl:=` on mixed
  exactness. This is a sampled observation on the host.
- Shen-CL's `(* 0 true)` answers 0. This is a theorem, and it is also
  observed on SBCL.

A further finding: the all-arity `pred_refines` fields are stronger than the
bodies justify.

Seven altered byte copies are refused (proof mutations 90). Open: vectors,
closures, floats, `numeric-equal`, 9 assumed `primitive_contracts` fields,
every `none` entry, and all host operations. E2E-17 is not complete.

## Shen-Scheme pass composition and the let/if/cond/equality branches (E2E-15, in progress)

The exact upstream `yields-boolean?`, `force-boolean`, `emit-symbol`,
`emit-let`, `emit-if`, `emit-cond`, `emit-cond-clauses` and
`emit-equality-check`, read inside the exact upstream package header, and the
kernel `element?` are new captures (`compiler_branches`, `kernel_element`),
regenerated and diffed by `make prove`. `SchemeBranches` proves exact
denotations of every captured emitter for ARBITRARY `compile-expression`,
`order-call` and other uncaptured operations: every completed outcome, final
state and compile-time trace equals a stated sequencing of sub-compilations
(literal tests compile only the selected branch; other tests are forced
boolean; equality selects eq?/eqv?/equal?/null?/fallback as the source says).
`SchemeCompose` composes the proved passes on the captured code:
`order_then_merge_preserves` (captured merge on the let around any successful
captured order-call output preserves outcomes, error payloads, state and trace
of the unordered let) and `let_clause_preserves` (captured emit-let, ordering
and merge: the let clause as `compile-expression` invokes it, with the two
uncaptured `compile-expression` calls as named premises); `strict_if` (forced
conditions keep the boolean domain and branch laziness);
`numeric_equality_preserves` (eqv? lowering through the captured order-call).

Two **confirmed port disagreements** are recorded as refuted obligations with
sampled counterexamples, not hidden: a cond with no true clause returns
`#<void>` on Shen-Scheme (profile: `XCondFail`; `cond_without_true_unread`
proves such emitted conds are outside the reader), and `=` with a literal
number lowers to `eqv?`, which disagrees with the `kl:=` path on mixed
exactness (`(= 1 (* 2 (/ 1 2)))` is false; through variables it is true).
Successors `OB-SCHEME-COND-ADMISSION` (open) and `OB-SCHEME-EQV-EXACT`
(partial, exact integers proved) carry the fix. Twenty sampled Shen checks
(two of them the counterexamples) and six new rejected mutants are separate
evidence.

Open: the `compile-expression` dispatcher (closures and `scm.` escapes keep
it outside the first-order reader), `unbound-symbol?` (its `,` symbol is
outside the capture codec), the boolean-yielding-head premise, the KLambda
profile to decoded Scheme relation, termination with the real `gensym`, boot
image kernel identity and native Chez execution. E2E-15 is not complete.

Twenty-eight additional statements join the assumption audit (522 total).

## Executable Shen evaluator refines KLambda (E2E-07, in progress)

The actual `shen/klambda.shen` (BURI/KL-PURE-1), as compiled and installed by
the pinned image, is captured (profile `e2e07_klambda`, all 26 definitions),
regenerated and diffed by `make prove`, and executed by the Native model with
the captured `base.shen`/`kernel.shen` helpers and the pinned runtime helper
templates. Universally (`klambda_refines`, `klambda_decided_terminates`): for
every program of the proved subset (literals, variables, `lambda`, one-argument
`apply`, `let`, `if`, saturated `+ - * < = cons hd tl cons? number? string?`,
`raise`, `trap`), every definition table, budget and Native fuel, a value
returned by the captured `buri.eval` is an evaluator verdict, and under every
pinned profile (no stack bound; system-error messages equal to the evaluator's
texts) `[returned v]` and `[raised m]` are terminating KLambda behaviors of the
translated program with the translated value or an exception of the stated
class, found by `KLMetatheory.run` and excluding divergence.
`[unknown evaluation-budget]` and `[unsupported closure-equality]` make no
claim; `[unknown host-error]` comes only from the guard handler of
`buri.evaluate` (`evaluate_shape`). Per-construct equations about the captured
bodies are proved by VM reduction with the callee oracle abstracted, which
keeps proof checking fast. Ground runs of the captured evaluator are separate,
ground evidence.

Not proved: the converse (E2E07-COMPLETE; false for closure-vs-data `=`),
`[global]`/function values (uncaptured `kl:length`), `freeze`/`thaw`,
unsaturated primitives, the Chez `guard`, and Chez-to-Native simulation. No
change to `shen/klambda.shen` was needed; the profile differences are listed
in [E2E-07](E2E-07.md). This is a theorem about the reference evaluator, not
about Shen-Scheme.

Thirty-three additional statements join the assumption audit (527 total).

## EQ-1 captured drivers refine the reference kernel (E2E-09, EQ1-DRIVERS)

Every captured KLambda driver of `shen/kernel.shen`, read from the decoded
capture `ports/eq1-kernel.bits` (not restated), computes the reference kernel
for every input: the guarded body of `check-bundle`, `bundle-h`,
`bundle-next`, `goal?`, `check-theorem`, `check-cases`, `check-case-bound`,
`check-steps`, `check-step-result`, `after-rewrite`, `instantiate`,
`substitution?`, `replace` and `replace-arg` (`EqualityInductionDrivers`). The
`buri.nat?` decimal-spelling chain is proved to decide exactly `0 <= z` on
integers (part of EQ1-NUMERIC). `EqualityInductionRefinement.drivers` composes
the bodies by induction on oracle fuel; `native_*` restate them for the
actual Native evaluator. `captured_bundle_sound`: whatever the captured
`bundle-h` accepts is valid in the standard model. `check-bundle` is a Chez
`guard`; its literal handler is pinned (`check_bundle_captured`) and its
meaning is the stated contract `guard_model`, under which
`captured_check_bundle_sound` and `captured_false_lemma_never_accepted` hold
for the captured code. All are universal partial-correctness theorems; the
technique is a directed symbolic evaluation with lazily exposed branches, so
proof terms stay small (the drivers module checks in about three minutes).
Five modified captured driver bodies are refused by Rocq.

Not proved: Chez `guard` semantics (EQ1-GUARD; `guard_model` is a contract),
termination (EQ1-TERM), numeric `kl:=` versus `equal?`, and Chez-to-Native
simulation. A theorem about the Native evaluation of the decoded capture is
not a theorem about Chez executing it. See [EQ1](EQ1.md).

Twenty-three additional statements join the assumption audit (517 total);
five driver mutants join the proof mutations (88 total).

## ARM byte-level proofs (E2E-20, Wave B, in progress)

[ARM-FOUNDATION](ARM-FOUNDATION.md) section 10 records two checked proofs.
Neither is in `scripts/prove`: each needs a separate toolchain and has its own
opt-in check. The repository's proven boundary, its Coq 8.18.0 pins and the
audited statement count (494 total) are therefore unchanged.

* **Model theorem, sail-arm Armv9.4 Coq model** (`ports/arm/coq/BuriArmAdds.v`,
  `scripts/check-arm.sh`; Coq 8.18.0, stdpp 1.10.0, coq-sail 0.19). For the
  captured Chez word `0xab010017` (`ADDS X23, X0, X1`, `kl:buri-arm-add+0x14`),
  it is an exact, universal-over-`pc` equation. The model's `__DecodeA64` is
  "read SEE; if SEE < 15 then write SEE := 15 and run the ADDS execute, else
  throw Error_Undefined". A second equation turns the execute into an explicit
  read-R0/R1, write-NZCV, write-R23 program. A corollary states that, under
  SEE < 15, coq-sail's `iTrace_match` admits the sequential trace with
  X23 := (X0 + X1) mod 2^64. The `SEE` premise is explicit; this model never
  resets SEE. Statements that mention the decoder inherit the model's three
  Coq-stdlib Reals axioms. The execute and arithmetic lemmas are closed. The
  check binds the word to the stored bytes and rejects a one-bit mutant. This
  covers one word, not fetch/PC update, memory, faults or branches.
* **Islaris theorem** (`ports/arm/islaris/buri_chez_add.v`). It runs in a
  separate Coq 8.19.0 + Iris + Lithium + Islaris environment,
  `nix/arm/islaris.nix`, whose dev pins come by exact commit from GitHub
  mirrors. For all fixnum-tagged a, b with no signed overflow, X23 = 2 and an
  aligned frame slot holding ra, the Chez fast path `+0x00..+0x23` (the
  captured bytes) reaches ra with X23 = a + b. The three slow-path branches are
  proved infeasible. The result is closed under the global context. It is
  relative to Islaris's semantics of isla traces: isla `b8e614bd`, and also
  `e9b5d945`, over the Armv8.5 IR under Islaris's EL2/MMU-off register
  constraints. It is not about the Armv9.4 Coq model and not about EL0 Linux.
  "Trace = architecture" is trusted to isla and z3.

Open: no bridge theorem connects isla traces and the Coq model. Proofs for a
call, store, fault, allocation stub and atomic are still missing, and so are
the SBCL code, fetch/execute and PC update in the v9.4 model, and the
EL0/MMU-on profile. E2E-20 is not complete.

## Shen-CL lowering contracts from captured bodies (E2E-16/E2E-17, Wave C)

The proven boundary moves in three ways. See [PRIMITIVES](PRIMITIVES.md) and
[CL-PORT](CL-PORT.md).

* **Narrowed record.** The nine predicate fields of
  `CLLowering.primitive_contracts` were stated for every argument count, which
  was a false requirement. Wrong-arity calls are never emitted, and the
  captured body cannot justify them: `CLContracts.all_arity_unjustified`, and
  `captured_all_arity_false` for the captured world. Each field is now stated
  at exactly the emitted arity. `optimise_sound` and `emit_if_refines` are
  re-proved with `sem_pred1`/`sem_pred2`. Every world admitted before is still
  admitted (`pred_refines_narrows`).
* **Discharge.** `rocq/CLContracts.v` connects CLLowering's relational CL
  model to CLWrappers' functional evaluator: a helper call's outcome is the
  result on which the fuel-indexed evaluation stabilises.
  `captured_contracts` proves every field for the world that runs the
  admitted `primitives.lsp` bodies, for every state type, every relation for
  unmodeled forms, every host table and every kernel relation satisfying the
  named records. Eight fields need no host premise at all. Nine are reduced to
  individually named contracts:
  - `cl_host_ops`: 16 SBCL operations, E2E-21/24;
  - `cl_kernel_ops`: compiled kernel `not`, `empty?`, `fail`, E2E-16.

  This includes, for every value and not only first-order data, the captured
  `absequal` against symbol, NIL, string and numeric literals, and
  `numeric-equal`. `discharged_optimise_sound` and
  `discharged_emit_if_refines` are the captured lowering theorems with only
  those contracts and `qsafe` left. They are universal theorems. The
  instantiation keeps fn_heads host operations pure and quotients
  fresh-condition identity.
* **Increment/decrement.** The pinned `shen-cl.increment`/`decrement` are now
  packaged and admitted. `step_refines_rules` proves them exact on every
  integer, assuming `cl_step_ops`.

Not proved: the host and kernel contracts themselves, `cf-vectors`, floats in
the arithmetic wrappers, `emit-cond-clauses`, `compile-expression`, the CL
reader and SBCL execution. A theorem about this CL model is not a theorem
about SBCL.

Twenty-four statements join the assumption audit (`rocq/Audit_Clcontracts.v`,
630 total). Two admission mutants and three restated-claim mutants join the
proof mutations (106 total). The matrix names 123 contracts.

## Native representation relations (E2E-21, Wave C, in progress)

[REPRESENTATION](REPRESENTATION.md) is the source-bound specification of the
Chez Scheme 10.3.0 tarm64le object representation. It covers fixnums,
immediates, characters, pairs, symbols, strings, vectors, flonums, bignums,
closures and code objects, records, ports, and the TC/frame/argument
registers.

The constants come from pinned inputs in `ports/repr/`:

* the upstream `cmacros.ss`, `arm64.ss`, `arm64.def` and `types.h`;
* the build-time `equates.h` and `machine.def` from the ARM lane's tarm64le
  build.

The inert `scripts/package-repr-layout.py` extracts them into the generated
`rocq/ChezLayout.v` and `rocq/SbclLayout.v`, which `scripts/prove`
regenerates and diffs.

New modules: `ChezLayout`, `SbclLayout`, `ChezWord`, `ChezRepr`, `SbclRepr`
(`rocq/modules.d/50-repr.list`). There are 45 audited statements
(`rocq/Audit_Repr.v`), all closed. Their kinds:

* **Universal theorems:**
  * fixnum encode/decode round trip, injectivity and surjectivity on tag-0
    words;
  * tagged addition `(fx x + fx y) mod 2^64 = fx (x+y)`, and no signed
    overflow iff `x + y` is a fixnum;
  * the representation relation `ChezRepr.rv` between KLambda values and
    words over a byte memory. It comes with a total tag decoder (`rv_classify`),
    kind uniqueness, pointer/immediate/fixnum disjointness, and a proof that
    void, unbound, eof, bwp and the GC markers represent no Shen value;
  * a word represents at most one first-order value (`rv_functional`);
  * pointer-field alignment, and car/cdr, string-ref/length and
    vector-ref/length reading the abstract components;
  * `shen_int_add_fast_path`: for words representing Shen integers, the
    fast path's tag test holds iff both are fixnums, and its overflow test
    holds iff the sum is.
* **Ground derivations:** the cmacros/equates/types.h/arm64.def agreement,
  the register layout, the SBCL source-versus-image agreement and the SBCL
  layout facts.
* **Sampled agreement:** one qemu tarm64le process (`chez_sample_agrees`).

The relation is about one memory snapshot. Closures, ports and conditions
enter through meaning parameters owed by E2E-22, E2E-27 and E2E-17.

**Islaris (separate Coq 8.19 toolchain, not in `scripts/prove`).**
`ports/arm/islaris/buri_chez_add_shen.v` derives the E2E-20 fast-path
theorem for X0/X1 holding fixnum words of Shen integers x, y with x, y and
x + y fixnums. It discharges the `(a|b)&7 = 0` and no-overflow premises. Its
result is that X23 holds the fixnum word of x + y. It is closed under the
global context. The EL2/MMU-off constraints, the Armv8.5 isla traces, the base
address, the X20 frame-slot premises and the continuation remain assumed.

**SBCL 2.6.8 arm64:** a specification table only (lowtags, widetags, slots,
registers, features); no relation yet.

**Found (sampled):** on Shen-Scheme v0.52, `(intern "12")` is the integer 12,
not a symbol, against the model's `rule_intern` (`tests/representation.shen`;
OB-SCHEME-INTERN-NUMERIC, refuted).

Four proof mutations join (105 total). They include the naive "two fixnums
never overflow" premise, which Rocq refuses. One gate test joins (27): the
extractor refuses a changed pinned input. One Shen suite joins (26).

Open, with owners recorded in `spec/obligations.json`:

* frames, closures, continuations and multiple values (E2E-22);
* symbols, globals, bignum normalisation and FFI (E2E-24);
* allocation and moving GC (E2E-25);
* ports (E2E-27);
* asynchronous ownership (E2E-28);
* flonum meaning and conditions (E2E-17);
* the EL0 profile of the Islaris result (E2E-20);
* that Shen-Scheme stays inside the relation (E2E-15);
* the whole CL relation (E2E-21).

E2E-21 is not complete.

## Port-fix lane: proved proposed upstream patches (Wave C)

Five unified diffs live in `ports/patches/` (see its README and NATIVE.md).
They target the pinned Shen-Scheme `8d261518` and Shen-CL `4844072d` files.
`make prove` re-applies them with pinned sha256 and patched blobs and
re-captures the patched definitions. These are theorems about the
**patched** code only. Stock Shen-Scheme and Shen-CL are unchanged, and
their obligations stay refuted.

* **Universal theorems** (`rocq/SchemePatched.v`):
  - The patched Scheme `emit-cond-clauses` ends every cond with no
    literal-true test in a `#t` clause holding the compiled
    `(simple-error "condition failure")`. Under the stated read premises, the
    cond is read as `(if T1 B1 (if ... E))`.
  - The patched numeric-literal `=` path is read as exactly
    `(kl:= d1 d2)`, so it agrees with `kl:=` on all values. Premise:
    `prefix-op` names `kl:=`.
* **Universal theorems** (`rocq/CLLoweringPatch.v`):
  - The patched CL `optimise-boolean-check` is test-equivalent to its input
    for every datum, with **no qsafe premise**. It holds for any `symbol?`
    oracle that answers true only on symbols.
  - The patched CL `emit-cond-clauses` always ends in a `T` clause, whose
    body is the compiled error when no source test is literally `true`.
* **Ground derivations:** stock CL `[]` and `[[false 1]]` emit no clauses.
* **Universal theorems** (`rocq/CLMultiplyPatched.v`): the patched
  `shen-cl.multiply` returns the exact product on integers. It raises on a
  non-number in either position. This is a profile choice: upstream keeps
  `(* 0 x) = 0` on purpose.
* **Sampled:**
  - Full Shen-CL images (SBCL 2.6.8), stock and patched:
    - `(* 0 true)` returns `0`, then raises after the patch.
    - `(eval-kl [cond [false 1]])` returns `[]`, then raises
      "condition failure".
    - The `lisp.` EQ case returns `no`, then `yes`.
    - The upstream suites pass with the accompanying test change.
  - Shen-Scheme v0.52 binary, with the patched emitters called directly (no
    rebuild): the cond raises, and `(= X 1)` with an inexact X is true.

New ledger entries:

- Discharged, about the patched code only:
  - OB-SCHEME-COND-PATCH
  - OB-SCHEME-EQ-LITERAL-PATCH
  - OB-CL-COND-PATCH
  - OB-CL-MULTIPLY-PATCH
  - OB-CL-EQ-REWRITE-PATCH
- Refuted, stock: OB-CL-COND-FALLTHROUGH and OB-CL-EQ-REWRITE.
- `lane_audits` lists `rocq/Audit_Portfix.v`, so the ledger audits lane
  theorems.

## Chez nanopass translation validation (E2E-22, Wave C, in progress)

[CHEZ-NANOPASS](CHEZ-NANOPASS.md) starts package 22 for Chez Scheme 10.3.0
tarm64le, the shen-scheme v0.52 pin, under Shen-Scheme's eval parameters. The
compiler stays untrusted. Twenty statements join the assumption audit in
`rocq/Audit_Nanopass.v`, and all are closed. Three proof mutants join the
mutation gate (104 total).

* **Inventory.** `spec/chez-passes.json` lists the pipeline that actually
  runs: the front end (expand, cpvalid, cp0/cptypes/cpletrec twice, cpcheck,
  cpcommonize), 40 nanopass passes, and 13 register-allocator sub-passes per
  lambda. It records languages, line ranges and conditions.
  `trace_pass_order` is a ground derivation of the traced order.
* **Grammars.** Rocq reads the pinned `np-languages.ss` and resolves every
  `extends`. It obtains exactly the grammars behind the generated inductive
  syntax for all 28 languages, including L15a-L16 (`np_languages_resolved`,
  ground derivation).
* **Captures.** Every traced pass output of real tarm64le Chez for
  `kl:buri-arm-add` is captured and reproducible byte for byte. The x86_64
  trace is a sampled agreement with it: identical up to
  `$np-expand-primitives`.
* **np-recognize-mrvs.** `check_recognize_mrvs_sound` is a universal theorem
  over a core semantics. It is parametric in primitive semantics and in the
  argument-evaluation order. Applied to the capture it gives a ground
  derivation.
* **Bytes.** `check_code_object_sound` is a universal theorem.
  `codegen_buri_arm_add_instance` is a ground derivation: the 152 captured
  bytes are exactly `np-generate-code`'s template with its three relocation
  windows rewritten by `arm64_set_abs`.

Ten same-language passes print identically. This covers the printed form only.

Open:

* 38 nanopass passes, the front end and register allocation are unvalidated.
* Only one function has been captured.
* The printed IR omits info fields (`OB-CHEZ-NP-PRINTER`, assumed).
* There is no aarch64 Shen-Scheme process.

`OB-CHEZ-COMPILATION` is partial and is not discharged.

## Termination: EQ-1 checker and Shen-Scheme ordering pass (E2E-09, E2E-15, Wave C)

Universal theorems, axiom-free, audited in `rocq/Audit_Termination.v` (31
statements; modules in `rocq/modules.d/50-termination.list`).

* **EQ1-TERM** ([EQ1](EQ1.md)). `EqualityInductionTermination.native_guarded_body_total`:
  for every theory `T`, bundle `B` and budget `N` whose numbers are integers
  (`idata B`, `numok N`), the actual Native evaluation of the decoded captured
  `check-bundle` guarded body returns exactly `r_check_bundle T B N` at some
  fuel and at every larger fuel. `captured_check_bundle_total` /
  `captured_check_bundle_decides` lift this through the stated `guard_model`.
  With the existing refinement theorems this is total correctness of the
  captured checker under Native. The fuel is existential (constructive proof),
  not a closed bound. Every helper the acceptance path calls is also total on
  its validated domain (`EqualityInductionTotalBase`, `EqualityInductionTotalTerms`).
  Ground derivation, not universal: `fraction_budget_unsupported` (a 1/2 budget
  makes Native reach an unsupported primitive, so the integer condition is
  needed).
* **Ordering pass progress** ([SCHEME-PORT](SCHEME-PORT.md)).
  `OrderCallProgress.order_call_progress`: with the counter-based gensym
  contract of pinned `sys.shen`, the captured order-call returns on every
  application call from every counter value. The composed preservation
  theorems no longer assume a successful run (`order_call_preserves_total`,
  `order_then_merge_total`, `let_clause_total`).

Not changed: EQ1-GUARD (the guard is the stated `guard_model`), the numeric
`kl:=` contract, gensym as a contract rather than a capture, and every
Chez-to-Native gap (E2E-32). A theorem about Native evaluation of the decoded
capture is not a theorem about Chez executing it.
Three proof mutations join the gate (104 total): a non-decreasing `member?`
recursion fails the inductive termination step (its unmutated control is
accepted), dropping the integer-budget condition is refused, and a gensym
counter that does not advance is refused.

## ARM decode coverage and the first trace-to-model bridge (E2E-20, Wave C, in progress)

[ARM-FOUNDATION](ARM-FOUNDATION.md) section 11 has the details. Nothing here
is in `scripts/prove`. The opt-in check is `scripts/check-arm.sh`, Part B. The
repository's proven boundary, its Coq 8.18.0 pins and the audit count are
unchanged.

* **One Coq for traces and model.** coq-sail 0.19 and the sail-arm
  `7d058164` Armv9.4 Coq model compile in the Islaris Coq 8.19.0
  environment: `armv9.v` takes 7 min at 6.4 GB. The recipe is
  `nix/arm/sail-model.nix`.
* **Decode equations (model theorems, universal over `pc`)** in
  `ports/arm/coq/BuriArmDecode.v`. They cover twelve more captured words: the
  rest of the Chez fast path (`cmp`, `b.ne` ×2, `orr`, `tst`, `b.vs`, `ldur`,
  `br`), the Chez store `str x0,[x20,#8]`, and the SBCL `ret`, `blr x10`
  (the call into ALLOC-TRAMP) and `brk #15` (trap). Each fixes the selected
  encoding, the SEE guard, every decoder register read (BRK reads
  `FeatureImpl`) and the exact execute call. Execute-side behaviour is not
  covered.
* **Bridge (model theorem relating trace and model)** in
  `ports/arm/coq/BuriArmBridge.v`. `chez_0014_bridge` takes the Islaris trace
  `a14.v` for ADDS at +0x14, the very file the Islaris fast-path theorem
  uses. From any register map holding the model's inputs, the trace runs to
  completion under Islaris's own `seq_step`, never blocking. Its final map
  holds exactly the model's AddWithCarry result in R23 and the model's NZCV
  in PSTATE. At the same time, the v9.4 model's decoder admits its unique
  register trace. The isla side (`a14_run`) and the bit-level lemmas are
  closed under the global context. The pairing is an Armv8.5-IR trace
  (isla `b8e614bd`) against the Armv9.4 Coq model. The theorem does not cover
  the trace's `_PC += 4` against the model's `__InstructionExecute` PC
  advance, nor the other eight words. Islaris's fast-path theorem therefore
  still trusts isla for every word except +0x14 and for the PC step.
* **EL0 / MMU-on.** Under an EL0 Linux (non-VHE) isla config, traces exist
  for 8 of the 9 fast-path words. The branches differ from EL2 by a
  top-byte-ignore split. `ldur` exhausted memory twice (resource-exhausted;
  no trace), so no EL0 proof exists.
* **coqchk of the model** passes: 3 min 18 s at 1.0 GB. The context axioms
  are the model's six external memory/sleep primitives and five Coq-stdlib
  axioms. None comes from Buri.

Open: execute-side proofs for the load, store, call, return and trap; an
allocation stub and an atomic; the bridge for the other eight words and the
PC step; any EL0 proof; and the SBCL fast path in Islaris. E2E-20 is not
complete.

## E2E-07 extended: globals, function values, freeze/thaw and the converse (Wave C)

`shen/klambda.shen` changed to agree with the agreed KLambda semantics:
structural equality follows `KLValue.kl_eq` (a function value is unequal to
data; equality of two function values is undefined and stays
`[unsupported closure-equality]`), `thaw` of a closure and application of a
thunk raise `arity`, `thaw` of a partial application returns it, and the
uncaptured `kl:length` is replaced by the captured `buri.fewer?`.
`make conformance` passes. Unsaturated `[primitive ...]` syntax is rejected at
admission: a recorded profile difference (`kl-currying` /
`prim-partial-application`, owner E2E-07), now checked by the ledger
(owner and registered enforcement tests), not a theorem. This supersedes
"no change to `shen/klambda.shen` was needed" in the earlier E2E-07 section.

Universal, axiom-free, about the recaptured evaluator run by the Native model
(`rocq/Audit_E2e07b.v`): `klambda_refines_ext` extends soundness to every
KL-PURE-1 construct (`[global]`, currying through `[function ...]` values,
`freeze`, `thaw`) for every well-formed definition table translated into the
KLambda global namespace, and states `[unsupported]` as the KLambda machine
going wrong; `klambda_complete` is the converse: every silently terminating
KLambda run of a subset term is matched, for every budget above its step count
and all large enough Native fuel, by `[returned v]`/`[raised m]` with the
corresponding outcome. The pure-subset theorems keep their statements.
Completeness fails, by design, for small budgets and for unsaturated
primitives (outside the subset). Open: E2E07-GUARD (Chez `guard`),
E2E07-NATIVE (Chez-to-Native simulation), E2E07-ADMISSION (admission
predicates versus the subset). This is about the reference evaluator, not
Shen-Scheme. Twenty additional statements join the assumption audit
(`Audit_E2e07b.count` 20); six proof mutations join the gate (107).

## Application contract logic BURI/KL-CONTRACT-1 (E2E-08, Wave D, in progress)

New: a contract calculus over the formal KLambda semantics
([CONTRACT-LOGIC](CONTRACT-LOGIC.md)). There are three distinct judgments:
Partial (step-indexed safety), Total (every path terminates) and Always I
(every emitted event satisfies I). Assertions cover values, stores and local
IO traces in the Observation vocabulary. Exceptions are postconditions.
Resource failure is admitted only as `ResourceOut` within a recorded policy
that covers the profile's limits. Heap framing uses explicit footprints.
Primitive call contracts are proved; host contracts are named premises.

Universal, axiom-free (`rocq/Audit_Contracts.v`, 59 lines, 47 universal):

* `soundness` (every rule), `rec_partial`, and `rec_total` (explicit nat
  measure).
* `total_meaning` and `partial_meaning` (KLMetatheory maximal behaviors under
  every answering environment, with divergence, reaction and going wrong
  distinguished), `total_run` and `partial_run`.
* `prim_spec_valid`, `io_spec_valid` and `write_byte_visible`.
* Refutations of dropped premises: `if_nonbool_premise_needed` and
  `unmeasured_recursion_unsound`.
* A recursive higher-order `map` with a mutable global counter
  (`main_mut_behaviors`). Its pure instance is transported to the captured
  `shen/klambda.shen` verdicts in the Native model (`contract_verdict_sound`,
  `contract_verdict_exists`).
* Certificate checker theorems (`check_identity`, `check_hyps_declared`,
  `check_total_measures`, `check_shapes`, `fits_rule_shape`, stale-identity
  rejections).

Ground (12 lines): the example certificate is accepted, and its mutants are
rejected (`ContractCertExample`). Sampled: `tests/contracts.shen` (the Shen
checker `shen/contract-cert.shen`, 19 cases agreeing with Rocq). Seven proof
mutations join the gate (134).

Open:

* OB-CONTRACT-RULES-COVERAGE: and/or/cond, multi-argument closure application,
  eval-kl, history-dependent temporal properties, signals, and liveness.
* OB-CONTRACT-CERT-SEM: an accepted skeleton yields a derivation.
* OB-CONTRACT-CERT-SHEN: the Shen checker refines the Rocq checker.
* OB-CONTRACT-TRANSPORT: mutable state is not in KL-PURE-1, so `main_mut` is
  not transported; E2E07-NATIVE remains open.

This is not a theorem about Shen-Scheme.

## Primitives: intern, string and vector-read bodies (E2E-17, Wave D, in progress)

Two new modules hold body proofs of the actual pinned definitions. The
bytes are packaged by `scripts/package-prims2.py` into `rocq/Prims2Sources.v`,
re-checked by `scripts/check-prims2-package.py`, read by `PortReader` and
admitted by computed equality. Every theorem below quantifies over every
host table that satisfies the individually named contracts. None of it is a
theorem about Chez or SBCL.

* **Universal theorems** (`rocq/SchemeIntern.v`):
  - Stock Shen-Scheme `kl:intern` has an exact denotation. On every name
    that is digit-led with length > 1, it returns the host `string->number`
    answer when that answer is a number, which represents no KLambda symbol.
    OB-SCHEME-INTERN-NUMERIC therefore stays **refuted**. Elsewhere, stock
    and patched agree, so OB-SCHEME-INTERN-ADMISSION is now partial: the
    admission choice itself is still open.
  - The proposed patch `ports/patches/shen-scheme-primitives.diff` returns
    `#t`, `#f` or the symbol of the name for **every** string, and refines
    `rule_intern` (OB-SCHEME-INTERN-PATCH, about the patched code only).
    The compile-time fold of a literal `(intern S)` is covered only in a
    binary rebuilt with the patch.
* **Universal theorems** (`rocq/CLStrings.v`):
  - The captured Shen-CL `|pos|`, `|tlstr|`, `|n->string|`, `|string->n|`,
    `|<-address|` and `|intern|` refine their KLambda rules on their stated
    domains (OB-CL-STRING-PRIMS). Bounds and out-of-range calls raise
    exactly where the rule throws.
  - New contracts: `cl_string_ops`, `cl_vector_ops` and `cl_intern_ops`. The
    last one includes the uncaptured `shen-cl.process-intern` LOOP body as
    the named contract `process_plain`.
  - **Two divergences**, proved for every contract-satisfying host:
    `string->n` raises on strings of length >= 2 where the rule returns the
    first code point (OB-CL-STRING-TO-N-UNIT, refuted), and `n->string`
    returns a string on surrogates where the rule is a domain error
    (OB-CL-N-TO-STRING-SURROGATE, refuted). Shen-Scheme agrees with the
    rule in both cases (sampled).
* **Sampled:** `ports/prims2-native-samples.shen`, run on both pinned ports.
  Shen-Scheme host samples are in `tests/primitives.shen`. The `intern`
  upstream draft is `docs/UPSTREAM-ISSUES-INTERN.md`, not filed and only
  self-reviewed. It includes a Shen-CL intern collision,
  `(= (intern "a#b") (intern "a_hash1957b"))`, which is sampled only.
* **Matrix:** seven `none` entries are now `proved`: `shen-scheme:intern`,
  and `shen-cl:` `intern`, `pos`, `tlstr`, `n->string`, `string->n` and
  `<-address`. There are 27 new named contracts (150 in total).
* **Gates:** 26 statements join the audit (`rocq/Audit_Prims2.v`,
  `Audit_Prims2.count` 26). Seven proof mutations join the gate (134).
* **Open:** Shen-Scheme `str`, `pos`, `tlstr`, `n->string`, `string->n` and
  `absvector` / `address->` / `<-address`. These are compiler clauses that
  inline Chez operations and stay contract-assumed, or `kl:str`, which uses
  a `lambda` outside the decoder. Also open: Shen-CL `str`, `cn` (a DEFUN
  with a `declare` form), `absvector`, `address->` (SETF), code points >= 256
  in `n->string`, and the heap-vector correspondence premise of
  `<-address` (E2E-21).

## E2E-21 SBCL arm64 representation and the E2E-21 host operations (Wave D)

SBCL 2.6.8 arm64 now has representation relations, from the pinned layout
(`rocq/SbclLayout.v`): `SbclValues.kv` for KLValue values (one memory
snapshot, vector locations, an interned-symbol table, meaning parameters for
procedures, streams and conditions) and `SbclHostOps.cv` for the CL-model
values of CLLowering. NIL's list/symbol duality is taken from the pinned
genesis.lisp: Shen `[]` is NIL, SYMBOLP is true on it and on both Shen
booleans, and Shen `false` is CL true; the word of a Shen boolean also
represents the symbol of its name, so the KLValue relation is not a function
on words (the CL-model relation is, `cv_functional`).

The ten E2E-21 fields of `CLContracts.cl_host_ops` (EQ, TYPEP FIXNUM,
INTEGERP, NUMBERP, CONSP, STRINGP, ARRAYP, SYMBOLP, NOT, NULL) are inline
type tests in the pinned image. Their raw instruction words, compiled for an
untyped argument and read from the code objects under qemu-aarch64, are an
image capture (`ports/repr/sbcl/sbcl-2.6.8-arm64-type-tests.capture`,
packaged into `rocq/SbclTypeTests.v`). Rocq decodes them with a small A64
transcription (`rocq/SbclA64.v`, a trust boundary) and proves, universally
over registers and memory, the word-level test each window decides
(`SbclTests.*_window`); ground checks tie the windows to the standard entry
and return frames, show STRING=, EQUAL, EQL and = are full calls, and match
the header tests against the define-type-vop type codes of the pinned
sources. `SbclHostOps.e2e21_machine`/`eq_machine` then show the code returns
exactly the contract answers on every represented value, and
`sbcl_optimise_sound_e24`/`sbcl_emit_if_refines_e24` restate the CL lowering
theorems with only the six E2E-24 contracts (`cl_e2e24_ops`) and
`cl_kernel_ops` left. Not covered: type-specialised variants and the Shen-CL
call sites (OB-SBCL-INLINE-TESTS), frames, GC, symbol names, Shen-CL staying
inside the relation. OB-CL-HOST-OPS is narrowed to the E2E-24 fields;
OB-NATIVE-REPR-SBCL is partial. Seventy-two statements join the assumption
audit (`Audit_Sbclnative.count` 72); five proof mutations join the gate (132).
E2E-21 stays in progress.

## Chez primitive expansion and an info-carrying IR dump (E2E-22, Wave D, in progress)

Details: [CHEZ-NANOPASS](CHEZ-NANOPASS.md) sections 8-11. One function
(`kl:buri-arm-add`) only; E2E-22 is not complete.

* **Trusted dumping tool, not proved.** A three-line printing patch to the
  Chez 10.3.0 tracer (`ports/chez-np/patches/np-trace-raw.patch`) prints the
  nanopass raw unparse, with every info field, after each pass. This is the
  new assumed obligation `OB-CHEZ-NP-RAW-DUMP`. It supersedes
  `OB-CHEZ-NP-PRINTER` and is narrower: in L1-L14 nothing opaque remains but
  `#<void>`; uvar, label and register internals, L15a/L16 live-info and
  assembler procedures, and the register-allocator sub-pass outputs stay
  unprinted (`raw_opaque_census`, `raw_coverage`, ground derivations). That
  the patch leaves compilation unchanged is **sampled agreement** only (the
  stock-format output is unchanged except the block record-type uid, exactly
  as for an unpatched rebuild; `raw_codegen_same`).
* **Universal theorems** (`rocq/Audit_Chezprim.v`, 31 statements, 7
  universal): `check_raw_sound` (raw L4/L4.5 reading with info fields);
  `check_expand_plus_sound`, `plus_expansion_fast`, `plus_expansion_slow`
  (the `$np-expand-primitives` fixnum fast path for two-argument `+` over a
  stated word-level semantics, under H_fix and H_lib, the new assumed
  `OB-CHEZ-LIB-PLUS`; the fast path needs neither); `sort_refs_perm`,
  `check_block_order_sound` (np-optimize-block-order! changes block-list
  order only).
* **Ground derivations**: np-suppress-procedure-checks validated with its
  `check?` changes (the stock printer hid them); np-recognize-mrvs and nine
  identities re-checked on the raw form; `$np-expand-primitives` validated on
  the `+` clause; `expanded_fast_path_shen`: the L9 fast path returns
  `ChezWord.fx_enc (x + y)`, the value `buri_chez_add_shen` proves in X23;
  np-optimize-block-order! validated.
* **What does not connect**: the front end, L9 to L16 (calling convention,
  the register allocator, instruction selection) and the instruction
  encoding are unvalidated. The L9 term and the Islaris bytes agree only in
  statement, not by proof. The `main` clause's `$set-top-level-value!`
  expansion is unvalidated.
* Five proof mutations join the gate (132).

## ARM fast path: eight words bridged both ways, the PC step (E2E-20, Wave D, in progress)

Details are in [ARM-FOUNDATION](ARM-FOUNDATION.md) section 12. Nothing here
is in `scripts/prove`. Everything is checked by the opt-in
`scripts/check-arm.sh` Part B (Coq 8.19.0 with Islaris and the sail-arm
7d058164 Armv9.4 model), and the audit count does not change.

* **Sequential semantics** (`BuriArmSeq.v`). This is a universal theorem,
  closed under the global context. It reads the model's `iMon` trees against
  its own register record, and proves that reading equivalent to coq-sail's
  `iTrace_match` over a single-threaded register file.
* **Model IFFs on eight words** (`BuriArmFastPath.v`). These are universal
  over `pc` and the register record. For `cmp`, both `b.ne`, `orr`, `tst`,
  `adds`, `b.vs` and `br x10`, the model's decode and execute have exactly
  one sequential behaviour, given as the model's own write sequence. The
  premises are SEE below the guard, and for the branches the stated EL2
  configuration. Each IFF carries only the decoder's three Coq-stdlib Reals
  axioms.
* **PC step** (`BuriArmPC.v`). `__InstructionExecute` contains, by
  conversion, the model's PC advance. Its behaviour is _PC := _PC + 4 when
  __BranchTaken is false, and no change when it is true. The rest of
  `__InstructionExecute` is not proved.
* **Bridges** (`BuriArmFastPathBridge.v`). These are closed under the global
  context. For each of the eight words and its exact Islaris trace, and for
  any model and isla states that agree on R0..R30, _PC and PSTATE.NZCV:
  * the trace has a complete run;
  * every complete run agrees with the model's unique result after the
    model's PC step.

  This is both directions of the bridge. `chez_0014_exact` states the ADDS
  converse as one theorem. The branch traces' `AssumeReg` configuration and
  __BranchTaken = false are stated premises.
* **EL0 `ldur`** is still resource-exhausted. It was retried with Islaris's
  X20 constraint. Both runs died at the 7 GiB cap: the default-threads run at a
  peak RSS of 7,100,404 kB, and the `-T 1` run at 7,148,272 kB. So there is no
  trace. The top-byte-ignore premise for an EL0
  statement, ra[63:56] = 0, is recorded but not used, because no EL0 proof
  exists.

Open: the load at +0x1c (its trace and its model execute path through
translation and `MemRead`) and the store; the rest of
`__InstructionExecute`; an EL0 trace and proof; the allocation stub, an
atomic, and the SBCL fast path. The Islaris theorem still trusts isla for
the load and for the configuration premises. E2E-20 is not complete.

## Shen/JIT lane (E2E-37, in progress)

[SHEN-JIT](SHEN-JIT.md) adds a Rocq profile and an executable bytecode semantics for one RV64 build, pinned at
release 0.6 (`934cfa5`, re-pinned from 0.4 on 9 November 2026), and `rocq/KLPort.v` adds per-port options to the KLambda semantics, with a proof that the agreed options
are exactly `KLSemantics.next`, so the existing lanes are unchanged. One hundred and sixty-nine statements are in the assumption audit
in `rocq/Audit_Jit.v`, all about the models. Eighteen are the port-primitive option (`port_prim`, a ninth field of
`port_rules`, off in both `agreed_rules` and `jit_rules`) and a proposed meaning for 18 of the 35 port primitives the
v0.6 normal form calls (`jit_port_prims_proposed`, with a sanity lemma for each; not wired in, pending a decision,
`OB-JIT-PORT-PRIMS`). The five added at 0.6 state `shen-jit.write-bytes`, the read-error raise
and `n->string`'s UTF-8 rule, which 0.6 changed (`write_bytes_io`, `write_bytes_empty`, `read_byte_error_raises`,
`n_to_string_utf8`, `jit_n_to_string_agrees`). Stage 0: 111 of 955 kernel definitions validated at 0.6. Some relate the bytecode to KLambda for the fragment the lowerer relation
admits: `preservation`, `related_progress` and `call_preservation` (`rocq/JitLowerThm.v`) relate runs of
`KLPort.step_r (jit_rules sealed) jit_profile` to runs of `JitBytecode.next`, with the end case tied to the bytecode's
final machine (`Ends_final`), and `chk_sound` and `check_fn_sound` make the per-definition checker establish that
relation. They relate the bytecode to the expression `lower.shen` emits code for, after `share` and `norm`, not yet to
the source body, and nothing relates either model to machine code. Three of them (`OB-JIT-SYM-INJECTIVE`) make a symbol its name: `sym_of_text` is injective on
every text, so distinct KLambda symbols are distinct machine symbols; the `ShenJitSymBase256` mutant, the old base-256
numeral, is rejected. `p_eq` admits `=` against a safe constant. Thirteen are about the
refinement relation for the lowerer's front passes, and the composition of two front links with `call_preservation`,
proved as an implication from the relation's fundamental property, which is not yet proved (`OB-JIT-LOWER-FRONT`).
Since K00 their statements are in `rocq/JitKRef.v` and their proofs in `rocq/JitKRefGround.v` and
`rocq/JitKRefCompose.v`; `rocq/JitLowerEquiv.v` keeps the old qualified names as abbreviations, so the audit names
and counts are unchanged. `JitKRef.v` also states, without proof, the index-local interface the fundamental property
will be proved through (`fv`, `fund_below`, `fund_gen_statement`, `PrimOutRel`, `prim_compat_statement`).
Twenty-four are in `rocq/JitKRefCompatCtl.v` (branch `p2/kref-ctl`): the JitKRef statements `compat_lit`, `compat_var`,
`compat_let`, `compat_if`, `compat_and`, `compat_or`, `compat_cond`, `compat_type` and `compat_defun`, closed, with their
ERel-level lemmas; trap only conditionally: `compat_trap_lt` takes `fund_below k` AND `prim_compat_statement` (a handler
may be a partial primitive), and `compat_trap_of_fund` derives `compat_trap_statement` from `prim_compat_statement` and
`fund_gen_statement`. The trap acceptance criterion (closed with `fund_below` as the only hypothesis) is NOT met; the
fund_below-only form is expected true (it is `compat_trap_lt` applied to a proof of `prim_compat_statement`, the same premise
shape as the merged `JitKRefCompatClo.app_rel`) and awaits kref-prim or an orchestrator decision. Not the closure
compatibility lemmas or the fundamental property, so `OB-JIT-LOWER-FRONT` stays open.
Fifty-seven are in `rocq/JitKRefBase.v` (branch `p2/kref-base`), KRef's structure: the JitKRef statements `VRel_down`,
`VRel_wext`, `ERel_down`, `KRef_scope`, `sealed_stable` and `storehas_stable`; monotonicity of SRel, KRel, ERel, EnvRel
and ObsT (two listed directions, SRel and ObsT up in wext, are false and refuted in Rocq: `SRel_wext_refuted`,
`ObsT_wext_refuted`); source anti-reduction with and without an IO prefix and in ERel form for let, if, cond, type, a named
call of a D function and lambda application; target-step reduction with a target resource step matched by the source's;
wrong-state matching; the bind lemma `ERel_push` and a KRel lemma for every frame kind, the application frames under
`AppRel`, which is a hypothesis there; and `world_closed`, world reachability for the `=` budget (S-local lok does not follow from SRel: `SRel_lok_refuted`). No compatibility lemma
and not the fundamental property, so `OB-JIT-LOWER-FRONT` stays open.
Five are in `rocq/JitEqBudget.v`: the old `=` budget statement refuted, `=` on jit numbers a partial equivalence, and
the budget lemma reduced to one cell step, whose core is proved in `JitEqBudgetCore.v` (below).
Thirteen are in `rocq/JitEqBudgetStep.v`: the step of the core's induction on a closed set of cells, under S-relativized
hypotheses only (`closed_in`, `lok_in`; no global lok). For the least-budget true pair x, y: their pointers are identical and
their other leaves agree (`least_true_pointers`; the `ShenJitEqStepNotLeast` mutant, without the least premise, is rejected), the
surgery redirecting y to x keeps the rest closed (`closed_after`), it simulates at the same budget (`same_budget_sim`) and back
with one more (`shifted_sim`), and `step_settled` carries settledness from S minus y at n to S at n + 1. The base case is proved
in `JitEqBudgetWalk.v` (below) and the assembly in `JitEqBudgetCore.v`.
Eight are in `rocq/JitEqBudgetWalk.v`, the core's base case (branch `p2/eq-walk`): for a set S of cells closed under the
pointers in their data, with no two distinct cells ever comparing true, a cell comparison that answers at some budget
answers the same at budget |S| - 1 (`walk_bound_pred`, and `walk_bound` at |S|). It needs only that number equality is
symmetric and transitive, and no lok hypothesis. `walk_bound_needs_trans` refutes it without transitivity (the
tolerance profile on h5). The step case is the `JitEqBudgetStep.v` work above.
Proof mutants `ShenJitWalkNoTrans`, `ShenJitWalkTolInstance` and `ShenJitWalkPrefixAbove` are rejected.
Three are in `rocq/JitEqBudgetCore.v`, the assembly (branch `p2/eq-assembly`), which discharges `OB-JIT-EQ-BUDGET-CORE`:
`eq_budget_closed` says that for number equality symmetric and transitive, a heap h and a NoDup set S of allocated cells
closed under the pointers in their data, = on two operands whose pointers lie in S answers at every budget >= |S| + 1 what it
answers at |S| + 1 (no lok hypothesis, global or S-local; induction on |S| with the step and `walk_bound`, and a case split
on the decidable goal, so no excluded middle). `eq_core` is `eq_core_statement (jit_rules sealed)`, with S all cells, and
`eq_budget` is `JitLowerEquiv.eq_budget_statement sealed`, through `eq_budget_from_core`. Proof mutants `ShenJitEqCoreNoTrans`
and `ShenJitEqCoreNoClosure` are rejected.
Comparison with the binary is test evidence. Shen/JIT is not verified.

Pass split, wave 1b (opt-in, not gated): `rocq/JitNorm.v` and `rocq/JitNormStage0.v` model `lower.shen`'s normal form,
its erasure to KLambda, and a judge of the emit pass alone on witnesses `capture_passes.sh` regenerates. 133 of 955
stage 0 definitions are accepted at 0.6 (131 of 950 at 0.4), all with the front end unchecked: acceptance relates code to the erased witness, not to the source body.
Their statements are not in an audit count; `scripts/check-shen-jit-norm.sh` checks that they use no axioms.
