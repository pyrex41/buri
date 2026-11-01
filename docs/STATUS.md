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
glibc on each route, and recorded environment variables. This is identity
evidence only. It adds no theorem and does not change the audited count (357).
Shen-Scheme is a prebuilt binary trusted by hash. Rebuilding Shen-Scheme and Chez
from source, rebuilding Coq from source, pinning `/bin/sh`, and producing ARM
artifacts all remain open. aarch64-linux is declared in the flake but not built.
