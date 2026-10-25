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
| Wrong compiler instructions and false equations rejected | Fifty Rocq mutation cases, including eight altered native constructors | Tests of the gates, not a completeness claim |
| Full Shen-Scheme or any other port correct | OPEN | No verified-port claim |

The audit enumerates 231 theorems/corollaries/bridge goals and prints their exact
signatures and assumptions. It requires no custom axioms and independently
rechecks their compiled proof objects. The rule-validity premise of
`check_sound_under_rules` is an explicit theorem hypothesis, not a discharged
claim about arbitrary imported equations.

`buri.obligations` is a static inventory. `proof-available` means an artifact
exists; it is not acceptance of the current checkout. Only a fresh successful
gate run produces `_build/report.json`. Reports are unsigned and retain exact
source hashes, toolchain identity, theorem log, and remaining assumptions.

The native validation lane has 78 additional Rocq regression examples and thirteen
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
provenance, the broader Shen evaluator and proof checker remain open. Reverse machine-to-evaluator simulation and
divergence correspondence are not claimed. Chez compiler/runtime verification
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
