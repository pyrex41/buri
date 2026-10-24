# Trust boundary

## Independent Rocq lane

Rocq/Coq's kernel checks the formal proofs. The proof scripts contain no custom
axioms, `Admitted`, or native-computation escape hatches. `coqchk` independently
replays the compiled proof objects. Its binary, OCaml toolchain, standard
library, operating system, and hardware remain trusted. The mathematical
statements and semantics must still be reviewed for fidelity to Shen.

The equality-checker theorem has an explicit hypothesis: each supplied rule is
valid in the chosen interpretation. It does not make arbitrary equations true.
The arithmetic model supplies concrete total definitions; each exported Shen
defining equation is separately checked against those definitions.

`rocq/Lambda.v` uses de Bruijn variables and a smaller syntax than the named Shen
reference interpreter. Its generic fuel/determinism/lowering theorems are about
that precise Rocq definition. Their correspondence to `shen/klambda.shen` is
OPEN. A similar-looking model is not verification of the executable interpreter.

## Shen lane

The equational kernel trusts its fixed sorted signature, defining equations,
equality replacement, universal instantiation, and structural induction for the
free expression constructors. Its own implementation has tests, not a completed
Rocq refinement proof. Acceptance also trusts Shen-Scheme, Chez, and the host.
The independent Rocq compiler theorem does not retroactively verify this kernel.

The reference normalizer is outside proof acceptance. Changing it can break an
execution demo without creating a proof. The compiler/evaluator equations are
shared data, so there is no second handwritten arithmetic compiler hidden behind
the proof. Proving the normalizer correctly implements those equations remains
an implementation obligation.

The wider KLambda interpreter uses tagged inert input. It rejects unsupported
forms, duplicate global names, malformed literal values, and direct host code.
It models an immutable global definition table, not dynamic function rebinding.
Integers use the selected host's arbitrary-precision exact arithmetic and decimal
printing profile; representation correctness remains an assumption. Integral
source spellings may be canonicalized by the Shen reader before the checker sees
them. Floats, ratios, NaNs, infinities, and closure equality are outside the profile.

## Crossing between lanes

The bridge exporter is untrusted as a theorem producer: a false emitted equation
is rejected by Rocq. However, the assertion that its emitted term faithfully
represents the loaded Shen source is still trusted. A bad exporter could omit
or alter source while emitting an independently true equation. Hash binding,
committed output diffs, 18 equation checks, and negative tests improve review;
they do not prove translation correctness. See PLAN B04 for the required proof.

The two compiler theorem statements are regenerated too. Changing the source
claim cannot silently reuse a proof about another conclusion. Nevertheless,
exporter correctness is required for a complete source-to-Rocq guarantee.

The original native-output AST exporter is retained as a regression cross-check.
A required raw-capture path now moves syntax decoding and variable resolution
inside Rocq. Its generic codec proves full consumption, round trips, and exact
input identity. Its resolver and symbolic normalizer have preservation theorems.
The acceptance theorem validates every supplied record in order and the release
requires all 12 expected schemas. See [CAPTURE.md](CAPTURE.md) for the formal scope.

The raw source/target grammar and named integer semantics are now reviewed Rocq
specifications, rather than a semantic transformation delegated to Shen. The
capture encoder now has a source-linked program proof: Rocq checks the exact
loaded source against a rendered first-order program and proves termination,
unique canonical output, and a decoder round trip. This does not establish native
execution preservation. Reader/define compilation, primitive contracts, native
representations, loading without rebinding, and the backend/runtime remain open
or assumed. The registered KLambda output for the three encoder definitions is
now translation-validated against their proved bodies, with a generic named
execution and recursive-call preservation theorem. This assumes the fidelity of
the `ps` metadata and the inert tagging adapter; it does not inspect native code.
See [ENCODER.md](ENCODER.md) and [FRONTEND.md](FRONTEND.md). Capture origin, source/port provenance,
exact-byte packaging, and correspondence to real Scheme primitives also retain
their trust boundaries.
This is instance translation validation, not universal port preservation.

## Artifacts and execution

`load`, `eval`, FFI, and redefining functions execute trusted code. This repository
is not a sandbox. The native port adapter deliberately runs trusted generated
fixtures and is not imported by `buri.shen`. Do not expose it to untrusted input.
Lists named `accepted` are forgeable. They carry no authority: rerun the checker
on the exact evidence and theory. `buri.evidence-kind` only classifies a label.

Budgets cap proof rewrite counts or evaluator tree depth, not total allocation,
input size, elapsed time, or machine stack. Budget exhaustion means unknown,
never divergence, unsafety, or a catchable language exception. Process failures
must fail the gate; the wrapper also requires a success marker because a Shen
launcher can print an exception and return exit code zero. Export inputs are
removed before generation and an explicit completion marker is required. A stale
file or missing proof dependency cannot satisfy the export or mutation gate.

The report binds source and selected host bytes. It does not prove that the host
binary was built from the reviewed upstream source. Bootstrap checks archive
identity, not compiler correctness. Loading PR #117 establishes which checker
code ran, not that the optimization is sound. The Búri checks currently run under
`tc -`; the Rocq proofs carry the independent logical assurance.

## Audited assumptions

[TRUST-AUDIT](TRUST-AUDIT.md) separates the outstanding obligations and their
closure criteria. Two assumptions cannot be used without qualification: native
halving is not exact on all naturals, and `ps` metadata can change independently
of executable behavior. `CaptureTag.v` now proves the typed transport protocol
lossless, but does not prove the native tagging adapter implements it.

## Observed target lane

The [observed loader](OBSERVED.md) validates actual paired frontend/backend
outputs while installing that captured Scheme value in a fresh controlled
image. It does not depend on `ps` metadata. Its observer fidelity, reader,
tagging/serialization execution, primitive contracts, immutable transitive
bindings and Chez runtime remain assumptions. Administrative sequencing and
successful target behavior are now proved in the admitted target semantics.
