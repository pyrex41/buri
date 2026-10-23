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

The native-output bridge captures `_scm.compile-expression` output for 12 fixed
schemas and emits source/target ASTs in `rocq/NativeOutput.v`. Rocq checks their
semantics for every integer input, not a finite input table. The source-to-AST
and Scheme-output-to-AST decoders remain trusted. So does the correspondence
between the modeled integer Scheme operations and Chez execution. This checks
those compiler outputs; it does not prove the compiler for every source program.
The captured input/output transcript and generated claims are committed and
regenerated on every proof run. A changed target operation is a negative test.

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
launcher can print an exception and return exit code zero.

The report binds source and selected host bytes. It does not prove that the host
binary was built from the reviewed upstream source. Bootstrap checks archive
identity, not compiler correctness. Loading PR #117 establishes which checker
code ran, not that the optimization is sound. The Búri checks currently run under
`tc -`; the Rocq proofs carry the independent logical assurance.
