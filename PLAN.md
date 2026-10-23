# Búri implementation and verification plan

## Goal and release standard

For each admitted fragment and pinned port, establish that all observable target
behaviors correspond to allowed source behaviors, under named representation,
resource, and host assumptions. A completed port claim must identify the exact
compiler/runtime implementation, not a nearby model of it.

Búri supplies language and implementation correctness to Vör. Vör supplies
business correctness. Their composition must bind the exact semantics, admitted
program, and runtime artifact. Neither project may inherit the other's tests as
proofs.

Current implementation includes B00 and reference demonstrations within B01–B03.
It does NOT complete their generic implementation-correspondence obligations.
Every exit below requires the named code and replayable proofs, hostile cases,
exact identities, and documented residual assumptions.

## B00 — Executable foundation (implemented)

Artifacts: closed arithmetic theory in Shen, sorted rewrite/induction checker,
explicit compiler certificates, independent Rocq arithmetic/equality/lexical
models, generated equation bridge, native Shen-Scheme adapter, tests and report.

Evidence: generic reference compiler preservation; no stack faults; arithmetic
adequacy/determinism; equational checker soundness under valid rules; lexical
fuel stability/determinism and let lowering. 18 defining-equation bridges and two
claim bridges. Twelve actual Shen-Scheme compiler-output schemas have quantified
integer-equivalence proofs under decoder/target-semantics assumptions. Tests remain separate. See docs/STATUS.md for exact counts/scope.

Open even here: proof that the Shen implementations implement the Rocq models,
proof of exporter/source correspondence, and any real-port preservation theorem.

## Current advance: raw native-capture validation

B01 now has a canonical finite-datum wire codec with proved round trips, exact
input consumption, and injectivity. The admitted arithmetic grammar has a generic
name-resolution preservation theorem covering shadowing and lexical extension.
A proved symbolic normalizer handles real compiler-generated administrative lets.

B04 now has a required native validation path that receives only captured data
and performs semantic decoding and comparison inside Rocq. Its acceptance theorem
binds the supplied string to every checked record in order; the release requires
12 records. Exporters no longer supply semantic indices or ASTs for this path.
The Shen serializer/source-object correspondence, capture provenance, broader
Shen evaluator, proof checker, and runtime remain open. The original Peano
arithmetic equation exporter retains its own translation obligation.

See docs/CAPTURE.md. These results close specific initial-fragment gaps; they do
not complete B01/B04 for the full KLambda language or prove the whole port.

## B01 — Shared syntax and semantic identity

Add canonical algebraic syntax for KLambda, closed environments, primitive
inventories, outcomes, and observations. Formalize the same representation in
Rocq and Shen. Specify symbols separately from variable and function references.
Resolve named-to-de-Bruijn correspondence with capture-avoiding substitution.

Prove parser/decoder round trip, name-resolution soundness, well-scopedness,
canonical identity, and rejection of malformed artifacts. A parser must return
inert data; it must never load an artifact's declarations into its own root logic.

Hostile cases: shadowing, variable capture, duplicate binders, Unicode/byte
confusion, altered primitive identity, mismatched signatures, cyclic inputs.

Exit: one documented canonical source identity and mechanically checked syntax
correspondence for the initial fragment. Hash equality alone is not semantic
preservation.

## B02 — Reference evaluator adequacy

Connect the Shen normalizer and lexical interpreter to the Rocq semantics.
Extend beyond the present arithmetic demonstration to closures, closed named
recursion, partial/oversaturated application, exceptions, and freeze/thaw.
Specify missing definitions, wrong arity, improper lists, and primitive errors.

Prove simulation/adequacy, deterministic outcomes, budget stability, and explicit
partiality. Do not assert termination for unrestricted recursion. For terminating
subfragments, prove totality and well-founded measures separately.

Hostile cases: evaluation-order changes, wrong captured environment, catching
budget exhaustion as an exception, confusing a function symbol with a global
variable, dropping a recursive error, forcing an unused branch.

Exit: exact executable evaluator definitions have a correspondence theorem.

## B03 — Proof checker implementation correctness

The current Rocq certificate checker is proved sound, but it is not the Shen
rewrite/induction checker. Either align their representations and prove the
Shen implementation refines it, or generate both from a verified common kernel.
Prove path replacement, sorted substitution, lemma environments, induction-case
coverage, freshness, and weakening/instantiation. Include malformed artifacts.

The structural induction rule must be justified for the declared free datatype;
user-supplied recursive equations are not automatically terminating definitions.
No artifact can introduce the axioms that make itself pass.

Hostile cases: circular lemmas, omitted constructors, non-subterm hypotheses,
variable capture, wrong sorts, substitution collisions, theorem substitution,
forged `accepted` records, and changing trusted rules after a proof.

Exit: acceptance by the bound Shen checker implies the formal judgment.

## B04 — Verified bridge and source binding

Replace the presently trusted Shen-to-Rocq exporter correspondence with a proved
encoding/decoding relation or an independently checked translation certificate.
Bind source, signature, definitions, theorem, dependencies, and proof together.
Prove that every admitted source rule is accounted for; do not merely prove that
all emitted rules happen to be true.

Hostile cases: omitted rule, changed theorem, unmentioned primitive, reordered
arguments, silently strengthened precondition, exporter replacing source with a
true but unrelated expression.

Exit: a source edit cannot retain proof authority through a faulty translation.

## B05 — Actual Shen-to-KLambda front end

Pin the upstream Shen 43.1 compiler/kernel and define its admissible source
forms. Formalize pattern matching and ordered clauses, guards, macros, packages,
function application/currying, and declaration environments. Generated KLambda
must retain exact behavior and specified error outcomes.

Start with translation validation for each admitted compilation, then prove
reusable passes. Tie any reconstructed compiler model to the actual source.
System S's use of the compiler makes the same obligation relevant to proof code.

Exit: an actual admitted Shen definition reaches verified KLambda with checked
preservation, not merely matching examples.

## B06 — Shen-Scheme backend preservation

Target the pinned `src/compiler.shen`, beginning with literals, variables, lambda,
application, if, and let. Define the relevant Scheme target semantics. Give
closures, environments, primitive calls, and exceptions explicit relations.
Cover `order-call`, nested-let rewrites, direct/indirect application, currying,
and optimizations only as their preservation proofs are supplied.

Use the basic let/lambda theorem as a lemma, not as evidence that the whole
`emit-let` implementation is verified. Extend translation validation or prove the
actual backend, with unchanged source identity.

Exit: semantic refinement for a useful fragment of the real Shen-Scheme compiler.

## B07 — Primitive representation contracts

Prove exact integers, floating numbers (as a separate profile), equality,
strings/bytes, symbol interning, lists, vectors, errors, and global bindings.
Differentiate pointer identity from structural equality and immutable from
mutable values. Numeric conversion and division need explicit semantics.

Hostile cases: float/bignum mixing, overflow, NaNs, aliasing, equality of cycles,
invalid indices, exception payload conversion, and mutation through an alias.

Exit: primitive implementations preserve the formal contracts under named host
operations. An unproved host primitive remains an assumption in every consumer.

## B08 — Mutation and effects

Extend semantics with stores, vector allocation/mutation, separate global
namespaces, I/O requests/responses, and explicit environmental nondeterminism.
Model exceptions that occur after effects. Introduce frame/ownership invariants
and proof rules justified against the store semantics.

Exit: representation relations and simulations cover observable effects and
error paths, with no claim that a timeout proves no effect occurred.

## B09 — Dynamic evaluation and redefinition

Model `eval-kl`, loading, function replacement, package/macro changes, and live
images. Admission records must close over the bindings that affect the theorem.
Compatible and sealed compilation modes need different, explicit contracts.

Hostile cases: post-proof rebinding, stale compiled references, changed arity,
changed primitive table, and a checker image loading untrusted datatype rules.

Exit: sound invalidation or versioned admission for dynamic behavior. Sealing a
fragment is acceptable; silently treating unrestricted Shen as sealed is not.

## B10 — System S and upstream checker changes

Formalize the supported typing judgments, assumptions, user datatype rules,
Prolog side conditions, and rule elaboration. Prove the admitted rule discipline
sound relative to the semantics. The default language's extensibility must not
be confused with a proof that every user-added rule is sound.

For PR #117, prove the optimization preserves judgments/search behavior under
stated preconditions; a pinned overlay and 134 canonical tests are not that proof.
Consider proof certificates so search can evolve outside the acceptance root.

Exit: the specific System S behavior used for proof checking has justified
implementation and rule-extension boundaries.

## B11 — GC, tail calls, runtime resources

Model allocation, roots, forwarding/moving objects, write barriers, and foreign
references for a selected runtime. Prove representation invariants through GC.
Treat tail-call behavior and bounded-space execution separately from extensional
function equality. Define out-of-memory, host stack overflow, and interruption.

Exit: the promised resource/memory guarantees have theorems, or remain explicitly
excluded. Mathematical termination never implies unlimited physical resources.

## B12 — Compilation below Scheme

Choose and justify the bottom boundary: trusted Chez; a verified lower compiler;
or proof/translation validation of the deployed machine code. A proof of Scheme
emission does not prove Chez, its runtime, or the CPU model.

Bind binary artifacts, bootstrap compilers, options, linked libraries, and
runtime configuration. Reproducible builds help identity; they are not compiler
correctness. Preserve both successful and exceptional behaviors.

Exit: a concrete end-to-end claim identifies the lowest proved layer and every
remaining assumption. Never label it unconditional bug-freeness.

## B13 — Additional ports

Add Lua/LuaJIT, Go, Common Lisp, LLVM, and BEAM lanes one at a time against the
same versioned source semantics. Each needs its own value/store relations,
compiler preservation, primitive proofs, and host trust inventory.
JIT traces, specialization, concurrency, and foreign calls have separate proof
obligations. Differential execution finds counterexamples; it does not discharge
these universal obligations.

Exit: a second real port meets the same defined fragment contract, enabling
business proofs to transfer through independently checked preservation theorems.

## B14 — Vör integration and release

Define a machine-readable contract that Vör can consume: semantic profile,
exact program/environment, port artifact, preservation theorem, and assumptions.
Compose Vör's business invariant theorem with Búri's implementation theorem.
Refuse profiles with missing language forms or weaker effect/error guarantees.

A reviewer command must replay foundational proofs independently, validate source
and binary identities, execute admitted programs, and reject stale or substituted
proofs. Reports retain formal-model, implementation-refinement, ground-check,
sampled-test, assumed, and open categories.

Exit: at least one real Vör program runs on a port with a checked preservation
chain to a precisely named lower trust boundary.

## Priority

Close B01–B04 before expanding the claim surface. In parallel conceptually,
B05/B06 may produce translation-validation evidence for the pure fragment, but
cannot bypass the source-correspondence obligation. B07–B12 expand toward the
real runtime; B13 follows shared-contract stability. No amount of test volume
or proof-script volume changes an open obligation into a theorem.
