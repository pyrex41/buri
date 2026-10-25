# Six-stage correctness program: checked progress and remaining boundary

The full objective is still open. `spec/six-stages.json` is the machine-readable
ledger: all six stages remain **partial**, with scoped theorem names and explicit
remaining work. A successful report requires every cited theorem to be in the
fresh audit. The ledger never infers stage completion from theorem counts.
Chez internals remain deferred at the user's direction.

| Stage | New checked result | Still required for the full stage |
|---|---|---|
| 1. Language contract | General first-order effect semantics: immutable lexical scope, exact state/trace/error outcomes, completed-fuel monotonicity; total typed certificate admission | Full KLambda closures, computed calls, currying, mutation, vectors and executable Shen evaluator correspondence |
| 2. Primitive wrappers | Actual stock division body for all input values and named division/classification/rounding responses; errors propagate; signed exact denominator normalization | The underlying representations and remaining community equality/string/vector wrappers; actual Chez primitives remain contracts |
| 3. Compiler pipeline | Fresh administrative let insertion preserves arbitrary operands and argument tails, all modeled outcomes/effects/traces; captured name loop handles changing/erroring generators | Composition through every actual `order-call-inputs` branch, occurrence/gensym implementation correspondence, remaining passes and higher-order code |
| 4. Execution relation | Both directions between evaluator and instruction machine for every private first-order model program, including errors/unsupported; pure-model divergence equivalence | General generated-Scheme/native representation relation beyond this core; native bootstrap/capture provenance |
| 5. Observer and IO | Exact combined behavior of the actual three-form loader for every frontend/backend/activation response, covering all nine failure positions | Complete higher-order observer entry, parsing/encoding/writes together, native IO/activation provenance and resource cleanup |
| 6. Proof machinery | Actual compiled Shen axiom-free congruence deriver agrees with the Rocq checker; raw admission and private-capsule soundness | Original EQ-1 induction checker, Shen typechecker/sequent rules, general frontend, macros/loading/dynamic evaluation |

## An executable, checked proof-kernel profile

`shen/equality-core.shen` implements reflexivity, symmetry, transitivity and
congruence over inert first-order terms. Its exact compiler targets are captured
and proved to implement `Equality.check []` for every typed certificate. Rule
instances are rejected: this profile has **no artifact-supplied axioms**. It
establishes congruences of uninterpreted terms, not general Shen business-logic
properties or arithmetic definitions.

`EqualityAdmission.v` supplies independent, rejecting typed admission. Successful
parsing recovers the exact original data, and every supported finite typed
certificate is admitted with enough depth. The public logical decision derives
its depth from the finite input's size; an insufficient caller-supplied depth is
not labelled an invalid derivation. The public verdict distinguishes data outside
the certificate profile from a well-typed invalid derivation and an accepted
equation. An accepted equation is valid for every interpretation of its constants,
application and variables. Host memory/time availability is not proved.

The native deriver returns **candidate data**, not an `accepted` authority token.
For example, a `refl` around an `eval-kl` payload remains inert candidate data;
the typed acceptance layer rejects that payload. It is never run as code.

`shen/sealed-equality.shen` builds a native checker with four private recursive
procedures and one private equality helper. The actual captured constructor is
proved for arbitrary four-definition inputs, then instantiated on the exact
checked kernel targets. Its parsed table has exactly the same lookup behavior
as the proved checker table. Entry wiring passes precisely the constructed
program and restricted environment to native activation.

The environment contains exactly seventeen Chez bindings/forms:
`lambda let let* letrec if cond and or quote eq? equal? null? pair? car cdr cons list`.
It grants no `eval`, `set!`, file opening or loading inside the checker. Static
checks cover both the normalized call inventory and the raw Scheme identifiers,
including binding scopes and syntax forms such as `cond`. Removing `cond` is
proved to fail the raw identifier check. Native tests separately reject requests
for unavailable capabilities.

**Compiler records are code authority. Certificates are data.** The factory is
fed by the controlled compiler-record producer, not by untrusted proof payloads.
Both complete four-definition captures reject omitted or extra records. The gate
captures the core and constructor in the same native process, builds the capsule
from those exact core records, and compares its core capture to the authoritative
literal input. Native activation itself remains the named Chez contract.

The private instruction model proves soundness under arbitrary ambient rebinding
steps. Native regressions exercise rebinding all four public procedures and a
synchronized hostile rebinding of the public deriver. Those regressions sample
native behavior; they do not prove the Chez implementation. Construction context,
actual capture identity, primitive/representation contracts and immutable input
data remain explicit assumptions.

## General effect and execution results

`EffectContract.v` proves environment congruence and preservation under a fresh
binding for arbitrary first-order expressions, external operations, states and
outcomes. Raised owner/message payloads and unsupported outcomes remain exact.
`PureEffectBridge.v` proves that the existing pure evaluator is precisely the
state-preserving, empty-trace specialization of that evaluator.

`CallRefinement.v` proves both directions of fresh let lifting for any operand and
any argument tail, under its explicit variable-freshness premise. Source and
target budgets can differ. This is a general semantic building block, **not** a
proof of every branch of the upstream ordering pass. Its stateful noncompletion
result means absence of a completed observation; an external operation may itself
report exhaustion, so that result is not called native divergence.

`NativeReverse.v` closes the previous reverse-simulation gap for the existing
pure first-order grammar. Every non-exhausted instruction result has an evaluator
witness, and conversely. Divergence is equivalence of exhaustion at every finite
budget under the pure primitive contracts. It is not an equality of instruction
counts and evaluator depth, or an OS resource guarantee.

`FreshSupply.v` executes the actual captured fresh-name loop against an arbitrary
stateful generator. Failed generator responses preserve their effects, successful
candidates are absent, and a finite supply reaches its first absent candidate
after any finite colliding prefix. Occurrence counting is still an explicit
contract. The generator/count interface is symbol based; non-symbol responses
are unsupported in this model, not a newly proved native rejection guarantee.

`ObserverTotal.v` composes the actual loader and installer for all response
combinations. Completed earlier installations/records remain when a later stage
fails; no transaction rollback is claimed. Compile/activate responses and their
noninterference with the record cell remain operation contracts. The exact
summary covers errors, unsupported operations and exhaustion distinctly.

## Regressions and limits

New regression cases include a capture-violating let transformation that changes
the result, fuel-depth changes, evaluator/machine infinite loops, changing name
supplies, generator errors, all nine loader failure positions, negative/zero
numeric inputs, certificate-rule injection and malformed data. Native checks
include large exact indices, nested proofs, retained loader prefixes, inert
payloads, authority rejection, and hostile rebinding.

The stress harness catches worker failures and signals completion on those paths.
An earlier test attempted to assign the imported `kl:=` binding; Chez correctly
rejected that immutable binding. This was a harness error, not a Shen bug. The
regression now targets mutable community function bindings.

The remaining acceptance conditions are in [CORRECTNESS](CORRECTNESS.md) and the
ledger. No full Shen/port/compiler/checker-correctness claim is made by these
scoped results.
