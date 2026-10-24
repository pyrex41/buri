# Private lexical encoder capsule

The new lane removes the mutable-global identity guard from encoder execution.
It does not certify that guard or claim to verify Chez. The legacy
`buri.guarded-wire` API retains its sequential-only limitations.

`shen/sealed-encoder.shen` assembles the actual three observed Scheme target
bodies into a `letrec`, together with seven private helper lambdas. The result
is evaluated in `(environment '(only (chezscheme) ...))` and returns only the
private encoder procedure. Recursive calls and helper calls use lexical
bindings, not Shen global procedure cells. Keep that procedure in a local
variable and call it directly; replacing a global variable that stores the
handle is outside this guarantee.

Construction requires the trusted controlled load/validation workflow. Calling
`buri.make-sealed-encoder` with arbitrary records is **not** proof acceptance.
The constructor is execution tooling, never an inert certificate checker.

```shen
(let Encoder (buri.make-sealed-encoder (reverse (value buri.observed)))
  (Encoder [invoice 42]))
```

Load the observer and sealed module first, and obtain `buri.observed` through
`buri.observe-encoder`. `make report` regenerates the source snapshot, observed
pairs, capsule and proof input in a fresh process and checks the complete gate.
Construction and validation are trusted phases; racing changes to their own
code or evidence are not covered. Post-construction global rebinding cannot
reach the capsule's lexical cells, assuming Chez implements lexical scope and
its library environment correctly. No lock cooperation from redefining code is
required, and there is no pre/post observation window.

## Dependency boundary

All ten procedure bodies are traversed by the independent Rocq checker,
including unused branches and helper bodies. It understands lambda, recursive
lambda bindings, parallel let, sequential let*, conditionals, conjunction,
disjunction, quotation and named applications. Unsupported forms fail closed.
It checks the whole assembled capsule, not just a hand-maintained call list.

Every free identifier must be one of these 29 primitive roots:

```
eq? eqv? equal? null? pair? car cdr + - * / >= <
string-append string-ref string substring string-length char->integer
integer? exact? number? inexact floor boolean? symbol? symbol->string
number->string error
```

The exact import list is independently checked. Dynamic eval, global lookup,
mutation, thread creation, loading and environment access are absent. The
native restricted environment rejects unbound dependencies before returning
the procedure. Syntax imports are also explicit.

This is complete **application-level syntactic closure up to the primitive
boundary**, not the transitive implementation closure of Chez. Allocation,
strings, integers, exceptions, GC, library implementation, compiler, OS and
hardware remain trusted. The capsule contains no decimal-classification helper
chain or mutable Shen globals. Its private classification uses exact native
integers, its integer spelling uses radix-10 `number->string`, and symbol
spelling uses `symbol->string`. These are a new, explicit execution profile;
equivalence to every edge case of stock Shen primitives is not asserted.
Booleans, inexact numbers and strings as input datums are rejected. Supported
symbols must have byte-valued spellings. Pair inputs must be finite and must
not be mutated concurrently.

## What the proof establishes

`Sealed.v` proves the dependency guard sound and complete relative to its
syntactic traversal, absence of dynamic authority in accepted free dependencies,
and invariance of dependency resolution under arbitrary changes outside the
primitive boundary. It also proves exact structural equality for linkage and
soundness of the combined capture check.

`SealedInput.v` contains the exact bit capture. Rocq checks that:

- Both source and target records pass the existing translation validator.
- The three private encoder lambdas retain those exact target parameters and
  bodies, in order; assembly cannot substitute another target unnoticed.
- The seven private helper names and bodies match the fixed shim template;
  their abstract primitive contracts remain assumptions.
- All helper and encoder dependencies are closed at the declared boundary.
- The reported imports match the fixed import specification.

The existing generic target execution theorems apply in their admitted
semantics. The new noninterference theorem is about dependency resolution, not
an operational proof of Chez execution, scheduling or native machine code.
The seven shim bodies are traversed for dependencies but their implementation
of the abstract primitive contracts is not yet formally refined. Observer,
constructor and packaging provenance remain explicit assumptions; exact-byte
packaging and fresh regeneration are checked by orchestration.

## Native and negative evidence

The 270 native checks include a condition-variable rendezvous: a second Chez
thread poisons the global encoder binding and keeps it poisoned until calls to
the private capsule finish. The test verifies both that the global binding is
poisoned and that the capsule returns the expected values, then waits for the
worker to restore the binding. It also tests rebinding every encoder entry and
classification helpers, forbidden imports, and all 256 byte inputs at counts
0 through 8 against a subtraction-only oracle. These are tests, not proofs of
thread scheduling or primitive correctness.

Seven malformed capsules must fail actual Rocq proof compilation: unknown
dependency, eval dependency, mutation form, changed target, changed helper, omitted helper, and
expanded imports. An eighth orchestration regression rejects a mismatched
packaged capsule.

## Remaining work

The old guard's native implementation remains unverified, but this lane does
not rely on it. To turn the capsule's operational isolation into a native
execution theorem, refine the constructor/library environment and private shim
bodies, then discharge the 29 primitive contracts against Chez semantics.
Runtime internals below those roots still require their own implementation
proofs. Concurrent mutation of input objects is a separate problem from global
procedure rebinding and is not protected here.
