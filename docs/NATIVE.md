# Captured native execution and the remaining Chez boundary

The sealed lane now has execution proofs for its actual generated constructor
and exact private shim bodies. The earlier dependency-resolution theorem is
supplemented by an instruction machine that permits arbitrary ambient rebinding
between instructions. This narrows the assumptions; it does not verify the
implementation of Chez or claim a verified Shen port.

## Constructor code, not a parallel specification

`shen/observe-constructor.shen` reads `shen/sealed-encoder.shen` once and feeds
that same string to the reader. It submits each frontend result to the actual
backend, evaluates the exact generated Scheme, then records the successful
installation. It does not read `ps`. The saved source is compared byte for byte
with the checkout, and all ten generated definitions are captured.

The new syntax transport distinguishes native booleans from symbols. A native
`#t` in a generated `cond` is not a variable named `true`. Strings, integers,
symbols, booleans and pairs have distinct tags. The adapter and its execution
remain provenance assumptions, with native regressions and exact packaging
checks; they are not made trustworthy just by having a transport format.

`ConstructorInput.v` contains the literal capture. Rocq decodes it into the
expression grammar in `Native.v`. Twelve checked goals establish:

- The decoded program is exactly the supplied capture, with ten definitions.
- For arbitrary supplied names, arguments and bodies, the actual definition
  constructor preserves those values in the private lambda.
- All three observed target records retain their order and exact bodies.
- The actual helper/import constructors produce the pinned templates.
- The actual program constructor assembles the seven helpers and three
  supplied targets into the intended `letrec`, for arbitrary supplied bodies.
- Missing records and malformed definitions produce the specified modeled
  errors, including owner and message.
- The authority request quotes the supplied program and selects the exact
  restricted library environment.
- The actual executor and entry bodies have exactly the intended call shapes:
  one host `eval` of the request; assembly followed by that executor.

The constructor uses its own captured recursive append implementation. Its
proof does not assume that Shen's global `append` has the required behavior.
The error/IO exporter and host activation are not proved executable inside the
pure interpreter. Executor/entry shape proofs expose the activation seam; they
do not prove the semantics of host `eval` or `environment`.

Source/reader/compiler provenance and binding stability during trusted
construction remain assumptions. These proofs validate the captured target;
they are not a universal source-to-Scheme compiler theorem.

## Exact private helper contracts

`NativeHelpers.v` parses the exact pinned shim syntax, rather than giving an
unrelated mathematical function the same name. It checks that parsing produces
the program being proved. Its mathematical primitive layer distinguishes exact
integers, exact fractions, inexact values, booleans, symbols, strings, finite
pairs, characters and opaque handles. Unsupported types/operations are explicit.

| Private helper | Proved behavior in the admitted primitive semantics |
|---|---|
| `non-rational-/` | Exact division for positive integer denominators |
| `kl:floor` | Exact integer identity and rational floor |
| `kl:=` | Integer equality |
| `kl:_scm.assert-boolean` | Boolean identity; specified error for every other represented type |
| `kl:buri.exact-integer?` | Exact integer acceptance, inexact rejection, and fraction integrality classification |
| `kl:symbol?` | Symbol classification across all represented value kinds |
| `kl:str` | Canonical integer spelling and symbol spelling |

The sealed division helper now preserves exact rational results. It deliberately
does not reproduce the stock `non-rational-/` conversion to inexact arithmetic.
`natural_halving` proves that division by two followed by floor returns
`Nat.div2` for every natural input. The native regression checks the formerly
failing `9007199254740995` case. The stock global encoder retains its original
behavior and its existing counterexample characterization.

The helper proofs discharge whole-shim assumptions relative to the explicit
primitive contracts. They do **not** prove the algorithms in Chez's `/`,
`floor`, integer arithmetic or printers. Numeric representation must respect
Chez's canonical exact-number representation; arbitrary noncanonical fractions
in the mathematical datatype are not claimed to be native values. Inexact
values are classification tokens here, not a floating-point arithmetic model.

## Instructions and concurrent rebinding

`NativeRuntime.v` supplies a lexical instruction machine over the same decoded
expression grammar. Its frames implement left-to-right arguments, conditionals,
lexical lets, short-circuit conjunction/disjunction, recursive private calls,
primitive calls and explicit errors. Argument failures stop before subsequent
arguments. Unsupported execution, exhaustion and raised errors remain distinct.

The world is separate from private code, lexical environments and continuations.
An interleaving may replace the entire ambient world between any two
instructions. The projection theorem erases those updates into a valid private
execution trace. Deterministic instruction steps then imply that two completed
executions from the same private state return the same value under any such
interleavings. This is an operational proof, not just equality of dependency
names. It assumes that a world update cannot mutate the private cells themselves.

The helper contracts are also checked directly on this machine. A computed
helper result determines any completed interleaved helper result. The exact
decoded ten-definition capsule is loaded into this machine too, with checked
helper coverage and executions for integers, symbols, pairs and type errors.
`sealed_native_concurrent` instantiates the arbitrary-input, arbitrary-world
completed-output uniqueness theorem on that captured capsule.

This is not a liveness theorem: a scheduler can starve computation forever.
There is no theorem yet equating every execution of the earlier abstract codec
with this lower-level machine. The existing abstract codec termination theorem,
the new operational helper theorems, and the checked concrete capsule executions
retain their different scopes. Twelve semantic regression examples cover
evaluation order, shadowing, truthiness, typed booleans, errors and unsupported
forms. They do not stand in for missing universal refinement proofs.

## Functional evaluator to instruction execution

`NativeSimulation.v` connects the two Buri engines for arbitrary private
programs, environments and expressions. Every functional result other than fuel
exhaustion has a finite machine execution with exactly that result. Success
traces preserve any continuation stack. Error traces may retain unused frames,
which the machine never resumes; owner and message remain exact. Unsupported
execution stays unsupported. The argument-list proof preserves order and stops
at the first failure, including recursive calls and lexical shadowing.

Fuel is deliberately not equated: the evaluator counts nesting depth while the
machine counts transitions. The theorem supplies a sufficient finite machine
budget. Exhaustion does not imply divergence and is excluded from this transfer.
A terminal machine result under any finite ambient rebinding schedule agrees
with the evaluator result, including errors. No scheduler fairness is assumed
or proved. This is a forward simulation; a converse and divergence equivalence
are not established.

`NativeApplications.v` applies the general theorem to the captured constructor:
assembly for arbitrary three target bodies, authority requests for arbitrary
program syntax, and both specified malformed-input errors now have machine
execution proofs. These transfer the existing captured-code theorems; they do
not introduce a hand-written stand-in constructor. Host activation remains
outside the pure interpreter, as before.

This closes the evaluator-to-machine link for completed evaluations. It does
not yet connect the older abstract codec to `Native.eval` for every datum.
Chez compiler/runtime internals are explicitly deferred; these new obligations
and proofs concern Buri's own engines and captured Shen-generated code.

## What remains trusted

The required primitive boundary is reduced from 29 to 27 roots by removing
unused `eq?` and `inexact` imports from the sealed capsule. The constructor's
symbol-only `eq?` use has a separate restricted contract; pointer equality for
arbitrary objects is not modeled as structural equality.

The remaining implementation obligations are:

1. Relate actual Chez execution, lexical closures and restricted library
   environments to the proved instruction machine, including allocation,
   exceptions and numeric/string representation.
2. Verify the 27 primitive implementations and their transitive runtime
   dependencies against the explicit contracts. Printers, exact arithmetic,
   GC, compiler and native artifact execution remain below this boundary.
3. Connect all admitted composite encoder operations and the abstract codec
   to the lower-level machine universally. Concrete executions are not that
   theorem.
4. Prove source/reader/compiler/capture and native tagging correspondence.
   Exact bytes and captured-target proofs cannot prove provenance.

The legacy identity guard is still unverified and is not called by this lane.
Concurrent mutation of input objects or replacement of the caller's procedure
handle is excluded. None of these assumptions is silently converted into an
axiom: `Audit.v` and `coqchk` replay all the proof objects independently.

Eight new constructor mutations must fail proof compilation: altered lambda,
expanded authority, boolean/symbol confusion, altered executor, altered entry,
reversed assembly, omitted definition and extra definition. The gate also
rejects stale constructor outputs and mismatched literal packaging.
