# Implementation correctness: contract and work ledger

The target is observational preservation for the actual pinned implementation:
for every admitted Shen program, source execution and its compiled target agree
on values, exceptions, state transitions and externally visible effects.
Termination and divergence need separate statements; finite fuel exhaustion is
not a source-language exception. Resource limits, concurrency, and durability
must be named rather than inferred from a value-preservation theorem.

Búri has **not** established this whole-system theorem. The entries below are
implementation-linked components of it. Chez internals remain deferred; that
choice does not make the Shen compiler, wrappers or observer implicitly correct.

## Prior component proofs

| Actual implementation | Checked claim | Remaining boundary |
|---|---|---|
| `non-rational-/` from `src/primitives.scm` | Independently parse the exact extracted Scheme source; integral exact quotients pass through, fractions delegate to the supplied rounding operation; its failures propagate | Positive-denominator exact input profile; Chez arithmetic, floating-point rounding, all other numeric representations and exceptions remain contracts |
| Búri's existing exact private division/floor helpers | For every signed integer numerator and positive integer denominator, composition returns mathematical floor division | Mathematical primitive/representation model, not a proof of Chez internals |
| Captured `_scm.fresh-call-variable` | Under a constant-symbol generator and specified symbol-occurrence operation: an absent candidate is accepted, a colliding generator exhausts at every finite fuel, every successful candidate is absent, and binding it preserves existing symbol lookups | General changing/erroring generators and native `occurrences` implementation are not proved |
| Captured `_scm.order-call` and its five dependencies | An exact two-computation syntax instance transforms to the checked let/call; that transformation preserves arbitrary modeled runtime operations, state, errors and traces | Captured transformation result is a closed instance; generic preservation covers two nullary computations. Arbitrary argument lists, lexical operators, closures, and all pass branches remain open |
| Captured `buri.observe-forms` plus installer | Three arbitrary valid translated definitions compile, activate and publish in source order; exact complete traces and final record lists are proved | Frontend/backend translation and native activation remain operations with explicit supplied responses |
| Same captured loader, failure paths | First or second frontend failure stops subsequent work; third backend failure preserves the two completed records and does not activate/publish the failed target | No transaction rollback of already installed functions or arity changes; remaining failure positions and activation failures need full composition coverage |
| Captured pinned `read-file-as-string` override | Construct `home-directory ++ filename` and exactly forward the Chez reader's returned value, failure, state and trace | Correct home lookup, native execution and Chez reader behavior remain contracts; no concurrency or filesystem durability theorem |

`StockDivision.v`, `OrderCallCorrect.v`, `ObserverPipeline.v`, and
`IOReadCorrect.v` contain the statements. The audit prints their hypotheses and
checks that no custom axioms are used. Supporting lemmas are checked by Rocq and
independent `coqchk` replay too.

The ordering theorem uses distinct evaluator budgets for source and target;
introducing a let changes interpreter nesting depth. It does not equate fuel
with native instruction counts or running time. Every runtime effect handler is
allowed to fail or change the modeled world. Native IO samples are separate
from these universal model claims.

## Numeric finding: what is and is not a bug claim

The pinned wrapper explicitly calls `inexact` when division yields a noninteger.
Thus `floor (/ 9007199254740995 2)` can yield `4503599627370498` instead of the
mathematical `4503599627370497`. This disproves the encoder's required unrestricted
exact-halving contract on the stock path. It does **not**, by itself, establish
that the port violates Shen's permitted numeric specification. Calling this an
unqualified Shen language bug would overstate the evidence.

The private exact codec path repairs that encoder requirement. We have not
silently changed the port's numeric semantics or submitted an upstream patch.
Stock negative-denominator arithmetic is tested natively but lies outside the
current mathematical `Native.ratio` profile; `Unsupported` there is a model
boundary, not a prediction that Shen rejects that input.

## Evidence and reproducibility

Full upstream `compiler.shen`, `primitives.scm`, and `overrides.shen` are pinned by
Git blob identities and retain their licenses. The lineage gate checks extracted
function bytes. Only existing compiler package qualification is permitted for
the ordering helpers. The division and read override retain their upstream
bodies. Source identity is not a proof that the downloaded native executable
was built from that source.

The gate freshly compiles and captures the ordering helpers and read override,
regenerates literal Rocq inputs, independently compares their bytes, then checks
the implementation-linked proofs. Tampering tests change the fresh-name guard,
reverse operation, frontend operation, fractional branch, and read path builder;
all must be rejected by proof compilation. Missing tools/imports cannot count as
rejected proof mutations.

Thirty-nine additional native assertions cover numeric signs, precision loss,
zero division, fresh-name collisions, classification, ordered state changes,
error short-circuiting, completed-prefix loader behavior, all 256 input bytes,
empty/missing files and home-directory prefixes. These are samples/regressions,
not universal native correctness proofs.

## Remaining implementation sequence and acceptance conditions

1. **Language contract.** Finish explicit KLambda semantics for computed calls,
   currying, closures, global value/function mutation, errors, strings, vectors,
   numeric representation and IO. Specify accepted representation relations and
   the observable trace. Keep unsupported constructs rejected. Acceptance:
   admission soundness and correspondence to the executable Shen semantics.
2. **Primitive wrappers.** Extend the source-linked numeric profile to all
   specified signs, exact/inexact representations and errors; cover equality,
   strings and vectors. Acceptance: actual wrapper execution refines each
   primitive contract, with a separate list of remaining Chez operations.
3. **Compiler pipeline.** Prove arbitrary `order-call-inputs` lists and changing
   generator hygiene, then symbol emission, let/if/cond, direct/computed calls,
   closures, exceptions, mutation, dynamic binding and tail calls. Compose each
   actual pass's theorem; validate exact artifacts where universal translation
   correctness is not available. Acceptance: one preservation theorem for a
   declared fragment, with a mechanically checked coverage inventory.
4. **Native execution relation.** Relate generated Scheme representations,
   environments, procedure lookup/installation and primitive calls to the
   semantic machine. Add reverse/termination/divergence correspondence rather
   than treating forward finite execution as equivalence. Acceptance: the source
   outcome is connected to actual admitted generated Scheme under named Chez
   contracts. Chez machine-code/compiler internals remain excluded.
5. **Whole observer and IO.** Prove the remaining loader failures and the full
   entry's higher-order call, source read/parse, metadata resets, encoding and
   all checked writes together. Connect byte/port wrappers and cleanup to Chez
   contracts; specify concurrent mutation, persistence and durability separately.
   Acceptance: success evidence identifies the exact executed source/target and
   its promised effects; every failure prefix is characterized.
6. **Shen frontend and proof machinery.** Prove Shen-to-KLambda preservation,
   then checker/admission soundness and actual checker correspondence for the
   supported rules. Extend loading, macros and dynamic evaluation only with
   explicit preservation conditions. Acceptance: accepted business-logic proofs
   survive the entire declared compilation/execution chain.

A milestone is complete only when its acceptance statement is proved about the
implementation or its outputs. A new oracle assumption, native regression,
source hash or theorem count cannot discharge that condition by itself.


## Current six-stage progress

[SIX-STAGES](SIX-STAGES.md) describes the newer general effect/freshness results,
reverse execution/divergence correspondence, complete loader failure summary,
all-value division wrapper contract, and the executable sealed congruence kernel.
The machine-readable `spec/six-stages.json` ledger is checked against the fresh
audit. All six full stages remain partial. The new congruence profile has no
artifact-supplied axioms and does not replace the original induction checker or
verify Shen's entire typechecker/compiler.
