# KLambda semantics and observations (E2E-04, E2E-05, E2E-06)

Status: **in progress**, not complete. This wave adds a Rocq small-step
semantics for the whole canonical KLambda surface, a common observation and
behavior-refinement vocabulary, and the value/store model
([VALUE-MODEL](VALUE-MODEL.md)). It does not prove anything about
`shen/klambda.shen`, the Shen frontend, either port, or native code. A theorem
here is a theorem about this formal semantics only.

## Files

| Module | Content |
|---|---|
| `rocq/Observation.v` | Events (IO request/response pairs, signals, cancellation), outcomes, maximal behaviors, verdicts, refinement, generic LTS behaviors |
| `rocq/KLSyntax.v` | 36 primitives + 10 special forms (the canonical 46), resolved expressions |
| `rocq/KLValue.v` | Values, exceptions, store, semantic profile, equality, well-formed values |
| `rocq/KLSemantics.v` | `eval-kl` parser, one named rule per primitive, CEK-style machine, `next`, `step` |
| `rocq/KLMetatheory.v` | Progress, exact final/stuck states, determinism, closed system with environment, fuel evaluator theorems |
| `rocq/KLWellFormed.v` | Well-formed-state preservation |
| `rocq/KLTail.v` | Tail-position rules, stack-bound enforcement, bounded-space divergence of a tail loop |
| `rocq/KLBridge.v` | Embedding of the `Lambda.v` lexical fragment |
| `rocq/KLExamples.v` | Ground derivations under one concrete profile |
| `rocq/KLPort.v` | Per-port options on this machine; `next_r_agreed` proves the agreed options are exactly `next` |
| `shen/observation.shen`, `tests/observation.shen` | Executable Shen observation vocabulary and ground refinement checks |

## Observations (E2E-04)

Labels are `Tau` (the only unobservable step) or an observable event: an IO
event `EvIO request response` or an environment event (`Signal`, `Cancel`).
Requests: open, close, read (up to n bytes), write (byte list), clock, random.
Responses include partial reads (fewer bytes), `REof`, partial writes
(`RWrote n` below the request length) and `RFailed e`. Outcomes: `Normal`,
`Error` (structured payload), `ResourceOut heap|stack`, `Exit`, `Killed`,
`Cancelled`. Behaviors: `Terminates trace outcome`, `Diverges trace` (an
infinite silent tail, coinductive), `Reacts stream` (infinitely many events,
coinductive), `GoesWrong trace` (explicit undefined state). Evaluator verdicts
(`VDone`, `VWrong`, `VExhausted`, `VUnknown`, `VUnsupported`, `VRejected`) are
a separate type: budget exhaustion is never a behavior.

`refines` requires identical traces and constructor-matching outcomes with
related payloads. `refines_res` additionally lets a target stop with a named
resource failure after a prefix of a source behavior; this is the only allowed
early stop. Universal theorems: `refinement_preserves_errors(_res)`,
`refinement_preserves_events`, `refinement_preserves_failed_writes`,
`divergence_not_hidden`, `diverging_target_needs_diverging_source`,
`terminating_source_forbids_divergence`,
`strict_refinement_preserves_resource_failure`, `exhaustion_claims_only_prefix`,
and for deterministic systems `terminates_excludes_divergence`,
`wrong_excludes_divergence`, `terminates_unique`.

Open: time and randomness are inputs only through responses; no fairness or
input-availability premise for termination claims is stated yet; `Exit` has no
KLambda producer (no exit primitive in the core); allocation and publication
are not observable events (allocation failure is an outcome). The Shen
vocabulary is checked by ground tests only and is not proved equal to the
Rocq one.

## Semantics (E2E-06)

Configurations are `(control, continuation, store)`. Control is `Eval env e`,
`Ret v`, `Throw x`, `Fail r`, `Halted ev` or `Wrong why`. `next` is the rule
table; `step` is its labeled graph (IO steps take the environment response as
input). Determinism of `step` is therefore immediate given the response; the
substance is in the rules and the theorems below. Every special form:

| Form | Rule (eval_move / ret_move) | Tail position |
|---|---|---|
| `lambda`, `freeze` | closure capturing env | body, when applied/thawed |
| `let` | `KLet` frame | body |
| `if` | `KIf`; non-Boolean → `XNotBoolean` | both branches |
| `and`, `or` | short-circuit; second operand checked Boolean (`KAndR`/`KOrR`) | **no** |
| `cond` | clauses in order; none true → `XCondFail` | clause bodies |
| `trap-error` | `KTrap`; handler evaluated only on an exception, then applied to it | **no** (body) |
| `defun` | new function-namespace entry, returns the name; duplicate params → `XBadDefinition` | — |
| `type` | erased; evaluates the expression | expression |
| direct call `(f a ...)` | arguments left to right, namespace lookup at call time | saturated call body |
| computed call `(e a ...)` | head, then arguments left to right, then apply | closure body |

Application: fewer arguments than the arity yield `VPartial` (currying); more
arguments apply the result to the rest (`KApply`, over-application); a closure
applied to zero arguments, or a frozen value to arguments, raises `XArity`;
non-functions raise `XNotCallable`. Exceptions unwind one frame at a time.

Primitives — every one has a named rule in `KLSemantics.v`:

| Fully specified | Specified with a profile slot | Environment (IO) |
|---|---|---|
| `intern pos tlstr cn string? n->string string->n set value simple-error cons hd tl cons? eval-kl absvector address-> <-address absvector? number?` and exact `+ - * / > < >= <=` | `str` (floats, strings, nil, streams), `error-to-string` (system messages), `=` (inexact numbers; `Wrong` for closures/exceptions/over-deep vectors), inexact arithmetic and comparison, `absvector` fill, `get-time` conversion | `open close read-byte write-byte get-time` |

No primitive is a parametric oracle: each profile slot computes only the
specified sub-case (for example printing a float), and every theorem quantifies
over all profiles. Pinning the slots is E2E-05/E2E-17 work.

## What is universal, ground, or sampled

* **Universal theorems** (all programs, stores, profiles, environments, as
  stated): `final_iff`, `progress`, `wrong_iff`, `stuck_iff_wrong` (the only
  stuck states are explicit `Wrong` states), `step_deterministic`,
  `closed_deterministic` (with a functional oracle), `closed_terminates_unique`,
  `closed_terminates_excludes_divergence`, `run_sound` (every evaluator answer
  has a small-step witness; exhaustion witnesses only the executed prefix),
  `run_monotone` (fuel monotonicity), `run_complete` (every terminating
  behavior is found with enough fuel), `divergence_exhausts_every_fuel`,
  `rule_ok`/`next_preserves_wf`/`step_preserves_wf`, tail rules and
  `stack_bound_enforced`, `loop_diverges` (any tail-recursive self-call loop
  diverges with constant continuation length, under any stack bound with one
  free frame), `KLBridge.embed`, and the 46-form surface check
  `canonical_kl_surface`.
* **Ground derivations** (`KLExamples.v`): factorial, currying,
  over-application, trap/error-to-string, left-to-right exceptions,
  redefinition, vector aliasing and bounds, cond fall-through, non-Boolean `if`,
  undefined closure equality, `eval-kl`, successful/failed/partial writes,
  open+read, and the fuel example used by the universal
  `exhaustion_does_not_imply_divergence`.
* **Sampled**: Shen observation tests; native Shen-Scheme probes recorded in
  VALUE-MODEL.md. Neither is a proof.

## Relation to existing models

`KLBridge.embed`: every terminating `Lambda.v` evaluation (value or any of its
four errors) is reached by internal KLambda steps from the translated term, for
every continuation and store, provided `+` is bound to the primitive and the
profile has no stack bound. This is forward simulation of terminating runs
only; divergence/exhaustion of `Lambda.v` says nothing (its fuel is not a
behavior). `Native.v`/`NativeRuntime.v` model generated Scheme, not KLambda;
relating them is a port obligation (E2E-14/15), not done here.

## Obligations for E2E-07 (`shen/klambda.shen`, profile KL-PURE-1)

Progress: [E2E-07](E2E-07.md) proves the refinement for the captured
evaluator on a construct subset and records how each obligation below was
discharged, narrowed or left open.

The executable evaluator is a different, smaller language; the refinement
statement must translate both syntax and verdicts:

* Syntax: `[apply F A]` is one-argument computed call; `[primitive Op Args]` is
  a direct primitive call that does **not** consult the function namespace
  (this semantics does — the translation must target a store whose namespace
  binds those names to the primitives); `[global X]` is a named function value
  (`VPartial X []`); `[raise E]` is `simple-error` with a non-string check;
  `[thaw E]` is a special form there but a namespace function here; definition
  tables are closed and immutable there (≥1 parameter), mutable here.
* Values: `[int N]`, `[bool B]`, `[str S]`, `[sym S]`, `nil`, `[pair A B]`,
  closures, `[function Name Args]`, `[thunk E Env]` map to `VNum (NInt)`,
  `VBool`, `VStr` (Shen strings to code points), `VSym`, `VNil`, `VCons`,
  `VLam`, `VPartial`, `VFrozen`.
* Verdicts: `[returned V]` ↔ `Normal`; `[raised Msg]` ↔ `Error` with
  `"unbound-variable"`, `"nonboolean-condition"`, `"not-callable"`,
  `"primitive-domain-or-arity"`, `"arity"`, `"not-frozen"`,
  `"error-message-not-string"` mapped to the corresponding exception classes
  (the mapping is many-to-one and must be stated, e.g. `"not-frozen"` is
  `XNotCallable`/`XArity` here); `[unknown evaluation-budget]` ↔ `VExhausted`
  (no behavior claim); `[unknown host-error]` has **no** counterpart and must be
  excluded or tied to a modeled resource failure; `[unsupported
  closure-equality]` ↔ `Wrong`; `[rejected ...]` is admission, outside the
  semantics.
* Fuel: the Shen budget bounds evaluation-tree depth, this evaluator counts
  machine steps; the refinement must be existential in fuel in both
  directions, as `KLBridge.embed` already is for `Lambda.v`.
* Statement shape: for admitted D, E, B, if `buri.evaluate D E B` returns a
  decided verdict then `run` (some fuel) returns the translated verdict from
  the translated configuration, and conversely within sufficient budget.

## Explicitly open

Inexact arithmetic semantics (slots unpinned); `str`/message printing; cyclic
vector equality; closure equality; Scheme `cond` fall-through disagreement;
mixed exact/inexact `=` lowering; symbol application on CL; eval-kl of vector
literals; package/macro/frontend forms (not KLambda); dynamic loading beyond
`eval-kl`; concurrency; a proof that non-tail recursion reaches `Fail RStack`
under a bound; reactive behaviors of concrete KLambda programs; fairness and
input-availability premises; correspondence of `shen/observation.shen` to
`Observation.v`; and reconciliation of the 46-form canonical list with the
exact primitive inventory of the pinned Shen 43.1 kernel and port extensions
(`do`, `thaw`, `fn`, `$`, `scm.` escapes, `*stinput*`/`*stoutput*`/`*sterror*`
and other port globals), which belongs with E2E-01/E2E-17.

## Port options

`rocq/KLPort.v` leaves `KLSemantics.next` and every theorem about it unchanged, and defines `next_r R` and `step_r R`, the
same machine with eight points open to a port: integer range, which integers `n->string` takes, closure identity, arity
errors in place of currying, refusing `defun`, the clock's domain, unchecked writes, and catchable resource failures.
`next_r_agreed` and `step_r_agreed` prove that `agreed_rules` gives exactly `next` and `step` for every profile and
configuration. The Scheme and CL lanes use `next` directly. Only the Shen/JIT lane uses `next_r`
([SHEN-JIT](SHEN-JIT.md)), and two exceptions stay undefined under `=` there. From Shen/JIT 0.4 it no longer sets
unchecked writes, which stays an option.
