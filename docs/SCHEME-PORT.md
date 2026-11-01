# Shen-Scheme: arbitrary sequential binding tails

`rocq/SchemePortMerge.v` extends the existing proof about the **actual captured
Shen-Scheme `merge-nested-lets` implementation**, rather than introducing a
second reference compiler. Its first clause rewrites:

```scheme
(let ((x initial)) (let* bindings body))
;; to
(let* ((x initial) . bindings) body)
```

The earlier `CompilerPassCorrect.v` theorem covered preservation for two
bindings. The new result admits an arbitrary successfully decoded binding tail,
including the empty tail and repeated variable names. No freshness assumption
is needed: both forms have the same sequential scope and shadowing behavior.

The universal theorem `captured_arbitrary_tail_preservation` connects execution
of the existing exact capture on the native small-step machine to equal decoded
expressions. `arbitrary_tail_preserves` covers every evaluator result, including
exceptions, unsupported operations, and exhaustion. The effect theorem also
preserves the complete modeled result, final state, and event trace for arbitrary
program, compiler, activation handler, environment, and previous records.

The admission premises explicitly require successful decoding of the tail and
of the first initializer at both relevant syntax depths. The source has one
extra syntactic wrapper, so its decoding budget is one larger. Evaluation uses
the same budget after both forms decode to the same nested `Let` expression;
this is not a claim that native execution takes the same number of instructions.

## Evidence and boundary

The implementation identity is inherited from `CompilerPassInput` and its
`compiler_pass_exact` theorem, with the source lineage recorded in
`ports/compiler-merge.shen`. The captured execution theorem reuses
`captured_merge_many`; no new primitive oracle or custom axiom is introduced.
Fresh capture/source verification remains part of the existing gate. The proof
covers this pass clause for all admitted tails; it does not establish full
Shen-to-KLambda correctness, arbitrary Scheme decoding, native Chez compilation,
garbage collection, or ARM machine-code correctness.

`tests/scheme-port-merge.shen` exercises the actual imported pass with empty,
long, and shadowing binding tails and checks malformed/nonmatching fallback.
Those finite checks are regressions, separate from the universal Rocq theorems.

# Shen-Scheme: argument ordering and fresh names (E2E-15, first item)

`rocq/OrderCallPass.v` and `rocq/OrderCallPreserve.v` cover **every branch** of
the actual captured `order-call`, `order-call-inputs`,
`fresh-call-variable`, `has-computation?`, `simple-scheme-expression?` and
`merge-nested-lets` (pinned `src/compiler.shen`, blob
`42ac753b8f305c578998b74693fc85b28112a814`), executed on the existing
first-order effect evaluator. Nothing is re-implemented: proofs reason about
the decoded captured bodies.

## What changed in the trusted inputs

- The kernel functions the pass calls are no longer Rocq oracles.
  `ports/kernel-list.shen` is the exact text of `occurrences`, `reverse`,
  `reverse-help` and `not` from Shen kernel 43.1 `sources/sys.shen`
  (`ports/upstream/sys.shen`, blob `92aab80f04afe0b91a8f37eb835c245441b7ef09`,
  from `ShenOSKernel-43.1.tar.gz` sha256 `900eedef…6920`, the archive pinned by
  the shen-scheme Makefile). Only the defined names and self-references are
  renamed into `buri.kernel.*` so capture does not redefine the running
  kernel; `scripts/check-upstream-pass.py` checks this byte-for-byte. The file
  is compiled by the actual Shen-Scheme compiler through the existing
  `observe-constructor` capture (`kernel_list` profile), regenerated and
  diffed by `make prove`. The Rocq program links `kl:occurrences`,
  `kl:reverse`, `kl:not` to these captured definitions.
- Gap: the boot image's precompiled kernel is not shown to be byte-identical
  to this recompilation of the same kernel source.
- `gensym` is an **arbitrary stateful generator** (any outcome, state change,
  trace or failure). Every theorem holds for all generators, so it covers the
  real counter-based `gensym` without modelling it.
- Remaining primitive contracts (from pinned `src/primitives.scm`):
  `kl:=` with a symbol on the left (eq? on interned symbols),
  `kl:_scm.assert-boolean` on booleans, and the list primitives of `Native.v`.

## Theorems (universal unless marked)

- `fresh_success`: any successful return of the captured fresh loop, for any
  generator, is a symbol whose captured kernel occurrence count in the used
  syntax is zero; `occurrences_returns` proves the captured kernel
  `occurrences` computes the occurrence count for every name and value.
- `order_call_success`: every successful run of the captured pass follows the
  exact keep/lift structure (`Ord`): keep when simple or nothing later
  computes, otherwise bind to a name absent from the call and all earlier
  names, then merge (only the three shapes the loop can build).
- `decode_vars`: the reader only produces variables occurring in the syntax;
  `decode_monotone`/`decode_default` (`DecodeFacts.v`) give budget
  monotonicity and the application reading of every non-keyword head.
- `lift_one`, `dord_preserves`: for arbitrary programs, operations, states and
  environments, the decoded target has exactly the same completed outcomes
  (value, raised error payload, unsupported), final state and full
  left-to-right event trace as the source call; `dord_noncompletion` gives the
  same for non-completion.
- `order_call_preserves` / `order_call_noncompletion`: composition. If the
  actual pass returns `c` on an admitted call `(f a1 … an)` read as
  `Call f es` at budget `S N`, then `c` is read at budget `S (S N)` as a
  target with identical observations. This includes empty and single
  argument lists, nested calls, effects in any argument and exceptions in the
  middle of the list.

Admission conditions (genuine, not scaffolding):

1. `f` is not one of `decode`'s special-form heads (the pass is only applied
   to applications; a keyword head would not be a call).
2. No argument is a `lambda` form: the pass treats closure construction as
   simple, but the first-order evaluator has no closures.
3. Every argument that is a variable reference is bound in the environment
   (lexical well-scopedness). An unbound variable would fail at a different
   point of the trace after lifting, so this condition is necessary.

Open: a progress theorem (with the real counter generator the pass always
terminates successfully), composition with the remaining compiler passes and
with the binding/conditional branches, native Chez execution, and the old
constant-generator statements in `OrderCallCorrect.v` (kept, superseded).

`tests/scheme-port-order.shen` is a SAMPLED regression of the actual imported
pass and helpers (empty, single, nested, effectful, raising, and a forced
gensym collision). `tests/mutate-order.py` adds four rejected mutants: a
swapped keep order, a fresh loop accepting collisions, kernel occurrences
dropping the tail (caught first by the ground `occurrences_sample`), and the
composed theorem restated for reversed arguments.
