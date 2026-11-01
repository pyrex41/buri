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

# Shen-Scheme: pass composition, bindings, conditionals, equality (E2E-15, Wave B)

`rocq/SchemeBranches.v` and `rocq/SchemeCompose.v` extend the proofs about the
**actual captured compiler** to the next branches of `compile-expression` and
compose them with the ordering and merge passes. Nothing is re-implemented.

## New captures

- `ports/compiler-branches.shen`: the exact upstream `yields-boolean?`,
  `force-boolean`, `emit-symbol`, `emit-let`, `emit-if`, `emit-cond`,
  `emit-cond-clauses` and `emit-equality-check` (pinned `src/compiler.shen`,
  blob `42ac753b…`), read **inside the exact upstream `(package _scm …)`
  header**, so Shen's own reader performs every `_scm.` qualification; nothing
  is renamed by hand. `scripts/check-upstream-pass.py` checks the bytes, and
  also checks that `compile-expression`'s let clause is literally
  `(merge-nested-lets (emit-let Var Value Body Scope))`.
- `ports/kernel-element.shen`: the exact kernel 43.1 `element?` (renamed
  `buri.kernel.element?` only), linked as `kl:element?`.
- Both are compiled by the actual Shen-Scheme compiler through the existing
  `observe-constructor` capture (`compiler_branches`, `kernel_element`
  profiles), regenerated and diffed by `make prove`, and decoded completely
  (`compiler_branches_exact`, `kernel_element_complete`).

`unbound-symbol?` could not be captured: its body contains the symbol `,`,
which the native capture codec has no encoding for. It stays an arbitrary
operation; the equality theorem takes its (pure, boolean) answers as premises.

## The compiler's own world

The captured emitters run on the existing first-order effect evaluator,
linked with the captured merge (first definition of the ordering capture) and
the captured `element?`. Every recursive `compile-expression` call, the
`order-call` call, and every other uncaptured compiler function
(`native-mode`, `emit-static-application-fallback`, `shen.f-error`,
`unbound-symbol?`) is an ARBITRARY stateful operation; every theorem holds for
all of them. Primitive contracts (pinned `src/primitives.scm`): `kl:=` (eq?
fast path, numbers by `=` — modelled for exact integers only, anything else
numeric is unsupported, never guessed — pairs and strings structurally,
identity otherwise), `assert-boolean` (identity on booleans, raises with the
value otherwise), and the static globals `*yields-boolean1/2*` as symbol lists
(the theorems quantify over the lists).

## Theorems (universal unless marked)

- `emit_let_exact`, `emit_if_exact`, `emit_cond_clauses_exact`,
  `emit_cond_exact`, `emit_equality_exact` are **exact denotations**: for every
  input, every completed outcome (value, raised error, unsupported), final
  state and compile-time trace of the captured emitter equals a stated
  sequencing of its sub-compilations. In particular: the let value is
  compiled in the outer scope, then the body in the scope extended by the
  variable; a literal `true`/`false` test compiles only the selected branch
  (the other is never compiled); other tests are passed through
  `force-boolean`, then test, then-branch, else-branch are compiled in order;
  cond clauses are compiled in order with forced tests, malformed clauses
  reach `shen.f-error`; equality selects `eq?` (unbound symbol or `[fail]`),
  `eqv?` (a number), `equal?` (a string), `null?` (an empty list) or the static
  fallback exactly as the source says, and hands `eq?/eqv?/equal?` calls to
  `order-call`.
- `yields_returns`, `force_returns`, `kernel_element_returns`: the captured
  `yields-boolean?` decides exactly literal booleans, `(let _ _ E)`/`(do _ E)`
  with boolean-yielding `E`, and two/three-element forms whose head is in the
  static lists; `force-boolean` wraps everything else in `_scm.assert-boolean`.
- **Composition** `order_then_merge_preserves`: for every generator and every
  successful run of the captured `order-call` on an admitted call, the
  captured `merge-nested-lets` applied to the let that `emit-let` builds
  around that output returns syntax read as a target whose completed outcomes,
  error payloads, final state and trace equal those of the unordered,
  unmerged let, for arbitrary programs, operations, environments and states.
  `let_clause_preserves` composes captured `emit-let`, ordering and merge: the
  whole let clause as `compile-expression` invokes it. Its premises name the
  two uncaptured `compile-expression` calls: the bound value is read as `a`,
  and the body (a static application) is compiled by the captured
  `order-call` (its `emit-static-application` route, not itself captured).
- `strict_if` (Scheme level, any program/operations satisfying the
  `assert-boolean` contract): a forced condition selects the then-branch on
  `#t`, the else-branch on `#f`, and never selects a branch otherwise; only the
  selected branch's effects occur. `world_assert_contract` shows the
  compiler's own contract satisfies it.
- `numeric_equality_preserves`: in the numeric branch, every successful run of
  the captured `emit-equality-check`, through the captured `order-call`, gives
  syntax with exactly the outcomes, state and trace of `(eqv? d1 d2)` on the
  compiled operands. `eqv_exact_agrees`: `eqv?` and `kl:=` agree on exact
  integers.

## Confirmed port disagreements (counterexamples, not hidden)

1. **cond with no true clause.** The KLambda profile raises `XCondFail`. The
   compiler emits `(cond (#f 1))` with no else clause and Shen-Scheme v0.52
   returns `#<void>` without raising (`tests/scheme-compose.shen`,
   `cond-no-true-clause-falls-through`). `cond_without_true_unread` proves the
   Scheme reader rejects every such emitted cond at every budget, so no
   preservation theorem covers it. Ledger: `OB-SCHEME-COND-FALLTHROUGH`
   (refuted) replaced by `OB-SCHEME-COND-ADMISSION` (open: admit only
   exhaustive cond, or emit an error else clause).
2. **`=` with a literal number.** The compiler emits `eqv?`. Scheme `eqv?` is
   false for mixed exactness, while the same KLambda `=` through variables
   calls `kl:=`, which compares numbers with `=`: `(= 1 (* 2 (/ 1 2)))` is
   `false` but `(let Y 1 (let X (* 2 (/ 1 2)) (= Y X)))` is `true` on the same
   compiled path (`eqv-literal-mixed-exactness-counterexample`). (Wave A's
   `(= 1 1.0)` sample does not show it: the Shen reader reads `1.0` as exact
   `1`.) `eqv_mixed_unmodelled`: the model claims nothing for mixed exactness.
   Ledger: `OB-SCHEME-EQV-LITERAL` (refuted) replaced by
   `OB-SCHEME-EQV-EXACT` (partial: exact integers proved; admission or a port
   change needed for mixed exactness, dependent on `OB-NUMERIC-PROFILE`).

## Evidence and boundary

`tests/scheme-compose.shen` is a SAMPLED regression (eighteen checks of the
running compiler and the loaded captured emitters) plus the two
counterexamples. `tests/mutate-compose.py` adds six rejected mutants: a
literal-true `if` compiling the else-branch, an unscoped let body, an
unforced cond test, an `equal?`-lowered numeric `=`, and restatements of the
composition (dropped binding) and strictness (swapped branches) theorems.

Open (E2E-15 is not complete): the `compile-expression` dispatcher itself
(uncapturable whole: it contains closures, `freeze` and `scm.` escapes outside
the first-order reader) — so the dispatch from `[let …]`/`[if …]`/`[= …]` to
these emitters, and from a forced test to a `kl:_scm.assert-boolean` call, is
source text, not a theorem; the boolean-yielding-head premise of
`yields-boolean?` (redefinition of `not`, `=` etc., OB-KL-GLOBAL-REBINDING);
the relation of the KLambda profile to the decoded Scheme (OB-GENERATED-SCHEME-
SEMANTICS); `unbound-symbol?`; termination of the ordering pass with the real
counter-based `gensym` (not attempted in this wave; every theorem quantifies
over all generators instead); boot-image kernel identity; native Chez
execution.
