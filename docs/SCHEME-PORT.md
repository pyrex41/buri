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
