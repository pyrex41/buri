# Validation of the encoder's registered KLambda

The checked boundary now reaches the three KLambda definitions registered by
Shen when the source-bound encoder is loaded. Previously, the encoder proof
stopped at the source and its formal program. The new path checks the registered
function bodies, parameter bindings, local renaming, and recursive calls against
that same proved program.

This is instance translation validation under the admitted semantics. It is not
a universal proof of Shen's compiler, a full KLambda semantics, or a proof about
Chez code. The exact remaining assumptions are below.

## Actual input to the checker

A fresh pinned Shen process loads `buri.shen` and the exact `shen/wire.shen` file
whose source equality Rocq already checks. `shen/export-encoder-kl.shen` reads:

- `(ps buri.wire-byte)`
- `(ps buri.wire-string)`
- `(ps buri.wire)`

On this port these are registered `defun` forms, with compiler-generated names
such as `V5893` and `W5895`. They are obtained from the live image's source
metadata. **`ps` is not a disassembler or an observation of the native executable.**

The adapter tags nil, pairs, numbers, symbols, and strings distinctly. Strings
become byte-code lists, so they cannot be confused with symbolic or numeric
atoms. It does not resolve names, rewrite expressions, choose semantic operators,
or decide equivalence. The existing wire encoder serializes this inert data to
`ports/encoder-kl.bits`; `ports/encoder-kl.sexp` records the readable definitions.
The capture header is `buri-encoder-kl-1`.

The packager embeds only the literal bits into `rocq/EncoderKLambda.v`. An
independent byte check, fresh-export sentinel, committed-file comparisons, and
source hashes bind the build inputs. Semantic decoding and acceptance take place
inside Rocq. A failed export cannot reuse a stale capture or proof module.

## Named execution and preservation

`rocq/EncoderNames.v` defines a named first-order execution semantics with an
immutable three-function definition table. Local bindings shadow earlier ones;
recursive calls install fresh parameter environments. Argument evaluation is
left-to-right and branches are lazy. `Returned`, `Exhausted`, and `Stuck` remain
distinct. Unary calls use the encoder model's internal unused second slot; it is
not a second argument in the captured KLambda syntax.

The generic `resolve_preserves` theorem proves equality with the existing
encoder evaluator for every abstract fuel value and every corresponding lexical
environment, provided the whole function table resolves to the proved program.
It covers recursive calls through that table, not only isolated expressions.
It preserves all modeled results, including exhaustion and stuckness. Abstract
fuel equality is not a native instruction-count or resource guarantee.

`program_encoder_total` and `program_encoder_unique` then transfer the previous
encoder results to the named program: every finite admitted datum has a
successful derivation, and every successful result is exactly `Wire.capture d`.
The existing codec theorem consequently gives decoding round trips.

## Strict admitted grammar

`rocq/EncoderFrontend.v` decodes the tagged syntax and admits only the shown
encoder fragment. Variables start with an uppercase ASCII letter, followed by
ASCII letters, digits, or underscores. Literal integers are bounded to 0–256;
this is a restriction on this program's syntax, not on encoded numeric payloads.
Strings contain bytes 0–255.

The checker requires exactly three definitions in the prescribed order, with
the expected names and arities (2, 1, 1). Duplicate parameter names, free
variables, unknown callees, malformed forms, and missing or extra definitions
cannot pass. Every body must resolve to the corresponding proved encoder body.
Local shadowing is permitted and interpreted by first binding.

Composite operations retain the explicit contracts from [ENCODER](ENCODER.md).
For example, `(floor (/ X 2))`, `(= X (* Y 2))`, and
`(and (>= X 0) (< X 256))` are recognized only in their exact forms. The range
check must refer to the same variable twice. Effectful operands cannot be
silently duplicated or discarded by this decoder. General arithmetic rewrites,
closures, partial application, mutable globals, and exception handlers are not
admitted. An unsupported form produces no certificate, not a proof of a bug.

`check_program_coverage` and `check_capture_coverage` account for the complete
three-definition capture. `encoder_kl_execution` combines exact source equality,
complete definition coverage, execution preservation, termination, and unique
canonical output for the concrete registered program.

## Boundary still open

The capture's origin, the correctness of the small tagging adapter, the host's
source metadata, and faithful loading without rebinding remain assumptions.
The record cannot prove that it came from the claimed process, or that `ps`
identifies the code actually compiled or executed by the backend.

The admitted grammar and composite primitive contracts remain reviewed formal
specifications. Their use does not prove the implementations of `floor`, `/`,
`str`, `symbol?`, `buri.exact-integer?`, or the string/pair primitives. Native
representation relations, Shen-Scheme lowering/optimization, Chez, memory,
resource behavior, and machine execution remain open or explicitly trusted.
The generic reader and front-end compiler also remain unverified; the captured
outputs for these three definitions are now checked individually.

## Regression evidence

Six additional mutated captures must fail kernel-checked acceptance proofs:
changed divisor, changed wire tag, wrong binder, duplicate parameters, omitted
definition, and wrong recursive callee. An import/tool failure cannot count as a
rejected mutation. Sixteen Rocq cases cover scope, shadowing, arity, strict
primitive forms, typed transport, non-byte characters, profile, and fuel.
Eight native adapter cases check tagging distinctions, improper pairs, embedded
zero bytes, and refusal of unsupported floats. These tests remain distinct from
the generic preservation theorems.
