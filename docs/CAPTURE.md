# Captured compiler data and the checked boundary

The native validation path now starts with a raw, inert datum rather than an
exporter-produced Coq AST. It addresses B01/B04's semantic translation gap for
the admitted arithmetic grammar. Capture provenance and runtime preservation
remain separate obligations.

## Required path

1. `shen/export-wire.shen` calls the pinned port's actual
   `_scm.compile-expression` on each fixed source/scope pair. It records
   `[buri-native-1 [[label scope source target] ...]]`.
2. The capture is serialized to `ports/native-capture.bits`. The adjacent `.sexp`
   is a human-readable transcript from the same captured data.
3. `scripts/package-wire.py` embeds only the literal 0/1 bytes in
   `rocq/NativeCapture.v`. It performs no syntax decoding, name resolution, or
   semantic comparison. A separate byte check compares that Coq string to the
   exact captured file.
4. `rocq/Wire.v` parses the string inside Rocq. `capture_exact` proves that
   successful decoding determines the complete original string. Round-trip and
   injectivity theorems cover every finite datum, including all byte characters.
5. `rocq/NativeValidation.v` defines the admitted raw source and target grammar.
   It decodes integer atoms, variables, arithmetic, source `let`, Scheme `let`,
   and Scheme's sequential `let*`. Input scopes must contain unique admissible
   variable names. Unsupported forms do not receive certificates.
6. `rocq/Resolve.v` resolves lexical names with first-binding shadowing. Its
   preservation theorem covers every named expression, environment, and successful
   resolution, including the environment extension at a `let`.
7. `rocq/Normalize.v` symbolically eliminates administrative bindings. A generic
   theorem proves preservation for total exact-integer expressions. The checker
   compares the resulting arithmetic trees; it does not assume compiler-produced
   temporary bindings are correct.
8. `check_capture_sound` and `native_capture_sound` connect accepted data to
   equality of source and target meanings for every named integer environment.
   The record-coverage theorem accounts for every record in order; the release
   also checks that the capture contains the expected 12 records.

## Wire format

The file consists exclusively of ASCII `0`/`1` bytes. Bits within a character
are least significant first, matching Coq's eight Boolean `ascii` fields.

| Data | Encoding |
|---|---|
| Nil | `00` |
| Atom | `01`, type bit, encoded byte string |
| Pair | `1`, encoded head, encoded tail |
| Empty byte string | `0` |
| Nonempty byte string | `1`, eight character bits, encoded remaining string |

The atom type bit distinguishes numeric text from a symbol. The entire input
must be consumed. The mathematical parser rejects truncation, extra trailing
data, and non-binary input. Runtime memory exhaustion remains outside this
mathematical totality claim.

## What acceptance establishes

For an accepted capture string `bits` and decoded entries `es`:

```text
capture(raw) = bits
and every raw record has a corresponding checked entry, in order
and for every entry and every environment of integer variable values:
    namedMeaning(source, environment) = namedMeaning(target, environment)
```

The source/target grammar and its arithmetic meaning are formal definitions in
Rocq. The parser, lexical resolution, normalization, and acceptance implications
are checked independently of the Shen AST exporter. `vm_compute` produces a
proof that Rocq's kernel checks; `coqchk` replays the resulting proof objects.

The older `NativeOutput.v` export is retained as a regression cross-check. It is
no longer the only basis for the native schema result. The separate Peano
arithmetic equation exporter retains its previously documented assumptions.

## Remaining assumptions

- The supplied capture originated from the claimed source data and compiler
  invocation. The serializer now has a source-linked correctness proof in the admitted
  first-order semantics; [ENCODER](ENCODER.md) specifies the exact chain. Native
  reader/compiler, primitive, representation, and runtime refinement remain
  open. A raw byte file cannot establish its own origin.
- The selected grammar and exact-integer Scheme meaning faithfully describe the
  port's admitted behavior. In particular, normalization assumes total pure
  arithmetic. It does not justify deleting effects, exceptions, divergence, or
  resource consumption in a broader language.
- Packaging/byte comparison, host artifact identity, Rocq's execution environment,
  Chez, and lower runtime behavior retain their named trust boundaries.
- The validator checks supplied compiler outputs. A preservation theorem for
  every possible invocation of the real compiler is still open.

The optional result `None` means no certificate was obtained. It can arise from
unsupported syntax, malformed data, out-of-scope names, different arithmetic
normal forms, or insufficient decoding fuel. It is not a proof of inequivalence
or a counterexample. Structural normalization is intentionally incomplete for
algebraic equalities such as commutative rewrites.

## Regression evidence

The validation lanes include 51 Rocq examples, 16 Shen encoder checks, and 8
native KLambda-tagging checks. They exercise
shadowing, temporary bindings, negative and large integers, numeric/symbol tag
confusion, reserved names, malformed wire data, and unsupported effects.

Five capture mutations must fail the acceptance proof: a changed target operator,
truncation, trailing bits, an omitted expected record, and the wrong profile.
The four existing compiler/equation mutations remain; three encoder/source
mutations additionally check the source-linked proof. Six more changed KLambda
captures exercise [registered-definition validation](FRONTEND.md). Mutation gates require a
proof unification failure; missing dependencies or a broken toolchain cannot
masquerade as a successfully rejected program.

Orchestration regressions also check that an exporter which prints an exception
and exits zero cannot reuse stale proof input, and that packaging cannot silently
substitute different capture bytes.
