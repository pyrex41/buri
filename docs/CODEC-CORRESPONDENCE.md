# Universal codec and source/capture correspondence

All proofs in this increment use Rocq 8.18 and independent `coqchk` replay.
There is no Lean proof lane or implied second-kernel validation.

## Exact captured codec

`NativeCodec.v` proves the actual decoded `sealed_native_program`, linked to
its literal capture by `sealed_native_exact`. No replacement encoder is inserted
into the program table. `NativeComposition.v` supplies fuel monotonicity and
compositional evaluation lemmas for the existing `Native.eval`. The proofs
follow the captured generated variable names, administrative lets and calls;
changing those bodies requires rechecking the correspondence.

The supported datum domain is finite trees of nil, exact signed integers,
byte-spelled symbols and pairs (including improper pairs). Integer serialization
uses the existing explicit canonical decimal primitive contract. It does not
identify arbitrary numeric-spelling strings with actual native integers.
Native input strings, booleans, fractions, handles and characters are not wire
datums. Strings and characters are internal encoder values. Actual Unicode
symbols outside the byte-string representation are not covered.

| Result | Quantification |
|---|---|
| Byte encoder | Every natural input and count, including inputs above machine-integer precision |
| String encoder | Every finite byte string, including empty strings and every byte code |
| Datum encoder | Every finite supported datum, arbitrary exact signed integers |
| Instruction execution | A sufficient finite instruction budget exists for each datum |
| Decoder roundtrip | Every successful instruction-produced text decodes to the represented datum |
| Concurrent output | Every completed textual result under modeled ambient rebinding is the canonical output |

The proof explicitly discharges composite operations: exact division/floor
halving, multiplication/equality parity, decrement, nested character access,
byte bounds, substring length arithmetic, classifications, spelling, recursive
calls and ordered concatenation. It uses the existing 27 primitive contracts;
it does not verify their Chez implementations. Existential budgets are logical
termination, not guarantees of available native heap, stack or wall-clock time.
Scheduler starvation and concurrent input-object mutation remain outside scope.

## Captured tagging implementation

`ports/adapter.bits` records the actual three definitions generated from
`shen/export-encoder-kl.shen`. `AdapterInput.v` checks exact decoding and names.
`AdapterCorrect.v` executes the first two pure functions, `buri.kl-bytes` and
`buri.kl-node`, in a fixed table with the seven pinned helpers. It deliberately
excludes the third, effectful metadata/IO exporter.

For every finite `EncoderFrontend.node`, these captured functions produce the
specified tagged value. The proof covers natural numerals without a bound.
Composition with the existing protocol decoder uses its admitted profile:
numerals must be at most 256; byte strings are arbitrary finite strings. That
bound belongs to the existing syntax decoder, not to the wire encoder. Native
negative numerals are regression-tested but are not claimed as nodes of that
natural-number syntax datatype.

The two pure functions additionally require `cons`, `list`, and `string?`.
Their fixed helper table is a model assumption. The current global exporter is
not thereby made immutable or certified under live rebinding. The boolean-aware bootstrap pure targets are now proved too; see
[OBSERVER-PROVENANCE](OBSERVER-PROVENANCE.md). Their native self-capture, source
reading, loader effects and IO remain provenance obligations. The adapter's own source-to-target compiler
execution is captured, not universally proved.

## Source and compiler artifact chain

`SourceReader.v` independently lexes and parses the exact committed encoder
source, rejecting malformed brackets, unterminated strings and trailing closers.
The closed profile has proper lists, byte strings, symbols and small natural
numerals. It is not a general Shen reader, and does not support reader macros,
comments, escapes or improper-list syntax. It checks the source against an AST
built structurally from the encoder definitions, independently of their textual
renderer. This is a checked closed-artifact parse, not a universal reader theorem.

`CodecCorrespondence.v` also proves that the observed compiler capture and the
sealed capsule contain exactly the same paired KLambda/Scheme records. The
existing paired validator checks the full three-definition coverage, source
resolution and target normalization. For every supported datum and every source
evaluator fuel, a successful captured-source-model result agrees with a finite
instruction execution of the captured sealed target. The independent source
parse, exact source equality, exact record linkage and universal target execution
are assembled into an explicit source-to-machine statement.

This is translation validation for this exact encoder compilation, universal in
its runtime inputs. It is not universal correctness of `shen.shen->kl-h`,
`_scm.kl->scheme`, or all Shen programs. The sealed exact-division shim deliberately
differs from the stock port's inexact helper, whose counterexample remains in the
suite. The proof never upgrades the stock encoder to this sealed guarantee.

## Gates and unresolved boundary

Fresh builds recapture the adapter, compare the single-read source snapshot and
literal capture, package bytes without semantic transformation, and require Rocq
proof replay. Four altered adapter bodies (wrong tag, tail, child and type test)
must fail their actual semantic proofs. Packaging mismatch and stale outputs are
rejected. Native cases and these adversarial fixtures remain tests, separately
reported from universal theorems.

Still unverified within the broader Shen/Buri system: general reader/frontend/
backend correctness, native observer and bootstrap execution provenance, effectful exporter IO,
installed-code provenance, the broad Shen evaluator and certificate checker.
Actual host activation and representation correspondence remain trusted too.
Chez compiler/runtime internals are deferred as requested. These obligations are
not hidden behind axioms or marked closed by the new artifact-level proofs.
