# Source-linked capture encoder

The encoder now has a correctness proof for a precisely defined first-order Shen
fragment, tied to the exact file that the capture path loads. This closes the
previous gap between two separately handwritten encoding algorithms at the
program/source level. Native execution of that source still needs the front-end,
primitive-representation, and runtime preservation proofs below. The registered
KLambda output for these three definitions is now separately translation-validated;
see [FRONTEND](FRONTEND.md).

## Checked chain

`shen/wire.shen` contains three executable Shen definitions: `buri.wire-byte`,
`buri.wire-string`, and `buri.wire`. The capture module loads this file; the byte
and datum format is unchanged. The source uses explicit `if` and `let`, avoiding
pattern-clause compilation in the program being modeled.

`rocq/Encoder.v` gives the program as expression data and evaluates that data with
explicit lexical environments, lazy branches, left-to-right arguments, local
bindings, and recursive named calls. Its operations have the contracts listed
below. A canonical renderer maps these exact bodies to Shen source.

`scripts/package-encoder.py` embeds the literal ASCII file contents into
`rocq/EncoderSource.v`. It performs no source parsing or semantic translation.
A separate byte comparison checks the packaging. **Inside Rocq**,
`encoder_source_exact` proves that those bytes equal the rendered program.
The gate regenerates the module and compares it to the committed proof input.
Changing the source while retaining the old model cannot satisfy that equation.
The renderer is for this closed program, not a verified arbitrary Shen printer
or reader.

The independently replayed proofs establish:

- `byte_correct`: for every natural input and finite bit count, the byte routine
  has a terminating derivation with the specified low-bit-first output.
- `byte_ascii`: its eight-bit result equals the eight Boolean fields of every
  Rocq ASCII character, including codes 0, 128, and 255.
- `string_correct`: the string routine returns the canonical wire string for
  every finite byte string, including empty strings and embedded zero bytes.
- `datum_correct`: the datum routine returns `Wire.capture d` for every finite
  abstract datum, including improper pairs and either atom tag.
- `evaluation_deterministic` and `encoder_output_unique`: any successful fuel
  witness has that same output. There is a sufficient fuel witness for every
  admitted datum; this is not a termination claim for arbitrary Shen recursion.
- `encoder_decodes`: decoding any such successful output recovers the original
  datum. This composes the program proof with the existing generic codec proof.
- `source_linked_encoder` and `source_linked_roundtrip`: the exact source equation
  accompanies those universal results in the generated source-bound module.

The evaluator returns `Returned`, `Exhausted`, or `Stuck` separately. `Stuck`
means an explicit error or undefined operation or binding in this narrow fragment. It is neither
an evidence-rejection verdict nor a model of Shen's exception payloads. The
proofs above cover normal encoding, not arbitrary exceptional executions.

## Primitive and representation boundary

The mathematical contracts are definitions, not theorems about the port.
Connecting native execution to them remains an explicit obligation.

| Source operation | Required contract on admitted values |
|---|---|
| `cn`, `= S ""`, `pos S 0`, `tlstr S` | Byte-string concatenation, emptiness, first character, and tail |
| `string->n` | Character code is exactly its unsigned eight-bit ASCII value |
| `floor (/ N 2)` | Natural-number halving, without rounding through an inexact representation |
| `= N (* Half 2)`, `- Count 1` | Exact integer comparison, multiplication, and subtraction on the reachable nonnegative domain |
| `and`, `>=`, `<` | Byte-range check with the shown Boolean meaning |
| `= X []`, `cons?`, `hd`, `tl` | Nil/pair discrimination and projection for finite acyclic data |
| `buri.exact-integer?`, `symbol?`, `str` | Correct atom classification and byte-string spelling, with distinct numeric and symbol tags |

An abstract `Wire.Atom true s` corresponds to a native exact integer only when
that integer's admitted spelling is exactly `s`. A symbolic atom requires a
native value satisfying Shen's `symbol?` and spelling contract. The proof does
not assert that every abstract atom has such a native representative. For
example, this pinned port does not classify `(intern "1")` as a Shen symbol;
the native encoder rejects that object. Ordinary strings and floats also remain
outside the datum encoder's admitted input profile.

The source equality alone is not a proof that Shen's reader, `define` compiler,
Shen-Scheme optimizer, or Chez preserves the fragment semantics. Nor does it
prove that `str`, integer arithmetic, or the native representation satisfies the
contracts above. The exact-integer predicate's own helper implementation remains
inside this primitive boundary. `tc -`, immutable loaded definitions, loading the
specified file, and the source/host identity checks remain named assumptions.
No compiler provenance, resource bounds, or whole-port claim follows from these
results. A finite mathematical derivation does not guarantee available native
stack, memory, or execution time.

## Gates

The release checks exact source bytes, 16 native encoder regressions, ten Rocq
encoder examples, and three additional rejected proof mutations: a wrong numeric
atom tag, a reversed bit choice, and substituted source bytes. Mutations must
produce an actual proof unification failure. Missing tools/imports cannot count
as rejection. The report records program proof and native execution assumptions
separately.
