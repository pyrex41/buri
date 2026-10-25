# Captured bootstrap, installer effects and compiler pass

This increment uses Rocq and `coqchk`. It reduces whole-component assumptions
into explicit pure-code and effect-contract obligations. It does not verify
Chez or label a trace specification as native IO correctness.

## Boolean-aware bootstrap code

The previous adapter proof covered `buri.kl-node`. The bootstrap observer uses a
separate function, `buri.native-node`, with native boolean tags. A fresh controlled
load captures the four definitions in `shen/observe-constructor.shen`.
`BootstrapInput.v` selects and exactly decodes the first two pure definitions.
`BootstrapCorrect.v` proves their actual generated bodies in a table with the
seven pinned helpers. Selection does not certify the two remaining effectful
functions in that source file.

Execution covers every finite typed node of nil, symbols, byte strings, natural
numerals, booleans and pairs. The output distinguishes `[bool 1]`, `[bool 0]`,
symbols and text. Composition with the proved sealed codec and `Native.untag`
recovers the original represented node. The roundtrip theorem uses the existing
syntax profile of numerals at most 256. Negative native integers are tested but
not claimed to inhabit this natural-number syntax datatype.

The producer algorithm is now proved in the model. The capture is not magically
self-authenticating: truthful native capture, execution and representation still
require external correspondence. A bootstrap algorithm proof does not prove
that it was the algorithm which produced a historical file.

## Captured installer with effects

`ObserverInput.v` decodes the actual generated `buri.install-observed` definition
from a fresh capture of `shen/observe-encoder.shen`. `ObserverEffects.v` gives
stateful semantics to the existing Native expression grammar, preserving
left-to-right arguments, lexical bindings, short-circuiting and failures.
The modeled mutable cell is the record list. Compilation and activation are
arbitrary response functions. Effects expose arity registration, compiler input
and response, activation input and response, record reads and record writes.

For every valid supplied name/argument list/body, successful execution proves:

1. Arity is registered for the supplied name and argument count.
2. The exact supplied definition is submitted to the compiler once.
3. The exact successful compiler result is submitted to activation once.
4. Only after successful activation are prior records read and the exact
   source/target pair prepended.
5. The installer returns the supplied definition name.

Separate quantified theorems cover compile failure and activation failure.
Their modeled record list remains unchanged and no record read/write event
occurs. Errors, unsupported responses and external exhaustion are preserved.
The arity effect is already performed and is **not** rolled back. No theorem
claims transactional rollback of all runtime state or that a failed activation
has made no partial host mutation.

These are execution proofs of the captured installer against explicit external
contracts. They do not establish compiler correctness, native activation
truthfulness, global-binding stability, or a Chez-to-effect-machine simulation.
The complete effectful observer entry also contains higher-order calls outside
this execution proof. Its IO plan receives a narrower structural check below.

## Read/parse/snapshot linkage

`ObserverIO.v` checks the captured entry directly. It contains exactly one token
for the source-read operation and one for parsing. The captured bindings pass
the same lexical source variable to `read-from-string`, the recorded source
cell, and the `.source` write. These are checked AST shape and data-flow facts,
not dynamic native read/write counts or a universal IO implementation theorem.

The native tests exercise a rejected definition, a compiled duplicate-parameter
target rejected during activation, unchanged publication records on failure,
and an installed function whose behavior and recorded source agree. These are
native regressions, separate from the quantified effect-model theorems.

## Actual upstream compiler pass

`ports/upstream/compiler.shen` is byte-pinned to Git blob
`42ac753b8f305c578998b74693fc85b28112a814` from reviewed Shen-Scheme commit
`8d261518db17fbfec32d1b268b40ed216b925c74`. Its BSD license is retained in
`LICENSES/Shen-Scheme.txt`. A byte-only gate checks that
`ports/compiler-merge.shen` changes only the selected function's explicit package
qualification. That source is compiled and captured through the normal loader.

`CompilerPassCorrect.v` proves the captured `merge-nested-lets` transformation
for arbitrary supplied binding and body values in both supported cases. In the
two-single-binding case, operands admitted at the stated decoder depths yield
exactly the same Native expression before and after the transformation.
Consequently every pure evaluator outcome and every modeled state/effect trace
is identical, for arbitrary private programs, environments, fuel and effect
responses. The decoding premises are explicit; no proof claims success for
malformed syntax or every compiler pass. The many-binding case currently has an
assembly proof, not a general semantic preservation theorem.

This is a first generic proof about a source-pinned upstream pass. It is not
universal correctness of the entire Shen frontend or backend.

## Decoder correction and gates

The work exposed a decoder bug: folding Scheme `and` onto a trailing true value
loses a truthy final operand. The decoder now preserves the final expression;
empty `and` still returns true. Rocq regressions cover empty, singleton and
`(and 1 2)` cases. The captured codec/helper proofs are rebuilt against the fix.

Fresh builds regenerate all three new captures, compare their single-read source
snapshots and literal proof inputs, then run all proof and mutation gates.
Tampering fixtures change bootstrap boolean tagging or pair traversal, observer
activation or publication, and the upstream pass keyword. IO origin, native
primitive contracts, mutable construction bindings and the remaining compiler
are still explicit trust obligations. There are no custom axioms.
