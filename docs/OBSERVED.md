# Observed compilation and encoder target validation

The release now includes an observed loading lane for the exact source-bound
encoder. It captures KLambda from the real Shen frontend, captures Scheme from
the real Shen-Scheme backend, and installs that very Scheme value. Rocq checks
all three source/target definition pairs against the encoder proof. This lane
never reads `ps` to obtain code.

## Which execution path is observed

`shen/observe-encoder.shen` is a controlled loader, not an interception of the
stock `load` primitive. The pinned host forbids ordinary redefinition of
`eval-kl`, and its Scheme binding is immutable. We do not claim a hook was
installed into that primitive.

A fresh process loads the pinned overlay, Buri helpers, the structural tagging
adapter, and the observer. It does **not** load `shen/wire.shen` with the stock
loader first. The observer:

1. Selects compatible backend mode with an empty native-local map, clears its
   record accumulator, and reads the exact `shen/wire.shen` path.
2. Requires a `tc -` form followed by exactly three forms. This is the existing
   source-bound encoder profile, not support for arbitrary top-level effects.
3. Calls `shen.shen->kl-h` for each definition. This is the actual frontend's
   compilation entry point before `record-and-evaluate` installs the result.
4. Registers the function arity, passes that KLambda directly to
   `_scm.kl->scheme`, and passes the returned Scheme value directly to Scheme
   `eval`. There is one backend compilation per installed definition.
5. Records the input/target pair after evaluation returns successfully. It
   serializes the ordered three-pair record only after all installs finish.

This is real installation of captured targets in the controlled image. It is
not a later recompilation of source metadata, a native executable disassembly,
or a proof of the observer itself. An exception can leave an incomplete image;
that run cannot produce a successful release export. The process is discarded.
The observer is trusted execution tooling, never an untrusted-artifact sandbox.

`ports/observed-encoder.bits` is the literal transport input;
`ports/observed-encoder.sexp` is its readable transcript. The header is
`buri-observed-encoder-1`. The record contains exactly one source and one target
for each of `buri.wire-byte`, `buri.wire-string`, and `buri.wire`, in that order.
The exporter still depends on the tagging adapter and encoder executing
faithfully. Their source/metadata proofs and protocol theorems do not remove
that native execution assumption.

## Target semantics and proof

`EncoderScheme.v` defines an admitted first-order target semantics with an
explicit immutable recursive definition table. It retains sequential bindings,
lazy Boolean branches, variables, calls and the encoder's specified primitive
operations. Its relational execution describes successful finite derivations.
Errors have no successful derivation; it does not identify native exception
payloads or prove preservation of divergence or resource exhaustion.

The generic `anf_preserves` theorem proves administrative let insertion preserves
successful execution. In particular, a computed first operand of concatenation
is bound before a computed second operand. The proof uses a generic lexical
renaming lemma to shift the second operand under the new binder without capture.
This transformation is proved for all expressions in the admitted model, not
only the concrete capture. `exec_deterministic` proves unique successful results
for any fixed definition table.

`ObservedEncoder.v` decodes the actual Scheme into this target language. It
retains single-binding `let` and sequential `let*`, including their shadowing
and temporary variables. It rejects multi-binding parallel `let`, unknown
calls, free variables, missing/extra definitions, wrong arities and incorrect
recursive callees. The entire resolved target body must equal the proved
administrative expansion of the encoder body. The entire source body must
resolve to the original proved body. Checking both complete tables prevents
mixing a correct source with an unchecked target or omitting a troublesome
function.

Composite primitive forms are admitted only in their exact recognized shape:
`kl:floor` over division by 2, numeric parity, character extraction, byte-range
tests, and the backend's local-binding/string-tail expansion. The tail binder
and both uses must match. Boolean assertion is contracted only around the
specified integer-classification predicate, whose formal result is Boolean.
These are **primitive specification contracts**, not proofs of Chez or the Shen
helpers. Unexpected variants produce no certificate. Generic assert elimination
and arbitrary arithmetic rewrites are not allowed.

`paired_execution` connects successful source execution with execution of the
resolved captured target table. The concrete `observed_encoder_execution`
theorem also supplies exact wire identity, complete paired-record coverage,
source-file equality, target termination for every finite abstract datum, and
unique canonical output. Lexical meaning of captured target syntax is defined
by the admitted decoder and de Bruijn resolver. This is a formal specification
of the supported Scheme fragment, not a universal semantic theorem about the
Scheme reader or host evaluator. Abstract fuel is not native instruction cost.

## Remaining assumptions

The capture mechanism, reader/source correspondence, faithful primitive
representations, and Scheme `eval`/Chez execution remain trusted. The exact
source equation is included, but it does not prove the reader consumed those
bytes or that the observer reported truthfully. The source/backend hashes,
configuration, capture hashes and theorem evidence are recorded in the release
report. Artifact identity is not source-to-binary provenance.

Helper/global bindings can still be changed after capture. The theorem uses an
immutable table and specified primitive meanings. No certificate enforcement
or rebinding invalidation mechanism is implemented. There is no verified binary
or full-port claim. The old metadata validation lane remains separately labeled;
its metadata-to-executable assumption is not used by the new observed lane.

The known unrestricted native halving counterexample also remains. String
encoding only calls the helper on byte codes; the proven mathematical bound and
exhaustive native tests cover that finite domain. They do not establish an
unrestricted native arithmetic refinement.

## Release gates

Every proof run removes stale captures, runs a fresh observed load, requires a
completion marker, compares the capture/transcript to committed bytes, packages
literal bits, independently compares those packaged bytes, and checks the result
in Rocq with `coqchk` replay. The larger literal capture needs a 64 MiB process
stack for the native OCaml parser/checker; this is a resource setting, not an
alternative proof acceptance path.

Eight adversarial paired captures must fail their acceptance proofs: target tag,
divisor, callee, sequential-to-parallel binding substitution, source tag,
unbound temporary, reordered pairs and omitted pair. Only an actual proof
unification failure counts as rejection. Native tests exercise the installed
functions, show forged `ps` metadata does not influence the observed load, and
check malformed observer inputs. Rocq examples cover sequential scope,
shadowing, malformed tail bindings, primitive restrictions and completeness.
