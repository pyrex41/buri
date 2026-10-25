# Remaining trust: obligations and counterexamples

This audit distinguishes mathematical protocol proofs, execution tests, source
review, and assumptions about the machine that produced an artifact. None of
these alone certifies a Shen port. `make report` records the distinctions.

## Findings that change the boundary

**Unrestricted native halving is false on the pinned host.** The source-linked
Rocq encoder uses `Nat.div2` and its `byte_correct` theorem quantifies over all
natural inputs. On Shen-Scheme v0.52, however:

```
(floor (/ 9007199254740995 2))  => 4503599627370498
mathematical floor             = 4503599627370497
(buri.wire-byte 9007199254740995 8) => "10100000"
correct low eight bits            = "11000000"
```

The pinned backend maps `/` to `non-rational-/`, which converts a nonintegral
rational result to inexact arithmetic. This is a counterexample to the proposed
unrestricted native refinement, not to the Rocq theorem. The helper remains
internal; do not give callers a native all-natural-input guarantee.

The string encoder calls the byte helper only on codes below 256 with count 8.
`ByteDomain.string_byte_domain` proves that the mathematical recursive call
sequence remains in codes 0–255 and counts 0–8. `tests/trust.shen` checks every
one of those 256 × 9 native input pairs against a subtraction-only bit oracle,
and checks halving, character conversion, string tail, and tagging for all 256
bytes. Those are finite-domain tests run on a trusted host, not kernel-checked
execution proofs. The domain theorem concerns the specified recursion; it is
not a native execution trace theorem. Large integers encoded by `buri.wire` are
printed and then encoded character by character, not passed to `wire-byte` as
large numeric inputs. Their spelling contract remains open.

**Registered source metadata does not identify executable code.** In a fresh
image, replacing `(put buri.wire shen.source ...)` changes `(ps buri.wire)` while
`(buri.wire [])` continues to return "00". The regression restores the metadata
before ending. This demonstrates why validating `ps` cannot certify installed
code, even if its captured bytes are authentic. Source loading without such
substitution is still a process assumption, not a theorem.

**The tagged transport protocol is now proved lossless.** `CaptureTag.v` defines
its canonical tagged representation and proves byte-string recovery, tree
recovery with sufficient fuel, injectivity, and composition with the existing
wire codec. It covers all finite trees with numeric syntax 0–256, arbitrary
byte strings, symbols, and improper pairs. The bound is the frontend's syntax
restriction, not a limit on integer data carried by the wire encoder.
`capture_root_exact` says that acceptance of a canonical tagged root validates
that exact root, with complete definition coverage and program preservation.
The canonical-tag premise is explicit. These proofs do **not** establish that
the native `buri.kl-node` implementation produces that representation. Its
source, compiler path, primitives, and execution still need refinement.

## Obligation ledger

| Boundary | Evidence and remaining assumption | What would discharge it |
|---|---|---|
| Capture origin and freshness | Fresh-process export markers, stale-input removal, committed diffs, and hashes; provenance still trusted | Observe capture at the actual compilation/execution boundary, bind source, compiler inputs/outputs and loaded artifact in one checked manifest; an external process identity/root of trust remains |
| `ps` metadata versus installed code | Concrete counterexample above; registered-body validation only | Capture the KLambda actually submitted to `eval-kl` and the Scheme actually submitted to `eval`/compilation; validate that pair and bind the installed artifact |
| Typed tagging adapter | Generic lossless protocol and exact-root theorem; native implementation unverified | Source-bound adapter evaluation proof with a native-value representation relation, then validate its actual compiled body |
| Primitive semantics and representation | All reachable byte/count combinations tested; unrestricted halving disproved | Primitive-by-primitive refinement on reachable types/ranges; separate exact integers, floats, symbols, byte strings, pairs and booleans; prove decimal spelling and classification helpers |
| Shen reader and frontend | Exact encoder source equation; three registered KLambda bodies checked | Link actual reader/compiler input to captured output; validate supported instances or prove compiler transformations generally, including macros and factorization |
| Shen-Scheme backend | Twelve arithmetic schemas and three observed encoder targets checked; administrative-let preservation proved | Extend target semantics/validator to the encoder's actual Scheme: sequential lets, conditionals, recursive calls, strings, pairs, arithmetic and explicit errors; prove each admitted transformation |
| Chez and native artifact | Pinned release archive and local binary hashes; source-to-binary correspondence unproved | Reproducible build evidence plus machine-code validation or a verified backend; reproducibility alone proves identity, not semantic correctness |
| Dynamic loading and rebinding | Sealed lane uses private lexical procedures with checked syntactic closure and target/helper linkage; synchronized native rebinding test; stock and legacy guard paths remain mutable | Refine constructor and Chez lexical/library execution; discharge the 27 primitive-root contracts and internals. See [SEALED](SEALED.md). |
| Exceptions and resources | Models distinguish returned, exhausted and stuck; native exceptions/stack/heap not refined | Relate native exceptions and termination outcomes explicitly; separate partial correctness from resource adequacy and prove or bound the required resources |
| Rocq checker/toolchain | No custom axioms; independent `coqchk` replay | Keep a small explicit checking base; independently replay/diversify or use a verified checker; its executing machine still needs a trust root |
| Theorem/specification fidelity | Reviewed admitted semantics and explicit hypotheses | Review/refine against language and port behavior; counterexample-driven domain correction; proofs cannot establish that a chosen specification expresses user intent |
| Shen certificate checker and evaluator | Formal foundations and native tests; executable correspondence open | Prove refinement of `shen/kernel.shen` and `shen/klambda.shen`, preserving rejection/unsupported/exhausted distinctions |
| Older equation bridge and packaging | True exported equations checked; byte comparisons and hashes | Prove original-source correspondence for the exporter; keep literal byte packaging outside semantic acceptance and audit it independently |
| OS, files, CPU and hardware | Assumed for every execution and hash/read/write | Explicit deployment trust base, integrity controls and independent replay; no whole-stack theorem currently exists |

A proof about artifact contents cannot establish where those contents came from.
Likewise, signatures or attestations establish who asserted provenance under a
key/process trust model; they do not prove program behavior.

## Pinned source review

Review targets are immutable revisions, not the current default branches:

- [Shen-Scheme primitives](https://github.com/tizoc/shen-scheme/blob/8d261518db17fbfec32d1b268b40ed216b925c74/src/primitives.scm):
  `non-rational-/`, `kl:str`, `kl:=`, `kl:eval-kl`. The last translates a form and
  passes the result to Scheme `eval`; it does not consult `ps` to recover code.
- [Shen-Scheme compiler](https://github.com/tizoc/shen-scheme/blob/8d261518db17fbfec32d1b268b40ed216b925c74/src/compiler.shen):
  `binary-op-mapping`, `emit-equality-check`, `order-call-inputs`, `kl->scheme`.
  Division and equality dispatch are semantically significant. Sequential lets
  inserted to order calls cannot be discarded without an execution argument.
- [Shen system definitions](https://github.com/Shen-Language/shen-sources/blob/ec16a9fa4fc2e87e2aa336fb1ae30e8ac2266394/sources/sys.shen):
  `ps` reads the source property; `symbol?` includes language-level classification,
  so it cannot be replaced by a bare Scheme `symbol?` assumption. Only the pinned
  typechecker overlay is loaded from this revision; review of another source
  file does not establish that the binary contains that file's implementation.

The first two source blob identities already appear in `toolchain.lock.json`.
These are review evidence, not proof that the release binary was built from them.

## Observed compilation advance

The observed compilation path is now implemented for the three encoder
definitions; see [OBSERVED](OBSERVED.md). It captures and installs actual
KLambda/Scheme pairs and validates the target fragment, including its sequential
bindings. The pure tagging targets are now captured and proved in a fixed helper model; native observer/IO truthfulness remains open. A fresh call that *recompiles* `ps` output is useful for
compiler testing but still does not show what was installed earlier. Capture
must occur on the load path, and the artifact must bind transitive helper and
primitive identities. Keep all of these obligations visible until each is
actually discharged; do not label protocol roundtrip as adapter verification or
bounded native tests as a universal port proof.

## Captured native execution checkpoint

[NATIVE](NATIVE.md) records code-linked constructor assembly, fixed helper-body
contracts, exact division and instruction-level rebinding isolation. These
replace whole-helper assumptions in the admitted native model. They do not
prove Chez's primitive implementations or the mapping from its executing
machine to that model. The legacy guard remains outside the sealed path.

## Universal codec and pure adapter checkpoint

[CODEC-CORRESPONDENCE](CODEC-CORRESPONDENCE.md) discharges the abstract-codec to
captured native-model gap for finite supported datums. It also proves captured
pure tagging-body execution and composes it with encoding and decoding. The
encoder uses the existing 27 primitive roots; tagging additionally uses `cons`,
`list`, and `string?`. The new `string?` mathematical classification contract
is not a proof of Chez's implementation. Fixed helper-table assumptions, native
representation, bootstrap observer/tagger and IO remain explicit. This does not
certify the stock inexact encoder, arbitrary Shen compiler inputs, or live global
exporter behavior under rebinding.

## Bootstrap and observer-effects checkpoint

[OBSERVER-PROVENANCE](OBSERVER-PROVENANCE.md) proves the captured boolean-aware
bootstrap tagging bodies and exact installer effect ordering/failure behavior.
It checks the captured entry's read/parse/snapshot variable flow and begins
source-pinned upstream compiler-pass preservation. Native effect truthfulness,
reader and whole-compiler correctness, source/binary identity, and live mutable
observer bindings are still assumptions. No model trace theorem is labelled
native IO verification. The discovered `and` final-value decoder bug is fixed
and all earlier proofs are replayed against the correction.
