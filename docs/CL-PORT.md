# Shen-CL strict Boolean guard: first verification boundary

This lane captures the actual `shen-cl.true?` definition in Shen-CL
`src/primitives.lsp` at commit `4844072dde0208c3e4b99dcbfea58e4fdfd812e8`.
It proves its strict Boolean behavior in an explicit, small Common Lisp model.
It does **not** prove the Shen-CL compiler, SBCL, garbage collector, entire
runtime, or generated ARM code correct.

## What is checked

- `ports/shen-cl-capture.lisp` reads the pinned source, selects the actual
  `DEFUN`, and exports every cons, symbol package/name, and string in that
  definition. `#.` is represented by inert syntax, never executed. Native
  tests evaluate only the actual guard and `simple-error` definitions.
- `rocq/CLPortCapture.v` contains the captured reader AST, not a replacement
  implementation. Rocq computes admission against a reviewed expected AST.
  Changes to package identity, arguments, branch order, or diagnostic text
  fail admission. `ports/shen-cl-guard.sexp` is the matching inert text capture.
- `rocq/CLPortGuard.v` interprets the supported CL expression forms: variables,
  quoted symbols, `EQ`, `COND`, the particular formatting call and error call.
  `actual_guard_refinement` quantifies over every admitted source AST and every
  modeled input. Only Shen `true` and `false` return host truth values; all
  other modeled values produce the Boolean-error observation.
- `conditional_refinement` quantifies over arbitrary continuation result and
  state types. Given an already evaluated condition, the modeled guard selects
  exactly the source branch or error continuation. The theorem does not prove
  evaluation of a generated condition expression or certify the compiler's
  `optimise-boolean-check` transformations.
- `shen/cl-port-guard.shen` provides an inert admission adapter and executable
  reference contract. Its text admission compares exact capture bytes without
  calling Shen's macroexpanding source reader or evaluating captured code.
  The adapter is regression-tested; its implementation is not itself proved
  equivalent to the Rocq checker in this increment.

## Boundaries and assumptions

`Other n` abstracts nonboolean Shen inputs; it is not a formalization of all
Common Lisp object representations. Error text and formatting are abstracted.
In particular `FORMAT ~A` may invoke user-defined printers for arbitrary host
objects. The proof does not establish absence of printer effects, allocation
failure, or termination of arbitrary printer methods. The error continuation
must account for such effects in any future whole-runtime refinement.

The CL reader, extraction harness, package environment and correspondence of
these modeled operations to native CL remain explicit assumptions. The pinned
checkout and native tests provide reproducible provenance/evidence, not proofs
of those assumptions. The native conditional tests establish sampled evaluation
order only. Nothing here upgrades Shen's own logical derivations to Rocq proofs
without a separately checked certificate.

## Reproduce

Portable proofs (Coq 8.18/Rocq-compatible syntax):

```sh
coqc -Q rocq Buri rocq/CLPortGuard.v
coqc -Q rocq Buri rocq/CLPortCapture.v
scripts/check-shen tests/cl-port-guard.shen
```

Actual source capture and native negative checks:

```sh
SHEN_CL_SOURCE=/path/to/pinned/shen-cl scripts/check-cl-port.sh
```

Set `SBCL` and `COQC` if they are not on `PATH`. An extracted SBCL installation
may also need `SBCL_HOME`. This gate requires the pinned clean primitive source,
regenerates both captures into a temporary directory, compares them with checked-in
captures, then checks the universal captured-input theorem. It never rewrites
checked-in captures. It also checks native true/false, nonboolean values, foreign
package symbols, and condition/branch event order. Three mutated captures must
fail specifically because the admission equality computes to false: replacing
true with false, using CL truthiness, and changing the diagnostic string.

## Next composition

Connect captured output from `emit-if` and `optimise-boolean-check` to the same
strict guard theorem, preserving expression evaluation order and error behavior.
Share a language-level Boolean contract with the Scheme port, while retaining
separate host syntax and semantics. Coalton can be evaluated independently as a
compiler implementation aid; it is neither a prerequisite nor proof evidence
for this lane.
