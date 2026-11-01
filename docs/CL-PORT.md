# Shen-CL conditionals: strict guard and actual IF lowering

This lane captures the actual `shen-cl.true?` definition in Shen-CL
`src/primitives.lsp` and the actual conditional lowering in `src/compiler.shen`
(`emit-if`, `optimise-boolean-check`, `optimise-boolean-sequence`,
`emit-boolean`) at commit `4844072dde0208c3e4b99dcbfea58e4fdfd812e8`.
It proves strict Boolean behavior of the guard and of every IF the captured
lowering emits, in an explicit, small Common Lisp model. It does **not** prove
the rest of the Shen-CL compiler, `compile-expression`, SBCL, the CL reader or
printer, the garbage collector, the runtime, or generated ARM code correct.

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
  exactly the source branch or error continuation. That theorem alone does not
  prove evaluation of a generated condition expression or certify the compiler's
  `optimise-boolean-check` transformations; the IF lowering section below does,
  under its stated premises.
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

The lowering modules (`CLLowering`, `CLLoweringCapture`, `CLLoweringSamples`)
are compiled by `make prove` from the stored inert captures; no SBCL or Shen-CL
checkout is needed for that. `scripts/proof-mutations` also requires three
altered copies of the stored capture (`tests/mutate-cl-lowering.py`) to fail
admission. `tests/cl-lowering-capture.shen` regression-tests the capture adapter
on inline sources; the adapter is not itself proved.

Actual source capture and native negative checks:

```sh
git clone https://github.com/Shen-Language/shen-cl /path/to/shen-cl
git -C /path/to/shen-cl checkout 4844072dde0208c3e4b99dcbfea58e4fdfd812e8
SHEN_CL_SOURCE=/path/to/shen-cl scripts/check-cl-port.sh
```

SBCL is not pinned by the charter yet. This lane was checked with SBCL 2.6.8,
`/nix/store/6z1jy0waigrsagpd8hg8crfaanrcrzax-sbcl-2.6.8` (nixpkgs
`885ba4d038f10c3d17d7a92e8c3cc185b99c9158`). Proposed pin: the nixpkgs revision
locked by Shen-CL's own `flake.lock` (`ac6b2166e7a9375683b8e98f860f273222337b16`),
recorded with its SBCL version and store path once realized.

For the lowering, the gate additionally requires `src/compiler.shen` to be clean
with the pinned blob, regenerates `CLLoweringCapture.v` byte-identically, rejects
four mutated captures (dropped guard, CL truthiness, swapped branches, `EQ` for
general equality) by failed Rocq admission, regenerates and checks the sampled
agreement module, and runs the SBCL contract samples.

Set `SBCL` and `COQC` if they are not on `PATH`. An extracted SBCL installation
may also need `SBCL_HOME`. This gate requires the pinned clean primitive source,
regenerates both captures into a temporary directory, compares them with checked-in
captures, then checks the universal captured-input theorem. It never rewrites
checked-in captures. It also checks native true/false, nonboolean values, foreign
package symbols, and condition/branch event order. Three mutated captures must
fail specifically because the admission equality computes to false: replacing
true with false, using CL truthiness, and changing the diagnostic string.

## Actual IF lowering (E2E-16, first item)

### Capture and admission (inert data)

- `shen/cl-lowering-capture.shen` is a Shen port adapter. It lexes the bytes of
  the pinned `src/compiler.shen` itself (parens, brackets, `|`, strings, atoms,
  `\\` and `\* *\` comments) and never calls Shen's reader, macroexpander,
  package expander or `eval`. It selects the unique top-level `package` form and
  inside it each of the four definitions exactly once, and emits
  `rocq/CLLoweringCapture.v`: the raw surface AST (no package prefixes applied),
  the package header, the git blob id `2d624377c02030f9513769f7bad11e84330b8c5a`
  and byte spans of every definition, and the capture host's answer to
  `shen.sysfunc?` for each captured spelling.
- `rocq/CLLowering.v` admits a capture by computed equality with a reviewed
  expected AST. Package identity is reconstructed in Rocq from the captured
  header with the kernel 43.1 `shen.internal?` rule (exception list, `sng?`,
  `dbl?`, system functions, variables, `shen.`/`shen-cl.` prefixes, Shen-CL's
  `lisp.` rule), so `true?` resolves to `shen-cl.true?` and `if`, `quote` and
  `let*` remain unprefixed. The system-function membership of the 22 relevant
  spellings is a reviewed table; the captured host observation must agree.
- The lowering is never re-implemented by hand: `run` interprets the admitted
  `define` clauses (patterns, repeated-variable equality, `where` guards, left to
  right list construction). Pattern-match failure, unsupported constructs and
  exhausted fuel are distinct results.

### Universal theorems (hypotheses explicit)

The CL model `ev` is a relation over an arbitrary state type with an arbitrary
primitive relation and an arbitrary relation for every unmodeled form, so
effects, nondeterminism and event traces are retained. It fixes only `QUOTE`,
`IF`, `PROGN`, `LET`, `LET*`, `AND`, `OR`, the Shen `and`/`or` macros, left to
right argument evaluation and the `shen-cl.true?` rule. `guard_rule_is_captured_guard`
proves that rule equals running the captured `primitives.lsp` guard.

- `optimise_sound`: for every datum `v` and every successful run of the captured
  `optimise-boolean-check`, `v` and the result are observationally equivalent in
  CL test position: `(shen-cl.true? v)` and the result give the same true/false
  selection, the same raised condition or Boolean error, and the same final
  state. Every one of the 29 clauses is justified separately, including the
  `IF`/`LET`/`LET*`/`PROGN` recursion, `and`/`or`/`not`, the equality
  specializations and the argument swap of literal operands (sound because the
  literal is effect-free).
- `emit_if_refines`: for every Test/Then/Else/Scope and every
  `compile-expression` function, the captured `emit-if` either returns the
  compiled Then for literal `true`, the compiled Else for literal `false`, or an
  `IF` whose evaluation is exactly Shen `if`: the compiled condition is evaluated
  once; `true` runs only Then, `false` runs only Else, any other value yields the
  Boolean error, and raised conditions propagate, with state threaded through.
- `emit_boolean_shape`, `emit_boolean_test`, `generated_if`, and
  `captured_*` corollaries instantiate the results at the stored capture.

Premises, all explicit in the statements:

- `primitive_contracts` (owned by E2E-17): `cons?`/`CONSP`, `string?`/`STRINGP`,
  `number?`/`NUMBERP`, `empty?`/`NULL`, the four comparisons, `shen-cl.equal?`
  versus `shen-cl.absequal`, `NULL`, `EQUAL`, `shen-cl.numeric-equal` and `EQ` in
  the shapes the optimizer uses, the value of `(fail)`, Shen `not` and CL `NOT`.
  `model_contracts` shows the hypotheses are jointly satisfiable (anti-vacuity);
  it is not a model of SBCL.
- `qsafe`: no `(shen-cl.equal? _ 'd)` or `(shen-cl.equal? 'd _)` with `d` other
  than a symbol or NIL. The optimizer rewrites those to `EQ`, which disagrees
  with Shen equality for a quoted cons, string or number; the native gate shows
  `(shen-cl.equal? (list 1 2) '(1 2))` is true while `EQ` is false. Such inputs
  are reachable only through `lisp.` escapes or direct calls of the internal
  `shen-cl.equal?`; this is a discovered port defect boundary, not assumed away.
- Diagnostic text of Boolean errors is quotiented: `shen-cl.true?` reports
  "boolean expected: not ~A", the `|if|` macro behind `and`/`or` reports
  "~S is not a boolean". `error-to-string` can observe the difference.
- `compile-expression` is an opaque function; its compile-time effects (gensym)
  are not modeled. `shen-cl.cl`/`kl` are modeled from `overwrite.lsp`/
  `compiler.shen` text: interning upcased names in package SHEN yields the
  inherited COMMON-LISP symbol, and `NIL` is the empty list (CL symbol-identity
  contract). The `bind-accessor-chains` post-pass in `eval-kl`, `factorise-defun`
  and the self-compilation of `compiler.shen` to `compiled/compiler.lsp` are not
  covered. Malformed shapes of modeled operators have no modeled behavior.
- SBCL execution and compilation, the CL reader, the printer (including any
  effects of formatting diagnostics) and the package system remain contracts.

### Sampled and native evidence (distinct kinds)

- `rocq/CLLoweringSamples.v`: 34 outputs of the actual `compiler.shen`, run on
  the Buri Shen host (Shen-Scheme, not SBCL), equal Rocq's interpretation of the
  admitted capture. Sampled agreement only.
- `ports/shen-cl-contracts.lisp`: SBCL evaluates only the selected
  `primitives.lsp` definitions (read with `*read-eval*` off) and samples every
  named contract, the strict `|and|`/`|or|` macros' event order, and the `qsafe`
  counterexample. Sampled native evidence only.

## Next composition

Cover `emit-cond-clauses` (which also calls the optimizer), discharge the named
contracts from captured `primitives.lsp` bodies (E2E-17), relate
`compile-expression` and `bind-accessor-chains` to the KLambda semantics, and
share a language-level Boolean contract with the Scheme port while retaining
separate host syntax and semantics. Coalton is neither a prerequisite nor proof
evidence for this lane.
