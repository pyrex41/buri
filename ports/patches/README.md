# Proposed upstream port patches

Unified diffs against the exact pinned upstream files. Nothing here has been
filed or sent upstream. Each patch is pinned by sha256 in
`scripts/package-patched.py`, which applies it to the vendored upstream file
(blob-checked) and checks the blob of the patched result. The stock ports and
their refuted obligations are unchanged. The proofs describe the **patched**
code only.

| Patch | Applies to | Patched blob |
|---|---|---|
| `shen-scheme-compiler.diff` | tizoc/shen-scheme `8d261518` `src/compiler.shen` (blob `42ac753b`) | `8a0aa129` |
| `shen-cl-compiler.diff` | Shen-Language/shen-cl `4844072d` `src/compiler.shen` (blob `2d624377`) | `60522d09` |
| `shen-cl-primitives.diff` | shen-cl `4844072d` `src/primitives.lsp` (blob `f9b11c8a`) | `3872f83e` |
| `shen-cl-primitives-tests.diff` | shen-cl `4844072d` `tests/primitives-tests.shen` (blob `73ea5b85`) | n/a (not vendored) |

Evidence kinds are kept apart below. A **theorem** is a Rocq universal theorem
about the captured patched definitions. **Native** means a sampled run of the
real runtime, recorded in the lane report with the exact commands.

## Shen-Scheme finding 1: `cond` with no true clause

- **Patch:** `emit-cond-clauses` gets two new first clauses. `[] Scope` emits
  `[[true (compile-expression [simple-error "condition failure"] Scope)]]`.
  A final `[[true Body]]` emits only `[[true (compile-expression Body Scope)]]`,
  so a cond that already ends in a literal true gets no extra clause.
- **Theorems** (`rocq/SchemePatched.v`):
  - `patched_emit_cond_clauses_exact`: the patched emitter has an exact
    denotation.
  - `patched_cond_no_true`: every run on a clause list with no literal-true
    test ends in a `#t` clause holding the compiled
    `(simple-error "condition failure")`.
  - `patched_cond_reads`: under the stated read premises, the result is read
    as `(if T1 B1 (if ... E))`, where E is the reading of that compiled
    error. That is the porting rule `(cond) = (simple-error "condition failure")`.
  - The stock contrast is still `SchemeCompose.cond_without_true_unread`.
- **Native:** checked on the v0.52 binary by calling the loaded patched
  definitions directly. A full rebuild was not done. Loading the patch does
  not replace the compiler built into the binary.

## Shen-Scheme finding 2: `=` against a numeric literal

This is a compiler/runtime inconsistency: the compiled path and `kl:=`
disagree when numerically equal values differ in exactness. It is not framed
as a violation of a written spec.

- **Patch:** the numeric-literal clause of `emit-equality-check` emits
  `(order-call [(prefix-op =) C1 C2])`, which is `(kl:= C1 C2)`, in place of
  `eqv?`. The order-call structure and the left-to-right compilation order
  are unchanged.
- **Theorems:**
  - `patched_emit_equality_exact`: exact denotation of the patched emitter.
  - `patched_numeric_equality_is_kleq`: the numeric-literal path is read as
    exactly the call `(kl:= d1 d2)`. It therefore agrees with `kl:=` on every
    pair of values, including mixed exactness, whatever numeric profile
    `kl:=` has.
  - Premise: the uncaptured `prefix-op` answers `kl:=` for `=`. Upstream
    defines it as `*kl-prefix*` concatenated with `=`.

## Shen-CL: `cond` with no true clause

This was found by the independent review: `(eval-kl [cond [false 1]])`
returns `[]`.

- **Patch:** `emit-cond-clauses` `[] Scope` emits
  `[[(cl t) (compile-expression [simple-error "condition failure"] Scope)]]`.
  The existing clause for a literal-true test already drops the dead tail.
- **Theorems** (`rocq/CLLoweringPatch.v`):
  - `patched_cond_final_t`: every emitted clause list ends in a `T` clause.
    When no source test is literally `true`, its body is the compiled
    `(simple-error "condition failure")`.
  - `patched_cond_profile`: when every emitted test evaluates to NIL, the CL
    `COND` evaluates as that compiled error.
  - Ground derivations on the captured stock definition: `stock_cond_empty`
    and `stock_cond_false_only`. Stock emits no clause, and CL `(COND)` is NIL.

## Shen-CL finding 3: `(* 0 <non-number>)`

This is a **profile choice**, not a stock-port bug. Upstream deliberately
keeps the zero shortcut: `tests/primitives-tests.shen` asserts
`(multiply 0 bad) = 0`. The stock obligation is refuted only against Búri's
stricter arithmetic profile, in which `*` on a non-number is a domain error.

- **Patch:** the shortcut clause becomes
  `((and (numberp x) (numberp y) (or (zerop x) (zerop y))) 0)`. The upstream
  test must change too (`shen-cl-primitives-tests.diff`). `0.0 * 2.0` still
  returns integer `0`, as upstream's test requires.
- **Theorems** (`rocq/CLMultiplyPatched.v`):
  - `patched_multiply_admitted`: the packaged bytes match the reviewed AST.
  - `patched_multiply_int`: on integers the result is the exact product,
    unchanged from stock.
  - `patched_multiply_rejects_nonnumber`: a non-number in either position
    raises.
  - Host contracts: these hold for every host that satisfies
    `CLWrappers.sbcl_arith_ops` and the new `sbcl_nonnumber_ops`. One
    concrete host satisfies both (`model_satisfiable`).

## Shen-CL finding 4: `optimise-boolean-check` EQ rewrite

This is reachable through `lisp.` escapes. Ordinary `=` does not reach it.

- **Patch:** both EQ-rewrite clauses get `where (and (= (cl quote) Quote) (symbol? S))`.
- **Theorem:** `patched_optimise_sound` holds for every CL world that
  satisfies `primitive_contracts`, and for every Shen `symbol?` oracle that
  answers true only on symbols. It has **no qsafe premise**, so the rewrite is
  exact on its whole input domain. The stock theorem `optimise_sound` still
  needs qsafe.
- **Caveat:** `CLWrappers.eq_rewrite_unsafe` is an "iff" only within Búri's
  CL model (`model_h`), not a native SBCL iff.

## Regenerating

`make prove` re-applies every patch into `_build/patched`. It then checks
`ports/compiler-branches-patched.shen` against the patched upstream file,
recaptures the patched definitions, and compares them with the committed
`rocq/CompilerBranchesPatchedInput.v`, `rocq/CLLoweringPatchCapture.v` and
`rocq/PatchedPrimitiveSources.v`.
