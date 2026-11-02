# Handoff: independently confirm the upstream port findings

> **Status:** completed by an independent reviewer on 2026-11-02. Verdicts and
> every correction are recorded in [UPSTREAM-ISSUES.md](UPSTREAM-ISSUES.md#review-record-2026-11-02).
> The steps below remain valid for re-verification. Do not name a probe
> function `g`: it is a protected system function. Use `verify-g`.

You are verifying four claimed bugs before they are filed upstream. The drafts are in
[UPSTREAM-ISSUES.md](UPSTREAM-ISSUES.md). Treat every claim there as **unverified**.
Your job is to reproduce or refute each one from clean inputs. Do not take the
drafts' wording, or the Búri proofs, as evidence that the behaviour is real.

Report one verdict per finding: **CONFIRMED**, **NOT REPRODUCED**, or
**CONFIRMED WITH CORRECTIONS**. A finding marked CONFIRMED WITH CORRECTIONS must
list every corrected claim. For each finding, give the exact commands you ran and
their verbatim output. Then state whether it is a bug against a written
specification or only an internal inconsistency in the port.

Do not file issues, push or comment anywhere. Only report back.

## Inputs to pin

| Item | Exact identity |
|---|---|
| Shen-Scheme source | https://github.com/tizoc/shen-scheme at `8d261518db17fbfec32d1b268b40ed216b925c74` |
| Shen-Scheme runtime | release v0.52 asset `shen-scheme-v0.52-linux-x64-bin.tar.gz`, sha256 `aa711f576ea0ec96d86b0120eeba875153317a9af9e6a69f9c6ef4c00a4ad8c9` |
| Shen-CL source | https://github.com/Shen-Language/shen-cl at `4844072dde0208c3e4b99dcbfea58e4fdfd812e8` |
| SBCL | 2.6.8 (any official 2.6.x is acceptable; record the exact version) |
| Shen spec text | ShenOSKernel-43.1 `doc/porting.md` (from the shen-sources `shen-43.1` release tarball) |

Also check whether the upstream default branch has moved past these commits. If
it has, re-test on the new HEAD and say whether each finding still holds.

## Finding 1: Shen-Scheme `cond` fall-through

Claim: a `cond` with no true clause returns `#<void>`, where the spec requires
`(simple-error "condition failure")`.

1. Read `doc/porting.md` and quote the exact `(cond)` rule. Check that it really is
   a requirement for KLambda `cond`, not just an illustrative reduction.
2. Read `src/compiler.shen` `emit-cond` and `emit-cond-clauses`. Confirm no `else`
   clause is emitted.
3. Use the v0.52 binary directly (`shen-scheme eval -e ...`), with no Búri
   overlays. Run each of these:
   - `(eval-kl [cond [false 1]])`
   - `(define f X -> (cond ((= X 1) a)))` then `(f 2)`
   - `(trap-error (f 2) (/. E (error-to-string E)))`

   Record what each returns or raises.
4. Check whether Shen's own frontend ever emits a `cond` without a final `true`
   clause. Compiled Shen `define`s usually end with a `true` branch. Say whether
   ordinary user code can hit this, or only hand-written KLambda and `eval-kl`.
5. If you can, compare with another port such as Shen-CL. A different result
   there strengthens the report but is not required.

## Finding 2: Shen-Scheme `=` against a numeric literal

Claim: `(= X <number literal>)` compiles to `eqv?`, so it is false for an inexact
`X` equal to the literal. `kl:=` returns true for the same values.

1. Read `src/compiler.shen` `emit-equality-check` and `src/primitives.scm` `kl:=`.
   Confirm the `eqv?` clause and the use of Scheme `=` for numbers in `kl:=`.
2. Using the v0.52 binary with no Búri overlays, run:
   - `(* 2 (/ 1 2))`
   - `(integer? (* 2 (/ 1 2)))`
   - `(= 1 (* 2 (/ 1 2)))`
   - `(define verify-g X -> (= X 1))` then `(verify-g (* 2 (/ 1 2)))`
   - `(define h X Y -> (= X Y))` then `(h 1 (* 2 (/ 1 2)))`
   - `(= 1 1.0)`
3. The draft says the reader reads `1.0` as exact `1`, so the last form returns
   true. Confirm or refute that explanation.
4. Find out what Shen specifies for numeric `=` between integers and floats, if
   anything. If the spec is silent, the honest framing is "the compiled path
   disagrees with the port's own `kl:=`". Say which framing the evidence supports.

## Finding 3: Shen-CL `(* 0 <non-number>)`

Claim: `shen-cl.multiply` returns `0` for `(0, non-number)`, but raises for
`(non-number, 0)`.

1. Read `src/primitives.lsp` `|shen-cl.multiply|`. Confirm the
   `((or (zerop x) (zerop y)) 0)` clause and that it short-circuits.
2. **This has not been done yet. Please do it:** build Shen-CL at the pinned commit
   (`make sbcl` or the repo's documented build). In its REPL, run:
   - `(* 0 true)`
   - `(* true 0)`
   - `(* 0 "s")`
   - `(define m X Y -> (* X Y))` then `(m 0 true)`

   The earlier evidence called the wrapper directly in bare SBCL. The compiler may
   specialize or constant-fold `*`, so the REPL result for literal arguments could
   differ from the wrapper. Report both the literal and the function-call results.
3. Check whether `(* 0.0 x)` returning exact `0` (losing inexactness and the sign
   of zero) is intended. Mention it only as a side observation.

## Finding 4: Shen-CL `optimise-boolean-check` EQ rewrite (latent)

Claim: `[equal? X [Quote S]] -> [(cl eq) X [Quote S]]` is wrong for non-symbol
`S`, but ordinary Shen `=` cannot reach it.

1. Read `src/compiler.shen` `optimise-boolean-check` (around lines 101–128) and
   `emit-equality-check` (around line 238). Check whether any path from ordinary
   Shen source produces `(shen-cl.equal? X 'S)` with `S` a cons, string or number.
   The likely suspects are pattern-matching compilation, `lisp.` escapes, and
   macros. Report what you find.
2. In SBCL, confirm that `(eq (list 1 2) '(1 2))` is false while `shen-cl.equal?`
   on the same values is true.
3. Decide whether this is worth filing at all. A report that ordinary code
   cannot reach is low value. Recommend file, merge into another issue, or drop.

## Cross-checks against Búri (secondary evidence only)

These are proofs about captured source under Búri's own models. They support the
findings but do not replace running the real runtime:

- `rocq/SchemeCompose.v`: `cond_without_true_unread`
- `rocq/SchemeBranches.v`: `emit_cond_exact`
- `rocq/SchemeCompose.v`: `numeric_equality_preserves`
- `rocq/SchemeWrappers.v`: `stock_mixed_exactness`
- `rocq/CLWrappers.v`: `multiply_zero_absorbs_symbol`, `eq_rewrite_safe`, `eq_rewrite_unsafe`
- Ledger entries in `spec/obligations.json`: OB-SCHEME-COND-FALLTHROUGH,
  OB-SCHEME-EQ-LITERAL, OB-SCHEME-EQV-LITERAL, OB-CL-MULTIPLY-DOMAIN
- Sampled tests: `tests/scheme-compose.shen` (`cond-no-true-clause-falls-through`),
  `tests/primitives.shen`, and `ports/shen-cl-primitive-samples.lisp`
  (`sbcl --script ports/shen-cl-primitive-samples.lisp <shen-cl>/src/primitives.lsp`)

If a theorem's statement does not actually say what the draft claims, report that
too. It would be a Búri documentation error.

## Also check

- Search each upstream repo's open and closed issues and PRs for duplicates.
- Check that every line number and quoted snippet in the drafts matches the
  pinned commits exactly.
- Flag any wording in the drafts that overstates the evidence.
