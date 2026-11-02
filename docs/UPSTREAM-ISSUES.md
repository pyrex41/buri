# Upstream issue drafts (Shen-Scheme, Shen-CL)

Drafted 2026-11-02 from Búri proof work, then corrected after an independent
review on 2026-11-02 (see "Review record" at the end). **Not yet filed**: this
session had no access to open issues on `tizoc/shen-scheme` or
`Shen-Language/shen-cl`.

Upstream HEADs checked (both still equal the commits Búri pins):

| Repo | HEAD | Runtime used for reproduction |
|---|---|---|
| tizoc/shen-scheme | `8d261518db17fbfec32d1b268b40ed216b925c74` | release asset `shen-scheme-v0.52-linux-x64-bin.tar.gz`, sha256 `aa711f576ea0ec96d86b0120eeba875153317a9af9e6a69f9c6ef4c00a4ad8c9`. The release predates the source HEAD; the reviewer checked that the relevant conditional and equality code is unchanged. |
| Shen-Language/shen-cl | `4844072dde0208c3e4b99dcbfea58e4fdfd812e8` | full Shen-CL 3.2.0 image built from that commit with official SBCL 2.6.8 (`make precompile` with the Shen-Scheme binary, then `make build-sbcl`) |

No duplicate issue or PR was found: all 45 Shen-Scheme and 67 Shen-CL issue and
PR records were searched by title and body, though not every comment. Shen-CL PR
#57 is related precedent for numeric-equality lowering but is not a duplicate.

| # | Repo | Verdict | Kind |
|---|---|---|---|
| 1 | shen-scheme | confirmed | violates the written KLambda `cond` rule; reachable from ordinary code |
| 1b | shen-cl | confirmed (reviewer's discovery) | the same `cond` violation; returns `[]` |
| 2 | shen-scheme | confirmed | compiler/runtime inconsistency in numeric `=` |
| 3 | shen-cl | confirmed, but deliberate upstream | asymmetric zero short-circuit in `*`, preserved by upstream tests |
| 4 | shen-cl | confirmed, low priority | `EQ` rewrite miscompiles a reachable `lisp.` interop case |

---

## 1. shen-scheme: `cond` with no true clause returns `#<void>` instead of raising

**Title:** `cond` with no true clause returns #<void> instead of raising "condition failure"

**Body:**

ShenOSKernel 43.1 `doc/porting.md` (lines 95–96) defines the KLambda boolean
operations by equivalence:

```
(cond (P Q) ... R ...) = (if P Q (cond ... R ...))
(cond) = (simple-error "condition failure")
```

Shen-Scheme compiles `cond` to a host `cond` with no fallback clause
(`src/compiler.shen`, `emit-cond` / `emit-cond-clauses`, lines 232–242 at
8d26151). When no test is true the result is Scheme's unspecified value and no
error is raised. With the v0.52 release binary:

```
$ shen-scheme eval -e '(eval-kl [cond [false 1]])' \
    -e '(define f X -> (cond ((= X 1) a)))' -e '(f 2)' \
    -e '(trap-error (f 2) (/. E (error-to-string E)))'
#<void>
(fn f)
#<void>
#<void>
```

This is reachable from ordinary Shen code. The frontend adds an error fallback to
pattern-dispatch clauses, but an explicit `cond` in a function body is passed
through unchanged:

```
(shen.shen->kl-h [define f X -> [cond [[= X 1] a]]])
=> [defun f [V3013] [cond [[= V3013 1] a]]]
```

Possible fix: have `emit-cond-clauses` end with a clause that raises
`"condition failure"` unless the last test is the literal `true`.

## 1b. shen-cl: `cond` with no true clause returns `[]` instead of raising

**Title:** `cond` with no true clause returns [] instead of raising "condition failure"

**Body:** the same `doc/porting.md` rule as in 1. Shen-CL's `emit-cond`
(`src/compiler.shen` lines 190–201 at 4844072) emits a CL `cond` with no fallback,
so an exhausted `cond` yields NIL, which is Shen's `[]`. In the built Shen-CL 3.2.0
REPL on SBCL 2.6.8:

```
$ shen eval -e '(eval-kl [cond [false 1]])' \
    -e '(define f X -> (cond ((= X 1) a)))' \
    -e '(trap-error (f 2) (/. E (error-to-string E)))'
[]
(fn f)
[]
```

Possible fix: as in 1, a final clause that raises `"condition failure"`.

---

## 2. shen-scheme: `=` against a numeric literal uses `eqv?` and can disagree with `kl:=`

**Title:** `=` with a numeric literal compiles to eqv? and can disagree with kl:= on mixed exactness

**Body:**

`emit-equality-check` (`src/compiler.shen` lines 287–289 at 8d26151) emits `eqv?`
whenever either operand is a numeric literal. The runtime primitive `kl:=`
(`src/primitives.scm` lines 79–81) compares numbers with Scheme `=`. The two can
disagree when numerically equal values have different exactness, so the same
comparison gives different answers depending on whether an operand is a literal
or a parameter. With the v0.52 release binary:

```
$ shen-scheme eval -e '(* 2 (/ 1 2))' -e '(= 1 (* 2 (/ 1 2)))' \
    -e '(define verify-g X -> (= X 1))' -e '(verify-g (* 2 (/ 1 2)))' \
    -e '(define h X Y -> (= X Y))' -e '(h 1 (* 2 (/ 1 2)))'
1.0
false
(fn verify-g)
false
(fn h)
true
```

The host exactness, via `eval-kl`, explains the result. `(eval-kl [scm.exact? [* 2 [/ 1 2]]])`
is `false`, while `(eval-kl [scm.exact? 1.0])` is `true`, because the reader reads
`1.0` as exact `1`. That is also why `(= 1 1.0)` typed at the REPL returns `true`.
A computed inexact value is needed to see the difference.

This report does not claim that the porting document settles mixed
integer/float equality. The inconsistency between the compiled literal path and
the port's own `kl:=` is the issue.

Possible fix: emit numeric `=` (guarded by `number?` on the non-literal operand),
or call `kl:=`, instead of `eqv?` for numeric literals.

---

## 3. shen-cl: zero short-circuit in `*` is asymmetric (deliberate upstream; raise as a semantics question)

**Title:** (* 0 x) returns 0 for non-numeric x while (* x 0) raises — intended?

**Body:**

`|shen-cl.multiply|` (`src/primitives.lsp` lines 712–717 at 4844072) returns `0`
in its third clause when `x` is zero, without checking that `y` is a number.
`(zerop x)` short-circuits the `or`. In the built Shen-CL 3.2.0 REPL on SBCL 2.6.8:

```
(0-) (* 0 true)            => 0
(1-) (* true 0)            => The value |true| is not of type NUMBER
(2-) (* 0 "s")             => 0
(3-) (define m X Y -> (* X Y))
(4-) (m 0 true)            => 0
```

This behaviour is deliberately preserved by the upstream tests:
`tests/primitives-tests.shen` lines 80–81 assert both that `(multiply bad 0)` is
caught and that `(multiply 0 bad)` returns `0`. Lines 50–51 likewise keep an
integer zero result for a zero double-float product.

This is therefore not a regression, and the porting document does not
independently require an error here. The question for upstream is whether the
asymmetry, where the result depends on argument order for a non-number operand,
is intended. Búri's arithmetic profile treats `*` on a non-number as an error in
either position; that is Búri's specification choice, not the upstream one.

---

## 4. shen-cl (low priority): `optimise-boolean-check` rewrites `shen-cl.equal?` against quoted data to `EQ`

**Title:** optimise-boolean-check rewrites (shen-cl.equal? X 'S) to EQ, changing the result for quoted non-symbol data

**Body:**

`src/compiler.shen` lines 125–126 at 4844072:

```
[equal? X [Quote S]] -> [(cl eq) X [Quote S]]    where (= (cl quote) Quote)
[equal? [Quote S] X] -> [(cl eq) X [Quote S]]    where (= (cl quote) Quote)
```

`EQ` is not in general a valid replacement for the structural and numeric
equality that `shen-cl.equal?` performs. This is reachable through a KLambda
`lisp.` host escape. The same expression gives a different answer once it is
compiled as an `if` test:

```
$ shen eval \
  -e '(eval-kl [lisp. "(|shen-cl.equal?| (list 1 2) (quote (1 2)))"])' \
  -e '(eval-kl [lisp. "(eq (list 1 2) (quote (1 2)))"])' \
  -e '(eval-kl [if [lisp. "(|shen-cl.equal?| (list 1 2) (quote (1 2)))"] yes no])'
true
[]
no
```

`shen-cl.kl->lisp` shows the rewrite:
`[if [lisp. "(|shen-cl.equal?| (list 1 2) (quote (1 2)))"] yes no]` compiles to
`[IF [EQ [LIST 1 2] [QUOTE [1 2]]] ...]`.

Ordinary `=` does not reach this rewrite. With a function parameter it compiles
to `shen-cl.absequal` (`[DEFUN probe [X] [IF [shen-cl.absequal X [LIST 1 2]] ...]]`),
and `(if (= [1 2] [1 2]) yes no)` returns `yes`. No standard macro route creating
the problematic host call was found, although a user macro could inject one.

Suggested fix: add `where (symbol? S)` (or an equivalent symbol/NIL test) to both
clauses.

---

## Review record (2026-11-02)

An independent reviewer reproduced every finding without Búri overlays. They
used the checksum-verified Shen-Scheme release, and a fresh Shen-CL build from
the pinned commit with official SBCL 2.6.8. Corrections applied to the first
draft:

- **Release asset name:** corrected to `shen-scheme-v0.52-linux-x64-bin.tar.gz`.
- **Finding 1:** shown reachable from ordinary code. The reviewer found the same
  violation in Shen-CL, now finding 1b.
- **Finding 2:**
  - The first draft's example used `g`, a protected system function, so it could
    not run unchanged.
  - The line range is now 287–289.
  - "disagree whenever" is now "can disagree when numerically equal values have
    different exactness".
  - It is framed as a compiler/runtime inconsistency, not a spec violation.
- **Finding 3:**
  - Reproduced in the full REPL, so the old "not yet reproduced" caveat is gone.
  - The upstream tests that preserve the behaviour are now cited.
  - The draft no longer claims a written-spec violation.
  - Exact zero and the loss of signed zero are treated as intentional
    compatibility behaviour.
- **Finding 4:**
  - Now described as reachable through `lisp.`, with the working
    case-sensitive escape syntax; the draft had called it latent.
  - The "EQ differs for any cons/string/number" wording is replaced.
  - The draft's claim of a Búri proof of an unrestricted "if and only if" is
    removed. `eq_rewrite_safe`/`eq_rewrite_unsafe` hold only in Búri's CL model,
    whose `EQ` never identifies non-symbol data.

The Búri theorems cited in the handoff are evidence about Búri's models of
captured source, not about native behaviour:

| Theorem | What its statement establishes |
|---|---|
| `cond_without_true_unread` | Búri's decoder rejects this clause shape; not that Chez returns void |
| `emit_cond_exact` | correspondence to the modelled emitter output |
| `numeric_equality_preserves` | preservation of the emitted `eqv?` computation under stated assumptions |
| `stock_mixed_exactness` | a modelled result under specified host-operation answers |
| `multiply_zero_absorbs_symbol` | wrapper/model discrepancy under named host contracts |

The native reproductions above are the evidence for filing.
