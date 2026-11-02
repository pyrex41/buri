# Upstream issue drafts (Shen-Scheme, Shen-CL)

Drafted 2026-11-02 from Búri proof work. **Not yet filed**: this session had no
access to open issues on `tizoc/shen-scheme` or `Shen-Language/shen-cl`.
Before filing, have the findings independently confirmed with
[UPSTREAM-ISSUES-HANDOFF.md](UPSTREAM-ISSUES-HANDOFF.md).

Upstream HEADs checked (both equal the commits Búri pins):

| Repo | HEAD checked | Runtime used for reproduction |
|---|---|---|
| tizoc/shen-scheme | `8d261518db17fbfec32d1b268b40ed216b925c74` (2026-10-21) | release v0.52 linux-x64 binary, archive sha256 `aa711f57…` |
| Shen-Language/shen-cl | `4844072dde0208c3e4b99dcbfea58e4fdfd812e8` (2026-10-16, "Prepare Shen CL 3.2.0 release") | SBCL 2.6.8 loading the wrapper definitions from `src/primitives.lsp` only (not a full Shen-CL image) |

A search of each repo's issues for `cond`, `eqv`, `void`, `equal`, `multiply`
and `optimise` found no existing report.

Evidence kinds are kept separate below. **Proved** means a Coq theorem about
the exact captured source. **Observed** means a run of the actual runtime.

---

## 1. shen-scheme: `cond` with no true clause returns `#<void>` instead of raising

**Repo:** tizoc/shen-scheme. **Severity:** correctness. A silent wrong value
replaces an error.

**Title:** `cond` with no true clause returns #<void> instead of raising "condition failure"

**Body:**

The KLambda porting spec (ShenOSKernel 43.1, `doc/porting.md`, boolean
operations section) defines:

```
(cond (P Q) ... R ...) = (if P Q (cond ... R ...))
(cond) = (simple-error "condition failure")
```

Shen-Scheme compiles `cond` to a Scheme `cond` without an `else` clause
(`src/compiler.shen`, `emit-cond` / `emit-cond-clauses`, lines 232–242 at
8d26151), so when no test is true the result is Scheme's unspecified value:

```shen
(eval-kl [cond [false 1]])                 \\ => #<void>, expected error "condition failure"
(define f X -> (cond ((= X 1) a)))
(f 2)                                       \\ => #<void>, expected error
(trap-error (f 2) (/. E (error-to-string E)))  \\ => #<void>; the handler never runs
```

Observed with the v0.52 release binary. Because no error is raised, code that
relies on `trap-error` around a non-exhaustive `cond` silently continues with
a non-Shen value.

Possible fix: have `emit-cond-clauses` end with
`[else [simple-error "condition failure"]]` (or the port's equivalent error
call) unless the last test is the literal `true`.

---

## 2. shen-scheme: `=` against a numeric literal uses `eqv?` and disagrees with `kl:=`

**Repo:** tizoc/shen-scheme. **Severity:** correctness. The same comparison
gives different answers depending on how it is written.

**Title:** `(= X 1)` compiles to eqv? and returns false for X = 1.0, unlike kl:=

**Body:**

`emit-equality-check` (`src/compiler.shen` lines 286–288 at 8d26151) emits
`eqv?` whenever either operand is a number literal:

```shen
V1 V2 Scope -> (order-call [eqv? ...]) where (or (number? V1) (number? V2))
```

The runtime primitive `kl:=` (`src/primitives.scm` lines 79–81) compares numbers
with Scheme `=`, so `1` and `1.0` are equal there. The compiled literal path and
the primitive therefore disagree whenever an inexact value meets an exact
literal. Observed with the v0.52 release binary:

```shen
(* 2 (/ 1 2))                     \\ => 1.0   ((integer? (* 2 (/ 1 2))) => true)
(= 1 (* 2 (/ 1 2)))               \\ => false  (literal path, eqv?)
(define g X -> (= X 1))
(g (* 2 (/ 1 2)))                 \\ => false
(define h X Y -> (= X Y))
(h 1 (* 2 (/ 1 2)))               \\ => true   (kl:= path)
(let A 1 B (* 2 (/ 1 2)) (= A B)) \\ => true
```

Note that `(= 1 1.0)` typed at the REPL returns `true`, because the reader reads
`1.0` as exact `1`. A computed inexact value is needed to see the bug.

Possible fix: emit `=` (guarded by `number?` on the non-literal operand) rather
than `eqv?` for numeric literals, or call `kl:=`.

---

## 3. shen-cl: `shen-cl.multiply` returns 0 for `(* 0 <non-number>)`

**Repo:** Shen-Language/shen-cl. **Severity:** correctness, and asymmetric. A
type error is silently swallowed in one argument order only.

**Title:** (* 0 true) returns 0 instead of a type error; (* true 0) errors

**Body:**

`|shen-cl.multiply|` (`src/primitives.lsp` lines 712–717 at 4844072):

```lisp
(defun |shen-cl.multiply| (x y)
  (cond ((and (typep x 'fixnum) (typep y 'fixnum)) (* x y))
        ((and (typep x 'double-float) (typep y 'double-float))
         (if (or (zerop x) (zerop y)) 0 (* x y)))
        ((or (zerop x) (zerop y)) 0)
        (t (* (|shen-cl.double-precision| x) (|shen-cl.double-precision| y)))))
```

In the third clause, `(zerop x)` short-circuits the `or`, so `y` is never
checked to be a number. Observed on SBCL 2.6.8 by loading the definitions from
`src/primitives.lsp` and calling the wrapper directly:

```
(shen-cl.multiply 0 'true)   => 0          ; expected: error (non-number argument)
(shen-cl.multiply 0 "s")     => 0
(shen-cl.multiply 'true 0)   => TYPE-ERROR ; zerop on a symbol
```

In KLambda, `*` on a non-number is an error, and the result should not depend
on argument order. Possible fix: check `(and (numberp x) (numberp y))` before
the zero shortcut.

(Not yet reproduced inside a full Shen-CL REPL as `(* 0 true)`. See the
verification handoff.)

---

## 4. shen-cl (latent, low severity): `optimise-boolean-check` rewrites `equal?` against any quoted datum to `EQ`

**Repo:** Shen-Language/shen-cl. **Severity:** low. This is latent: ordinary
KLambda `=` does not reach it.

**Title:** optimise-boolean-check turns (shen-cl.equal? X 'S) into EQ for non-symbol S

**Body:**

`src/compiler.shen` lines 125–126 at 4844072:

```shen
[equal? X [Quote S]] -> [(cl eq) X [Quote S]]    where (= (cl quote) Quote)
[equal? [Quote S] X] -> [(cl eq) X [Quote S]]    where (= (cl quote) Quote)
```

`EQ` agrees with `shen-cl.equal?`/`absequal` only when `S` is a symbol (or
`NIL`). For a quoted cons, string or number it differs. On SBCL 2.6.8:
`(shen-cl.equal? (list 1 2) '(1 2))` is true but `(eq (list 1 2) '(1 2))` is
false, and the same holds for mixed-exactness numbers and fresh strings.

Ordinary Shen `=` is compiled by `emit-equality-check`, and the clauses above
these handle unquoted number and string literals. So this is reachable only
through `lisp.` escapes or direct calls to the internal `shen-cl.equal?` with a
quoted non-symbol. Suggest adding `where (symbol? S)` to both clauses.

Búri proves (Coq, `rocq/CLWrappers.v`: `eq_rewrite_safe` / `eq_rewrite_unsafe`)
that the rewrite is exact if and only if the quoted datum is a symbol or `NIL`.

---

_Drafted by [Claude Code](https://claude.ai/code) from the Búri verification
work; please verify before filing._
