# Native runs of the proposed patches

All evidence on this page is **sampled**: single runs of the real runtimes.
None of it is a proof. The patches were applied to scratch copies outside
this repository with `patch -p1`.

## Shen-Scheme (v0.52 release binary)

Archive sha256 `aa711f576ea0ec96d86b0120eeba875153317a9af9e6a69f9c6ef4c00a4ad8c9`.

No full rebuild was done. Loading Shen definitions into the binary does not
replace the compiler built into it, because `eval-kl` and the loaded
`emit-cond` keep calling the binary's own bindings. So this check:

1. loads `ports/compiler-branches.shen` (stock) or
   `ports/compiler-branches-patched.shen` (patched);
2. calls the loaded `_scm.emit-cond-clauses` and `_scm.emit-equality-check`
   directly;
3. runs the emitted Scheme with Chez `eval`, through
   `(eval-kl [scm. "(lambda (x) (eval x))"])`.

Command: `shen-scheme eval -l <defines> -l scheme-emit.shen`.

| Probe | Stock | Patched |
|---|---|---|
| `emit-cond-clauses [] []` | `[]` | `[[true [error [quote *toplevel*] "condition failure"]]]` |
| cond `[[false 1]]`, emitted | `[cond [false 1]]` | `[cond [false 1] [true [error [quote *toplevel*] "condition failure"]]]` |
| cond `[[false 1]]`, run | `#<void>` | raises `"condition failure"` |
| same, inside `(guard (e (else 'caught)) ...)` | `#<void>` | `caught` |
| cond `[[false 1] [true 2]]`, emitted and run | `[cond [false 1] [true 2]]` => `2` | same |
| `emit-equality-check X 1 [X]` | `[eqv? X 1]` | `[kl:= X 1]` |
| run with `X = (exact->inexact 1)` | `false` | `true` |
| run with `X = 'a` / `2` / `1` | `false` / `false` / `true` | `false` / `false` / `true` |

The same binary with no overlay, through the ordinary REPL path:

| Expression | Result |
|---|---|
| `(eval-kl [cond [false 1]])` | `#<void>` |
| `(define fcond X -> (cond ((= X 1) a)))`, then `(fcond 2)` | `#<void>` |
| `(* 2 (/ 1 2))` | `1.0` |
| `(= 1 (* 2 (/ 1 2)))` | `false` |
| `(eqone (* 2 (/ 1 2)))`, where `(define eqone X -> (= X 1))` | `false` |
| `(eqxy 1 (* 2 (/ 1 2)))`, where `eqxy` compares two variables | `true` |

## Shen-CL (full images, SBCL 2.6.8)

Build steps:

1. `cp -r /home/user/shen-cl` to a stock copy and a patched copy.
2. In the patched copy, apply `shen-cl-compiler.diff`,
   `shen-cl-primitives.diff` and `shen-cl-primitives-tests.diff`.
3. `scripts/fetch-kernel.sh ShenOSKernel-43.1.tar.gz` (sha256 verified).
4. `make precompile SHEN=<shen-scheme v0.52>`.
5. `make build-sbcl SBCL=/nix/store/6z1jy0waigrsagpd8hg8crfaanrcrzax-sbcl-2.6.8/bin/sbcl`.

Probes were run with `bin/sbcl/shen eval -l cl-repro.shen`. Each value is
the result, or the error message caught by `trap-error`.

| Expression | Stock | Patched |
|---|---|---|
| `(* 0 true)` | `0` | error (`The value ...`) |
| `(* true 0)` | error | error |
| `(* 0 "s")` | `0` | error |
| `(mul 0 true)`, where `(define mul X Y -> (* X Y))` | `0` | error |
| `(mul 0 [1 2])` | `0` | error |
| `(mul [] 0)` | error | error |
| `(mul 0 7)` | `0` | `0` |
| `(mul 3 7)` | `21` | `21` |
| `(mul 0.0 2.0)` | `0` | `0` |
| `(mul 0 1.5)` | `0` | `0` |
| `(eval-kl [cond [false 1]])` | `[]` | error `"condition failure"` |
| `(fcond 2)` | `[]` | error `"condition failure"` |
| `(eval-kl [cond [false 1] [true 2]])` | `2` | `2` |
| `(eval-kl [lisp. "(\|shen-cl.equal?\| (list 1 2) (quote (1 2)))"])` | `true` | `true` |
| `(eval-kl [if [lisp. "<same>"] yes no])` | `no` | `yes` |
| `(eval-kl [if [lisp. "(\|shen-cl.equal?\| (quote foo) (quote foo))"] yes no])` | `yes` | `yes` |

This confirms upstream finding 3 in a real image: `(* 0 true)` returns `0`
on stock Shen-CL.

Upstream test suites, run on both copies:

| Suite | Stock | Patched (with the test diff) |
|---|---|---|
| `make test-sbcl` | 154 passed, 0 failed | 154 passed, 0 failed |
| `make test-compiler` | all passed | all passed |
| `make test-port` | `PORT-TESTS-PASS 333` | `PORT-TESTS-PASS 333` |
