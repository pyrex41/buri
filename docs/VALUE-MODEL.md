# KLambda value and store model (E2E-05) and per-port obligations

Status: **in progress**. This is the agreed semantic profile against which both
ports must prove representation relations. It is a Rocq definition
(`rocq/KLValue.v`, `rocq/KLSyntax.v`), not a description of either host. It
does not claim that Shen-Scheme or Shen-CL implement it; the obligation matrix
below names what each port must still prove, and where a sampled native
observation already shows a disagreement.

## Values

| Value | Model | Notes |
|---|---|---|
| Exact integer | `VNum (NInt z)`, `z : Z` | Unbounded. `+ - *`, exact division, comparisons and `=` are fully specified. |
| Inexact number | `VNum (NFloat bits)`, IEEE-754 binary64 bit pattern | Every inexact operation is a named profile slot (`inexact_op`, `inexact_cmp`, `int_div_inexact`, `float_text`). See numeric profile. |
| Symbol | `VSym name` | Names are sequences of Unicode scalar values. `true`/`false` are **not** symbols. |
| Boolean | `VBool b` | `intern "true"` yields the Boolean. `if`/`and`/`or`/`cond` reject non-Booleans with `XNotBoolean`. |
| String | `VStr text`, `text = list N` of code points | Character (code point) strings, not bytes. `pos`, `tlstr`, `n->string`, `string->n` index code points. |
| Empty list | `VNil` | Distinct from `false` and from every symbol. |
| Pair | `VCons a d` | Immutable tree; improper lists allowed. KLambda has no pair mutation, so pair identity is unobservable and pairs are never cyclic. |
| Vector | `VVec l`, heap location | Mutable, fixed length, identity by location; aliasing is visible (`KLExamples.vector_aliasing`). Bounds violations raise `XBounds`. |
| Stream | `VStream h`, environment handle | Stream state is owned by the environment (E2E-04 requests/responses). |
| Closure | `VLam x body env`, `VFrozen body env` | Lexical environment captured at creation. |
| Partial application | `VPartial f args` | Named global function; the name is resolved when saturated (late binding). |
| Exception | `VExn x` | First-class (passed to `trap-error` handlers). Classes listed below. |

Exception classes (`exn`): `XUser msg` (simple-error), `XUnboundVar`,
`XUnboundGlobal`, `XUndefinedFun`, `XNotCallable`, `XNotBoolean`, `XArity`,
`XPrim p` (primitive domain), `XDivZero`, `XBounds`, `XCondFail`,
`XBadDefinition` (duplicate parameters), `XIO e`, `XEvalKL`. All are catchable
by `trap-error`. `error-to-string` of a system exception uses the profile slot
`sys_message`: message text is port-specific and not part of the agreed
semantics; the exception class is.

## Store

`store = { heap; gvals; gfuns }`: vector heap (list of cell lists), the global
value namespace (`set`/`value`) and the global function namespace (`defun`,
initially the primitives). Namespaces are newest-first association lists;
redefinition is visible to every later call (`KLExamples.redefinition`).
`store_ok`/`wf` (KLWellFormed.v) require every location reachable from the
control, continuation, globals and heap cells to be allocated; it is preserved
by every step and every environment response (`step_preserves_wf`).

## Numeric profile (explicit, partially parametric)

* Exact integers: fully specified. Division of integers is exact when the
  remainder is zero (`(/ 4 2) = 2`, sampled on Shen-Scheme as integer 2), and
  otherwise the profile slot `int_div_inexact` (Shen-Scheme samples `(/ 7 2)` as
  `3.5`). Division by an exact zero raises `XDivZero` for any numerator (sampled:
  Shen-Scheme also errors on `(/ 1.0 0)`).
* Inexact numbers: **required but not yet pinned.** The representation is
  binary64 bit patterns; arithmetic, mixed exact/inexact comparison and
  equality, rounding, signed zero, infinities/NaN, and printing are profile
  parameters. No float operation is silently dropped: each has a named slot,
  and every theorem quantifies over all profiles. Pinning these slots to
  IEEE-754 semantics (e.g. via a float formalization) is an open E2E-05/E2E-17
  item; until then no inexact claim follows from these proofs.
* Rationals are **not** Shen values. Chez exact rationals and CL ratios are host
  representations that must never escape to Shen code; this is a per-port
  obligation (both hosts have them).
* Mixed comparison: the slot `inexact_cmp` decides `1 = 1.0` etc. Shen-Scheme
  samples `(= 1 1.0)` as `true` through `eval-kl`. The Scheme compiler emits
  `eqv?` when a literal number occurs in `=`; for mixed exactness `eqv?` is false
  in Scheme, so compiled and evaluated code may disagree. This is recorded as a
  **actual disagreement**, now confirmed natively (E2E-17, docs/PRIMITIVES.md):
  `(= X 1)` with X the inexact 1.0 is false on the compiled and eval-kl literal
  path and true through `kl:=` (sampled, `tests/primitives.shen`;
  `OB-SCHEME-EQ-LITERAL`). The literal lowering is safe exactly when the other
  operand is not inexact.
  Independently (E2E-15 Wave B, docs/SCHEME-PORT.md): the `(= 1 1.0)` reader
  sample is exact 1, but `(= 1 (* 2 (/ 1 2)))` is `false` on the compiled path and
  `true` through `kl:=` (OB-SCHEME-EQV-LITERAL, OB-SCHEME-EQV-EXACT).

## Per-port representation obligation matrix

The Chez tarm64le object representation, a Rocq relation `ChezRepr.rv` from
these values to machine words, and the SBCL arm64 layout table are in
[REPRESENTATION](REPRESENTATION.md) (E2E-21). There, `intern` of names such as
`"12"` is a sampled disagreement on Shen-Scheme: it returns the integer 12, not
`VSym`.

"Sampled" means a native Shen-Scheme 0.52 / Shen 43.1 probe in this wave (ground
observation, not proof). CL entries rest on the captured guard (docs/CL-PORT.md)
or on Common Lisp language facts and are **not** sampled here.

| Item | Agreed semantics | Shen-Scheme (Chez) | Shen-CL (SBCL) | Obligation (owner) |
|---|---|---|---|---|
| Truth values | `VBool`, distinct from symbols | `#t`/`#f`; sampled `(symbol? true)` = false, `(boolean? (intern "true"))` = true | Symbols `true`/`false` (captured `shen-cl.true?`) | Representation relation for Booleans; `symbol?`/`intern` agreement on CL (E2E-21, E2E-17) |
| Non-Boolean condition | `XNotBoolean` | `assert-boolean` raises; sampled for `if` and `and` | Strict guard proved in model (CLPortGuard) | Compiled conditions must keep the check, including `optimise-boolean-check` (E2E-15/16) |
| Empty list | `VNil`, not false | `'()` | `NIL`, which is also CL false and a symbol | CL must never let `NIL` act as false or symbol at Shen level (E2E-16/21) |
| Integers | unbounded `Z` | exact integers | integers | Representation is direct; overflow-free bignum contracts (E2E-17, 24) |
| Inexact | binary64, profile slots | flonums | default float format must be double | Pin slots to IEEE semantics; CL reader float format (E2E-05, 17) |
| Integer division | exact or `int_div_inexact` | `non-rational-/` (proved in StockDivision.v for exact inputs) | `shen-cl.divide` proved: exact quotient, DIVISION-BY-ZERO, or host double, never a ratio (`CLWrappers.divide_int`) | Pin `int_div_inexact` per port (E2E-17, OB-NUMERIC-PROFILE) |
| Mixed `=` | `inexact_cmp PEqual` | `eqv?` literal lowering vs `kl:=`: confirmed disagreement (sampled; OB-SCHEME-EQ-LITERAL and OB-SCHEME-EQV-LITERAL record the same defect from E2E-17 and E2E-15) | `absequal` uses `=` (1 = 1.0); the EQ rewrite is exact only for symbolic literals (`CLWrappers.eq_rewrite_safe`) | Fix or exclude the Scheme literal lowering (E2E-15/17) |
| Strings | code-point sequences | Unicode strings; sampled `(string->n (n->string 955))` = 955 | Unicode character strings | Encoding at IO boundary is bytes; file/stream decoding contract (E2E-11, 27) |
| `str` of a string | profile slot `str_other` | sampled: quoted, `(str "a")` = `"\"a\""`; `(str [])` = `"()"` | unsampled | Pin printing (E2E-17) |
| Symbols | code-point names | Chez symbols (package prefix conventions) | CL symbols in `SHEN` package | Name/package identity (E2E-11, 21) |
| `=` on closures | undefined (`Wrong`) | sampled `(= F F)` = true (identity) | `equal` identity | Admission must exclude, or profile must define identity (E2E-10/17) |
| `=` on vectors | structural; `Wrong` only past heap depth (cycles) | sampled `(= (@p 1 2) (@p 1 2))` = true; Chez `equal?` handles cycles | `equalp`-like semantics to confirm | Cyclic case and element equality (E2E-17) |
| Vector fill | profile slot `absvector_fill` | `(fail)` symbol `shen.fail!` (compiler source) | unsampled | Pin (E2E-17) |
| Vector bounds | `XBounds`, catchable | sampled Chez error, catchable | SBCL safety level dependent | Safety settings must keep checks (E2E-16, 24) |
| Applying a symbol | `XNotCallable` | sampled error "attempt to apply non-procedure" | `FUNCALL` of a symbol calls its function | Real divergence: CL must not call, or the profile changes (E2E-16) |
| `cond` with no true clause | `XCondFail` | sampled: returns `#<void>` (host value outside the model) | unsampled | **Actual disagreement** on Scheme: fix emitted `cond` or admit only exhaustive `cond` (E2E-15) |
| Zero-argument closure call `((lambda X X))` | `XArity` | sampled arity error | unsampled | Confirm (E2E-16) |
| Partial application binding | late (name resolved at saturation) | compiled curried lambdas refer to the global; arity fixed at compile time | unsampled | Redefinition with different arity (E2E-12, 19) |
| `thaw`, `do` | ordinary kernel functions in the namespace | compiler inlines both | compiler inlines | Inlining valid only while not redefined (E2E-12/15/16) |
| eval-kl of vector literals | rejected (`XEvalKL`) | compiler quotes absvectors as literals | unsampled | Profile choice to confirm (E2E-07/11) |
| Error messages | class fixed, text = `sys_message` | Chez condition text | CL condition text | Message relation per port (E2E-17) |
| Resource failure | `Fail RHeap`/`Fail RStack`, uncatchable | Chez heap exhaustion/handlers | SBCL storage/stack conditions may be catchable by `handler-case` | Catchability of resource conditions (E2E-24/25) |
| Object identity | vectors by location, streams by handle | `eq?` | `eq` (unreliable on numbers/chars) | No `eq` on numbers in emitted code (E2E-15/16) |
