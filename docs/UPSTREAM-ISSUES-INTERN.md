# Upstream issue drafts: `intern` (draft section for docs/UPSTREAM-ISSUES.md)

Drafted 2026-11-03 by the Wave-D primitives lane, for the lead to merge into
[UPSTREAM-ISSUES.md](UPSTREAM-ISSUES.md). **Not filed, and not reviewed
independently.** The review record at the end is a self-review only.

Pins and runtimes are the same as in UPSTREAM-ISSUES.md:

| Repo | Commit | Runtime used |
|---|---|---|
| tizoc/shen-scheme | `8d261518` (HEAD). `kl:intern` is byte-identical at the `v0.52` tag `fa071737`. | release asset `shen-scheme-v0.52-linux-x64-bin.tar.gz`, sha256 `aa711f57…c8c9` |
| Shen-Language/shen-cl | `4844072d` | Shen-CL image built from that commit with SBCL 2.6.8 by the Wave-C port-fix lane. Its `src/primitives.lsp` blob is `f9b11c8a` and `src/overwrite.lsp` is `8108c9d4` (both re-checked). The image sha256 is `5fd8dcfc…ac6e`. |
| ShenOSKernel | 43.1 (`ShenOSKernel-43.1.tar.gz`, sha256 `900eedef…1920`) | sources and `doc/` only |

Every native result on this page is **sampled**: one run of the real runtime.
The Rocq results cited are universal theorems about Búri's models of the
captured bytes, not about Chez or SBCL.

| # | Repo | Verdict | Kind |
|---|---|---|---|
| 5 | shen-scheme | confirmed | `intern` returns a number for digit-led names. This is an internal inconsistency and a cross-port divergence. It is not a violation of a written rule found in the pinned kernel tree. |
| 6 | shen-cl | confirmed, low priority | the `intern` escape mangling is not injective |

---

## 5. shen-scheme: `(intern "12")` returns the integer 12

**Title:** intern returns a number, not a symbol, for names such as "12", "007" or "1/2"

**Body:**

`kl:intern` (`src/primitives.scm` lines 15–21 at 8d26151, unchanged since
v0.52) passes a name through `string->number` when it has more than one
character and the first character is a digit:

```scheme
(define (kl:intern name)
  (cond ((equal? name "true") #t)
        ((equal? name "false") #f)
        (else (or (and (> (string-length name) 1)
                      (char-numeric? (string-ref name 0))
                      (string->number name))
                  (string->symbol name)))))
```

The compiler folds a literal call at compile time:
`[intern S] _ -> [quote (intern S)] where (string? S)` (`src/compiler.shen`
line 129). Compiled code therefore gets the same value. With the v0.52
release binary (`shen-scheme eval -l probe.shen`). The predicates are
Shen's; `scheme kind` comes from a `scm.` escape that calls Chez
`symbol?`, `exact?` and `integer?`.

| Input | Result | Shen `symbol?` | `integer?` | `number?` | Chez `symbol?` | Chez kind |
|---|---|---|---|---|---|---|
| `"12"` | `12` | false | true | true | false | exact integer |
| `"007"` | `7` | false | true | true | false | exact integer |
| `"1/2"` | `1/2` | false | false | true | false | exact **ratio** |
| `"1e5"` | `100000.0` | false | true | true | false | inexact |
| `"1.5"` | `1.5` | false | false | true | false | inexact |
| `"1e400"` | `+inf.0` | false | false | true | false | inexact |
| `"3.0"` | `3.0` | false | true | true | false | inexact |
| `"7"` (one character) | `7` | false | false | false | **true** | symbol |
| `"1+"`, `"12abc"`, `"1#2"` | the symbol | false | false | false | true | symbol |
| `"-5"`, `"+5"`, `"#x1F"` | the symbol (first character not a digit) | true | false | false | true | symbol |
| `"true"` / `"false"` | `true` / `false` (Booleans) | false | false | false | false | Boolean |

Further runs in the same session:

```
(integer? (intern "12"))                 => true     literal, folded at compile time
(eval-kl [integer? [intern "12"]])       => true
(define probe-k -> (intern "12"))        => (probe-k) is an integer
(define probe-rt S -> (intern S))        => (probe-rt "12") is an integer
(string->symbol "12")                    => error "cannot intern "12" to a symbol"
(str (intern "12"))                      => "12"
```

**What the pinned specification text says.** No written rule in the
ShenOSKernel 43.1 tree requires `intern` to return a symbol for these names:

- `sources/types.shen` gives `string->symbol` the type `string --> symbol`
  (line 171), but gives `intern` no type.
- `sources/sys.shen` lines 427–431 define `string->symbol` as `intern`
  followed by a `symbol?` check, raising `"cannot intern ~S to a symbol"`.
  The kernel therefore expects that `intern` may return a non-symbol.
  `string->symbol "12"` raises on **both** ports, because kernel `symbol?`
  needs an alphabetic first character (`analyse-symbol?`).
- The reader interns only `<sym>` tokens, which start with an `<alpha>`
  byte (`sources/reader.shen` lines 281–286). Ordinary source text never
  reaches the numeric branch.
- `doc/porting.md` (lines 148–158, "Unwelcome Symbols") lets a port
  reprogram `intern` to rename symbols, and says nothing about numbers.
- `doc/system-functions.md` defers to the System Functions document at
  shenlanguage.org. That host could not be resolved from this session, so
  **it was not consulted**. Any wording it has on `intern` remains to be
  checked before filing.

The draft therefore does not claim a violation of the written spec. The
issue is that the behaviour is inconsistent within the port and between
ports:

1. `(intern "7")` is a symbol, but `(intern "07")` is the integer 7.
2. `(intern "1/2")` makes an exact rational. No Shen arithmetic in this port
   produces one, because `/` goes through `non-rational-/`
   (`src/primitives.scm` line 26) to avoid exactly that value.
3. Shen-CL returns a symbol for every input in the table (below).
4. Búri's formal rule (`rocq/KLSemantics.v` `rule_intern`) maps every name
   other than `"true"` and `"false"` to a symbol. The divergence is
   therefore recorded against Búri's rule as OB-SCHEME-INTERN-NUMERIC,
   which is **refuted**. That rule is Búri's specification choice.

**Shen-CL comparison** (the image above, same probe file). Every input
gives a CL symbol whose name is the input. For example `(intern "12")` has
`symbol-name` `"12"`, and Shen `integer?` and `number?` are false. The
exception is the input containing `#`, which is mangled (finding 6).
`true` and `false` are the symbols that Shen-CL uses as Booleans. A literal
`(intern "12")`, its `eval-kl` form, and compiled and run-time calls all
give a symbol.

**Possible fix** (proposed as `ports/patches/shen-scheme-primitives.diff`,
not sent upstream):

```diff
-        (else (or (and (> (string-length name) 1)
-                      (char-numeric? (string-ref name 0))
-                      (string->number name))
-                  (string->symbol name)))))
+        (else (string->symbol name))))
```

A review of every `intern` call found by grep in `src/` and in the kernel
`sources/` found none that needs the numeric branch. If upstream relies on
it anyway, the alternative is to document it.

**Patched native check** (sampled). The patched definition was loaded into
the v0.52 binary through `(eval-kl [scm. "(define (kl:intern name) ...)"])`.
Run-time calls then return symbols: `(probe-rt "12")` gives a Chez symbol,
and every row of the table above becomes a symbol, except that
`"true"`/`"false"` stay Booleans. Two things did **not** change in the
overlay. A literal `(intern "12")` is folded by the compiler built into the
binary, which still calls the stock binding, and that literal stays the
integer 12. The kernel's compiled `concat` also keeps the stock binding.
Both need a rebuilt binary, which was not done. Reader output is
unaffected: `(read-from-string "[a 12 b 1.5 -3]")` still reads 12, 1.5
and -3 as numbers.

**Búri evidence** (`rocq/SchemeIntern.v`, audited in `rocq/Audit_Prims2.v`):

| Theorem | Kind | Statement |
|---|---|---|
| `intern_admitted` | ground derivation | the stock and patched byte excerpts read and decode to the reviewed ASTs |
| `stock_intern_body` | universal | exact denotation of the stock body for every string and every Chez table satisfying `chez_intern_ops` |
| `stock_intern_digit_led`, `stock_intern_twelve` | universal | on a digit-led name of length > 1 that the host reads as a number, the stock body returns that number. The number represents no KLambda symbol, while `rule_intern` returns the symbol. |
| `stock_patched_agree` | universal | elsewhere, stock and patched give identical results |
| `patched_intern_body`, `patched_intern_symbol`, `patched_intern_refines_rule` | universal | the patched body returns `#t`/`#f`/the symbol for **every** string, and refines `rule_intern` |

These hold for every table that satisfies the named contracts; they are not
proofs about Chez. The compile-time fold is outside them: it is covered
only in a binary built with the patch.

---

## 6. shen-cl (low priority): `intern` mangling is not injective

**Title:** intern maps "a#b" and "a_hash1957b" to the same symbol

**Body:** `|intern|` (`src/primitives.lsp` line 129 at 4844072) calls
`shen-cl.process-intern` (line 132). That function replaces `#`, `'`,
`` ` `` and `|` with `_hash1957`, `_quote1957`, `_backquote1957` and
`bar!1957`. `doc/porting.md` endorses this "unwelcome symbol" technique.
But a name that already contains the replacement text collides with the
escaped one, and `str` decodes both to the escaped form:

```
(= (intern "a#b") (intern "a_hash1957b"))   => true      Shen-Scheme: false
(= (intern "a|b") (intern "abar!1957b"))    => true      Shen-Scheme: false
(str (intern "a_hash1957b"))                => "a#b"     Shen-Scheme: "a_hash1957b"
(= (intern "ab") (intern "a_b"))            => false     (control)
```

The collision needs a name that contains the escape text literally, so it is
unlikely in practice. A possible fix is to escape the escape character too,
for example by doubling `_` before the suffix, so that the mapping is
injective.

**Búri evidence:** `CLStrings.intern_refines` (universal) proves that
`|intern|` refines `rule_intern` only on names **without** those four
characters. Its premise is the named contract
`CLStrings.cl_intern_ops.process_plain`, the identity behaviour of the
uncaptured LOOP body. The collision itself is sampled only.

---

## Review record (self-review, 2026-11-03)

This is not an independent review. Choices made to keep within the evidence:

- **Finding 5 is not framed as a spec violation.** The pinned kernel tree
  contains no typed or written rule for `intern`, and the kernel guards
  `string->symbol` against non-symbols. The online System Functions
  document was not reachable and was not checked. That check is an open
  item before filing.
- **Revision.** The obligation's identity names `fa071737` (the v0.52
  tag), while the matrix pins `8d261518`. The two `primitives.scm` blobs
  differ (`f07d5070` and `92b8875a`), but lines 15–21 are identical, and
  `git log -L15,21` shows a single commit (`8702c49`) in the available
  history.
- **Overlay limits.** The patched native check covers run-time calls only.
  Literal folding and calls already compiled into the binary need a rebuild.
- **Finding 6** is reported as a collision. Mangling itself is sanctioned
  by `doc/porting.md`. No proof covers the mangled names.
- **Profile divergences, not upstream issues** (`docs/PRIMITIVES.md`). For
  `(string->n "ab")` Shen-CL raises and Shen-Scheme returns 97. For
  `(n->string 55296)` Shen-CL returns a string and Shen-Scheme raises. Both
  are proved against Búri's rules (`CLStrings.string_to_n_long`,
  `CLStrings.n_to_string_surrogate`). Neither is drafted as an upstream
  issue: whether upstream intends a unit string, or rejects surrogates, was
  not established from a written source.
