# Findings against Shen/JIT

The lane moved to 0.6 (`934cfa56a5723165c63bf679f15d2d5214955a5d`, binary `e0acd513...10c8d`) on 9 November 2026.
These findings were not re-run on that binary; 0.6 still checks `fputc` and `fclose`, and its new `write-bytes`
checks `fwrite` (source read only).

Rechecked at `tizoc/shen-jit` `d3348cefbb2b209992039c1c0f55751241750364` (0.4), on the named RV64 binary (SHA-256
`5eb9f433...1872`) under `qemu-riscv64`. The sections below record what was found at 0.3
(`b4ccf2dff97031ee624692bb32d2addd18cacb39`, binary `2d444d92...7a5a`) and what 0.4 did to each.
**Finding 2 was filed as [tizoc/shen-jit#12](https://github.com/tizoc/shen-jit/issues/12) on 6 November 2026, and is fixed
at 0.4.** Upstream issues were searched on 6 November 2026 for "NaN", "write-byte" and "fputc"; none matched.

## 1. NaN equality: no longer a finding

At 0.2, `docs/semantics.md` said NaN equals nothing. At 0.3, line 89 says NaN "equals no other value, itself
included unless both sides are the same object". That matches the binary:

```text
[nan-text +nan.0]
[same-object true]
[other-nan false]
[in-lists true]
[in-lists-other false]
```

No issue to file. The behavior remains a gap between the KLambda profile and the port: a real has no identity
there, so `=` on one NaN object is tracked by `OB-JIT-NAN-IDENTITY`.

## 2. `write-byte` ignores a failed write: fixed at 0.4

At 0.4, `a0a6517` ("Raise when write-byte or close fails to write", which says `Fixes #12`) checks `fputc` and
`fclose`. On the 0.4 named binary, the reproduction below gives:

```text
[write-byte-result 65]
[close "close: No space left on device"]
[close-again []]
```

Output is buffered, so `write-byte` returns and `close` raises for what was left, leaving the stream closed;
`docs/semantics.md` section 12 now says so. `JitBytecode.v` raises on `JFailed` for both, and `jit_rules` no longer
sets `unchecked_writes`. The report at 0.3 follows.

### At 0.3

`write_byte` calls `fputc` and returns its argument whatever happens (`src/runtime/prims.c:1202`).
`docs/semantics.md:274` gives only "B from 0 to 255; returns B", and says nothing about failure.

Reproduction, with `/dev/full`, where every flush fails with `ENOSPC`:

```shen
(set s (open "/dev/full" out))
(print [write-byte-result (trap-error (write-byte 65 (value s)) (/. E (error-to-string E)))])
(nl)
(print [close (trap-error (close (value s)) (/. E (error-to-string E)))])
(nl)
```

Output, exit status 0:

```text
[write-byte-result 65]
[close []]
```

`close` reports no error either, so the byte is lost with no sign of it.

### Draft issue text

**Title:** `write-byte` and `close` don't report a failed write

> `write_byte` (`src/runtime/prims.c:1202`) ignores `fputc`'s result, so a failed write isn't an error. On
> `/dev/full`, where every write fails with `ENOSPC`:
>
> ```shen
> (set s (open "/dev/full" out))
> (write-byte 65 (value s))  \\ returns 65
> (close (value s))          \\ returns []
> ```
>
> Both succeed and the process exits 0, so the data is lost with nothing to catch. `docs/semantics.md` doesn't
> say either way.
>
> If this is intended, a line in section 12 saying that write failures aren't reported would settle it. Otherwise,
> `write-byte` could raise when `fputc` returns `EOF`, and `close` when `fclose` fails.
>
> Tested on 0.3 (`b4ccf2d`), a static RV64 build under `qemu-riscv64`. I read the `fputc` call on the shared
> source, but haven't run this on the release binaries.

Reproduced on the `shen-jit-0.3-linux-arm64-static` release (hash checked against `SHA256SUMS`), with the same output and exit status 0. `fputc` and `fclose` were still unchecked at upstream `cb442cf` when filed, read from source. The filed text is in the issue.

### Upstream response

On #12, tizoc said the behavior isn't intentional and is worth fixing. They also said Shen's default I/O
functions are deliberately under-specified for portability, and that they plan to add fuller `io` and `fs`
modules soon to cover this ground. So don't spend proof effort on the default stream primitives beyond what
the claim needs, and expect the I/O surface to change.

## Smaller prose points

Doc-only, no behavior at stake. Not worth separate issues. All four that remained at 0.3 are gone at 0.4: see the
`Findings against the source` section of [SHEN-JIT](../SHEN-JIT.md).

## tizoc/shen-jit#1 at 0.4

Not filed by this work, but tracked as `OB-JIT-ISSUE-1`. Kernel 43.4's factoriser takes a `cond` with no true clause.
On the 0.4 named binary, `(define f X -> (cond ((= X 1) a)))` gives `(fn f)`, `(f 1)` gives `a`, and `(f 2)` raises
"condition failure", the kernel's message; at 0.3 the same `define` failed in `shen.factor-recognisors`.

