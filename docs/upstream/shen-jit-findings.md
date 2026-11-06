# Findings against Shen/JIT at 0.3

Checked at `tizoc/shen-jit` `b4ccf2dff97031ee624692bb32d2addd18cacb39` ("Prepare 0.3"), on the named RV64
binary (SHA-256 `2d444d92...7a5a`) under `qemu-riscv64`. **Nothing here has been filed.** Upstream issues were
searched on 6 November 2026 for "NaN", "write-byte" and "fputc"; none matched.

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

## 2. `write-byte` ignores a failed write: survives

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

Before filing, confirm `close`'s path in `prims.c` and test a release binary.

## Smaller prose points

Doc-only, no behavior at stake. Not worth separate issues: see the `Findings against the source` section of
[SHEN-JIT](../SHEN-JIT.md) for which remain at 0.3.

