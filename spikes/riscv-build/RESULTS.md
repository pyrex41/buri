# Spike 2: Shen/JIT on static musl RV64

Phase 0, spike 2 of the Shen/JIT verification plan. Shen/JIT commit `715bf60`, unmodified except
for `shen-jit-rv64-arena.patch`.

**Verdict: go.** SLJIT's RISC-V backend worked with no backend changes, and a static RWX code arena
runs the full language suites with no `PROT_EXEC` syscall. All of this ran under `qemu-riscv64`, not
under Theorem's model and not on RISC-V hardware. Four model gaps are listed under "Blockers".

## Build

```sh
docker run --rm --platform linux/arm64 -v "$PWD":/spike ubuntu:24.04 bash /spike/build.sh
```

| Item | Value |
|---|---|
| Compiler | `zig cc` 0.13.0 (clang 18.1.6), `-target riscv64-linux-musl -mcpu=baseline_rv64 -fno-pie -no-pie` |
| Zig archive SHA-256 | `041ac42323837eb5624068acd8b00cd5777dac4cf91179e8dad7a7e90dd0c556` |
| Emulator | qemu-riscv64 8.2.2 (Ubuntu 24.04), linux/arm64 container |
| Stage 0 | Pinned host and kernel 43.2 from `make deps`; matches all 48 `generated.sha256` stage 0 entries |
| `runtime` SHA-256 | `de349ea06fc770e1dcf735f416a1713c93715aa7371528001918bdd635dcbd38` |
| `shen-jit.img` SHA-256 | `36670c54330f7d9a12f45c966ca498ee59550a5d2fb7ed33d5bbefd9d06a7789` |
| `shen-jit` SHA-256 | `603b0d582310b3a82540148fd3f434a452c0cd1a43f2aa4504e595705db25d8d` |
| Rebuild | A second clean checkout in the same container gave byte-identical `shen-jit` |
| ELF | `ET_EXEC`, one `PT_LOAD` flagged RWE, base `0x10000`, no `PT_TLS`, no `PT_INTERP` |

The patch changes one line of `heap.c` and adds `local.mk` plus `spikes-overlay/arena.{c,h,lds}`. The
Makefile and SLJIT are untouched: SLJIT's own `SLJIT_EXECUTABLE_ALLOCATOR=0`,
`SLJIT_MALLOC_EXEC`, `SLJIT_FREE_EXEC` and `SLJIT_CACHE_FLUSH` hooks are enough.

The 64 MiB arena is `NOBITS` at the end of the segment. Allocation failure takes the documented path
in `docs/semantics.md` section 14: the process terminates with a diagnostic.

## Test results

| Suite | (a) stock allocator, `STATIC=1` | (b) arena (`603b0d58`) |
|---|---|---|
| Contract examples | 157 passed, 0 failed | 157 passed, 0 failed |
| Kernel tests | 154 passed, 0 failed | 154 passed, 0 failed |
| Extension tests | 123 passed, 0 failed | 123 passed, 0 failed |
| Búri corpus (scratch `conf-jit.shen`) | 107 passed, 1 failed | 107 passed, 1 failed |
| `tests/cli.sh` | 134-136 of 140 | 133-135 of 140 |

- **Búri corpus:** the one failure is `huge-product`, the documented lack of bignums. arm64 gives the
  same result.
- **`tests/cli.sh`:** failures fall in two groups, present in both variants:
  - Four always fail, from running through a QEMU wrapper script: `bare-runtime`, `application`,
    `save-exe-one-image` (each expects a directly runnable executable) and `profile` (the sampler sees
    QEMU's translated code). I confirmed by hand only that `bare-runtime`'s message appears when run
    directly; the other three weren't separately confirmed.
  - The `interrupt-compiled-early*` checks fail intermittently, 0 to 3 of them per run. They
    send SIGINT to a run under emulation at load around 30. I did not find the cause. Signals are
    outside the planned claim, and the arena isn't the cause, since the stock variant fails too.
- **GC stress, `test-native`, `test-ffi`, `test-stlib`, `fuzz-native`:** not run.

## Syscalls against Theorem's model

Traced with `qemu-riscv64 -strace` on the final variant (b) binary; the `madvise` row comes from
an earlier arena build without the `heap.c` change. Runs: small program (`script`), `eval -e`, REPL, stage 1, contract
examples.

The "Model" column comes from **reading** `theories/LinuxProcessSem/Sys` at
`5e13f6b0`. Nothing was executed in the model.

| Syscall and shape | Where | Model |
|---|---|---|
| `set_tid_address`, `exit_group`, `close` | All | Modeled |
| `brk(NULL)`, `brk(addr)` | All | Modeled |
| `mmap(NULL, n, RW, PRIVATE\|ANON)` | All; up to about 2,400 per run | Modeled, with non-deterministic placement |
| `mmap(NULL, n, NONE, PRIVATE\|ANON)` | Heap reservation, once | Modeled ("fresh `PROT_NONE`") |
| `mmap(brk, 4096, NONE, PRIVATE\|ANON\|FIXED)` | musl guard page, once | Modeled ("contained `MAP_FIXED` guard-page overwrite") |
| `mprotect(reservation, 32 MiB, RW)` | Heap semispaces, twice | Modeled (`PROT_NONE` to RW) |
| `munmap` of the above | All | Modeled |
| `mremap(..., MREMAP_MAYMOVE)` | Stage 1 only | Modeled shape, exact conditions not checked |
| `madvise(MADV_HUGEPAGE)` | Stock heap | **Unmodeled**; removed by the patch |
| `riscv_flush_icache` (259) | Not called; arena build uses `fence.i` | **Not in the syscall table** |
| `clone`, `futex` | **Never called** in any trace | Parent-only `clone`; only `thread_start` reaches it in source |
| `mmap`/`mprotect` with `PROT_EXEC` | **Never called** | Deliberately unmodeled |
| `openat(rel-path, O_RDONLY\|O_LARGEFILE)` | Image and source files | Flags modeled; see Blockers |
| `openat(rel-path, O_WRONLY\|O_CREAT\|O_TRUNC)` | Contract examples | Flags modeled |
| `lseek(SEEK_END/SEEK_CUR)`, `read`, `readv`, `writev` | All | Modeled |
| `ioctl(fd, TIOCGWINSZ)` | musl stdio | Modeled (`-ENOTTY` for every model fd) |
| `prlimit64(0, RLIMIT_STACK, NULL, old)` | Startup | Modeled; 8 MiB |
| `clock_gettime(MONOTONIC/REALTIME/PROCESS_CPUTIME_ID)` | Time primitives | Modeled |
| `rt_sigaction(SIGINT, SA_RESTART, NULL)` | **REPL only** (`catch_interrupts`) | **Unmodeled**: `SA_RESTART` fails closed |
| `rt_sigprocmask(SIG_UNBLOCK)` | REPL only | Modeled |
| `pselect6(1, ...)` | REPL only | Modeled for some shapes; this shape not checked |

Memory: the heap reserves `PROT_NONE` then commits two 32 MiB semispaces with `mprotect`. The guest
stack and small objects come from musl's `malloc`, over anonymous RW `mmap`. The guest stack
is separate from the C stack. C code runs on the main thread's stack, whose limit is read as 8 MiB,
the model's value.

## Instruction counts

| Binary | Instructions | `.text` |
|---|---|---|
| `runtime` (no image) | 72,268 | 211,376 bytes |
| `shen-jit` (with image) | 72,268 | same; the image holds no native code |

Counted from `objdump -d` of the linked `runtime`, by function, with function ownership from each
object's symbols:

| Group | Instructions | In the planned claim? |
|---|---|---|
| `jit.c` | 18,253 | Yes |
| `sljitLir.c` (with RISC-V backend) | 16,622 | Yes |
| libc and compiler-rt | 16,994 | Partly |
| `prims.c` | 5,333 | Yes |
| `objects.c` | 3,265 | Yes |
| `ffi.c` | 2,766 | Excluded, but linked |
| `heap.c` | 2,595 | Yes |
| `loader.c` | 1,923 | Yes |
| `main.c` | 1,091 | Yes |
| `image.c` | 1,009 | Yes |
| `dict.c` | 729 | Yes |
| `thread.c` | 718 | Excluded, but linked |
| `reader.c` | 516 | Yes |
| `profile.c` | 454 | Excluded, but linked |

The binary also generates code at run time. Peak arena use, including 16-byte block headers:
229,168 bytes for `(+ 1 2)`, 621,696 for the contract examples, 2,954,000 for the kernel tests.
Those counts are from a build differing only in arena tracing.

The image is 764,680 bytes. `elf_snapshot.py` accepts the binary, but writes the arena's zeros as hex:
about 129 MiB in total for 64 MiB. An 8 MiB arena gives 17 MiB, and it passed contract (157/0)
and kernel (154/0), so 8 MiB is the better size for proofs.

## Blockers and open questions for the model

1. **Image loaded from a file.** The binary reads its image from `argv[0]`, or searches `PATH` for it.
   The model only has what its `in_fs` input declares, with no link between that file and the ELF. A
   statement would need the premise "this file holds these bytes". Embedding the image in the ELF as
   loaded data avoids that but needs an `image_load` change. Not attempted. I also did not confirm how
   the model treats a relative key with a `/`, such as `build/shen-jit`.
2. **`fence.i` from user space.** The model treats `fence.i` as a no-op, so proofs can't catch a
   missing flush. On real multi-hart Linux, a user-space `fence.i` isn't enough if the thread migrates
   between harts; that is what `riscv_flush_icache` is for, and the model lacks it. So this build
   matches the model and QEMU, but isn't a safe recipe for real RISC-V Linux as it stands.
3. **REPL.** `rt_sigaction` with `SA_RESTART` fails closed. The theorem has to cover non-REPL modes
   (`script`, `eval`), or the REPL needs a build without interrupts.
4. **Toolchain differs from Theorem's** (clang 20.1.8 and their musl). This doesn't affect statements
   about exact bytes, but their proof library's musl lemmas may not match these bytes.

## Not done

- No execution or proof in Theorem's model. That is spike 1.
- No RISC-V hardware.
- `arena.c` is spike-quality and untested apart from the suites above.
- Excluded code (`thread.c`, `ffi.c`, `profile.c`) is still linked. No build yet removes it.
