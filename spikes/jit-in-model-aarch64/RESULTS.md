# AArch64 spike: results (Shen/JIT Phase 0)

Run 5 November 2026. Evidence kinds follow `docs/ARM-FOUNDATION.md`. Nothing here is in
`scripts/prove`, and nothing here verifies Shen/JIT on AArch64.

## Verdict

- **Stock Shen/JIT works on Linux arm64** and passes its suites (sampled tests, not proof).
- **Búri's Sail foundation can state each instruction's behavior, including the generated
  words, but it can't express "the bytes I stored are the bytes I fetch".** The Sail model has
  no memory state, and Islaris has a fixed instruction table. Either one needs an added memory
  and fetch relation, and that relation becomes trusted.
- **The stock binary's syscalls fall outside Theorem's modeled surface**, which would matter on any
  CPU: executable `mmap`, `madvise(MADV_HUGEPAGE)`, and `prlimit64(RLIMIT_STACK)`. See Part A.
- **Recommended route for AArch64:** port the process layer by swapping its step function for an
  AArch64 subset, with each instruction form proved equal to Sail. Measured sizes suggest this is
  far smaller than lifting Sail's full fetch/execute loop, but no port was attempted.

## Pins

| Item | Value |
|---|---|
| Host | Apple CPU (implementer 0x61) through an OrbStack Linux VM, kernel 7.2.12, aarch64, Ubuntu 24.04 container, 4 CPUs, 10 GB, host load about 30 |
| Shen/JIT | `715bf60fb88647fa44ccb0a2f0b53c656290b6e1` |
| Kernel and stage 0 | Kernel 43.2 via `tools/ci-deps.sh`; 48 stage 0 files from the macOS build, matching `generated.sha256` (`stage0_check_rc=0`) |
| C compiler | gcc 13.3.0, glibc, dynamic link |
| `build/shen-jit` | `362163d9efeca154ae9dd04b7e5b8857700721267f23819cbf1b8c8664c79a96` |
| `build/runtime` | `588bd04f647e1c4a810108dc2eb3d68fd8b901b441f931abb8d2dff628bccfc8` |
| `build/shen-jit.img` | `98737960543bef9a98a9533e2012ff08ff4b253b292065d971332a50e2926d5b` |
| Coq toolchain | `coq/env.nix`: Coq 8.19.0, stdpp `a1a12e00`, coq-sail 0.19 `6918e8f3`, sail-arm `7d058164` (`armv9.v` sha256 `5169ce7f...`, confirmed on the downloaded text) |
| Theorem's model | `rocq-linux-process-semantics` `5e13f6b0` |
| Islaris source read | `theories/opsem.v` from the default branch via the GitHub API, not checked out at Búri's pin `c978e10f` |

`nix/arm/islaris.nix` hardcodes `x86_64-linux`, so `coq/env.nix` repeats the pins for the host's
system and leaves Islaris out. The container also needed `sandbox = false`, and a loop removing
`/homeless-shelter` between Nix builds. `armv9.vo` here has sha256 `126e9b41...`, which differs from
the x86-64 value in the docs (`8899bcc0...`); I didn't investigate why.

## Part A: stock Shen/JIT on Linux arm64

Evidence kind: native run. Samples only.

| Suite | Result |
|---|---|
| Contract examples | 157 passed, 0 failed |
| Kernel suite | 154 passed, 0 failed |
| Extension tests | 123 passed, 0 failed |
| `tests/cli.sh` | 161 passed, 0 failed |

Runtime size, without libc: 42,854 instructions, 128 distinct mnemonics, `.text` plus rodata
224,024 bytes by `size`. By object: `jit` 13,981; `sljitLir` 9,255; `prims` 6,355; `ffi` 2,739;
`heap` 2,470; `loader` 1,764; `objects` 1,429; `image` 1,020; `thread` 606; `dict` 603; `reader`
529; `profile` 503. The runtime contains atomics and pointer-auth forms (`ldaxr`, `stlxr`, `casal`,
`swpa`, `paciasp`, `autiasp`), a few of each. The forms that emitted code uses were not measured.

### Syscalls

Traced with `strace -f` on `script small.shen` (recursion, a redefinition, a caught error, file
write and read). The trace is a dynamically linked glibc build, so some rows disappear with a
static musl build. **Every arm64 number checked equals the model's table entry**: all 17 syscalls
below that have an arm, plus `rt_sigaction`, `rt_sigprocmask`, `clone` and `clone3`. `rseq` has no arm.

| Syscall | No. | Shape seen | Model |
|---|---:|---|---|
| `read` | 63 | files, stdin | Modeled |
| `write` | 64 | files, stdout | Modeled |
| `openat` | 56 | `O_RDONLY`, `O_WRONLY\|O_CREAT\|O_TRUNC` | Modeled; own-executable read below |
| `close` | 57 | | Modeled |
| `fstat` | 80 | | Modeled |
| `lseek` | 62 | `SEEK_SET`, for the appended image | Modeled |
| `brk` | 214 | | Modeled |
| `munmap` | 215 | anonymous | Restricted: recorded anonymous mappings |
| `mmap` | 222 | `PROT_READ\|PROT_WRITE`, anonymous | Modeled |
| `mmap` | 222 | `PROT_NONE`, 137 GB heap reservation | Restricted: fresh `PROT_NONE` is recognized; size against the model's budget not checked |
| `mmap` | 222 | **`PROT_READ\|PROT_WRITE\|PROT_EXEC`, 64 KB blocks** | **Unmodeled** |
| `mprotect` | 226 | `PROT_READ\|PROT_WRITE` on the reservation | Restricted: noaccess to read-write is the modeled case |
| `madvise` | 233 | **`MADV_HUGEPAGE`** | **Unmodeled**: only `MADV_DONTNEED` is answered |
| `prlimit64` | 261 | **`RLIMIT_STACK` read** | **Unmodeled**: the arm is limited to `RLIMIT_CORE` |
| `getrandom` | 278 | `GRND_NONBLOCK` | Modeled |
| `faccessat` | 48 | glibc loader only | Modeled |
| `exit_group` | 94 | | Modeled |
| `set_tid_address` | 96 | glibc startup | Modeled |
| `set_robust_list` | 99 | glibc startup | Modeled |
| `rseq` | 293 | glibc startup | **Unmodeled**: no table arm; not expected with musl, unconfirmed |
| `mmap`, `mprotect` | | file-backed libc mapping, `PROT_READ\|PROT_EXEC`, `PROT_NONE` from the loader | Unmodeled; goes away with a static binary |

- `clone` and `rt_sigaction` weren't called on this path. Neither was a cache-flush syscall (arm64
  flushes from user mode).
- The image is read by opening the executable's own path from `argv[0]`. The model's file state has
  to contain that file, and its argument and path limits (`SCOPE.md`) were not checked against this.
- "Modeled" means a table arm exists. Each call's exact arguments were not run through the model.

### Self-patching

Measured with a counter added to a scratch copy; these aren't the pinned hashes above.

| Run | Patch sites recorded | Sites rewritten by redefinition |
|---|---:|---:|
| `small.shen` | 0 | 0 |
| Contract examples | 24 | 2 |
| Kernel suite | 66 | 11 |

How it works on Linux (`src/runtime/jit.c`):
- `patch_put` records one site per open self tail call or inline guard: the address, cell, and a
  precomputed `b` to the slow path. The site must already be a `b` or a `nop`, or the process aborts.
- A redefinition (`patches_drop`) `memcpy`s the 4 bytes over the site and calls
  `__builtin___clear_cache` on them. The write-protect toggling is macOS-only.
- The whole runtime disassembly contains one `dc`, one `ic`, one `isb` and two `dsb`, which fits a
  single flush routine; I didn't trace that it's the only path.

So AArch64 needs a proof of stores over already-run code, which the RISC-V build avoids
(`PATCH_SELF 0`). A build profile with `PATCH_SELF 0` on arm64 would avoid it too, at some speed
cost, but that wouldn't be the shipping binary.

## Part B: can the foundation express "store code, then fetch and run it"?

### Islaris: no

Confirmed by reading `theories/opsem.v`. `seq_global_state` has `seq_instrs : gmap addr isla_trace`
and `seq_mem : mem_map`. `seq_instrs` appears only in the record, its settable instance, and the
`LDone` rule, which looks up the next trace by PC with `σ' = σ`. The `LWriteMem` rule updates only
`seq_mem`. So no step changes the table, and nothing relates it to memory. You could pre-populate
the arena's traces, but nothing would tie them to the stored bytes.

### Sail model: only as an unconstrained event

Evidence kind: model text read, and model theorems in `coq/BuriJitMem.v`.

- **Fetch:** `__InstructionExecute` calls `__FetchInstr`, which calls `AArch64_MemSingle_read` with
  an `AccessType_IFETCH` descriptor, down to `sail_mem_read`, which is exactly one
  `Interface.MemRead` event. (`read_mem_ifetch_` and `write_mem_` are `Axiom`s that nothing else in
  `armv9.v` uses, by grep, so they aren't this path.)
- **Reads and writes:** `iTrace_match` accepts any answer to an event. The monad has no memory.
- **`DSB` and `ISB`:** one `Barrier` event each, via `sail_barrier`, after feature checks.
- **`DC` and `IC`:** after system-access checks and translation, one `CacheOp` event via `CACHE_OP`.
  Their execute paths weren't run through a proof.
- **`BuriArmSeq.v`:** tracks registers only; memory, barrier and cache events carry any answer.

**Coherence isn't modeled at all.** A binary with cache maintenance and one without differ in their
event lists, and nothing in the model gives those events meaning. So the proofs can't yet show that
the sync variant is right and the `-DNO_SYNC` variant isn't. That would take an added relation over
traces, such as a sequential memory with a fetch rule. Published work on Arm instruction-fetch
semantics exists (Simner et al., ESOP 2020, cited from memory and not read for this spike).

Theorem's RISC-V model has a similar gap in another form: `fence.i` is a no-op, and fetches see the
latest stores. An AArch64 port can do better by treating a fetch from code written since the last
complete sync as `unmodeled`, which is sound for a program that does sync correctly.

### Checked theorems

Evidence kind: model theorem. Sources in `coq/`; gate in `coq/check.sh`.

| File | Theorem | Statement |
|---|---|---|
| `BuriJitWords.v` | `mov_decode` | `0x52800540` (generated) decodes to MOVZ, X0, 32-bit, imm 0x2A |
| | `ret_decode` | `0xD65F03C0` (generated) decodes to `RET` through X30 |
| | `str_decode` | `0xB90000A4` decodes to a 32-bit store, X4 to `[X5]` |
| | `blr_decode` | `0xD63F00A0` decodes to `INDCALL` through X5 |
| | `isb_decode`, `dsb_decode` | Barrier words, to their execute functions and arguments |
| | `ic_decode`, `dc_decode` | `IC IVAU`, `DC CVAU`, to the access check and `sysops` |
| `BuriJitModels.v` | `mov_model`, `mov_value_is_42` | Iff: result is exactly X0 := 42 plus the `SEE` write, in every state with `SEE < 698` |
| | `isb_model` | Iff: only the `SEE` write, with `FEAT_BRBE` and `FEAT_SPE` absent |
| | `ret_model`, `blr_model` | Iff: exact branch final state, **under Búri's `el2_cfg` (EL2)**, `FEAT_GCS` absent, both PAuth values |
| | `branch_target_id` | The target expression equals the register value |
| `BuriJitMem.v` | `read_after_write_unconstrained` | After any 4-byte write, any 4-byte read may take any answer |
| | `sail_mem_read_is_one_event` | The model's read is exactly one `MemRead` |
| | `sexec_read_any`, `sexec_write_no_state` | The sequential reading has no memory |
| | `isb_`, `dsb_`, `cache_op_no_register_effect` | One event, no register change |

That's 21 statements. Theorems mentioning `__DecodeA64` depend on its three Coq-stdlib axioms
(`sig_not_dec`, `sig_forall_dec`, `functional_extensionality_dep`). All seven in `BuriJitMem.v` are
closed under the global context. None depends on the model's memory axioms.

### Not proved

- **Fetch, and `__InstructionExecute`.** No theorem connects a word to what's fetched.
- **`str`'s execute path**, through address translation and `MemWrite`. Not attempted: Búri's docs
  §11.4 and §12.5 record the isla trace for the same kind of access (`ldur` at EL0) as resource-exhausted.
- **`DC` and `IC` execute paths, and `dsb` behavior.** `dsb` needs premises for `FEAT_TME` and
  `FEAT_XS`; not attempted.
- **EL0.** One attempt on `ret` at EL0 stopped: with `FEAT_VHE`, `FEAT_BRBE`, `FEAT_SPE` and
  `FEAT_GCS` absent, `nRW = 0` and `EL = 00`, the proof still reads `SCR_EL3`-dependent state in
  `ELUsingAArch32`, and `TCR_EL1` through `EffectiveTBI`, which also branches on target bit 55. So a
  process-level branch theorem needs a premise set for EL3, EL2 and EL1 configuration, plus a TBI
  premise or a TBI-aware postcondition. `ret_model` and `blr_model` therefore don't cover a hosted
  process yet.
- **The other words of `program.S`:** `adr`, `movz`/`movk`, `svc`. No decode theorem was attempted.
- **A composed run of the program.**

## Part C: process layer

Sizes measured from Theorem's model at `5e13f6b0`.

| Part | Files | Lines | Tie to RISC-V |
|---|---:|---:|---|
| `theories/Riscv` (decode, semantics, FPU) | 8 | 2,835 | Replaced |
| `RiscvSemantics.v` (step wrapper) | 1 | 1,085 | Replaced; includes fetch and ecall detection |
| `LinuxProcessSem/Sys` | 37 | 26,189 | Mostly kept: 7 files name machine state, 30 mention riscv at least in comments |
| `State.v`, `Run.v`, `StackLayout.v` | 3 | 12,532 | Adapted: 58, 34 and 17 riscv mentions; `Sv48` window, auxv, HWCAP are per-architecture |
| `LinuxProcessSem/Checks` | 135 | 70,228 | 53 files mention Riscv |
| `theories/Common` (proof library) | 97 | 80,734 | 60 files mention instructions or the step; largely redone |

The process model's whole `LinuxProcessSem` tree is 112,363 lines. The trusted machine part being
swapped is about 3,900 lines. Syscall numbers carry over for everything in the trace above.

**Option 1, recommended: swap the step for an AArch64 subset proved equal to Sail per instruction
form.** About 128 mnemonics in the runtime, plus emitted forms and libc. Each form gets what this
spike did for `mov`, at an EL0 premise set instead of EL2: a Sail decode and `sexec` theorem, then
equality with the subset's step. The process layer supplies memory, fetch and the sync rule, which
Sail leaves open. Cost per form from this run, under load: decode 0.1 to 35 seconds (`str` took 35 s), and about
90 s for `mov`, `isb`, `ret` and `blr` model theorems together, at EL2 and not yet at EL0.

Known obstacles:
- The toolchains conflict: Sail's Coq model is on 8.19 and Theorem's needs Rocq 9.2+. Building the
  42 MB `armv9.v` on Rocq 9.2 **was not tried**, and it's the first thing to test.
- Loads and stores are unsolved. `str` needs a theorem that, under an EL0 and MMU premise, translation
  yields a `MemWrite` to the process model's address, or an explicit statement that translation
  is trusted.
- Atomics and pointer auth in the runtime need decisions, though a single-thread profile may not reach them.

**Option 2: lift Sail's whole fetch/execute loop.** Most faithful, and much heavier. `__InstructionExecute`
also runs debug, PMU, SPE, BTYPE and single-step logic per instruction, unbridged per docs §12.6.
Translation is in the path of every fetch and memory access, and §12.5 records the isla trace for `ldur` at EL0 as
resource-exhausted. I would keep this as a later audit of Option 1 rather than the route to a first
theorem.

Neither option has been built. Line counts above are sizes of the existing model, not effort estimates.

## Reproduce

```sh
docker run -d --name buri-a64 --platform linux/arm64 --cpus=4 --memory=10g \
  -v "$PWD":/buri ubuntu:24.04 sleep infinity
# inside: install gcc, make, python3, strace, curl, xz-utils, git; install single-user Nix with
# sandbox = false and build-users-group empty, then:
nix-build spikes/jit-in-model-aarch64/coq/env.nix -A env -o /root/env
bash spikes/jit-in-model-aarch64/coq/check.sh
```

`check.sh` builds `program.S`, binds the eight words to its bytes (the generated ones to their
`movz`/`movk` immediates), compiles everything, audits assumptions, rejects one-bit mutants of both
generated words, and replays the result with `coqchk`.

### Last gate run

`W=/work4 bash coq/check.sh` from a clean directory: `CHECK_OK`, exit 0.

- `prog` sha256 `ed48b0ba0a1b427d3978f6c9b874bdc415741b2a77aea279d1dc0dfb3541dd6e`, all eight words bound.
  The earlier parent-session build of the same source hashed `e4d44f69...`; I didn't investigate why it differs.
- 21 `Print Assumptions` blocks audited, with only the three stdlib axioms above.
- One-bit mutants rejected: `52800540 -> 52800541` and `D65F03C0 -> D65F03C1`.
- `coqchk` passed. Its whole-library context lists 11 axioms: the model's 6 external primitives (`__SleepRequest`,
  `read_mem_`, `read_mem_ifetch_`, `read_mem_exclusive_`, `write_mem_`, `write_mem_exclusive_`) plus 5
  Coq-stdlib axioms. None is the spike's. No type-in-type, unsafe fixpoints or assumed positivity.
- Compile times under load: `BuriArmDecode` 314 s, `BuriArmFastPath` 218 s, `BuriJitWords` 185 s
  (3.4 GB peak), `BuriJitModels` 93 s.
