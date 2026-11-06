# Shen/JIT lane (E2E-37 to E2E-41)

Status: **Phase 1 in progress. Nothing about Shen/JIT is verified.** This lane has a written
scope, a Rocq semantic profile, and an executable bytecode semantics that has been compared
with the binary on samples. No theorem yet relates that semantics to KLambda or to machine
code.

The goal is the zlib-style claim in the [plan's gate](../spikes/GATE.md): the exact binary
refines Búri's KLambda semantics, or stops with a named resource failure.

## The named build

Every claim is about this one build, and not about any upstream release.

| Item | Pin |
|---|---|
| Source | `tizoc/shen-jit` `715bf60fb88647fa44ccb0a2f0b53c656290b6e1`, release 0.2 |
| Patch | [`spikes/riscv-build/shen-jit-rv64-arena.patch`](../spikes/riscv-build/shen-jit-rv64-arena.patch): a static RWX code arena and no `MADV_HUGEPAGE` |
| Target | Static `ET_EXEC`, musl, RV64GC, one RWX `PT_LOAD` |
| Binary | SHA-256 `603b0d582310b3a82540148fd3f434a452c0cd1a43f2aa4504e595705db25d8d`, including its image |
| Kernel | 43.2, archive SHA-256 `23c71508...`; Búri's shared lanes are on 43.1 with PR117 |
| SLJIT | `a0020dd49a21020434ff838fc308626c48cd8f05`, as vendored |
| Process model | `theorem-labs/rocq-linux-process-semantics` `5e13f6b0f82936aa5d006438e07e265c5d9fcfc4` |
| Prover | Rocq 9.3.0, OCaml 5.2.1 for the process model; the same `rocq/Jit*.v` sources under Coq 8.18.0 in `make prove` |

**Excluded from the claim:** threads, FFI and pointers, `lib/native.shen` and hand-written code,
the profiler, Ctrl-C handling, `save-executable`, the REPL, and backtrace text. In the
model each of these primitives stops with `RExcluded`, and `excluded_prims_stuck` states that. The
code is still linked in the binary (`OB-JIT-EXCLUSIONS-ENFORCED`).

**Upstream has moved.** On 6 November 2026, `main` was 15 commits ahead at `6270d18`, and the
difference is material: `jit.c` +817/-93, `ops.h` +100/-3, `prims.c` +121/-19, `heap.c` +128/-41,
`loader.c` +36/-10, `lower.shen` +8/-4, `bytecode.md` +69/-5, and changed stage 0 hashes. Nothing
here applies to it. Proofs bind to exact bytes, so re-pinning is a deliberate step.

## Claim wording

The only claim available today:

> A Rocq specification of Shen/JIT's bytecode exists for one pinned RV64 build. It has been
> compared with that binary on samples under QEMU.

When the composition theorem exists, the claim will read:

> For the binary with this SHA-256, in the named process model, and for admitted inputs within
> its memory budget, each behavior refines the KLambda semantics under the Shen/JIT profile, or
> stops early with a named resource failure.

**Do not say:**

- "Shen/JIT is verified", without the build and its limits.
- Anything about the arm64 or x86-64 binaries, or about upstream releases. None of them is covered.
- That agreement with the binary is proof. The differential runs are tests.
- That cache coherence is covered. The process model treats `fence.i` as a no-op.
- That threads, FFI or hand-written native code are covered.

## Trusted base

Trusted even when the lane closes: the Rocq kernel and logic, the process model's description of
Linux and QEMU, its RISC-V semantics, the ELF snapshot tool, the theorem statements, and the
hardware or QEMU underneath. Until proved, these are also assumptions: the musl code the binary
links (`OB-JIT-LIBC`), and the `e_hash`, `e_oom` and `e_stack` parameters.

## Input boundary

A run's input is `argv`, the modeled file system, and stdin, within the process model's
`Run.valid_input`, which rejects `/` in arguments after `argv[0]`.

| Mode | Bytes | Route to KLambda |
|---|---|---|
| `shen-jit script NAME` | The file `NAME`, with no `/`, in the modeled file system | Kernel reader and compiler, then `eval-kl` per form |
| `shen-jit eval ...` | The arguments | The same route |
| `repl` | Excluded: it installs a signal handler the model refuses |

So "an admitted KLambda program" has two levels. Phases 2 to 4 are stated for KLambda forms passed
to `shen-jit.eval-kl` in a state reached from the image. Bytes to those forms go through kernel code
running on Shen/JIT, and belong to Phase 5 with the shared frontend packages (E2E-11, E2E-12). A form
is admitted when the lowerer accepts it; a form it rejects raises, and that is part of the claim.
Inputs that overflow the C stack through `=` are not covered (`OB-JIT-ISSUE-3`).

## Image obligation

The binary's hash covers its heap image, about 765 KB of its 1 MB on arm64, which stage 1 made by
running the runtime itself. Validating stage 0 doesn't cover that. `OB-JIT-IMAGE` requires decoding
the image in Rocq and relating it to the KLambda store after initialisation, or proving stage 1 is an
instance of the main theorem. Separately, the run reads the image from its own file, which the
process model doesn't relate to the loaded binary (`OB-JIT-IMAGE-FILE`).

## What exists

| File | Content |
|---|---|
| `rocq/JitFloat.v` | binary64 over bit patterns in exact integers, printing and decimal parsing |
| `rocq/JitBytecode.v` | Syntax, loader checks, primitives, machine, one-step function `next` |
| `rocq/JitMeta.v` | Determinism, explicit stuck classification, loader and control laws |
| `rocq/JitProfile.v` | `KLValue.profile` instance and the deviation table |
| `rocq/Audit_Jit.v` | Assumption audit of 18 statements |
| `tests/shen-jit/` | Capture from the binary, packaging, Rocq harness, known differences |
| `scripts/check-shen-jit.sh` | `make check-shen-jit`, the opt-in gate |

Sources live in `rocq/`, so one copy compiles under both provers: the only rewrite for 9.3 is
the import line, and the gate refuses any other difference.

**A departure from AGENTS.md's usual split:** Búri normally keeps executable semantics in Shen and
checks them in Rocq. This semantics is executable in Rocq and has no Shen counterpart. See Decisions.

## Semantics limits

- **No identity for pairs, strings or reals.** `same?`, `tagged?` and `deref` on two of them stop
  with `RIdentity`, as does `=` on two NaNs.
- **Sealed calls** read the current function cell, not a slot bound once (`OB-JIT-SEALED-SLOTS`).
- **Dictionary entries** are replaced rather than mutated (`OB-JIT-DICT-ALIAS`).
- **`e_hash` is a parameter**, so XXH3 values and dictionary order are not determined.
- **Slots read before being written stop** with `RBadSlot`. The real machine reads whatever is there.
  `check.shen`'s rules exclude this for lowered code, but `shen-jit.install` doesn't check it.
- **IO** is a request and a response at this level; failure of a write is not observed, as in the code.

## Changes Búri's KLambda semantics would need

These are proposals. `rocq/KLSemantics.v` and `rocq/KLValue.v` are unchanged, so **the Shen/JIT
profile cannot currently be refined**: the rules below contradict the port.

1. A profile slot for the integer range and an overflow error. `int_or` is unbounded and "fixed by this file".
2. A profile choice of byte strings: `rule_n_to_string` takes any Unicode scalar.
3. Identity for closures and exceptions under `=`: `kl_eq` is undefined there.
4. A profile choice between currying and arity errors for named calls: `call_named` builds `VPartial`.
5. An error for `defun` of fixed and sealed names, and a sealed set in the store.
6. `get-time` responses as reals: `QTime` responses are integers.
7. Unchecked writes: `rule_write_byte` raises on a short write, and the port doesn't.
8. Catchable resource errors: `Fail` is final in the semantics, and these are catchable in the port.

Item 7 could instead be fixed upstream.

## Findings against the source

Prose against code, at the pin. Tests are under QEMU on the named binary.

1. **NaN.** `docs/semantics.md:88` says NaN equals nothing. `sj_equal` (`prims.c`) tests the two words
   first. On the binary, `(= N N)` with one NaN object is true, `=` with another NaN is false, and
   `(= [N] [N])` is true.
2. **Mixed comparison.** `semantics.md` says mathematical value, and `comparison` and `sj_equal` convert
   to double. Already upstream as `tizoc/shen-jit#2`.
3. **Hash range.** `semantics.md` section 6 says 0 to N inclusive; `bytecode.md` and `hash` in `prims.c`
   give 1 to N-1, and 1 when N is 1, which is N.
4. **A missing reference.** `bytecode.md` points to a "Primitive contract" section of `semantics.md` that
   doesn't exist.
5. **A family that doesn't exist.** `semantics.md` section 2 lists a Primitive object family; `value.h` has
   no such type, and primitives are not procedures.
6. **Unchecked writes.** `write-byte` ignores `fputc`'s result, and section 12 doesn't say so.
7. **A different message.** `bytecode.md` says `jump-if-false` raises "expected a boolean"; `h_boolean_error`
   (`jit.c`) raises "~S is not a boolean". Messages aren't a compatibility requirement, so this is minor.
8. **Partial doc coverage.** Section 2's special values omit Prolog variables, and section 6 omits byte buffers.

None of these has been filed upstream by this work.

## What Phase 2 needs from this

- `JitBytecode.next` as the target semantics, and `rocq/KLSemantics.v` as the source, once the
  changes above are decided. The refinement can't be stated until they are.
- A value relation from `KLValue.value` to `JitBytecode.val`, which differ on closures, vectors and exceptions.
- A Rocq model of `lower.shen`, source-linked as `rocq/EncoderKLambda.v` does.
- The `check.shen` rules as an invariant, to rule out `RBadSlot`, `RBadLabel` and `RFallOff`. Only the
  classification exists so far.

**Surprises that change Phase 2's cost:**

- The source semantics needs eight changes first, and they touch rules other lanes depend on.
- The lowerer does much more than lower. `bytecode.md`'s rules include inlining, fusing frozen goto
  bindings, copying lambdas up to 1,500 nodes, Prolog-specific rewrites, list constant folding and
  factorised-pattern rewrites. Each needs its own preservation argument, and many depend on
  `shen.factor`'s output shape.
- The lowerer consults mutable state: `shen-jit.sealed?` and `shen-jit.inline-body` make output depend
  on the store, so the theorem quantifies over stores.
- Runtime `eval-kl` runs the lowerer as guest code, so that theorem depends on the main theorem for the
  lowerer's own code, as planned.

**A cheaper part than expected:** the bytecode model matched the binary on nearly every sampled case on
the first run. Its first disagreements were in harness setup and an unfinished printer, not in instruction
semantics.

## Differential results

Tests under `qemu-riscv64` on the named binary, at the pin. Each case's code comes from the real lowerer, and
Rocq computes the verdict by `vm_compute`. Agreement is sampled evidence, not proof.

| Set | Source | Compared | Agree | Not compared | Differ |
|---|---|---|---|---|---|
| `ev` | `tests/kl/eval-cases.kl` | 431 | 421 | 8 IO, 2 excluded | 0 |
| `ops` | `tests/kl/ops.kl` plus the table in `test_ops.c` | 138 | 138 | 0 | 0 |
| `ct` | `contract/examples.shen` | 155 | 146 | 8 IO | 1 |

The one difference is `(fn append)`, which reads the kernel's property vector. That is image state the harness
doesn't load, so it is a limit of the harness, not a known fault in the semantics. Five forms that the lowerer
rejected are outside these counts, as lowering is Phase 2. The harness has no IO oracle, so the 16 IO cases are not
compared; streams and files have had no differential test. Kernel functions run from the stage 0 closure, up to
331 definitions, without the initialised image, so state-dependent kernel behavior is barely sampled. GC stress,
the kernel test suite, and other inputs were not run through the model.

## Running it

`make check-shen-jit`, in the container from `spikes/jit-in-model/setup.sh`, with the binary from
`spikes/riscv-build/build.sh`. Differential runs take tens of minutes.

## Decisions for Reuben

1. **Change the shared KLambda semantics?** The refinement needs the eight changes above. They would be
   per-profile slots to keep Scheme and CL unchanged, but they alter `rocq/KLValue.v` and `rocq/KLSemantics.v`.
2. **Re-pin now or stay at `715bf60`?** All spike evidence is at the pin, and upstream changes quickly.
3. **Shen counterpart?** AGENTS.md keeps executable semantics in Shen. Should this bytecode semantics get
   one, or is Rocq alone acceptable here?
4. **File the new prose findings upstream?** They are read from the source, and the NaN one was tested.
5. **Lane status in the charter.** The packages are `mandatory_for_closed_deployment: false`, and the charter
   target stays closed deployment on both ports. Making this the lead track doesn't change that target.
