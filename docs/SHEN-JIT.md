# Shen/JIT lane (E2E-37 to E2E-41)

Status: **Phase 1 done, at the 0.3 pin. Nothing about Shen/JIT is verified.** This lane has a written
scope, a Rocq semantic profile, and an executable bytecode semantics that has been compared
with the binary on samples. No theorem yet relates that semantics to KLambda or to machine
code.

The goal is the zlib-style claim in the [plan's gate](../spikes/GATE.md): the exact binary
refines Búri's KLambda semantics, or stops with a named resource failure.

## The named build

Every claim is about this one build, and not about any upstream release.

| Item | Pin |
|---|---|
| Source | `tizoc/shen-jit` `b4ccf2dff97031ee624692bb32d2addd18cacb39`, release 0.3, frozen for this phase |
| Patch | [`ports/shen-jit/shen-jit-rv64-arena.patch`](../ports/shen-jit/shen-jit-rv64-arena.patch), built by [`build.sh`](../ports/shen-jit/build.sh): a static RWX code arena, no `MADV_HUGEPAGE`, and `fsqrt.d` for the RV64 `real-sqrt` emitter, which 0.3 otherwise refuses to compile |
| Target | Static `ET_EXEC`, musl, RV64GC, one RWX `PT_LOAD` |
| Binary | SHA-256 `2d444d926e6faec26ffdfa4ab9e107be24e404773d53165f48139a8b60cf7a5a`, including its image |
| Kernel | 43.2, archive SHA-256 `23c71508...`; Búri's shared lanes are on 43.1 with PR117 |
| SLJIT | `a0020dd49a21020434ff838fc308626c48cd8f05`, as vendored |
| Process model | `theorem-labs/rocq-linux-process-semantics` `5e13f6b0f82936aa5d006438e07e265c5d9fcfc4` |
| Prover | Rocq 9.3.0, OCaml 5.2.1 for the process model; the same `rocq/Jit*.v` sources under Coq 8.18.0 in `make prove` |

**Excluded from the claim:** threads, FFI and pointers, `lib/native.shen` and hand-written code, the
real and word registers and loops added at 0.3 (`lib/mmap.shen` and `lib/handle.shen` depend on them), the wide
byte-buffer accessors `s32` to `f64!`, the profiler, Ctrl-C handling, `save-executable`, the REPL, and backtrace text.
In the model each excluded primitive stops with `RExcluded`, as `excluded_prims_stuck` states, and each of the 55 excluded
instructions is refused at load (`excluded_ops`, compared with `ops.h` by the gate), where the real loader
accepts them. The lowerer doesn't emit them. The code is still linked in the binary (`OB-JIT-EXCLUSIONS-ENFORCED`).

**Spikes stay at the old pin.** `spikes/` and its results are evidence about `715bf60` and aren't rewritten.
Upstream moves quickly, so this pin won't be `main` for long; proofs bind to exact bytes, and moving again is a
deliberate step.

### What changed at 0.3

| Upstream change | In the model |
|---|---|
| `=` and comparisons across integers and reals are exact (#2) | Changed: `compare_fix_real`, used by `eq_val`, `prim_step`, and the profile's `jit_inexact_cmp` |
| `=` no longer overflows the C stack; on a cycle or past its budgets it ends the process (#3) | Unchanged: fuel-limited `eq_val` stops with `RCyclic`. Tracked by `OB-JIT-EQ-CYCLE` |
| `get-time` no longer interns symbols (#4) | No effect |
| 55 instructions for hand-written code: `loop`, `again`, `real-*`, `word-*` | Excluded, named in `excluded_ops` |
| 14 primitives: `s32` to `f64!`, `pointer-sized` and others | Excluded |
| `shen-jit.collect` | Modeled: returns `true`, since collection is not observable |
| One allocation area, heap growth, register allocation, comparisons on constants | No effect at this level, as neither the model nor the claim states memory layout. They do change the binary, the collector and the emitter that later phases prove |
| Lowerer: new arities only | `lower.shen` emits none of the excluded instructions, so nothing changes for Phase 2 beyond the arity table |

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
| `rocq/KLPort.v` | The port options on the KLambda semantics, and `next_r_agreed` |
| `rocq/JitProfile.v` | `KLValue.profile` instance, `jit_rules`, and the deviation table |
| `rocq/Audit_Jit.v` | Assumption audit of 34 statements |
| `tests/shen-jit/` | Capture from the binary, packaging, Rocq harness, known differences |
| `ports/shen-jit/` | The named build's script and patch |
| `scripts/check-shen-jit.sh` | `make check-shen-jit`, the opt-in gate |

Sources live in `rocq/`, so one copy compiles under both provers: the only rewrite for 9.3 is
the import line, and the gate refuses any other difference.

**A recorded exception to AGENTS.md's usual split:** Búri normally keeps executable semantics in Shen and
checks them in Rocq. This semantics is executable in Rocq and has no Shen counterpart, by Reuben's decision
(`OB-JIT-ROCQ-ONLY`). So it has no second implementation behind it, only differential tests against the binary.

## Semantics limits

- **No identity for pairs, strings or reals.** `same?`, `tagged?` and `deref` on two of them stop
  with `RIdentity`, as does `=` on two NaNs.
- **Sealed calls** read the current function cell, not a slot bound once (`OB-JIT-SEALED-SLOTS`).
- **Dictionary entries** are replaced rather than mutated (`OB-JIT-DICT-ALIAS`).
- **`e_hash` is a parameter**, so XXH3 values and dictionary order are not determined.
- **Slots read before being written stop** with `RBadSlot`. The real machine reads whatever is there.
  `check.shen`'s rules exclude this for lowered code, but `shen-jit.install` doesn't check it.
- **IO** is a request and a response at this level; failure of a write is not observed, as in the code.

## Port options on the KLambda semantics

`rocq/KLPort.v` opens the eight points where Búri's KLambda rules contradicted this port, as a `port_rules` record.
`rocq/KLSemantics.v` and `rocq/KLValue.v` are unchanged, so no existing statement changed. `next_r_agreed` and
`step_r_agreed` prove that `agreed_rules` gives exactly `next` and `step` for every profile and configuration, which
also stops this copy drifting from `KLSemantics.v`. `jit_rules` in `rocq/JitProfile.v` is the Shen/JIT instance.

| # | Option | Shen/JIT | Limit |
|---|---|---|---|
| 1 | `int_range` | 62-bit fixnums; a result out of range raises | Raises `XPrim`, since messages aren't a compatibility requirement |
| 2 | `char_ok` | `n->string` takes 0 to 255 | |
| 3 | `object_identity` | Each closure gets a location, an empty heap cell kept in its environment | **Two exceptions stay undefined under `=`**: see below |
| 4 | `arity_errors` | A named call of the wrong count raises `XArity` | |
| 5 | `defun_allowed` | `defun` of a primitive, special form, `do`, `thaw`, or sealed name raises | The sealed set is a parameter, not yet related to the image |
| 6 | `time_kind_ok`, and the profile's `jit_time` | `run` and `unix` only, and `RTime`'s integer is read as binary64 bits | No theorem yet |
| 7 | `unchecked_writes` | `write-byte` returns its byte whatever the environment answers | Upstream may change this |
| 8 | `resource_exn` | Out of memory and stack overflow raise `XUser` with their message | `step_r_resource` lets them happen at any evaluation or return, which is broader than the binary (`OB-JIT-RESOURCES`) |

**Exception identity isn't stated.** An `exn` has nowhere to hold a location, and adding a constructor breaks the
exhaustive case splits in `rocq/KLambdaEvaluatorComplete.v` and `KLambdaEvaluatorRefinement.v`. So `=` on two exceptions
stays `equality-undefined`: on those inputs, for example `(= E E)`, the source semantics makes no claim. A real has
no identity there either (`OB-JIT-NAN-IDENTITY`).

**These options don't relate the port to anything.** They let the refinement be stated, which Phase 2 onward has to prove.

## Findings against the source

Rechecked at 0.3. Reproductions and a draft issue are in
[upstream/shen-jit-findings.md](upstream/shen-jit-findings.md). **None has been filed by this work.**

1. **Unchecked writes survive.** `write-byte` ignores `fputc`'s result (`prims.c:1202`), and on `/dev/full` both it and
   `close` report success.
2. **NaN no longer applies.** `semantics.md` now says what the binary does.
3. **Mixed comparison no longer applies.** Fixed upstream as `tizoc/shen-jit#2`.
4. **Hash range remains.** `semantics.md:155` says 0 to N inclusive; `bytecode.md` and `hash` in `prims.c`
   give 1 to N-1, and 1 when N is 1, which is N.
5. **A missing reference remains.** `bytecode.md:104` points to a "Primitive contract" section that doesn't exist.
6. **A family that doesn't exist remains.** `semantics.md:53` lists a Primitive object family; `value.h` has no such type.
7. **A different message remains.** `bytecode.md:89` says `jump-if-false` raises "expected a boolean"; `h_boolean_error`
   (`jit.c:397`) raises "~S is not a boolean". Messages aren't a compatibility requirement, so this is minor.

## What Phase 2 needs from this

- `JitBytecode.next` as the target semantics, and `KLPort.step_r (jit_rules sealed) jit_profile` as the source.
- A value relation from `KLValue.value` to `JitBytecode.val`, which differ on closures, vectors and exceptions.
- A Rocq model of `lower.shen`, source-linked as `rocq/EncoderKLambda.v` does.
- The `check.shen` rules as an invariant, to rule out `RBadSlot`, `RBadLabel` and `RFallOff`. Only the
  classification exists so far.

**Surprises that change Phase 2's cost:**

- The source semantics allocates a location per closure under `jit_rules`, so the value relation has to map
  locations to `JitBytecode` closures.
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

**732 cases, 713 agree, 19 known differences, 0 new.** Of those differences, 16 need IO responses the harness can't supply,
2 use the excluded `save-executable`, and 1 is a harness limit: `(fn append)` reads the kernel's property vector, which is
image state the harness doesn't load. Five forms the lowerer rejected are outside these counts, as lowering is Phase 2.

Moving to 0.3 added 8 cases from upstream's tests, and every one agreed. The model changes above were made from reading the
source before this ran, so the run is a check of them rather than where they came from.

Streams and files have had no differential test. Kernel functions run from the stage 0 closure without the initialised image,
so state-dependent kernel behavior is barely sampled. GC stress, the kernel test suite, and other inputs were not run through the model.

## Running it

`make check-shen-jit`, in the container from `spikes/jit-in-model/setup.sh`, with the binary from
`ports/shen-jit/build.sh`. Differential runs take tens of minutes.

## Decisions for Reuben

Decided on 6 November 2026: options added without changing the agreed rules, re-pinned once to 0.3 and frozen, and the
bytecode semantics stays Rocq-only. Filing upstream waits on [the draft](upstream/shen-jit-findings.md).

**Lane status in the charter.** The packages are `mandatory_for_closed_deployment: false`, and the charter
target stays closed deployment on both ports. Making this the lead track doesn't change that target.
