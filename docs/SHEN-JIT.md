# Shen/JIT lane (E2E-37 to E2E-41)

Status: **Phase 1 done, re-pinned to 0.4. Nothing about Shen/JIT is verified.** This lane has a written
scope, a Rocq semantic profile, and an executable bytecode semantics that has been compared
with the binary on samples. No theorem yet relates that semantics to KLambda or to machine
code.

The goal is the zlib-style claim in the [plan's gate](../spikes/GATE.md): the exact binary
refines Búri's KLambda semantics, or stops with a named resource failure.

## The named build

Every claim is about this one build, and not about any upstream release.

| Item | Pin |
|---|---|
| Source | `tizoc/shen-jit` `d3348cefbb2b209992039c1c0f55751241750364`, release 0.4, frozen for this phase |
| Patch | [`ports/shen-jit/shen-jit-rv64-arena.patch`](../ports/shen-jit/shen-jit-rv64-arena.patch), built by [`build.sh`](../ports/shen-jit/build.sh): a static RWX code arena, no `MADV_HUGEPAGE`, and `fsqrt.d` for the RV64 `real-sqrt` emitter, which upstream otherwise refuses to compile. It applies to 0.4 unchanged |
| Target | Static `ET_EXEC`, musl, RV64GC, one RWX `PT_LOAD` |
| Binary | SHA-256 `5eb9f4336aee535b93577c436f589b65262853defc2602aee41d8cc7d6c51872`, including its image (runtime `a06f85d8...`, image `0a135cab...`). Built by `build.sh /lps/p4/sj` in a fresh `ubuntu:24.04` linux/arm64 container, with Zig 0.13.0 (`zig cc`, riscv64-linux-musl); a second fresh build gave the same bytes. The hash depends on the output directory, which `-g` records |
| Kernel | 43.4, archive SHA-256 `15e7972e...`; Búri's shared lanes are on 43.1 with PR117 (`OB-JIT-KERNEL-43-2`; their move is [parked](KERNEL-43.4-PARKED.md)) |
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

### What changed at 0.4

`b4ccf2d..d3348ce`: 23 commits, 33 files. `ops.h`, `value.h` and the primitive table are unchanged, so the opcode
and primitive tables match as before (`check_tables.py`: 120 primitives, 76 opcodes, 55 excluded).

| Upstream change | In the model |
|---|---|
| `write-byte` and `close` raise on a failed write (#12, `a0a6517`). Output is buffered, so `write-byte` raises once the buffer fills and `close` for the rest, closing the stream either way | Changed: both raise on `JFailed` in `JitBytecode.v`, `close` after marking the stream closed. `jit_rules` sets `unchecked_writes` to false, so `write-byte` follows the agreed rule (`jit_writes_checked`). The message is fixed text, where the binary appends `strerror` |
| `absvector` and `shen-jit.filled-vector` refuse a length of 2^48 or more | Changed: both raise "not a valid length" from 2^48 |
| `cons` raises "out of memory" when allocation fails | No change: a resource failure, matched through `step_r_resource` |
| Kernel 43.4: 7 functions differ, none overridden by the port; its factoriser takes a `cond` with no true clause | Fixes `tizoc/shen-jit#1` on the named binary (`OB-JIT-ISSUE-1` superseded). Stage 0 has 950 definitions, from 941 |
| Lowerer: a `cons` chain with constant heads is computed into one slot, `(prim D cons (const K) D)`, when D is not a parameter's slot | Not admitted by `JitLowerRel`: the only cause of the stage 0 definitions accepted at 0.3 and rejected at 0.4 (below). Used by 169 of 950 definitions |
| Lowerer: constants are shared only when `=` as well as printed alike, and the pool is built in reverse | No effect: the checker reads constants by index and value, not by how they were shared |
| JIT: two more kept registers, carried across labels; `SHEN_JIT_SLOW_PRIMS` | No effect at the bytecode level. They change the emitter that later phases prove |
| Docs: `protect` listed as fixed; nested `defun` raises; a malformed primitive call raises when lowered, before any `trap-error` | `is_fixed_name` now includes `protect`, which `lower.shen` already treated as fixed at 0.3. The other two are lowerer behavior, for Phase 2 |
| Docs: Prolog variables as immediates; hash range and the other prose findings corrected | Already modeled (`VPvar`). Findings 4 to 7 below no longer apply |

A call's result slot below its window moved from `check.shen`'s list to the lowerer's own habits; `JitLowerRel` never
relied on it.

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
| `rocq/Audit_Jit.v` | Assumption audit of 42 statements |
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
- **IO** is a request and a response at this level. From 0.4 a write or close the environment answers with `JFailed`
  raises; when buffering lets that happen is the environment's choice.

## Port options on the KLambda semantics

`rocq/KLPort.v` opens the eight points where Búri's KLambda rules contradicted this port at 0.3, as a `port_rules` record.
At 0.4 the seventh no longer applies to Shen/JIT.
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
| 7 | `unchecked_writes` | False from 0.4: `write-byte` follows the agreed rule (`jit_writes_checked`) | True at 0.3, when `fputc`'s result was unchecked |
| 8 | `resource_exn` | Out of memory and stack overflow raise `XUser` with their message | `step_r_resource` lets them happen at any evaluation or return, which is broader than the binary (`OB-JIT-RESOURCES`) |

**Exception identity isn't stated.** An `exn` has nowhere to hold a location, and adding a constructor breaks the
exhaustive case splits in `rocq/KLambdaEvaluatorComplete.v` and `KLambdaEvaluatorRefinement.v`. So `=` on two exceptions
stays `equality-undefined`: on those inputs, for example `(= E E)`, the source semantics makes no claim. A real has
no identity there either (`OB-JIT-NAN-IDENTITY`).

**These options don't relate the port to anything.** They let the refinement be stated, which Phase 2 onward has to prove.

## Findings against the source

Rechecked at 0.4. Reproductions are in [upstream/shen-jit-findings.md](upstream/shen-jit-findings.md). Finding 1 was filed
as `tizoc/shen-jit#12`; nothing else has been filed by this work. **None remains at 0.4.**

1. **Unchecked writes: fixed at 0.4.** `write-byte` and `close` raise on a failed write; on `/dev/full` the named binary's
   `close` raises "close: No space left on device".
2. **NaN no longer applies** (since 0.3).
3. **Mixed comparison no longer applies** (since 0.3, `tizoc/shen-jit#2`).
4. **Hash range: fixed in the docs.** `semantics.md` now gives 1 to N-1, or 1 when N is 1, as `prims.c` does.
5. **The missing reference: gone.** `bytecode.md` no longer points to a "Primitive contract" section.
6. **The family that doesn't exist: gone.** `semantics.md`'s families are now those of `value.h`.
7. **The message: fixed in the docs.** `bytecode.md` gives "X is not a boolean".

No new probable upstream bug was found at 0.4.

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

## Phase 2: KLambda to bytecode (in progress)

Written at 0.3 (`b4ccf2d`) and rechecked at 0.4 (`d3348ce`), 6 November 2026. **Nothing here proves that `lower.shen` is correct.** There is a
preservation theorem for code a stated relation accepts, a checker proved to decide that relation, and the
checker's verdict on every stage 0 definition.

**Route.** Translation validation first, as Búri does for captured compiler output: a relation between a
KLambda definition and its code, preservation proved once over the relation, and a Rocq checker run on real
output. This gave a first theorem within the first session. It cannot cover runtime `eval-kl`, which lowers
definitions that don't exist yet, so the general proof over a source-linked model of `lower.shen`
(`OB-JIT-LOWER-GENERAL`) is still needed. Two ways are open: prove the lowerer, or run this checker on every
runtime lowering and prove the checker's binary later, as the emitter spike chose. Not decided.

| File | Contents |
|---|---|
| `rocq/JitLowerRel.v` | `Comp` and companions: code that is a lowering of an expression, following `lower.shen`'s emission |
| `rocq/JitLowerKont.v`, `JitLowerStable.v` | The continuation relation, and that writes above the live slots leave it intact |
| `rocq/JitLowerPrim.v` | `prim_agree`: the admitted primitives agree on related arguments, or both raise |
| `rocq/JitLowerStep.v` | `sim`: one step of the simulation, with stuttering bounded by a measure |
| `rocq/JitLowerThm.v` | `preservation`, `related_progress`, `call_preservation` |
| `rocq/JitLowerCheck.v` | The checker and `check_fn_sound`: acceptance is a proof of the relation |
| `rocq/JitLowerStage0.v`, `tests/shen-jit/stage0_to_rocq.py` | Decoding stage 0 files in Rocq, from a trusted tokenizer |

**The theorem.** `preservation` says: for every store, configuration and machine in the simulation relation, and
every n, either the bytecode takes at least n steps while the source keeps a related configuration, or both end
together, with related values or an error both raise. `call_preservation` starts it from a call of an accepted
function with related arguments. The source is `KLPort.step_r (jit_rules sealed) jit_profile`, the target
`JitBytecode.next`, for every environment `E` and primitive table. `Print Assumptions` is closed for all of them.

**What the relation admits:** integer, real, string, symbol, boolean and nil literals; variables in slots; `let`,
including sharing a slot; `if`, `cond`, `and` and `or`, as values and as tests; `type`; the primitives `+ - *`,
the four comparisons, `cons hd tl cons? number? string?`; 0.4's one-slot `cons` chain with constant heads; named calls and named tail calls, with
`lower.shen`'s in-place argument moves. **Not admitted:** closures, captured variables, `trap-error`, `=`,
dynamic application, `set` and `value`, the other primitives, `do`, `thaw`, `defun` and `eval-kl`, and every
rewrite listed under the surprises above.

**Premises, each a ledger entry:**

- `FunRel` in `Com`: every function the source store defines is an installed closure of accepted code, and
  primitive names are fixed (`OB-JIT-LOWER-FUNREL`, which depends on the image).
- No handler is installed while related code runs, since the fragment has no `trap-error`.
- The source may raise a catchable stack or heap error at any running state (`KLPort.step_r_resource`,
  `OB-JIT-RESOURCES`). The bytecode's `out of memory` and `stack overflow` are matched through it, so the
  theorem says nothing about when those happen.
- `/` is left out of the fragment: its agreement with the bytecode wasn't proved this session.

**Stage 0.** `scripts/check-shen-jit.sh` decodes all 24 file pairs and runs the checker: **61 of 950 definitions
accepted** at 0.4, 889 rejected, none unreadable (`tests/shen-jit/stage0-accepted.txt`). At 0.3 it was 59 of 941. At the
re-pin to 0.4 it fell to 53: eight definitions accepted at 0.3 were rejected because of the one-slot `cons` chain
(`(prim D cons (const K) D)`). Admitting the chain (below) brought back exactly those eight and no others:
`shen.compile-to-kl`, `shen.x.expand-dynamic.wrap-in-defun`, `shen-jit.lower.lets`, `shen.tuple-up`,
`shen.create-skeleton`, `shen.macro-@ch`, `shen.macro-@c` and `<!>`. Two are new since 0.3: kernel 43.4's
`shen.precompiled-function?` and `shen.x.expand-dynamic.expand-initializer`. Of the 169 definitions whose code uses the
chain, 161 are still rejected for other constructs. Each accepted definition is a
lowering of its kernel KLambda in the relation's sense; a rejected one is unvalidated, not wrong. A census of the
forms (`tests/shen-jit/stage0_census.py`, a count, not proof) shows where the rest go:

| Construct | Definitions using it | Only blocker |
|---|---|---|
| `=` | 447 | 18 |
| Dynamic application | 403 | 18 |
| Port primitives (`shen-jit.*`) | 167 | 35 |
| `simple-error` | 143 | 5 |
| `lambda` | 125 | 23 |
| `do` | 123 | 4 |
| `value` | 121 | 35 |
| None of the constructs counted | 178 | |

These are 0.4's counts. Of the 178 using none of them, 128 are still rejected, counted by name against the accepted
list. (The 125 recorded at the re-pin, and 117 of 176 at 0.3, subtracted every accepted definition from the 178, but 11
accepted definitions use a counted construct, as when the census flags a call of a `shen-jit.` function; by name the
re-pin figure was 135.) The rewrites under the surprises above (sharing, folding, inlining, goto labels) are the likely
causes, not yet confirmed per definition.

**The one-slot `cons` chain** (`JitLowerRel.C_chain`). `lower.shen` computes `(cons K Tail)`, with K a constant and Tail
a `cons`, by lowering Tail into D and then emitting `(prim D cons (const K) D)`, which reads D and writes it. The rule
admits that for any tail expression. The simulation case runs three source steps without a bytecode step: the call
starts, K evaluates, and the tail starts with the `cons` pending. It then reuses the existing primitive-argument frame
with an empty environment, since nothing the frame binds lives in D, so the in-place write disturbs nothing. The frame,
stability and theorem statements are unchanged. `lower.shen` takes the chain only when D is not a parameter slot, which
`check.shen` asks of it (a written parameter is read only by a tail call). The simulation doesn't need that guard. The
checker keeps it, testing `2 + arity <= D` as `lower.shen` does, so it follows the lowerer's dispatch with no
backtracking. A checker without the guard is still sound, so no proof mutation can catch that, but it rejects `shen.mkstr`,
whose tail call computes `(cons shen.proc-nl (cons V7021 ()))` in place into parameter slot 2, where `lower.shen` puts
the inner `cons` in a slot above; then the stage 0 count gate fires
(`tests/shen-jit/gate_tests.sh`, `chain-guard-dropped`). Two proof mutants are rejected (`ShenJitLowerChainSlot`, the cons reads any slot; `ShenJitLowerChainConst`, any head constant). Lines added:
7 in `JitLowerRel.v`, 25 in `JitLowerStep.v`, 49 net in `JitLowerCheck.v`, 81 in all, under the 100 to 400 projected
per construct below.

**Measures.** Lines by hand, first session: about 70 minutes to the first theorem, about 2.5 hours in all, including
compile waits. Each Rocq file compiles in under 3 minutes under Rocq 9.3.

| Part | Lines, as written | Covers |
|---|---|---|
| Relation (`JitLowerRel.v`) | 169, then 176 | the fragment above |
| Continuations and stability (`JitLowerKont.v`, `JitLowerStable.v`) | 269 | |
| Primitives (`JitLowerPrim.v`) | 176 | 13 primitives |
| One step and the theorem (`JitLowerStep.v`, `JitLowerThm.v`) | 1,313, then 1,338 | every case of the fragment |
| Checker and soundness (`JitLowerCheck.v`) | 428, then 477 | |
| Stage 0 decoding and tokenizer | 133 | |

Calls and tail calls (frames, windows, argument moves, stack growth, arity errors) took about half the step proof.
Projection, from these numbers only: each further construct family costs a relation rule, a simulation case and a
checker case, roughly 100 to 400 lines by what each case here took (calls and tail calls together took about 600); closures and handlers will be at the high end,
since they change the continuation relation, and the rewrites each need their own argument. That is perhaps
3,000 to 8,000 more lines for the instance route across the whole kernel. The general proof over `lower.shen`
was not attempted and is not estimated here.

**Gaps found:**

- The source semantics has no `do`: `do` is an ordinary call of the kernel's definition, and the lowerer compiles
  it inline. Relating them needs the store's `do` to be the kernel's, as `OB-JIT-LOWER-OPTIMIZATIONS` lists.
- `=` cannot be admitted as it stands: the bytecode model is stuck (`RIdentity`) on two NaNs, where the source
  answers. Admitting it needs either a stuck outcome in the theorem or identity for reals in the model
  (`OB-JIT-NAN-IDENTITY`).
- No lowerer bug was found. Nothing was rejected for a reason that looked wrong; rejections weren't reviewed
  one by one.

### Pass split: the normal form (wave 1b)

`lower.shen` lowers in passes: `share` (KL to KL), `norm` (KL to the normal form), then emission (normal form to
bytecode). The stage 0 checker above relates source forms to code directly, so it rejects every definition the
first two passes rewrite. Wave 1b models the normal form, gives it a meaning in KLambda, and judges the emit
pass alone on captured `norm` witnesses. **Acceptance here is about emission only.** Every accepted definition is
also counted as "front end unchecked": nothing in these files relates a witness to its source body. That is
wave 2's obligation.

| File | Contents |
|---|---|
| `rocq/JitNorm.v` | `nexpr`, the normal form's 14 node shapes; `erase : list name -> nexpr -> option expr`; `port_prims`, `folded`; sanity lemmas |
| `rocq/JitNormStage0.v` | `decode` (witness trees to `nexpr`), `judge_core`/`judge_norm`, `judge_norm_sound`, the per-file tally |
| `tests/shen-jit/stage0_to_rocq.py --norm` | Tokenizes `<file>.norm` as well, into the same generic trees; decides nothing |
| `scripts/check-shen-jit-norm.sh` | Opt-in, report only: compiles the above, checks their assumptions, runs the judge over all 24 files |

**The IR.** The node shapes are `lower.shen`'s list above `shen-jit.lower.norm`: `[const V] [var X] [if C X Y]
[and X Y] [or X Y] [let X V Body] [do X Y] [lambda X Body] [freeze Body] [prim Op Args] [call F Args] [apply F]
[apply F X] [trap X E Handler]`. That covers everything `norm-cond`, `open-call`, `fn-call`, `unified-now`,
`bound-now` and the inliner build. A constant carries any KL `value`, so folded lists and the inline body in
`open-call`'s guard can be represented. So can the closures and vectors that the last `norm` clause turns into
constants at run time. Stage 0's writer refuses to print those, so no stage 0 witness has one.

**What `erase` means**, node by node, with the obligation each choice leaves:

| Node | Erasure | Obligation it leaves |
|---|---|---|
| `[const V]`, V an atom | the literal | none. `ESym` is a literal of resolved syntax: `eval_move` returns `VSym s` whatever the environment binds, so no variable captures a symbol constant (`erase_const_eval`, for any `rho`). Erase does not check scope for symbols. |
| `[const V]`, V a pair | the `cons` chain that builds it | Proved at the expression level: `erase_const_eval` shows the chain evaluates to V in any environment and continuation, leaving the store unchanged. This holds when `cons` names the primitive and the stack has room for `cdepth V` frames. Still open: emission. `lower.shen` emits one `(const d k)` of a pair, which `C_lit` does not admit (atoms only), so `check_fn` rejects it. That gap belongs to the emission relation. |
| `[const V]`, any other value | None | needs a constant form in KLSyntax |
| `[var X]` | `EVar X`; None if X is not in scope | none |
| `[let X V B]` | `ELet` | none |
| `[let stage0.lower.inlining [const F] B]` (also `shen-jit.lower.inlining`) | B, when V is a symbol constant and B never mentions the name; otherwise `ELet` | `marker_dead` states the side condition. Dropping the let changes no value or effect, but removes one `KLet` frame, so under a stack bound the two differ in when they run out of stack. The emitter makes no frame for it either. |
| `[do X Y]` | `ELet shen-jit.norm.do X Y`; None if Y mentions that name (`erase_do`) | Y stays in tail position and the meaning does not depend on the global `do`. The source's `(do X Y)` is a call of the kernel's `do`, so the front end needs the store's `do` to be the kernel's (`OB-JIT-LOWER-OPTIMIZATIONS`). The emitter lowers Y at the same top where `C_let` raises it, so `check_fn` rejects most `do`. That gap belongs to the emission relation. |
| `[prim raise-cond []]` | `ECond []` | none: it raises `XCondFail`, as `norm-cond`'s end does, and `C_cond_nil` admits it. `raise-cond` is not a KL name. |
| `[prim Op Args]`, Op a KL primitive | `ECall Op Args`; None if the count is not Op's arity | A primitive call is a named call in `KLSemantics`, resolved in `gfuns`. This is correct under the store invariant `JitLowerStep` already assumes (`fr_prim`/`fr_name`: primitive names are bound to their `FPrim`). |
| `[prim Op Args]`, any other Op | `ECall Op Args`, listed by `port_prims` | **Port primitive, no KL meaning**: the KL store defines no such name, so the call raises `XUndefinedFun`. Each one needs a primitive spec and a ledger entry. These include `shen-jit.inlined?` (`open-call`'s guard) and `shen-jit.arity?` (`fn-call`'s test). Both are C primitives (`src/runtime/prims.c`, `P_INLINEDP`/`P_ARITYP`) that read a function's current code object, and their specs must make the guard's two branches agree. |
| `[call F Args]` | `ECall F Args` | none for erase. Port functions called this way are ordinary KL defuns in `src/port/shen-jit.kl`, so the store's definitions give their meaning: `shen-jit.eval-kl` (line 10), `shen-jit.undo` (181), `shen-jit.unify=` (186), `shen-jit.unify=!` (219), `shen.bindv`. Relating `unified-now`/`bound-now`'s expansions to `is`, `is!` and `shen.bind!` belongs to the front end. One semantic difference goes in the ledger rather than being left as a pending proof: `shen-jit.eval-kl` returns any non-pair unchanged, while KL's `eval-kl` raises `XEvalKL` on a closure or vector (`parse` fails). |
| `[apply F]` | `EApp F []`, the thaw of a frozen value | Also `norm-apply`'s zero-argument dynamic call. Relating it to the source's `(thaw X)` needs the kernel's `thaw` (front end). |
| `[apply F X]` | `EApp F [X]` | Uncurrying back to `(F A B)` belongs to the front end. |
| `[trap X E H]` | `ETrap X (ELam E H)`, H in E's scope | none: `throw_move` applies the handler to the exception. The fresh-variable form `[trap X E [apply H' [var E]]]` is an eta-expansion of `(trap-error X H')`, which belongs to the front end. |

`erase` is not injective: a folded constant and the `cons` it came from erase alike, and so do a call and a prim of
the same name (`erase_not_injective_fold`, `_call`). The judge doesn't need injectivity, because it checks code
against the erasure. `erase_kl_shaped` shows the erasure exists for every node that is KL as written. `judge_norm_sound`
shows what acceptance gives: the form parses to `defun F Ps B`, the witness decodes with the same F and Ps, it erases
to e, and `CompFn c Ps e`. It does not give `e ~ B`. `Print Assumptions` is closed for all six statements the
script audits.

**Gate.** The two files are registered in `rocq/modules.d/70-jit.list`, because `scripts/prove` refuses unregistered
modules, so `make prove` compiles them. Nothing else changes: no audit module counts them, so `Audit_Jit.count`,
`scripts/report.py` and `check-shen-jit.sh` are untouched. The opt-in script checks their assumptions itself. The
judge is not a gate, and its counts are reported, not pinned.

**Stage 0 result** (witnesses from the pass-capture run, `.forms`/`.sbc` identical to the pin's `build/stage0`):

**75 of 950 definitions accepted** on the erased witness: 875 rejected, none failing erase, none unreadable. All
75 are front end unchecked. None uses a port primitive and none has a folded constant, because `check_fn` rejects
both. The stage 0 judge on the source bodies accepts the same definitions as before (61), and every one of the 61 is
also accepted on its witness: none lost, so no erase choice broke a definition the checker already took.

| File | Accepted | Was (source) | Gained |
|---|---:|---:|---|
| lower | 12 | 8 | `shen-jit.lower.code`, `.finish`, `.apply-all?`, `.value` |
| prolog | 9 | 8 | `shen.prolog-parameters` |
| reader | 8 | 7 | `shen.alpha?` |
| shen-jit | 10 | 6 | `shen.<shortnatters>`, `shen.<whitespaces>`, `shen.<digits>`, `shen-jit.digits` |
| sys | 12 | 11 | `eval` |
| toplevel | 1 | 0 | `shen.repl` |
| yacc | 5 | 3 | `shen.partial-parse-failure?`, `shen.parse-failure` |
| the other 17 files | 18 | 18 | |

Of the 14 gained, 12 contain an inlining marker that erase drops, and 3 contain a `do` erased to `ELet`
(`shen-jit.lower.finish` has both; `shen-jit.lower.value` and `shen.repl` have a `do` and no marker).
pass-capture's own census accepted 72 with only the marker dropped (61 + 11). That fits the 75 here, with the
difference coming from `do`, but the two name lists were not compared. Three hand mutations of `shen-jit.digits`'s witness each turned that one
verdict to rejected and changed nothing else: a constant changed (48 to 49), the marker's name used in its body, and
the marker renamed so that it is no longer dropped. These were hand checks; no proof mutation was added, since the
judge is not in a gate.

What the 75 mean: each code object is a lowering, in `JitLowerRel`'s sense, of its witness's erasure. For the 61
that were already accepted, the source-body verdict still stands on its own. For the 14 gained, nothing yet says
that the erasure is equivalent to the kernel's KLambda: inlining (`shen.digit?` and others) and sharing changed the
body, and that is wave 2's obligation. Most of the 875 rejections come from the emission relation (`=`, `value`,
closures, folded constants, port primitives), not from erase; pass-capture's census lists the first blocker for each.

**UNKNOWN:** `make prove` runs Rocq 8.18 (`toolchain.lock.json`), which was not available on this machine. The two
files compile under Rocq 9.3 (the `shen_jit` toolchain) and are written to the 8.18 library (`From Coq Require`,
explicit `@Forall_cons`), but no 8.18 compile was run.

## Differential results

Tests under `qemu-riscv64` on the named binary, at the pin. Each case's code comes from the real lowerer, and
Rocq computes the verdict by `vm_compute`. Agreement is sampled evidence, not proof.

**At 0.4: 1,344 cases, 1,238 agree, 106 known differences, 0 new or unexplained** (`tests/shen-jit/known-differences.txt`).
By set: eval cases 1,045 (948 agree), ops 138 (all agree), contract 161 (152 agree). Of the 106 differences:

| Kind | Cases | Why |
|---|---|---|
| Excluded feature reached | 80 | the wide byte-buffer accessors, pointers, threads, FFI and `save-executable`, which the model stops on with `RExcluded` |
| Depends on an excluded feature | 6 | three loops waiting for what an excluded thread sets (fuel), two globals only such a thread sets, and a function only FFI defines |
| No identity in the model | 3 | `same?` on two pairs, and `=` on NaNs (`OB-JIT-NAN-IDENTITY`) |
| IO responses | 16 | the harness has no IO oracle |
| Image state | 1 | `(fn append)` reads the kernel's property vector, which the harness doesn't load |

None is a model bug or an upstream bug. The ten eval cases upstream added at 0.4 all agree; they exercise the
`absvector` bound of 2^48, Prolog variable offsets and the one-slot `cons` chain. Five forms the lowerer rejected
(three eval, two contract) are outside these counts, as lowering is Phase 2.

**Correction to the earlier counts.** Until this re-pin, the eval set stopped at its 439th case. The case
`(error "save-executable: not running from an executable" (shen-jit.save-executable "x" ()))` succeeds on the named build,
which runs from an executable: it saves one and ends the process with status 0, so no later case ran and nothing
reported it. The 0.3 figures (732 cases, 713 agree, 19 known differences) are true of what ran, but about 600 of the
1,039 eval forms never did, including 196 of the 206 lines upstream added at 0.3. `capture.shen` now skips that one case.
Every form is accounted for: 1,049 `value` and `error` forms are 1,045 cases, 3 lowering errors and the one skipped.

Streams and files have had no differential test. Kernel functions run from the stage 0 closure without the initialised image,
so state-dependent kernel behavior is barely sampled. GC stress, the kernel test suite, and other inputs were not run through the model.

## Running it

`make check-shen-jit`, in the container from `spikes/jit-in-model/setup.sh`, with the binary from
`ports/shen-jit/build.sh`. Differential runs take tens of minutes.

## Decisions for Reuben

Decided on 6 November 2026: options added without changing the agreed rules, re-pinned to 0.3 and then to 0.4 and frozen
again, and the bytecode semantics stays Rocq-only. `#12`, filed from [the findings](upstream/shen-jit-findings.md), is fixed at 0.4.

**Lane status in the charter.** The packages are `mandatory_for_closed_deployment: false`, and the charter
target stays closed deployment on both ports. Making this the lead track doesn't change that target.
