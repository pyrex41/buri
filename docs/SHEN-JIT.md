# Shen/JIT lane (E2E-37 to E2E-41)

Status: **Phase 1 done, re-pinned to 0.6. Nothing about Shen/JIT is verified.** This lane has a written
scope, a Rocq semantic profile, and an executable bytecode semantics that has been compared
with the binary on samples. No theorem yet relates that semantics to KLambda or to machine
code.

The goal is the zlib-style claim in the [plan's gate](../spikes/GATE.md): the exact binary
refines Búri's KLambda semantics, or stops with a named resource failure.

## The named build

Every claim is about this one build, and not about any upstream release.

| Item | Pin |
|---|---|
| Source | `tizoc/shen-jit` `934cfa56a5723165c63bf679f15d2d5214955a5d`, release 0.6 (tag `v0.6`, annotated tag object `68aa54f8390adec792f3538f8902fa23e542fe53`), frozen for this phase. `src/lowerer/lower.shen` SHA-256 `0048eebc...253d6b` |
| Patch | [`ports/shen-jit/shen-jit-rv64-arena.patch`](../ports/shen-jit/shen-jit-rv64-arena.patch), built by [`build.sh`](../ports/shen-jit/build.sh): a static RWX code arena, no `MADV_HUGEPAGE`, and `fsqrt.d` for the RV64 `real-sqrt` emitter, which upstream otherwise refuses to compile. It applies to 0.6 unchanged (one hunk offset by 113 lines in `jit.c`) |
| Target | Static `ET_EXEC`, musl, RV64GC, one RWX `PT_LOAD` |
| Binary | SHA-256 `e0acd5132a9d876e7618bf1f400706abd82330d18458d209ee064d81d3c10c8d`, including its image (runtime `13afde42...`, image `fd8485a5...`). Built by `JOBS=2 build.sh /lps/p6/sj` with Zig 0.13.0 (`zig cc`, riscv64-linux-musl), in `buri-lps` and in two fresh `ubuntu:24.04` linux/arm64 containers: all three gave the same bytes. The hash depends on the output directory, which `-g` records, and on the Zig cache's path: a first build in `buri-lps` with the shared `/tmp/zg` cache gave a different binary (`c2d6aa35...`), because Zig reused objects first compiled under another checkout (`/lps/s8/sj`) and their debug info named it. `build.sh` now uses an empty cache at `OUT.zig-cache` |
| Kernel | 43.4 (unchanged at 0.6, `tools/ci-deps.sh`), archive SHA-256 `15e7972e...`; Búri's shared lanes are on 43.1 with PR117 (`OB-JIT-KERNEL-43-2`; their move is [parked](KERNEL-43.4-PARKED.md)) |
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

### What changed at 0.6

`d3348ce..934cfa5`: 132 commits, 238 files (0.5 and 0.6). Kernel, SLJIT and `value.h` are unchanged. The primitive table
gains one entry, so `check_tables.py` now counts 121 primitives, 76 opcodes, 55 excluded; `raise-cond` moves to index 121.

| Upstream change | In the model |
|---|---|
| New primitive `shen-jit.write-bytes` (4): N bytes of a buffer from I to an output stream in one `fwrite`, returning N. The port's `pr` now prints through it | Modeled, not excluded: `PWriteBytes` in `JitBytecode.v`, checks in the C order (buffer, range, stream), one new request `JWrites h bytes`, none when N is 0. `write_bytes_io`, `write_bytes_empty` (audited). Mutation `ShenJitWriteBytesFrom` |
| `n->string` makes the UTF-8 bytes of a Unicode scalar value above 255; surrogates, negatives and values past U+10FFFF raise, with a new message | Changed in both models. `JitBytecode.utf8_of`; `KLPort` option 2 is now `char_text : Z -> option text` (the agreed rule is unchanged, `rule_n_to_string_agreed`, `next_r_agreed`), and `jit_rules` uses `utf8_of`. `jit_byte_strings` now states the 0.6 behavior (255, 256, 955, a 3- and a 4-byte value, a surrogate, U+110000, -1); `jit_n_to_string_agrees`, `n_to_string_utf8`. Mutations `ShenJitByteChars`, `ShenJitAgreedChars`. This follows an upstream semantic change; no statement was weakened |
| `read-byte` raises on a read error, where end of file still gives -1; `shen-jit.read-file` raises on a read error after the open instead of returning partial data | Changed: a new response `JReadFailed` raises in both (fixed text; the binary appends `strerror`). `read_byte_error_raises` (audited), mutation `ShenJitReadErrorIgnored` |
| Lowerer: norm rewrites THORN's cut-fail `(shen.cut B L K (freeze (when false B L K C)))` to `(if (shen.unlocked? L) (shen.lock K L) false)`, and `(= (shen.deref X B) (shen.deref Y B))` to `(shen-jit.deref= X Y B)`, a new port function | Not admitted by `JitLowerRel`, like the other rewrites (front-end obligation, wave 2). No accepted definition was lost; counted in the census as `cut-fail` and `deref-eq` |
| Lowerer: fixed names looked up in a dictionary; constants shared through a dictionary keyed so that NaN is never shared; an instruction counter in `mark` | No effect on the relation: `C_lit` reads a constant by index and value, never by how the pool was shared, and the counter equals the old list length (every write to the instruction list goes through `emit` or `mark`). Confirmed by stage 0: the only definitions whose verdict changed are lowerer functions upstream rewrote |
| Lowerer: `reads?`, which decides whether a named tail call's argument is computed into a temporary or in place, walks the argument term itself instead of a list of its variables | No effect on the relation: `CompTA` admits either choice (`TA_temp`, `TA_direct`) and does not depend on how it was made; stage 0 lost no definition |
| Loader: a count over 255 has its own message; constants read without `nth` | No effect at this level |
| Port: `shen-jit.deref=`, `shen.str->bytes` and `shen-jit.buffer->list` added, `pr` overridden | Stage 0 has 955 definitions, from 950 |
| JIT: up to eight kept memory parameters on arm64; `deref` follows a chain inline | No effect at the bytecode level |

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
| `rocq/JitEqBudget.v` | `=` on jit numbers a PER; the `=` budget lemma reduced to one cell step (`eq_core_statement`, proved in `JitEqBudgetCore.v`) |
| `rocq/JitEqBudgetStep.v` | Step of `eq_core_statement`: least true pair, surgery, same-budget and shifted simulation |
| `rocq/JitEqBudgetWalk.v` | Base case of `eq_core_statement`: the walk bound on a closed cell set with no true pairs |
| `rocq/JitEqBudgetCore.v` | Assembly: `eq_budget_closed` (relativized to a closed cell set), `eq_core`, `eq_budget` (`OB-JIT-EQ-BUDGET-CORE` discharged) |
| `rocq/Audit_Jit.v` | Assumption audit of 169 statements |
| `tests/shen-jit/` | Capture from the binary, packaging, Rocq harness, known differences |
| `ports/shen-jit/` | The named build's script and patch |
| `scripts/check-shen-jit.sh` | `make check-shen-jit`, the opt-in gate |

**Symbols are their names** (`OB-JIT-SYM-INJECTIVE`): the runtime interns by the name's bytes, and
`JitBytecode.sym_of_text` is a prefix code that `text_of_sym` reads back for every text, whatever its
elements (`text_of_sym_of_text`), so distinct names are distinct symbols (`sym_of_text_inj`) and the
machine's symbol test is the name test (`sym_of_text_eqb`). Until 8 November 2026 the name was a base-256
numeral, which merged names with an element of 257 or more with shorter ones (`[1; 1]` with `[65537]`).

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
  raises; when buffering lets that happen is the environment's choice. From 0.6 `write-bytes` is one request for all its
  bytes, and a read the environment answers with `JReadFailed` raises. A raise whose handler search ends the run leaves
  the IO continuation's machine unchanged, as before (a continuation returns a machine, not a move).

## Port options on the KLambda semantics

`rocq/KLPort.v` opens the eight points where Búri's KLambda rules contradicted this port at 0.3, as a `port_rules` record.
At 0.4 the seventh no longer applies to Shen/JIT. A ninth, `port_prim`, gives the port's own primitives a meaning; it is
off in both instances (below).
`rocq/KLSemantics.v` and `rocq/KLValue.v` are unchanged, so no existing statement changed. `next_r_agreed` and
`step_r_agreed` prove that `agreed_rules` gives exactly `next` and `step` for every profile and configuration, which
also stops this copy drifting from `KLSemantics.v`. `jit_rules` in `rocq/JitProfile.v` is the Shen/JIT instance.

| # | Option | Shen/JIT | Limit |
|---|---|---|---|
| 1 | `int_range` | 62-bit fixnums; a result out of range raises | Raises `XPrim`, since messages aren't a compatibility requirement |
| 2 | `char_text` | From 0.6, `n->string` makes one byte of 0 to 255 and the UTF-8 bytes of any other scalar value (`char_ok`, 0 to 255 only, until 0.4) | |
| 3 | `object_identity` | Each closure gets a location, an empty heap cell kept in its environment | **Two exceptions stay undefined under `=`**: see below |
| 4 | `arity_errors` | A named call of the wrong count raises `XArity` | |
| 5 | `defun_allowed` | `defun` of a primitive, special form, `do`, `thaw`, or sealed name raises | The sealed set is a parameter, not yet related to the image |
| 6 | `time_kind_ok`, and the profile's `jit_time` | `run` and `unix` only, and `RTime`'s integer is read as binary64 bits | No theorem yet |
| 7 | `unchecked_writes` | False from 0.4: `write-byte` follows the agreed rule (`jit_writes_checked`) | True at 0.3, when `fputc`'s result was unchecked |
| 8 | `resource_exn` | Out of memory and stack overflow raise `XUser` with their message | `step_r_resource` lets them happen at any evaluation or return, which is broader than the binary (`OB-JIT-RESOURCES`) |
| 9 | `port_prim` | None: a call of a name the store binds to no function raises `XUndefinedFun`, as agreed (`jit_port_prims_off`) | A candidate for 18 operators waits on a decision (`OB-JIT-PORT-PRIMS`, below) |

**Port primitives.** `port_prim : name -> option (nat * rule)` is consulted only where `lookup` finds no function, and
then is called as a table primitive is: arity check, `VPartial` below the arity, the rule's result through
`pout_config` (`undefined_without_port_prim`, `port_prim_called`). `agreed_rules` sets it to `fun _ => None`, so
`next_r_agreed` and `step_r_agreed` keep their statements; the mutant `ShenJitAgreedPortPrim`, which gives
`shen-jit.write-bytes` a rule in `agreed_rules`, is rejected there.

*Census, not evidence* (a walk of the 955 erased v0.6 witnesses, `/tmp/p2-v06-capture/witness`, set sha256
`e45add98...b69dd1`; `tally_norm`'s `port_prims_used` counts only accepted definitions and is empty at 0.6): 35 operators
of `NPrim` nodes are neither KL primitives nor `raise-cond`. Occurrences / definitions:
`shen-jit.deref` 662/37, `shen-jit.pvar-offset` 88/13, `shen-jit.append` 72/41, `shen-jit.symbol-kind` 70/50,
`shen-jit.pvar?` 60/12, `shen-jit.absvector3` 36/22, `char-stream?` 15/11, `shen-jit.integer?` 15/14,
`shen-jit.tagged?` 14/12, `read-unit-string` 13/9, `shen-jit.symbol?` 11/4, `shen-jit.sealed?` 10/4,
`shen-jit.dict-put` 5/5, `shen-jit.read-file` 5/4, `shen-jit.same?` 4/4, `shen-jit.vector?` 4/4,
`shen-jit.dict-entries` 3/3, `shen-jit.dict-find` 3/3, `shen-jit.quiet?` 3/2; 2/2 each `shen-jit.bytes-length`,
`.decimal`, `.exit`, `.hash`, `.inline-body`, `.pvar`, `.string->bytes` and `write-string`; 2/1 `shen-jit.install`
and `.sealing`; 1/1 each `shen-jit.dict-remove`, `.filled-vector`, `.mark-toplevel`, `.trace-text`, `.u8` and
`.write-bytes` (the port's `pr`). `shen-jit.inlined?` and `shen-jit.arity?` occur 0 times.

*Proposal, not wired in.* `jit_port_prims_proposed hash` in `rocq/JitProfile.v` gives 18 of them a rule in KL values,
following `prims.c` as `JitBytecode.prim_step` models it: `symbol?`, `integer?`, `append`, `absvector3`,
`filled-vector`, `tagged?`, `vector?`, `symbol-kind`, `same?`, `char-stream?`, `read-unit-string`, `write-string`,
`hash`, `decimal` and the four dictionary operators. Each has a closed sanity lemma (`pp_*_ok`, `pp_dict_ok`);
`jit_port_prims_arity` checks each against the bytecode table's name and arity, and `jit_port_prims_partition` that
every census operator, and `inlined?` and `arity?`, has a candidate or a reason in `jit_port_prims_residual`, not both.
The choices it makes: errors raise `XUser` with the message unformatted (`OB-JIT-ERROR-TEXT`); the hash, and so bucket
order, is a parameter (the environment's `sj_hash`); `same?` and `tagged?` are undefined (`OWrong`) on pairs, strings,
reals, exceptions and partial applications, where the bytecode is stuck on identity; dictionary keys compare by `=`
with closure identity. No candidate: the byte-buffer operators (`write-bytes`, `string->bytes`, `bytes-length`, `u8`)
and Prolog variables (`pvar`, `pvar?`, `pvar-offset`, `deref`), for want of a KL value to carry them; `read-file` (one
request for a whole file); `exit` (no such outcome); `quiet?` (handler state); `mark-toplevel`, `trace-text`
(excluded); and the operators that read code objects or the image (`install`, `inline-body`, `sealed?`, `sealing`,
`inlined?`, `arity?`). Wiring in the 14 that need no hash (`jit_port_prims_core`: all but `hash`, `dict-find`,
`dict-put`, `dict-remove`) replaces `(fun _ => None)` at the end of `jit_rules` with `jit_port_prims_core`; all 18
need `(jit_port_prims_proposed hash)` and `hash` as a new parameter of `jit_rules`, as `sealed` is, at each use site.
The mutant `ShenJitPortPrimsWired` (the core wired in) shows `jit_port_prims_off` stops that being done by accident. Even wired, no definition gains
a verdict until `JitLowerRel` has a rule and a refinement lemma for the operator.

**Exception identity isn't stated.** An `exn` has nowhere to hold a location, and adding a constructor breaks the
exhaustive case splits in `rocq/KLambdaEvaluatorComplete.v` and `KLambdaEvaluatorRefinement.v`. So `=` on two exceptions
stays `equality-undefined`: on those inputs, for example `(= E E)`, the source semantics makes no claim. A real has
no identity there either (`OB-JIT-NAN-IDENTITY`).

**These options don't relate the port to anything.** They let the refinement be stated, which Phase 2 onward has to prove.

## Findings against the source

Rechecked at 0.4; at 0.6 only the source diff was read for them (no finding was re-run on the 0.6 binary). Reproductions are in [upstream/shen-jit-findings.md](upstream/shen-jit-findings.md). Finding 1 was filed
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

Written at 0.3 (`b4ccf2d`), rechecked at 0.4 (`d3348ce`), 6 November 2026, and at 0.6 (`934cfa5`), 9 November 2026. **Nothing here proves that `lower.shen` is correct.** There is a
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
| `rocq/JitLowerThm.v` | `preservation`, `related_progress`, `call_preservation`, `Ends_final` |
| `rocq/JitLowerCheck.v` | The checker and `check_fn_sound`: acceptance is a proof of the relation |
| `rocq/JitKRef.v` | `KRef`, the front passes' refinement relation, and every statement about it (the interface; no proofs), with the index-local interface and the KRef file map |
| `rocq/JitKRefGround.v`, `JitKRefCompose.v` | Proofs: premise specifications, ground lemmas, `KRel_top`, adequacy and store reflexivity from the fundamental property; the composition with `call_preservation`, proved from the fundamental property |
| `rocq/JitKRefBase.v` | KRef's structure: index and world monotonicity, anti-reduction and target-step lemmas, the bind lemma and one KRel lemma per frame, world reachability, `sealed_stable` and `storehas_stable` |
| `rocq/JitKRefPrim.v` | `prim_compat`: every table primitive under `jit_rules`, and every port primitive it gives, maps related arguments and stores to related results (primitive parametricity) |
| `rocq/JitLowerEquiv.v` | Old qualified names (`JitLowerEquiv.JitLowerEquiv.*`) as abbreviations of the moved constants; no constants of its own |
| `rocq/JitLowerStage0.v`, `tests/shen-jit/stage0_to_rocq.py` | Decoding stage 0 files in Rocq, from a trusted tokenizer |

**The front passes** (`rocq/JitKRef.v` with proofs in `JitKRefGround.v` and `JitKRefCompose.v`; old names in `rocq/JitLowerEquiv.v`; `OB-JIT-LOWER-FRONT`). lower.shen shares (b0 to b1) and normalizes
(b1 to e) before it emits code for e. `KRef g e0 e` is a step-indexed Kripke refinement on KLambda expressions under
`step_r (jit_rules sealed) jit_profile`: every terminating run of e, after any IO trace, is matched by one of e0 with a
related value or the same exception and related stores. Worlds are partial bijections between heap locations, because
each lambda and freeze allocates a cell and the passes add and remove them. It is partial correctness; termination is
`OB-JIT-LOWER-TERM`. Proved: `call_preservation_src_of_fundamental`, that the fundamental property implies
`call_preservation` with the source body b0 in place of e, given `KRef ps b0 b1`, `KRef ps b1 e`, the definitions D the
rewrites rely on (sealed, `D_wf`) and a well-formed store; adequacy and store reflexivity from the same premise; the
ground relation's lemmas, `KRel_top`, and the premise checks' specifications. The source's final store is related to
the start by `GStore` under a world fixing the old locations, not equal to it. The `=` budget lemma is proved: `JitEqBudgetCore.eq_budget`
is `eq_budget_statement` (its induction step in `JitEqBudgetStep.v`, its base case, `walk_bound`, in `JitEqBudgetWalk.v`, the
assembly in `JitEqBudgetCore.v`). Not proved: the fundamental property, the compatibility lemmas, and any front-link checker. Under Com's
FunRel the callees b0 calls are the lowered bodies, not the kernel's source definitions. A checker must reject norm's
`(fn F)` rewrites, open-call inlining behind `shen-jit.inlined?` and eval-kl to `shen-jit.eval-kl`, which cannot satisfy
`KRef` in Búri's KLambda. Proof mutants `ShenJitEquivEndsSameStore`, `ShenJitEquivAdequacyStrict` and
`ShenJitEquivComposeLeft` are rejected (since K00 each is the chain JitKRef.v, JitKRefGround.v[, JitKRefCompose.v]
with the statement mutated). `rocq/JitKRefBase.v` proves the relation's structure (57 audited statements):
`VRel_down`, `VRel_wext`, `ERel_down`, `KRef_scope`, `sealed_stable` and `storehas_stable` (JitKRef statements); SRel, KRel,
ERel and EnvRel down in the index and, except SRel, up in wext; ObsT down in the index and antitone in the world.
SRel up in wext and ObsT up in wext are false and refuted in Rocq (`SRel_wext_refuted`, `ObsT_wext_refuted`; a pair the
larger world adds needs related cells, `SRel_wext_cells`). Observation: source anti-reduction (`ObsT_anti`, and
`ObsT_anti_io` with a source IO prefix, traces concatenated, through `ObsTr`), target-step reduction (`ObsT_step`;
`ObsT_running`, where a target resource step is matched by the source's through KRel's Throw clause, `resource_match`),
`wrong_match`. The bind lemma `ERel_push` (a first step that pushes a frame) and one KRel lemma per frame kind: KLet, KIf,
KCond, KAnd, KAndR, KOr, KOrR, KTrap (with the handler's KApply frame), KHead, KArgs, KCallArgs and KApply; the
application frames are reduced to `AppRel`, a hypothesis whose proof is compat_app's and compat_call's (`ObsT_swap`
moves between two frames with the same next move). ERel-form anti-reduction `ERel_anti` (source-only steps, possibly
with a new environment and one-sided cells) and its instances for let, if, cond, type, a named call of a D function and
lambda application. `world_closed` and `VRel_ptrs`: under SRel each side of the world is closed under the vector
pointers of its cells, duplicate-free, of size `length w`, so at most either heap's length, and related values point
into it pointwise, for the `=` budget (`world_closed_alloc` in JitEqBudgetStep's form). JitEqBudgetStep's S-local lok
does not follow from SRel (`SRel_lok_refuted`); the `=` case of `prim_compat` does not need it, since `JitEqBudgetCore.eq_budget_closed` takes no lok (below). Under `jit_rules` no step changes a sealed name's function (`sealed_step`: defun
and eval-kl's defun are refused, primitives keep gfuns, `port_prim` is None). Mutants `ShenJitKRefKRelStrict` (KRel
at j < k) and `ShenJitKRefDefunSealed` (defun admits sealed names) are rejected, each first by an existing proof
(`KRel_top`; `jit_defun_fixed_refused`; with JitProfile.v's refusal theorems deleted in a throwaway build, `sealed_step` fails). `JitKRef.v` also states the index-local interface: `fund_below k`, the
fundamental property below index k in scope-and-free-variable form, and `fund_gen_statement`, that it holds at every
index given `D_wf` (both unproved); and `prim_compat_statement`, that every primitive maps related arguments and stores to related
results (`PrimOutRel`: a related value and store at a larger world, the same exception, both wrong, the same
eval-kl expression or resource, or the same IO request with related continuations).
`rocq/JitKRefPrim.v` proves `prim_compat_statement` (`prim_compat`, Closed under the global context, 16 audited
statements). One lemma per family: arithmetic, comparisons and conversions (`prim_param_arith`: equal numbers in, equal
results out, through the integer range and the profile's inexact slots); lists, strings and symbols (`prim_param_data`;
`str` of a closure or a vector is the constant text `#<procedure>` or `#<absvector>`, so `jit_str_other` reads no
location and no body); vectors (`prim_param_vector`: `absvector` extends the world by the pair of new locations, fresh on
both sides because SRel allocates every world location; `address->` writes the partner cell the bijection gives;
`<-address`, `absvector?`); globals (`prim_param_globals`: `value` finds Forall2-positional partners, `set` adds a head
entry on both sides); IO (`prim_param_io`: the same request, outcomes related for every response); errors
(`prim_param_error`); `=` (`prim_param_eq`); and eval-kl's primitive step (`prim_param_eval_kl`: `parse_sk`, parse
reads only the first-order skeleton, so related data parse to the same expression; running it is the fundamental
property's job). The `=` case is `prim_param_eq_from`, whose only hypothesis is
`JitEqBudgetCore.eq_budget_closed_statement (jit_rules sealed)`, instantiated with `eq_budget_closed`: on each side
S is the world's side (`map fst w`, `map snd w`), closed, duplicate-free, of length `length w` and no longer than the
heap (`world_closed`, `world_closed_alloc`), so each side's budget `S (length heap)` moves to `S (length w)`; the
operands point into S (`VRel_ptrs`); then `eq_lock` walks the two comparisons at that one budget in lockstep (vectors
through the bijection, closures through `same_id`, numbers equal under GVal). `jit_eq_per` gives eq_budget_closed's
hypotheses on number equality; `eq_budget_statement`, with its global lok, is not used. The port half is
`port_compat_of`, for any port_prim table whose rules are each parametric (`rule_param`), with `port_param_jit`
discharging it vacuously for `jit_rules`, which gives none: wiring in an approved table (`OB-JIT-PORT-PRIMS`) needs
`rule_param` for each of its rules. No proposed rule is proved parametric; those that hash a key read the environment's
hash of heap and value, so their proof would need that hash invariant under the world's bijection (not proved; no
counterexample checked in Rocq). Mutants
`ShenJitKRefAbsvectorNoWext` (absvector at the same world) and `ShenJitKRefEqBudgetFree` (the `=` case at the two raw
budgets, without eq_budget_closed; a true statement whose proof then fails) are rejected.

**The theorem.** `preservation` says: for every store, configuration and machine in the simulation relation, and
every n, either the bytecode takes at least n steps while the source keeps a related configuration, or both end
together: the bytecode runs to a machine whose next step returns a value related to the source's, or raises an error
the source also raises. `call_preservation` starts it from a call of an accepted function with related arguments.
Until commit "Tie the JIT theorems' end case to the bytecode's final machine" (8 November 2026) the end case did not
say this: `Ends` bound its final machine inside each constructor, so the machine the bytecode run reached was not
tied to the machine that returned, and the end case of `preservation`, `related_progress` and `call_preservation`
held for any source run that ends, whatever the bytecode did. That statement was weaker than this document claimed.
`Ends` now takes the final machine as a parameter, `Ends_final` checks that it is the one that finishes, and the
proof mutant `ShenJitLowerEndsDecoupled` (the old form of `E_ok`) is rejected. The source is `KLPort.step_r (jit_rules sealed) jit_profile`, the target
`JitBytecode.next`, for every environment `E` and primitive table. `Print Assumptions` is closed for all of them.

**What the relation admits:** integer, real, string, symbol, boolean and nil literals; variables in slots; `let`,
including sharing a slot; `if`, `cond`, `and` and `or`, as values and as tests; `type`; the primitives `+ - *`,
the four comparisons, `cons hd tl cons? number? string?`; `=` when one operand is a constant fixnum, string, boolean, `()` or
non-NaN real; 0.4's one-slot `cons` chain with constant heads; named calls and named tail calls, with
`lower.shen`'s in-place argument moves. **Not admitted:** closures, captured variables, `trap-error`, `=` on two
computed values or against a symbol or NaN constant,
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

**Stage 0.** `scripts/check-shen-jit.sh` decodes all 24 file pairs and runs the checker: **111 of 955 kernel definitions
validated** at 0.6, 844 rejected, none unreadable (`tests/shen-jit/stage0-accepted.txt`). At 0.4 it was 110 of 950.
Compared by name, the re-pin lost `shen-jit.lower.constant-index` (removed upstream with the dictionary-keyed constant
pool) and gained `shen-jit.lower.list-key` (new) and `shen-jit.lower.prim-arity` (rewritten as a dictionary lookup);
the other 109 accepted definitions are accepted at both pins. Net, five definitions more: the lowerer gains
`constant-key`, `fill-table`, `fixed-entry`, `fixed-names`, `fixed-table` and `list-key` and loses `constant-index`,
`same-constant?` and `special?`; the port gains `shen-jit.deref=`, `shen-jit.buffer->list` and its own `pr` and
`shen.str->bytes`, which leave `writer` and `reader`. Of the new ones only `list-key` is accepted. At 0.3 it was 59 of 941. At the
re-pin to 0.4 it fell to 53: eight definitions accepted at 0.3 were rejected because of the one-slot `cons` chain
(`(prim D cons (const K) D)`). Admitting the chain (below) brought back exactly those eight and no others:
`shen.compile-to-kl`, `shen.x.expand-dynamic.wrap-in-defun`, `shen-jit.lower.lets`, `shen.tuple-up`,
`shen.create-skeleton`, `shen.macro-@ch`, `shen.macro-@c` and `<!>`. Two are new since 0.3: kernel 43.4's
`shen.precompiled-function?` and `shen.x.expand-dynamic.expand-initializer`. Of the 169 definitions whose code uses the
chain, 161 are still rejected for other constructs. Admitting `=` against a safe constant (below) took the count from
61 to 110 and lost none. Each accepted definition is a
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

At 0.6, `spikes/pass-split/FEATURES.md` and `features.tsv` (`tests/shen-jit/feature_census.py`, a census, not proof)
assign each of the 955 definitions the emit features its normal form needs and the front families that fired. Its
prediction for the current `Comp` matches the Rocq src (111), nf (112) and tf (133) verdicts on every definition. It also
forecasts what each feature, each family and each residual decision (port primitives, eval-kl, identity, NaN `=`)
would admit, directly and under the callee-closure limit. That limit cuts today's 111 to 46, because 450 definitions
reach a 181-definition strongly connected component.

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

**`=` against a safe constant** (`JitLowerRel.pguard`, `JitLowerPrim.p_eq`). `lower.shen` lowers `(= A B)` as a plain
`(prim D = A B)`, with a literal as `(const K)`. `pmap` now maps `=` to the bytecode's `PEq`, and `C_prim` and the
primitive frame `KD_prim` (`JitLowerKont.v`) carry one more premise: for `PEq`, some operand is a constant whose
value is a fixnum, string, boolean, `()` or a real that is not a NaN. The checker decides it on the code's
constant table. The value-level lemma `eq_core` shows that against such an atom the source's `eq_depth_r` and the
model's `eq_val` give the same answer for every pair of `VR`-related values, so `prim_agree` takes the guard as a
hypothesis that is trivially true for the other primitives. The frame's premise is about the instruction, not
the values, so it is the same in every frame of one call, and at the call `guard_read` finds the constant among
the values read. `JitLowerStable.v` needed no change.

How the three sides compare, on the values `VR` relates (numbers, symbols, booleans, strings, `()` and pairs of these):

| Pair | KLambda (`jit_profile`) | Bytecode model (`eq_val`) | C (`sj_equal`, `prims.c`) |
|---|---|---|---|
| fixnum, fixnum | `Z.eqb` | `Z.eqb` | identical words |
| fixnum, real | `compare_fix_real = Eq`, exact | the same | `compare_fix_real == 0`, exact |
| real, real | `compare = Eq`: -0.0 = 0.0, NaN unequal | the same, except two NaNs: stuck (`RIdentity`) | `==` after testing the words: one NaN object equals itself |
| string, string | code points equal | the same | header and payload words equal |
| symbol, symbol | names equal | `sym_of_text` numbers equal; injective since `OB-JIT-SYM-INJECTIVE` | interned: one object per name |
| pair, pair | heads then tails, structural | the same, structural recursion | tails iterative, heads recursive to depth 256, then a heap work list |
| different kinds | false | false | false |

Two disagreements were found, and C caused neither. The first is two NaNs (`OB-JIT-NAN-IDENTITY`, already known). The second
was symbols: `sym_of_text` read a name as digits in base 256, which is injective on bytes but not on the code points
the KLambda semantics uses, so `[1;1]` and `[65537]` were one symbol, as were `ab` and the one-character name U+16062.
C interns by name and agrees with the source, so the defect was the model's, and `intern` shared it. Restricting
`VR_sym` was ruled out, since it would narrow the related states. The encoding was made injective instead
(`OB-JIT-SYM-INJECTIVE`, discharged; `sym_of_text_eqb`, above). Before that fix, the guard left symbol constants
out, which cost the most: of the 447 definitions using `=`, 429 compare only against a literal, but only 140 against
literals that are not symbols.

Fuel plays no part. `eq_val` spends fuel only at absvectors, which `VR` never relates, and pairs recurse
structurally, so on related values the model never stops with `RCyclic`; the source's depth bound likewise matters
only for vectors. C's process exit on terms past 2^31 steps or 2 GiB of pending pairs (`OB-JIT-EQ-CYCLE`) is not
modelled, as before. So no case goes through the resource permission. Three proof mutants are rejected
(`ShenJitLowerEqSym` and `ShenJitLowerEqNaN`, which widen `eq_core`'s guard to symbols or to every real, and
`ShenJitLowerCheckEqGuard`, a checker without the guard). Lines, net: 15 in `JitLowerRel.v`, 58 in
`JitLowerPrim.v` (with the two checked witnesses), 18 in `JitLowerStep.v`, 91 in all, plus one premise in
`JitLowerKont.v` and three changed lines in `JitLowerCheck.v`.

**Measures.** Lines by hand, first session: about 70 minutes to the first theorem, about 2.5 hours in all, including
compile waits. Each Rocq file compiles in under 3 minutes under Rocq 9.3.

| Part | Lines, as written | Covers |
|---|---|---|
| Relation (`JitLowerRel.v`) | 169, then 176, then 191 | the fragment above |
| Continuations and stability (`JitLowerKont.v`, `JitLowerStable.v`) | 269 | |
| Primitives (`JitLowerPrim.v`) | 176, then 234 | 14 primitives |
| One step and the theorem (`JitLowerStep.v`, `JitLowerThm.v`) | 1,313, then 1,338, then 1,346, then 1,364 | every case of the fragment |
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
- `=` is admitted only against a safe constant: the bytecode model is stuck (`RIdentity`) on two NaNs, where the
  source answers (`OB-JIT-NAN-IDENTITY`), and until `OB-JIT-SYM-INJECTIVE` its symbols were not injective on code points.
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
| `scripts/check-shen-jit-norm.sh` | Opt-in, report only: regenerates the witnesses with `capture_passes.sh`, compiles the above, checks their assumptions, runs the judge over all 24 files |

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
| `[do X Y]` | `ECall do [X; Y]` (`erase_do`) | This is the named call the source `(do X Y)` is in KLSemantics, which is how `JitLowerEquiv` (pass-equiv) states the front end, so that step is congruence. The emitter instead inlines it: X goes into a temporary, then Y is lowered in place in tail position. `check_fn` expects a call, so it rejects every `do`. Admitting the inlining is the emission relation's job, under the premise that the store's `do` is the kernel's: `do` is sealed at stage 0, and its code `(return 3)` is the kind `check_fn` accepts, so `FunRel` can cover it. An earlier version erased `do` as a fresh `let`, which `check_fn` accepted in 3 more definitions (`shen-jit.lower.finish`, `.value`, `shen.repl`). It was switched to the named call to match the front end's interface. |
| `[prim raise-cond []]` | `ECond []` | none: it raises `XCondFail`, as `norm-cond`'s end does, and `C_cond_nil` admits it. `raise-cond` is not a KL name. |
| `[prim Op Args]`, Op a KL primitive | `ECall Op Args`; None if the count is not Op's arity | A primitive call is a named call in `KLSemantics`, resolved in `gfuns`. This is correct under the store invariant `JitLowerStep` already assumes (`fr_prim`/`fr_name`: primitive names are bound to their `FPrim`). |
| `[prim Op Args]`, any other Op | `ECall Op Args`, listed by `port_prims` | **Port primitive, no KL meaning**: the KL store defines no such name, and `jit_rules`' `port_prim` is off, so the call raises `XUndefinedFun` (see Port primitives above). Each one needs a primitive spec and a ledger entry. These include `shen-jit.inlined?` (`open-call`'s guard) and `shen-jit.arity?` (`fn-call`'s test). Both are C primitives (`src/runtime/prims.c`, `P_INLINEDP`/`P_ARITYP`) that read a function's current code object, and their specs must make the guard's two branches agree. |
| `[call F Args]` | `ECall F Args` | none for erase. Port functions called this way are ordinary KL defuns in `src/port/shen-jit.kl`, so the store's definitions give their meaning: `shen-jit.eval-kl` (line 10), `shen-jit.undo` (196), `shen-jit.unify=` (201), `shen-jit.unify=!` (234), `shen-jit.deref=` (177, 0.6), `shen.bindv`. Relating `unified-now`/`bound-now`'s expansions to `is`, `is!` and `shen.bind!` belongs to the front end. One semantic difference goes in the ledger rather than being left as a pending proof: `shen-jit.eval-kl` returns any non-pair unchanged, while KL's `eval-kl` raises `XEvalKL` on a closure or vector (`parse` fails). |
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

**Stage 0 result.** Inputs: the `.forms` and `.sbc` of the pin's `/lps/p4/sj/build/stage0`, and 24 `.norm`
witnesses. The witnesses are not committed: `scripts/check-shen-jit-norm.sh` regenerates them with
`tests/shen-jit/capture_passes.sh` unless `NORM_DIR` names a directory of them, and capture fails unless the build's
own lowerer reproduces every stage 0 code object byte for byte. On `p2/int` the command was
`JIT_OUT=/tmp/p2-int-norm scripts/check-shen-jit-norm.sh` in `buri-lps` (Rocq 9.3), on the tree of commit
"Reconcile wave 1 of the pass split on p2/int": witness and count runs 950 of 950 byte-identical, image run 939 of 950
(a measurement). `cd witness && sha256sum *.norm | sha256sum` is
`38a414a295c1aff39360a73a812591d0862fbc6c0bf32bc24314d8140993de20`, and every per-file hash equals that of the set
used for the earlier run below. The six statements are closed and `rocqchk` replays both modules.

**At 0.6: 133 of 955 definitions accepted** on the erased witness (`NORM_DIR=/tmp/p2-v06-capture/witness
JIT_OUT=/tmp/p2-v06-norm scripts/check-shen-jit-norm.sh` in `buri-lps`, witnesses from `capture_passes.sh` on
`/lps/p6/sj`: witness and count runs 955 of 955 byte-identical, image run 944 of 955; norm witness set sha256
`e45add98...b69dd1`, the same set again from the pinned binary): 822 rejected, none failing erase, none unreadable, all front end unchecked. The source-body judge
accepts 111, all also accepted on the witness; the 22 gained are the 21 below plus `shen-jit.lower.fixed?`, now a
dictionary lookup. The six statements are closed and `rocqchk` replays both modules.

**At 0.4: 131 of 950 definitions accepted** on the erased witness on `p2/int`, where the checker also admits `=` against a
safe constant (`pass/eq`): 819 rejected, none failing erase, none unreadable. All 131 are front end unchecked. None
uses a port primitive and none has a folded constant. The stage 0 judge on the source bodies accepts 110, and every
one of the 110 is also accepted on its witness: none is lost.

| File | Accepted | Was (source) | Gained |
|---|---:|---:|---|
| declarations | 2 | 1 | `shen.lambda-entry` |
| lower | 24 | 19 | `shen-jit.lower.call`, `.let-frozen`, `.code`, `.apply-all?`, `.inline-thaw?` |
| prolog | 13 | 11 | `shen.prolog-arity-check`, `shen.prolog-parameters` |
| reader | 14 | 13 | `shen.alpha?` |
| sequent | 6 | 5 | `shen.construct-context` |
| shen-jit | 19 | 13 | `shen.+string?`, `shen.<shortnatters>`, `shen.<whitespaces>`, `shen.<digits>`, `shen-jit.digits`, `shen-jit.number-start?` |
| sys | 16 | 15 | `eval` |
| writer | 5 | 3 | `shen.fbound?`, `shen.list?` |
| yacc | 7 | 5 | `shen.partial-parse-failure?`, `shen.parse-failure` |
| the other 15 files | 25 | 25 | |

**Earlier run, before `=` was admitted** (`pass/ir`, `NORM_DIR=<witness dir> JIT_OUT=/tmp/ir-norm3`): 72 of 950
accepted, 878 rejected; the source-body judge accepted 61, all also accepted on the witness. The 11 gained there
(`shen-jit.lower.code`, `shen-jit.lower.apply-all?`, `shen.prolog-parameters`, `shen.alpha?`, `shen.<shortnatters>`,
`shen.<whitespaces>`, `shen.<digits>`, `shen-jit.digits`, `eval`, `shen.partial-parse-failure?`, `shen.parse-failure`)
all contain an inlining marker, which erase drops; this agreed with pass-capture's census (72 with the marker dropped).
Three hand mutations of `shen-jit.digits`'s witness, on the earlier version of erase, whose marker handling is
unchanged, each turned that one verdict to rejected and changed nothing else: a constant changed (48 to 49), the
marker's name used in its body, and the marker renamed so that it is no longer dropped. These were hand checks. No
proof mutation was added, since the judge is not in a gate. The ten gained only on `p2/int` were not checked by hand.

What the 131 mean: each code object is a lowering, in `JitLowerRel`'s sense, of its witness's erasure. For the 110
that were already accepted, the source-body verdict still stands on its own. For the 21 gained, nothing yet says
that the erasure is equivalent to the kernel's KLambda: inlining (`shen.digit?` and others) and sharing changed the
body, and that is wave 2's obligation. Most of the 819 rejections come from the emission relation (`=` without a safe constant, `value`,
closures, folded constants, port primitives), not from erase; pass-capture's census lists the first blocker for each.

**Coq 8.18.** `make prove` runs Coq 8.18 (`toolchain.lock.json`, `scripts/bootstrap-rocq`). The pinned 8.18 debs
(checksums from `rocq-packages.lock`) were used in an amd64 Ubuntu 24.04 container. Under them, the 70-jit chain
from `Observation` through `JitNormStage0` compiled with `scripts/rocq coqc -Q . Buri`, the six statements printed
"Closed under the global context", and `coqchk` replayed `JitNorm` and `JitNormStage0`. A full `make prove` was not
run.

## Differential results

Tests under `qemu-riscv64` on the named binary, at the pin. Each case's code comes from the real lowerer, and
Rocq computes the verdict by `vm_compute`. Agreement is sampled evidence, not proof.

**At 0.6: 1,406 cases, 1,296 agree, 110 known differences, 0 new or unexplained** (`tests/shen-jit/known-differences.txt`).
By set: eval cases 1,106 (1,005 agree), ops 138 (all agree), contract 162 (153 agree). By kind: 80 excluded features reached, 6 depending on one, 4 with no identity in the model, 19 IO responses, 1 image state. The known list was carried from 0.4
by aligning each case's captured code and result between the two runs (every one of the 106 found its 0.6 index;
references between entries were renumbered with them), then four new differences were classified one by one: three
eval cases that `open` a file around `shen-jit.write-bytes` (IO responses, not compared) and `t.deref-eq-all`, whose
`(= (shen.deref X B) (shen.deref Y B))` now lowers to `shen-jit.deref=`, which calls `shen-jit.same?` on two pairs (no
identity in the model). Of the 63 eval cases new or changed at 0.6 the other 59 agree, among them every `n->string`
UTF-8 and range case, the `write-bytes` range and buffer errors and the constant-sharing cases; the two new contract
cases (`n->string` of 955 and of a surrogate) agree. Tests, not proof.

**At 0.4: 1,344 cases, 1,238 agree, 106 known differences, 0 new or unexplained**.
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
