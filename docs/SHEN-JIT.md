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

The binary's hash covers its heap image: the last 783096 of its 5440856 bytes (runtime `13afde42...`, image
`fd8485a5...`), which stage 1 made by loading stage 0 and running initialisation. Validating stage 0 doesn't cover that.
`OB-JIT-IMAGE` is now partial and split into five sub-obligations ([SHEN-JIT-IMAGE.md](SHEN-JIT-IMAGE.md)):
- `OB-JIT-IMAGE-CODE` (partial, lane-checked since r21-image-lane): `rocq/JitImage.v` decodes the image in the lane.
  Rocq proves `image_code_ok`: 955 of 955 stage 0 code objects equal the code objects their image function cells hold
  (`code_check_sound`, closed). `image_code_ok` is closed under the global context too: the reader copies the
  image's bytes as `byte` constructors and Rocq joins them. It stays partial because it depends on `-READER`, which
  is open (the reader is trusted), and the ledger does not discharge over an open dependency.
- `OB-JIT-IMAGE-INIT` (open): the 7 code objects initialisation made with the image's own lowerer, 357 closures
  outside function cells (352 of which run code reached from the 955), 55 bound value cells and the data they reach.
  The code part is feasible by judging initialisation's `eval-kl` forms. The data part is infeasible now.
- `OB-JIT-IMAGE-SEALING` (open): stage 1 seals 18 files where stage 0 sealed 24, which leaves 65 names redefinable
  behind 115 sealed call sites. Tested in the binary: after a redefinition, sealed sites keep the old closure while
  open calls see the new one. So only a stated exclusion of redefining the 65 is feasible.
- `OB-JIT-IMAGE-READER` (open): the reader (now `stage0_to_rocq.py --image`) and `image_load`.
- `OB-JIT-IMAGE-FILE` (partial): the run reads the image from `argv[0]` (resolved through `PATH`) unless
  `SHEN_JIT_IMAGE` is set, and the process model doesn't yet relate that file to the loaded binary. Feasible only as a
  stated premise.

Share's HT and HP (premises on branch `p2/r1-share-ht`), the image facts (Rocq, lane): thaw is sealed and its cell holds stage 0's code for it. hd and tl
are not sealed and have no function. The binary refuses `defun` of all three as fixed names. HP's requirement that hd
and tl be in `sealed` therefore does not match the image's sealed bits (see SHEN-JIT-IMAGE.md).

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
| `rocq/JitFrontProlog.v` | norm's Prolog rewrites: the bound-now rule, proved sound (`bind_rule_sound`); D00's `bind_site_sound_statement` refuted (`bind_site_unsound`); the source-shape scan `prolog_scan` |
| `rocq/JitImage.v` | r21-image-lane: the heap image decoder, `check_def` against `build_code`, `code_check_sound` (closed), and the census the lane's image step prints (OB-JIT-IMAGE-CODE) |
| `rocq/JitEmitRule<X>.v` | Seven emission families (Eq, Store, Prim, DoFold, Clo, App, Trap): each family's three empty rule hooks with their map and all lemmas |
| `rocq/JitEmitRel.v` | JitLowerRel's relations indexed by code object and capture names, with the family hooks; hand-written nested `Comp_ind'`; `comp_embed` |
| `rocq/JitEmitNestTest.v` | A copy with a non-empty nested dummy rule, its `Comp_ind'`, and `suffix` proved by it |
| `rocq/JitEmitKont.v` | Every continuation frame the families get (handler, dynamic-call window of at most one argument, do, closure-entry return, the primitives `frame_prim` admits) |
| `rocq/JitEmitInv.v` | The generalized back-end invariant and statements (`sim_X_statement`, `preservation'`, `call_preservation'`, `call_preservation_src'`), unproved |
| `rocq/JitEmitSim.v` | The generic parts as implications: `preservation'` from `sim'` and `raise_resolve`, `call_preservation'` from `preservation'`, `call_preservation_src'` from `call_preservation'` and `clo_scoped`; the slot-1 gap witnessed; `preservation'`, `call_preservation'`, `call_preservation_src'` refuted (stale `m_next`) (r22-emit-sim) |
| `rocq/JitKRefCallNoTableCex.v` | `call_rel` without SRel's table clause refuted (`call_rel_no_table_refuted`) |
| `rocq/Audit_Jit.v` | Assumption audit of 723 statements |
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
| `rocq/JitKRefCompatCtl.v` | KRef's control compatibility lemmas: compat_lit, var, let, if, and, or, cond, type and defun (JitKRef statements, closed); trap at index k from `fund_below k` alone (`compat_trap_fb`, the corollary `compat_trap_lt prim_compat`; `AppExn_fb`), and `compat_trap_statement` from `fund_gen_statement` alone (`compat_trap_of_gen`) |
| `rocq/JitKRefCompatCall.v` | KRef's named-call compatibility lemma: compat_call at index k from `fund_below k` alone (`compat_call_lt`; `compat_call_lt_pc` takes `prim_compat_statement`), the reflexive scope form `compat_call_refl_lt`, and `compat_call_statement` from `fund_gen_statement` alone (`compat_call_of_fund`) |
| `rocq/JitKRefBase.v` | KRef's structure: index and world monotonicity, anti-reduction and target-step lemmas, the bind lemma and one KRel lemma per frame, world reachability, `sealed_stable` and `storehas_stable` |
| `rocq/JitKRefCompatClo.v` | KRef compatibility for lambda, freeze and dynamic application: `compat_lambda`, `compat_freeze` (no induction hypothesis), the `_lt` forms from `fund_below`, `app_rel`, and `compat_app_of_fund` from `fund_gen_statement` and `prim_compat_statement` |
| `rocq/JitKRefFv.v` | `scoped_fv` (an expression scoped in g has its free variables in g), `fv` against binders and the list forms (`fv_lam_iff`, `fv_let_iff`, `scoped_defun_fv`, `fv_cond_iff`, `fv_app_iff`, `fv_call_iff`), `fund_below`'s scope condition carried to subterms and under binders (`fv_scope_*`), and the index induction `fund_below_all` / `fund_gen_of_step` that `fund_gen_statement` will be proved by; not `fund_gen_statement` itself |
| `rocq/JitKRefFund.v` | KRef's fundamental property outright: `fund_step` (the induction step over every constructor from the compat lemmas and `prim_compat`), `fund_gen`, `fundamental`, `KRef_refl`, `compat_trap`, `compat_app`, `compat_call`, `store_refl`, `adequacy` and `call_preservation_src`, each with no premise beyond its statement's own |
| `rocq/JitKTerm.v` | `rocq/JitKRef.v` over `jit_rules_nr sealed` (jit_rules with `resource_exn := fun _ => None`), with `srun_nil_Sstar_statement` and Section Compose left out: the relation KTerm reads backwards. No proofs |
| `rocq/JitKTermGround.v`, `JitKTermBase.v`, `JitKTermCompatCtl.v`, `JitKTermCompatClo.v`, `JitKTermPrim.v`, `JitKTermCompatCall.v`, `JitKTermFv.v`, `JitKTermFund.v` | KRef's proof files over `jit_rules_nr`, renamed; three proofs that built a resource step are restated for an uncatchable `Fail` (`step_from_ret_top`, `fail_obs`, `ObsT_fail`); no KRef statement or file is changed |
| `rocq/JitKRefTerm.v` | `KTerm` (`OB-JIT-LOWER-TERM`), `step_nr_sub` (a resource-free step is a jit_rules step), `KTerm_omega_refuted` (non-vacuity), `KTerm_compose_statement` and the open `KTerm_checker_statement` |
| `rocq/JitKRefTermThm.v` | KTerm's fundamental property and every compatibility lemma in its orientation, `KTerm_adequacy`, `KTerm_diverges`, `KTerm_compose`, source reduction (`ERel_red` and `ERel_red_let`, `_if`, `_cond`, `_type`, `_call`, `_app_lam`) and the front rule `KTerm_lambda_app` |
| `rocq/JitKRefPrim.v` | `prim_compat`: every table primitive under `jit_rules`, and every port primitive it gives, maps related arguments and stores to related results (primitive parametricity) |
| `rocq/JitLowerEquiv.v` | Old qualified names (`JitLowerEquiv.JitLowerEquiv.*`) as abbreviations of the moved constants; no constants of its own |
| `rocq/JitLowerStage0.v`, `tests/shen-jit/stage0_to_rocq.py` | Decoding stage 0 files in Rocq, from a trusted tokenizer |
| `rocq/JitFrontSugar.v` | r1-f-sugar: the norm checkers of the cond, sugar, thaw-sugar and trap-sugar families, each proved to establish KRef, and `chk_front` (congruence plus the four) proved sound from the compatibility lemmas |
| `rocq/JitFrontD.v` | D00: the front rules' store D (a lowered store), built from decoded stage 0 data; `D_compiled'`; the allowed store facts; the inline relation `inl_site` and `aeq`, with their soundness statements (unproved) |

**The front rules' store D** (`rocq/JitFrontD.v`, D00, 9 November 2026). D is a lowered store: for each callee a
definition's rewrites rely on, D holds `FUser ps e_F` with `e_F` the erased stage 0 normal form of F. Com's FunRel makes
a store body the body F's code is CompFn-related to, and that code lowers the inlined normal form, which the src judge
rejects for all 528 definitions with an inlining marker, so a source store cannot meet `D_compiled` on stage 0's
machine. `D_compiled'` is the per-callee emit check (proved to imply `D_compiled`). `D_of` builds a definition's D in
Rocq from the tables `stage0_to_rocq.py --D` tokenizes: the marker closure, `do` when the normal form has a do node
or the source calls it, `thaw` and `protect` when called, `shen.bind!` in either bound-now shape (a literal frozen last argument, or a let-bound freeze), and the port defuns `shen-jit.deref=` (alone) and `shen-jit.unify=` with `shen-jit.unify=!` (together) when the normal form calls them. `shen.bindv` and `shen.unwind` are ordinary inline callees (`D_has_inline_callee`, named `D_has_port_bindv`/`D_has_port_unwind`): `D_of` adds them through the marker closure, since bound-now's template is normalised and its bindv/unwind calls inlined, and shen.overbind and the unify forms inline bindv directly (bindv is in 10 definitions' D, unwind in 8, `shen.bind!` in the 6 with bound-now sites). Inside a bound-now expansion those regions belong to `bind_site`, which matches them against e_B's own inlined regions and uses no fact about either callee. Test, not proof (Rocq `bind_src_report` on the decoded table, witness set e45add98..., r1-d00-merge): all 37 bound-now sites, in 6 definitions, are accepted by `bind_site` against their `D_of` store with X, Y and B taken from the source call (`pair_src` pairs each site with a distinct source call whose arguments are `expr_eqb` to the site's let values); E is still read back from the expansion (no Rocq normaliser exists). `inl_site` on every real inline site (test, Rocq `inl_report`): 5430 sites, 5360 alpha, 24 integer substitution, 22 thaw-with, 18 depth cut, 6 accepted only with fold (the vector sites, waiting on interface item 2), 0 rejected; 522 of the 528 definitions with a marker have every site accepted without fold. Argument values are read back from the expansion; e_F comes from the table. `D_compiled'` today (single-entry D against the table's code objects): true for `do` and `protect`, false for `thaw`, `shen-jit.deref=`, `shen-jit.unify=`, `shen-jit.unify=!`, `shen.bind!`, `shen.bindv` and `shen.unwind`. Why, in Rocq (r1-d00-merge): `cblk_of` lists the constructs at positions `JitLowerRel.Comp` compiles that no Comp rule admits against the code (a special form, a primitive outside `pmap` or of the wrong arity, `=` with no literal operand, a named call with no call instruction), `cblk_of_Comp` proves a Comp derivation has none, so each listed blocker is a proved reason (`cblk_reject`), and `D_why` (with `D_why_spec`: empty exactly when `D_compiled'` holds) names them per entry. thaw: apply (emit family App, a missing feature). The other six all call port primitives with no approved source meaning (`shen-jit.pvar-offset`, and for the port forms `shen-jit.pvar?`, `shen-jit.deref`, `shen-jit.same?`: `OB-JIT-PORT-PRIMS`, identity `OB-JIT-IDENTITY-MODEL`), besides missing features (`address->` Store, `do` DoFold, apply App, `=` on computed operands Eq with its NaN gate), so they are named, decision-gated residuals: a `D_of` store holding bind!, bindv, unwind or a port form cannot meet `D_compiled'` until Reuben decides those items. `D_prims_fold` never holds of a D built by `D_of` (+ and - have no stage 0 row), so the folding inline sites wait on interface item 2. `D_of_wf` proves D_wf for any sealed list holding the stage 0 names. A smoke run (a test)
decoded all 955 rows with distinct names. The inline rule compares the inlined normal body with `e_F` by `inl_site`:
alpha-equivalence (`aeq`) plus integer substitution, thaw-with and depth cut; `bind_site` does the same for bound-now
against shen.bind!'s lowered body, with a seeded renaming. Their soundness and `aeq`'s are stated, not proved (F-inline). Census, not proof (`spikes/pass-split/d00_inline_census.py`): of 5430 inline sites, 5360 are alpha-equivalent, 30 integer substitution
(6 also folding +), 22 thaw-with and 18 depth cut. Under this design T02's end-state forecast is 955; a source store
(option B) would reach about 725. Two interface items for the KRef track: `fresh_ok` over `D_bodies` fails on lowered
bodies (the premise the rules use is `fresh_front`), and fold-arith's `(+, FPrim PAdd)` in D needs `+` in `sealed`.
No count changes: the source judge accepts 148 of 955 stage 0 definitions; the full-pipeline validated count is UNKNOWN.

**Norm checkers: cond and sugar** (`rocq/JitFrontSugar.v`, r1-f-sugar, 11 November 2026; `OB-JIT-LOWER-FRONT`, open). One
checker per family, each parametric in the recursive checker `rec` and proved to establish KRef for any `rec` that does
(`chk_cond_sound`, `chk_sugar_sound`, `chk_thaw_sound`, `chk_trap_sound`). A rule is a source anti-reduction to an
intermediate source term followed by `rec` on it: `(type X T)` to X, `(protect X)` to X (the kernel's protect in D,
`D_has_kernel_protect`) and a cond clause whose test is the literal true to its body. Four rules take the intermediate's
congruence step themselves and are proved in that composed form: any other cond clause to an if whose else is the rest of
the chain (`cond_if`), `(thaw X)` to `[apply X]` (the kernel's thaw in D, `thaw_sugar`), `((lambda X B) A)` to
`(let X A B)` (`sugar_lamapp`) and `(trap-error X H)` with H not a lambda to `[trap X E [apply H [var E]]]`, E fresh and
not in scope (`trap_sugar`); `(trap-error X (lambda E H))` erases back to its own shape and is congruence. Interface
limit: where another family rewrites that intermediate at the same node (copy's let-lambda on the let, copy's frozen-late
on norm-cond's if chain, copy's frozen-in and inline's thaw-with on thaw's `[apply [var G]]`), this checker rejects and
that family must take the source form. Rejected, with no rule: `fn` sugar, eval-kl to `shen-jit.eval-kl`, curried dynamic
application and lambda application with more than one argument (both argued unsound under `jit_rules`, not refuted in
Rocq; deferred to the uncurrying family). `chk_front` (congruence and the four families, by fuel) is proved sound under
Section hypotheses naming the thirteen compatibility statements (`chk_front_sound_h`), then instantiated with the
proved lemmas (`chk_front_sound`, only premise `D_wf`). Six mutants (`ShenJitFrontSugar*`, at least one per family) are
rejected. Test, not proof (Rocq `front_report`, vm_compute on the decoded table, `.norm` witness set e45add98..., each
definition's source form against the erasure of its normal form in its `D_of` store): `chk_front` accepts 418 of 955
norm links, among them all 390 definitions whose fired front families are within cond, sugar, thaw-sugar and
trap-sugar (194 with none fired); every rejected one has inline, share, copy, bind, eval-kl or fold-arith fired. No
validated count changes: no full-pipeline judge runs these checkers, and the census's forecast set for this family
(emit tf-accepted, source-judge rejected, required families within these four) is empty
(`spikes/pass-split/features.tsv` sha256 6eeef697...). KTerm lemmas for these rules (`OB-JIT-LOWER-TERM`) are not
written here.

**norm's Prolog rewrites** (`rocq/JitFrontProlog.v`, r1-f-prolog, 11 November 2026). The bound-now rule `bind_rule`, in F00's
front-rule shape (`rule`, `rule_sound`, same text as `JitFrontCheck`, not yet on `p2/int`), is proved sound for every store D
from `D_wf` alone (`bind_rule_sound`, audited, Closed under the global context): (shen.bind! X0 Y0 B0 (freeze E0)) refines
(let a1 X (let a2 Y (let a3 B N))) when the recursive checker relates X0, Y0, B0 to the let values and E0 to each place N runs
it (in the scope of that place's free names), and `beq` relates shen.bind!'s lowered body in D to N: alpha-equivalence with
bind!'s first three parameters renamed to a1, a2, a3, the fourth thawed in place, and an unused `let` read as the kernel's
`do` from D. No transitivity of KRef is used: `KRel_ca_let` and `KRel_ca_last` relate the source's argument frames to the
target's lets, the source enters e_B, and `beq_sound` relates e_B to N by a direct induction (with `ERel_letdo` and
`KRel_do_tail` for the target's do). A Rocq-checked finding: D00's `JitFrontD.bind_site_sound_statement` is **false**
(`bind_site_unsound`): bind_site accepts a frozen body that reads KLPort's closure-identity key `id_key`, which the source's
freeze closure binds to its own new cell while the expansion, running the body in place, reads the caller's; the target
returns the caller's value where the source can only return the cell or raise a resource error. `bind_rule` refuses it
(Example `bind_rule_rejects_id_key`). `inline_site_sound_statement`'s thaw-with case has the same unguarded position (not
refuted in Rocq here). Mutants `ShenJitFrontPrologIdKey`, `ShenJitFrontPrologHidden`, `ShenJitFrontPrologFreeVar`,
`ShenJitFrontPrologLetdo`, `ShenJitFrontPrologScope`, `ShenJitFrontPrologDoFirst` and `ShenJitFrontPrologP4Key` are rejected.
Test, not proof (Rocq `prolog_scan` over the 955 parsed stage 0 sources, `stage0_to_rocq.py --prolog`): bound-now's direct
shape in 6 definitions (25 sites), the let-frozen shape in 5 (23 lets; the freeze-copying family rewrites it to the direct
shape), unified-now's in 4 (7), cut-fail's and deref='s in 0 (16 calls of shen.cut with a frozen fourth argument, in 8
definitions, none freezing a `when` call). Residuals, each a ledger entry: `OB-JIT-FRONT-PROLOG-UNIFY` (unified-now: its
target calls port forms over `shen-jit.same?`, `shen-jit.deref`, `shen-jit.pvar?`, `shen-jit.pvar-offset`; identity and port
primitives, decision-gated), `OB-JIT-FRONT-PROLOG-DEREFEQ` (deref=: `shen-jit.same?` on one cell against = on two copies,
the NaN case; decision-gated; vacuous for stage 0) and `OB-JIT-FRONT-PROLOG-CUTFAIL` (no rule; vacuous for stage 0). Every D
holding shen.bind! still fails `D_compiled'` (`shen-jit.pvar-offset`, `OB-JIT-PORT-PRIMS`), so the 6 bound-now definitions
stay residual in the full pipeline. bind_rule on the real sites (test, not proof: Rocq `bind_rule_report` via `stage0_to_rocq.py --prolog-D` over the decoded table, witness set e45add98..., recursive checker accepting everything, empty scope, so the structural part `beq` is what is tested): all 37 bound-now sites in the 6 definitions accepted (shen.system-S-h 18, shen.primitive 3, shen.l-rules 1, shen.myassume 6, shen.p-hyps 6, shen.variancy-signature 3). No count
changes: the full-pipeline validated count is UNKNOWN.

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
assembly in `JitEqBudgetCore.v`). The fundamental property, every compatibility lemma, store reflexivity, adequacy and `call_preservation_src` itself are proved outright in `rocq/JitKRefFund.v` (below). Not proved: any front-link checker. Under Com's
FunRel the callees b0 calls are the lowered bodies, not the kernel's source definitions. A checker must reject norm's
`(fn F)` rewrites, open-call inlining behind `shen-jit.inlined?` and eval-kl to `shen-jit.eval-kl`, which cannot satisfy
`KRef` in Búri's KLambda. Proof mutants `ShenJitEquivEndsSameStore`, `ShenJitEquivAdequacyStrict` and
`ShenJitEquivComposeLeft` are rejected (since K00 each is the chain JitKRef.v, JitKRefGround.v[, JitKRefCompose.v]
with the statement mutated). `rocq/JitKRefCompatClo.v` (14 audited statements) proves `compat_lambda` and
`compat_freeze` outright, their reflexive forms `compat_lambda_lt` and `compat_freeze_lt` from `fund_below k`, `AppAll` for
related continuations (`app_rel`, from `fund_below k` and `prim_compat_statement`), `compat_app_lt`, and
`compat_app_statement` only as an implication from `fund_gen_statement` and `prim_compat_statement`
(`compat_app_of_fund`; `prim_compat_statement` is now proved in `rocq/JitKRefPrim.v`, so only `fund_gen_statement` remains,
not yet combined into an audited statement); mutant `ShenJitKRefLamNoSameId` is rejected.
`rocq/JitKRefCompatCtl.v` (27 audited statements) proves the JitKRef statements compat_lit, compat_var, compat_let, compat_if,
compat_and, compat_or, compat_cond, compat_type and compat_defun with no hypotheses beyond their own (compat_defun takes
`D_wf`, and gets StoreHas of the new store from `storehas_stable`), each from an ERel-level lemma built on `ERel_push`
and the frame lemmas. Applying a trap's handler to the exception may apply a partial primitive (a handler `(+ 1)` is
`VPartial "+" [1]`), which runs `prim_rule_r`, so `compat_trap_lt` takes `fund_below k` and `prim_compat_statement`;
with `JitKRefPrim.prim_compat` that premise is discharged: `AppExn_fb` and `compat_trap_fb` (the corollary
`compat_trap_lt prim_compat`) take `fund_below k` alone, and `compat_trap_of_gen` gives `compat_trap_statement` from
`fund_gen_statement` alone (`compat_trap_of_fund` keeps the two-premise form). Mutants `ShenJitKRefCondSwap` (a copy of
compat_cond with the target's clauses reversed), `ShenJitKRefTrapNoPrim` and `ShenJitKRefAppExnNoPrim` are rejected. Since
r21-mutation-hygiene the last two stop at a real obligation, not at a missing name: `ShenJitKRefTrapNoPrim` restricts `AppExn`
to handlers that are not a partial table primitive (so `AppExn_of` needs no `prim_compat` there) and is rejected at
`KRel_KApply_exn`, the trap frame's handler step, where the handler is any returned value; `ShenJitKRefAppExnNoPrim` weakens
`AppExn_of`'s premise to primitive outcomes on equal arguments and is rejected in its primitive case, where the two argument
lists are only VRel-related. Both statements are true (`prim_compat` is closed), so both are rejected proofs, not false
statements. (Before r21 they replaced the proof by `assumption` and failed with "No such assumption", which showed nothing.)
`rocq/JitKRefCompatCall.v` (7 audited statements) proves compat_call. A call with no argument moves through the function
table at once (`ERel_call_nil`: `JitKRefCompatClo.call_rel` relates the two `call_named_r` moves, the two tables being equal
under SRel; `JitKRefCompatCtl.ObsT_of_MRel` pays the target's step); a call with arguments pushes `KCallArgs`
(`ERel_call_cons`: `KRel_KCallArgs`, whose `AppRel` of `(VPartial f [])` against itself comes from `app_rel`).
`compat_call_lt` (compat_call at index k, KRef-related arguments) takes `fund_below k` alone, being
`compat_call_lt_pc JitKRefPrim.prim_compat`; it needs no `D_wf`. `compat_call_refl_lt` is the reflexive scope form, and
`compat_call_of_fund` gives `compat_call_statement` from `fund_gen_statement` alone. Mutant `ShenJitKRefCallNoTable`
(SRel and GStore without `gfuns s0 = gfuns s`) is rejected at `JitKRefCompatClo.call_rel`, the named-call move
compat_call rests on, after `JitKRef.v`, `JitKRefGround.v` and `JitKRefBase.v` compile under the mutation. That mutant is a
rejected proof only. `rocq/JitKRefCallNoTableCex.v` (4 audited statements) refutes in Rocq a separate statement,
`call_rel_nt_statement` (call_rel's statement over the unmutated VRel, KRel and fund_below, with only SRel's table clause
replaced by True), not the mutant's own call_rel:
`call_rel_no_table_refuted` refutes call_rel's statement with SRel's table clause replaced by True (`SRel_nt`, over the
unmutated VRel, KRel and fund_below), at sealed = D = [], j = 2, with every other premise discharged (`fund_gen`,
`prim_compat`, `KRel_top`, `app_at`): the source table lacks `f`, so the source raises `XUndefinedFun`, and the target's
`(defun f () 1)` returns 1. `call_rel_nt_of_table` gives the conclusion back once `gfuns s0 = gfuns s` is added. Mutant
`ShenJitKRefCallNoTableCexTable` (SRel_nt with the clause restored) is rejected at the counterexample's store premise, where it
tries the restored clause by `vm_compute; reflexivity` and Rocq finds the two tables different; `cx_tables_differ` proves
`gfuns cx_s0 <> gfuns cx_s`, so no proof of that premise exists. Not
shown: that the mutant's whole chain (its own VRel, KRel, fund_below and GStore) is false.
`rocq/JitKRefFund.v` (14 audited statements) closes the fundamental property (option A). `fund_step` proves
`D_wf -> fund_below k -> fund_at k` by structural induction on the expression: literals and variables by `ERel_sval`
(a variable bound on neither side raises `XUnboundVar` on both, `ERel_throw_both`), let by `ERel_let` (the body below k
from `fund_below k`, at k from the induction hypothesis), if, and, or, cond and type by their ERel lemmas, trap by
`ERel_trap` with `AppExn_fb`, defun by `ERel_defun`, and lambda, freeze, application and named call by
`compat_lambda_lt`, `compat_freeze_lt`, `compat_app_lt` (with `prim_compat`, whose `=` case rests on
`JitEqBudgetCore.eq_budget_closed`) and `compat_call_refl_lt`. `fund_gen` is `fund_gen_statement` by
`JitKRefFv.fund_gen_of_step`; `fundamental` relates EnvRelAll environments on their names (`EnvRelAll_scope`);
`KRef_refl`, `compat_trap`, `compat_app`, `compat_call`, `store_refl`, `adequacy` and `call_preservation_src` follow
with no hypothesis beyond each statement's own premises (for `call_preservation_src`: `D_wf`, the two KRef links,
`StoreHas`, `store_ok`, `Com`, `CompFn`, the arity and `entered`). `store_ok` is carried beside SRel as a premise,
since SRel does not give it (`SRel_lok_refuted`). Mutants `ShenJitKRefFundNoTrapCase` (fund_step's trap case proved
as a literal) and `ShenJitKRefStoreReflNoStoreOk` (`store_refl_statement` without `store_ok s`) are rejected.
`OB-JIT-LOWER-FRONT` stays open: its completion evidence also needs the front-link checkers.
`rocq/JitKRefBase.v` proves the relation's structure (57 audited statements):
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

**Termination of the front passes** (`rocq/JitKRefTerm.v`, `rocq/JitKRefTermThm.v`; `OB-JIT-LOWER-TERM`, precisely
stated, partially discharged). `KTerm sealed D g e0 e := JitKTerm.KRef sealed D g e e0`: KRef's relation, text for text,
over `jit_rules_nr sealed` (jit_rules with no catchable resource failure), read with the expressions swapped. Its index then
counts source steps, and it says that every resource-free run of the source e0 to a terminal state (a value, an exception or
a wrong state), after any IO trace, is matched by a resource-free run of the target e with the same trace to a terminal
state of the same kind, with related values and stores. So, from a first-order environment and a well-formed store meeting
D, a target with no IO-free resource-free run to a value or an exception has a source with no IO-free resource-free run to
a first-order value or an exception (`KTerm_diverges`, by contraposition, constructively; `KTerm_adequacy` and
`KTerm_compose` have the same IO-free, first-order scope, as KRef's adequacy does). The rules must be resource-free: under jit_rules any
running state may raise `(XUser "out of memory")`, so a looping target would "terminate" by raising.
`KTerm_omega_refuted` proves that a looping target (omega) does not refine a source raising `(simple-error "out of memory")`,
which under jit_rules it would; mutant `ShenJitKTermResourceSteps` puts the resource field back and Rocq rejects
`om_srun`. A resource-free run is a jit_rules run (`step_nr_sub`). Proved, each Closed under the global context (200 audited
statements: 40 in `JitKRefTerm.v` and `JitKRefTermThm.v`, 160 the JitKTerm copies' theorems): the fundamental property (`KTerm_refl`, `KTerm_fundamental`), every compatibility lemma, per-link adequacy,
the two-link composition `KTerm_compose` (through the first-order observation and `GStore_trans`, not transitivity), source
reduction (`ERel_red`: the source is the side whose runs are quantified, so KRef's source anti-reduction becomes source
reduction, free under the deterministic resource-free machine) with one lemma per KRef anti-reduction, and norm's
((lambda X B) A) to (let X A B') for an atomic A (`KTerm_lambda_app`; mutant `ShenJitKTermLamAppIdKey` drops its
id_key premise and is rejected). Open: front-link checkers that establish KTerm (`KTerm_checker_statement`; none exists,
and the same checkers owe KRef), rewrite lemmas for the other front rules, and the binding to the extended back end's
invariant (JitEmitInv, not on `p2/int`). Total correctness of a link is KTerm for termination and outcome in the
resource-free semantics together with KRef for every jit_rules run of the target.

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
the four comparisons, `cons hd tl cons? number? string?`; `=` when one operand is a constant fixnum, string, symbol, boolean, `()`
or non-NaN real; 0.4's one-slot `cons` chain with constant heads; named calls and named tail calls, with
`lower.shen`'s in-place argument moves. **Not admitted:** closures, captured variables, `trap-error`, `=` on two
computed values or against a NaN or pair constant,
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

**Stage 0.** `scripts/check-shen-jit.sh` decodes all 24 file pairs and runs the checker: **148 of 955 kernel definitions
accepted** by the source judge at 0.6, 807 rejected, none unreadable (`tests/shen-jit/stage0-accepted.txt`). At the re-pin it was 111 of 955, and admitting `=` against a symbol
constant (below) took it to 148, losing none. At 0.4 it was 110 of 950.
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
61 to 110 at 0.4, and none was lost; admitting symbol constants took 0.4 to 145 (branch `pass/eq`,
906b389) and 0.6 from 111 to 148. Each accepted definition is a
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
assign each of the 955 definitions the emit features its normal form needs and the front families that fired. Rerun
after `=` against a symbol constant was admitted (branch `p2/eq-guard-merge`, 10 November 2026), its prediction for the
current `Comp` matches the Rocq src (148), nf (150) and tf (174) verdicts on every definition (at the re-pin, before that
change: 111, 112 and 133). It also forecasts what each feature, each family and each residual decision (port
primitives, eval-kl, identity, NaN `=`) would admit, directly and under the callee-closure limit. That limit cuts the
current 148 to 63 (111 to 46 before), because 450 definitions reach a 181-definition strongly connected component.

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
value is a fixnum, string, symbol, boolean, `()` or a real that is not a NaN. The checker decides it on the code's
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
literals that are not symbols. With the fix the guard admits symbol constants. At 0.4 stage 0 went from 110 to 145
(35 definitions blocked only by `=` against a symbol); at 0.6 it went from 111 to 148, none lost, and the 37
gained are exactly the definitions `features.tsv` lists with `eq-symbol-const` as their only feature and no
required family (census, compared by name).

Fuel plays no part. `eq_val` spends fuel only at absvectors, which `VR` never relates, and pairs recurse
structurally, so on related values the model never stops with `RCyclic`; the source's depth bound likewise matters
only for vectors. C's process exit on terms past 2^31 steps or 2 GiB of pending pairs (`OB-JIT-EQ-CYCLE`) is not
modelled, as before. So no case goes through the resource permission. Three proof mutants are rejected
(`ShenJitLowerEqPair` and `ShenJitLowerEqNaN`, which widen `eq_core`'s guard to pairs, which can hold a NaN, or to every real, and
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
- `=` is admitted only against an atomic constant that is not a NaN: the bytecode model is stuck (`RIdentity`) on two NaNs, where the
  source answers (`OB-JIT-NAN-IDENTITY`), and until `OB-JIT-SYM-INJECTIVE` its symbols were not injective on code points.
- No lowerer bug was found. Nothing was rejected for a reason that looked wrong; rejections weren't reviewed
  one by one.

### Extended back end: statements (emit-spec)

Branch `p2/emit-spec`. Statements and design for the emission families; no family is simulated yet,
and the stage 0 judge is unchanged by it. When emit-spec was written the source judge accepted 111 of 955
definitions; on `p2/int` it now accepts 148 of 955 (`tests/shen-jit/stage0-accepted.txt`). Both are source-judge
counts, not the full-pipeline count, which is UNKNOWN (no full-pipeline judge has run).

- **Shape.** `rocq/JitEmitRel.v` copies JitLowerRel's six relations and indexes each by the code
  object and its capture names. JitLowerRel has the code as a Section variable instead. The spec asked
  for the old index shape, but a closure's body is nested code, and stating its derivation inside the
  same block needs the code as an index. With the code fixed, a second inductive over codes would have to
  nest through Comp's own parameter, and Rocq 9.3 refuses that ("Non strictly positive
  occurrence"). The evidence is now in the tree: `JitEmitNestTest.NestShape` reproduces the refused
  definition under `Fail` (the lane compiles it, and the `ShenJitEmitNestShapeAccepted` mutant,
  without `Fail`, is refused), and `JitEmitNestTest.NestIdx` is the accepted code-indexed form.
  The rules take all six relations, not three, for a second reason: family premises nest operand
  lists (`CompOps`) and windows (`CompW`, `CompTA`). **This deviation from the spec's index shape
  needs a review decision; it is not signed off.**
  Each of the seven families has an empty rule for Comp, CompT and CompOp (21 hooks), over relation
  variables for all six relations. lower.shen needs the CompT and CompOp hooks: its `test` lowers
  `(do X Y)` as value then test, and its `operand` lowers a folded list as `(const K)`.
- **Induction.** `Comp_ind'` is written by hand, one Fixpoint per relation, and recurses through each
  rule's `*_all` lemma. It is closed. A family's `*_all` must stay transparent: the
  `ShenJitEmitRuleOpaque` mutant, an opaque `*_all`, is refused by the guard checker.
  `rocq/JitEmitNestTest.v` checks the design on a non-empty rule that nests three derivations at the
  same code and one at another code. Its `Comp_ind'` proves `suffix`.
- **Frames.** `rocq/JitEmitKont.v` defines every frame once, generic in the value relation, the
  closure heap fact, and `DoK` (the store's `do` is the kernel's, asked only by the `do` frames):
  - the handler (`KD'_trap`, which consumes the handler its trap pushed; `trap_has_handler`);
  - the dynamic-call window (`KD'_head_*`, `KD'_args_*`, `KD'_hbind`), at most one argument;
  - `do` (`KD'_do1`, `KD'_do1t` and the transparent `*_do2`);
  - closure-entry return (`RK'_call`, with the caller's captures);
  - a primitive's pending argument, for the primitives `frame_prim` admits.

  `KApply` is related nowhere (see the file).
- **Counterexamples (fix round 1).** An adversarial review found that the first version of
  `sim'_statement`, and of `preservation'_statement` at n >= 1, was false with every rule empty: a
  frame admitted `get-time`, whose request `ev_of` did not translate, and `O'_io` quantified over
  every response. Checking the other frames found more of the same kind. Each is argued by hand
  from `KLSemantics.prim_rule`/`apply_value` and `JitBytecode.prim_step`/`enter`; none is
  mechanized at emit-spec; r1-emit-spec-merge checks each in Rocq as a primitive-level divergence
  (`dv_*` in `rocq/JitEmitInv.v`, below), `=` on a cycle included (`dv_eq_cycle`):
  - `absvector` of 2^48 allocates in the source, while the bytecode raises.
  - `error-to-string` of a primitive's exception is `"error"` in the source but the message in
    the bytecode.
  - `open` prefixes `*home-directory*` in the bytecode only.
  - `close`, `read-byte` and `write-byte` on a closed stream, or one with the wrong direction,
    send a request in the source and none in the bytecode.
  - `=` without `pguard`: two NaNs, or a cycle, leave the bytecode stuck.
  - A dynamic call of two arguments over-applies in the source (a `KApply` frame), while the
    bytecode raises an arity error.
  - An IO failure with no handler: JitBytecode's continuation resumes the machine where it was,
    while the source ends in an error.

  The fix narrows what the frames and statements cover. It weakens no proved theorem:
  - `frame_prim` keeps `pguard` on `=` and admits no frame for the six primitives above.
  - The window takes at most one argument.
  - `ev_of` translates the clock (`JTimeIs b` with b < 2^64, which `jit_time` reads back as the
    same bits).
  - The run statements quantify over environments `env_ok` admits: responses of the request's kind,
    and no failure. `env_ok_inhabited` shows the premise is satisfiable.

  A family that needs an excluded frame goes back through emit-spec. These residuals are open in
  `OB-JIT-LOWER-FRAGMENT`. Whether the new statements are true is UNKNOWN until emit-sim proves
  them.
- **Invariant and statements.** `rocq/JitEmitInv.v` defines:
  - `mu`, a partial bijection between KLambda locations and bytecode keys;
  - `VRh` (`VR_VRh`; it relates no partial application, `VRh_no_partial`);
  - `SM`: the globals (`GvalsRel`), the cells `mu` tracks, `FunRel'`, and the handlers against
    the KTrap frames (`HK`, with labels and quiet flags);
  - an evolving store, and target runs under every environment `env_ok` admits, with traces
    compared as equal lists through `ev_of`;
  - `Out'`, with IO and generic raising cases.

  `sim_X_statement` per family takes the nested IH as `Rule_X_All Comp SimC ...`. The file also states
  `preservation'`, `call_preservation'` and `call_preservation_src'`, each a `Definition ... : Prop` with a
  "Does NOT say" note. None of these is proved. `FunRel'` does not mention `VRh`: a source function
  is not a value, and its code is related at no captures.
- **Old fragment.** The old invariant embeds at any `mu` that relates the store's cells and
  globals (`StoreRel`). `kont_embed`, `sm_embed` and `ms_embed` are proved. The kernel's `do` is no
  longer a premise, because only the `do` frames ask it.
  - Fix round 2: each `*_old_statement` now has the **old** conclusion verbatim (`Sstar`, `TN`,
    `MS s` with the store constant, `JitLowerThm.Ends` / `JitKRef.EndsSrc`), at `mu = []` with no
    handler, and the old premises plus `GvalsRel [] s m`. `*_old_of_new` proves each (closed) from
    its new statement **and a reflection obligation** (`old_reflect_statement`,
    `old_reflect_src_statement`), through `ms_embed`/`sm_embed` at `mu = []` and proved bridges
    (`srun_nil_sstar`, `trun_nil_tn`, `tn_tstar`, `ms_entered`, `entered_embed`). The proofs do
    not use the old theorems.
  - The reflection `old_reflect_statement` is **false** (r1-emit-spec-merge, `old_reflect_false`,
    below), so the three `*_old_of_new` corollaries are vacuous. It was needed: the new conclusions
    pick some JitEmitRel derivation, some `mu'` and some trace, and nothing keeps an old-fragment
    run inside the old fragment, so the old conclusion does not follow from the new statements
    alone. Reflecting JitEmitRel derivations would invert the rules outside their files. A family
    whose rule overlaps the old fragment (Eq's `=` beside `C_prim` with `pguard`) puts the
    reflection at risk; whether such a family must re-prove it, beside its map and all lemmas, is
    a review decision.
  - `GvalsRel [] s m` is added because MS and Com leave the machine's globals unconstrained, and
    the new invariant needs them related. The corollaries' proofs use it to build
    `StoreRel [] s m` for `ms_embed`/`sm_embed` (`ShenJitEmitOldGvalsDropped`, the premise
    replaced by `True`, is refused there).
  - The old theorems are unchanged and stay proved on their own.
- **Pending review (not signed off).** The index shape above; the frame exclusions and the
  `env_ok` / one-argument-window narrowing (spec item 4 asks for all frames, so the affected
  families, Store, Prim, Eq, App and IO, go back through emit-spec until the open source-model or
  bytecode decisions are made: absvector bound, error-to-string text, stream state, the
  home-directory prefix on open, the raise continuation of an IO failure with no handler); the
  reflection obligation above. The counterexamples behind the narrowing are hand-argued, and the
  agreement of the newly admitted primitives (str, intern, pos, tlstr, cn, n->string, string->n,
  set, value, simple-error, <-address, address->, absvector?, /) is hand-checked: both UNKNOWN.
- **Evidence.** 92 statements were added to `Audit_Jit` (201 in all), each closed. There are 31
  emit-spec mutants, at least one per new relation or definition:
  - `MS'`, `Out'`, `EndsSrc'`, `TRun` and the six `Sim*`;
  - `HK`, `GvalsRel`, `DoOK`, `FunRel'` and `StoreRel`;
  - `resp_ok`, `ev_of` and `frame_prim`;
  - the reflection obligations, the old-fragment premise, the `TRun` bridge, and the refused
    uniform-code nesting.

  Each mutant is refused under Rocq 9.3 inside the lemma it names. The mutation pin is 215 (fix 1 recorded 209 for 26 added mutants; the history gives 184 + 31). Lane
  result: in the task report.

### Emit-spec premises settled in Rocq (r1-emit-spec-merge)

Branch `p2/r1-emit-spec-merge`: `p2/emit-spec` merged onto `p2/int` (`2ab3ffc`), plus the following
in `rocq/JitEmitInv.v`. Nothing here proves a back-end statement; `sim'_statement`,
`preservation'`, `call_preservation'` and `call_preservation_src'` stay unproved, truth UNKNOWN.

- **The reflection is refuted** (`old_reflect_false`, closed). The store defines the kernel's
  `do` and every primitive. In `(let Z (do 1 2) Z)` the machine is at `call 0 1 do 2`, with 1 and
  2 in the window. MS relates the source, at `Ret 2` with do's call pending (`cx_ms0`, through
  `KD_call`). After two silent steps (the call, and do's `return`) MS' relates the **same**
  configuration to the machine (`cx_ms'1`): `KD'_do2` makes the pending call of `do`
  transparent. MS does not (`cx_not_ms1`). So `old_reflect_statement`'s first conjunct fails at
  `c' = c`, `mu' = []`. It is JitEmitKont's do frames, not a family rule, that overlap the old
  syntax. The `*_old_of_new` corollaries take the reflection as a hypothesis, so they recover
  nothing; how the old conclusions are to be recovered is a review decision (for example a
  reflection to *some* MS-related configuration at a later machine, which the old preservation
  theorem gives, so it would not be independent evidence). `old_reflect_src_statement`: proved in
  fix round 4 (`old_reflect_src`, below).
- **get-time is modeled as IO on both sides** (`get_time_agree`, closed): on related arguments,
  both ask the clock with requests `ev_of` translates to each other, and for every answer
  `resp_ok` admits the source's result is `VRh`-related to what the bytecode writes; or both
  raise. An out-of-memory raise before the request is the source's resource exit, as for other
  allocating primitives.
- **The narrowing, checked in Rocq** (closed Examples; divergences at the primitive or call
  level, not refutations of `sim'_statement`): `dv_absvector_src/_byt` (2^48), `dv_ets_*`
  (error-to-string), `dv_open` (*home-directory*), `dv_close`, `dv_read_closed`, `dv_write_closed`
  (closed stream),
  `dv_eq_nan` (two NaNs: the bytecode is stuck), `dv_window` (two arguments to a one-parameter
  closure, related to the bytecode's by `dv_window_rel`: the source over-applies, the bytecode raises), `dv_io_fail` (an IO failure: the
  bytecode resumes with no result, the source throws; `resp_ok` excludes the answer).
  `gvals_needed`: MS holds and MS' at no `mu` when the store binds a global the machine does
  not, so `GvalsRel [] s m` is not implied by the old premises. `=` on two distinct cyclic vectors,
  related through `mu` (`dv_eq_cycle_rel`): the source goes wrong (`OWrong`, its depth bound
  exhausted) and the bytecode is stuck (`RCyclic`) (`dv_eq_cycle`). Neither side answers, so this
  is not a disagreement on an answer; it is a state `Out'` has no case for. On one cyclic vector
  both answer true (`dv_eq_cycle_same`). `env_ok_inhabited` shows only that an `env_ok`
  environment exists; it does not derive `env_ok` from the pinned environment or the premises.
  Each `dv_*` Example shows a divergence at the primitive or call level. None shows that a premise
  is necessary for `sim'_statement` or the run statements; whether that is enough evidence is
  Reuben's call.
- **Reflection with source catch-up (fix round 2 of r1-emit-spec-merge; a proposal, not a
  resolution).** `old_reflect'_statement` is `old_reflect_statement` with its first conjunct
  weakened on the conclusion side only: from the configuration `c'` that MS' relates, *some* `c''`
  the source reaches silently (`Sstar c' c''`) is MS-related to the same machine. The old
  conclusions ask only for some silently reached source configuration, so `*_old_of_new'` (closed)
  derive `preservation_old_statement`, `call_preservation_old_statement` and
  `call_preservation_src_old_statement`, each with the **old** conclusion verbatim, from the new
  statements plus `old_reflect'_statement` (and `old_reflect_src_statement` for the src one). The
  proofs use neither JitLowerThm's nor JitKRefCompose's theorems. `cx_catch_up` (closed) checks
  that `old_reflect_false`'s counterexample is not one to the new statement: two silent source
  steps (the call of `do`, then its body `Y`) reach the `let` frame, which MS relates to the
  machine after do's return (`cx_src_catch_up`, `cx_ms2`). `old_reflect_statement` and
  `old_reflect_false` are kept unchanged. **Not proved:** `old_reflect'_statement` (truth UNKNOWN; a
  proof needs a reflection of every KD'/TK'/KC'/RK' derivation over old-fragment syntax to KD/TK/KC/RK
  after catch-up, and source-side invariants that keep an old-fragment run IO-free and its store
  constant). The corollaries are therefore implications between unproved statements: they show the
  new statements, if proved, give the old conclusions, and they recover nothing yet.
- **`old_reflect_src_statement`: UNKNOWN, not refuted** (superseded: proved in fix round 4,
  `old_reflect_src`). Two cheap refutations were tried and do not
  work. The old `pmap` admits no IO primitive, so an old-fragment machine cannot make a request. And
  `EndsSrc'`'s existential final store `s'` is tied to b0's final store by `GStore` (functions
  equal, globals and w's cells positionally `GVal`-related), and no choice apart from `s` was found
  that keeps KRef's own end relation (a hand argument, not checked in Rocq). A proof needs the same machine-side invariants as the
  catch-up reflection (the machine's globals and the cells outside `mu'` unchanged), plus `VRh`
  injectivity on the first-order values VR relates. Not attempted in this round.
- **Awaiting Reuben** (none approved; no agent can approve them): `env_ok` on the run statements
  (evidence: `dv_io_fail`), the `frame_prim` exclusions (`dv_absvector_*`, `dv_ets_*`, `dv_open`,
  `dv_close`, `dv_read_closed`, `dv_write_closed`, `dv_eq_nan`, `dv_eq_cycle`), the one-argument
  window (`dv_window`, `dv_window_rel`), `GvalsRel` on the `*_old` statements (`gvals_needed`), the
  catch-up form of the reflection (`old_reflect'_statement`, `cx_catch_up`), and the six-parameter
  Rule_X index shape with `c`/`cv` indices. Every `dv_*` Example is primitive-level or call-level
  evidence, not a proof that the premise is necessary for the stated theorems.
- **Evidence.** 34 closed statements added to `Audit_Jit` (352 in all after the merge with kref-ctl). Mutants
  `ShenJitEmitGetTimeSwap` (run and unix swapped in `ev_of`; `get_time_agree` must fail) and
  `ShenJitEmitDo2Opaque` (`KD'_do2` needs `False`; `old_reflect_false` must fail); the pin was 227 (224 before kref-ctl's three).
  Fix round 2 adds 9 closed statements (377 in all, after the merge with r1-fv-mutants' 16) and two
  mutants: `ShenJitEmitCatchUpNone` (`cx_c2` is `cx_c`, no source step; `cx_ms2` must fail) and
  `ShenJitEmitEqCycleAcyclic` (the second cell no longer closes the cycle; `dv_eq_cycle` must fail).
  The pin is 233. Its history: 215 on `p2/emit-spec` was 184 (its base `b818355`) plus its 31 emit
  mutants; `p2/int` reached 198 independently (kref-prim, kref-ctl, r1-fv-mutants), so the merged
  count is 198 + 33 (emit-spec's 31 and this branch's two of the first round) + 2 = 233. The pin is
  `report.py`'s count of `Rejected proof mutation:` lines in `make check`; `make report` was not run
  on this branch, so 233 is checked against the mutant names, not through `report.py` (UNKNOWN).
  The lane and the emit mutants were run on this branch (task report); `make prove`, `make
  report`, the differential and the Coq 8.18 build were not, so their results are UNKNOWN.
- **Fix round 3: the reflections narrowed (closed).** `B.next` is a function, so under one
  environment the machine has one run. With the proved old theorems (`JitLowerThm.preservation`,
  `call_preservation`) this gives, in `rocq/JitEmitInv.v`:
  - `old_reflect'_silent`: from a state MS relates, every bytecode run under any environment is
    IO-free (`tT = []`), so the trace parts of `old_reflect'_statement` and
    `old_reflect_src_statement` hold;
  - `old_reflect'_ends`: the second conjunct of `old_reflect'_statement` (an `Ends'` at `mu = []`
    read back as `JitLowerThm.Ends` with the same store), proved outright;
  - `old_reflect'_iff_core`: `old_reflect'_statement` is **equivalent** to
    `old_reflect_core_statement`, the catch-up of MS' to MS along an IO-free run (no trace, no
    environment). The core is the one part of `old_reflect'` not proved; truth UNKNOWN. With the
    seven family hooks empty, it is a property of MS' and JitEmitKont's extra frames (do,
    handlers, closures, the primitives `frame_prim` admits). A family whose rule overlaps the old
    fragment must re-prove it;
  - `old_reflect_src_of_fundamental`: `old_reflect_src_statement` follows from
    `fundamental_statement`. This is a **reduction, not a proof**: its end case comes entirely
    from `JitKRefCompose.call_preservation_src_of_fundamental`, so the src corollary adds nothing
    beyond that theorem. (Fix round 4: DoD item (1) now proves the fundamental property,
    `JitKRefFund.fundamental`, so `old_reflect_src` proves `old_reflect_src_statement`.) (The round-2 note that a proof needs machine-side
    invariants is superseded: with the fundamental property, determinism suffices);
  - `preservation_old_holds`, `call_preservation_old_holds` and
    `call_preservation_src_old_of_fundamental`: the `*_old_statement` targets follow from the old
    theorems directly (the src one from the fundamental property). This is a sanity check that the
    targets of the `*_old_of_new'` corollaries are true. It says nothing about the new statements.
  - Helpers, all closed: `tn_trun`, `sstar_srun`, `trun_tn_prefix`, `tn_next_tau`,
    `tstar_final_trun`, `tstar_final_eq`.

  15 closed statements added (399 in `Audit_Jit` after the merge with `p2/int` `17379dc`, whose
  r1-compat-call adds 7). One mutant: `ShenJitEmitCoreNoCatchUp` (the core asks for MS at `c'`
  itself, which is `old_reflect_statement`'s refuted first conjunct; `old_reflect'_of_core` must
  fail). The pin is 235 = `p2/int`'s 199 + the 36 `ShenJitEmit*` mutants of this branch (84 JIT
  mutant names against 48 on `p2/int`). `make report` was not run, so the pin is checked against
  the mutant names, not through `report.py` (UNKNOWN).

  Still **awaiting Reuben** (no agent can approve them), each with its Rocq evidence:

  | Premise or design choice | Rocq evidence | What the evidence shows |
  |---|---|---|
  | `env_ok` on the run statements | `env_ok_needed`, `resp_ok_bound_needed`, `dv_io_fail`, `env_ok_inhabited` | statement level (fix round 4): `preservation'_statement` without `env_ok` is false, at an environment answering `JFailed` and at one answering a 2^64 clock reading; an `env_ok` environment exists. `env_ok` is an assumption on the environment, NOT derived from the pin; necessity is proved for `preservation'` only, the call statements are analogous but not proved |
  | `frame_prim` excludes absvector | `dv_absvector_src`, `dv_absvector_byt` | at 2^48 the source allocates a vector, the bytecode raises (primitive level) |
  | `frame_prim` excludes error-to-string | `dv_ets_*` | the source answers "error", the bytecode the exception's text (primitive level) |
  | `frame_prim` excludes open, close, read-byte, write-byte | `dv_open`, `dv_close`, `dv_read_closed`, `dv_write_closed` | home-directory prefix and closed-stream state differ (primitive level) |
  | `=` only with `pguard` | `dv_eq_nan`, `dv_eq_cycle`, `dv_eq_cycle_rel`, `dv_eq_cycle_same` | two NaNs: the bytecode is stuck; two cyclic vectors: source goes wrong, bytecode stuck (primitive level) |
  | dynamic-call window of at most one argument | `dv_window`, `dv_window_rel` | two arguments to a one-parameter closure: the source over-applies, the bytecode raises (call level) |
  | `GvalsRel [] s m` on the `*_old` statements | `gvals_needed` | MS holds and MS' holds at no `mu` (statement level for the embedding) |
  | the catch-up form of the reflection | `old_reflect_false`, `cx_catch_up`, `old_reflect'_iff_core` | the same-configuration reflection is false; catch-up handles its counterexample; what remains is exactly `old_reflect_core_statement` |
  | six-parameter `Rule_X` hooks with `c`/`cv` indices | `JitEmitNestTest` (nested `Comp_ind'` with a non-empty dummy rule) | the shape compiles and its induction principle works; the uniform-index alternative failed strict positivity (scratchpad evidence only, not committed) |

  None of the `dv_*` Examples shows that a premise is necessary for `sim'_statement` or the run
  statements; each shows a divergence at the primitive or call level. Fix round 4 adds the one
  statement-level necessity proof, for `env_ok` (below).

- **Fix round 4 (merged onto `p2/int` `5779555`, r1-kref-fund).** In `rocq/JitEmitInv.v`, all closed:
  - `old_reflect_src`: `old_reflect_src_statement` is **proved**, as
    `old_reflect_src_of_fundamental` applied to `JitKRefFund.fundamental`. With
    `old_reflect_false` (the refutation of `old_reflect_statement`), both reflection obligations of
    the spec are settled in Rocq: one refuted, one proved.
  - `call_preservation_src_old_holds`: the target `call_preservation_src_old_statement` holds.
  - `call_preservation_src_old_of_new''`: `call_preservation_src_old_of_new'` with its
    `old_reflect_src_statement` hypothesis discharged. The three `*_old_of_new'` corollaries now
    wait only on the new statements and `old_reflect'_statement`, which is exactly
    `old_reflect_core_statement` (`old_reflect'_iff_core`): NOT proved, truth UNKNOWN.
  - `env_ok_needed`: `preservation_noenv_statement` (`preservation'_statement` with `env_ok rs`
    dropped, nothing else changed; `preservation'_of_noenv`) is **false**. MS' relates the source at
    `get-time`'s pending frame, `run` evaluated (`KD'_prim`, then `KD'_ret`), to the machine at its
    `(get-time run)` instruction (`gt_ms`). Its first step asks the clock (`gt_next`). Under an
    environment that answers `JFailed`, every run of one step or more starts with an untranslated
    event (`gt_trun_none`), and the machine is not final at step 0, so neither disjunct holds at
    `n = 1` (`noenv_false_at`). `resp_ok_bound_needed`: the same at an environment answering a
    clock reading of 2^64, outside `resp_ok`'s 64 bits; neither environment is `env_ok`. So
    `env_ok` cannot be dropped from `preservation'_statement`. The refutation uses that `ev_of`
    leaves `JFailed` and readings of 2^64 or more untranslated. Translating a failure would not
    save the statement: the bytecode then resumes with no result while the source throws
    (`dv_io_fail`). It is an assumption about the
    environment, not derivable from the pin or the premises. `call_preservation'` and
    `call_preservation_src'` are analogous; their necessity is NOT proved here.
  - Mutant `ShenJitEmitIoFailTranslated`: `ev_of` translates `(JTime, JFailed)`, so the `JFailed`
    environment no longer refutes the statement and `env_ok_needed` must fail.

  11 closed statements added (424 in `Audit_Jit`: 399 + 14 from r1-kref-fund + 11; the lane on
  `95459c7` printed 424 closed, with 0 Axioms lines). The pin is 238 = 235 + r1-kref-fund's 2 + 1.
  That is a **census**, not `report.py` evidence. There are 87 ShenJit mutant names; `p2/int`
  `5779555` has 50, so 151 of its 201 are non-JIT. In addition, the 40 ShenJitEmit* and kref-fund
  mutants were all rejected under Rocq 9.3 on `95459c7`. `make prove` and `make report` were not
  run, so their result is UNKNOWN: buri-lps has only the Rocq 9.3 switch, and `scripts/prove`
  needs Coq 8.18.0 and `scripts/shen`. Still NOT proved, truth UNKNOWN: `sim'_statement`, every
  `sim_X_statement`, `preservation'`, `call_preservation'`, `call_preservation_src'` and
  `old_reflect_core_statement`. Still at primitive or call level only: the `frame_prim`
  exclusions and the one-argument window. A statement-level counterexample for those needs a KD'
  frame that MS' does not have, so it means changing JitEmitKont. Every row of the table above
  still awaits Reuben.

  r21-emit-spec-land (branch `p2/r21-emit-spec-land`; its merge into `p2/int` is the integrator's and is not
  recorded here): `52f913c` is a `--no-ff` merge of `7bb9bb7` onto `p2/int` `f42d6c4` with the JitEmit files
  byte-identical, and a later commit on the branch merges `p2/int` `da4b545` (r21-image-lane) into it, so that the
  integrator's merge adds no new conflict. On the branch: audit 704 (527 + 161 + 16 proved emit lemmas newly
  printed), pin 267 by arithmetic (230 + 37), and two non-inversion gates in `scripts/check-shen-jit.sh`, a
  syntactic one (exit 14) and a term-level one over the printed constants (exit 15). While every Rule_X hook
  is empty (`Inductive Rule_Eq ... := .` and so on), the syntactic gate's constructor-match check finds
  "0 hook constructors" and so checks nothing; the term-level gate is the operative non-inversion check at
  this stage. The constructor check becomes live when a family adds constructors to its hook. The planted
  destruct and inversion of `Rule_Eq` do fire on the empty hook. The spec asked for a rebase. The branch
  merges instead, because `p2/r1-emit-spec-merge` itself contains five merges of `p2/int`, and the docs and
  ledger cite `52f913c`, `fc0a9fd` and `b02db36` as evidence anchors, which a squash would orphan. The head is
  a fast-forward from `p2/int` `da4b545`. The evidence is in [STATUS](STATUS.md).

### Extended back end: the generic parts (r22-emit-sim)

`rocq/JitEmitSim.v` (branch `p2/r22-emit-sim` off `p2/int` `fe461f4`; its merge is the integrator's). Every
theorem there is an implication between statements, closed under the global context. Nothing in
`rocq/JitEmitInv.v` changed.

**`preservation'_statement`, `call_preservation'_statement` and `call_preservation_src'_statement` are FALSE as
stated** (closed in Rocq at `cx_E`, `cx_pt`, sealed `[]`: `preservation'_false`, `call_preservation'_false`,
`call_preservation_src'_false`; and `raise_resolve_false` for this task's own premise). SMs says nothing about the
machine's allocation pointer `m_next`, and `JitBytecode.alloc` writes at `m_next` without looking. The witness
`fx_m` is SM-related to JitEmitInv's `cx_s` with `m_next` = 1, the key of do's closure. It is entered on the
accepted function `(defun f (X) (hd X))` (CompFn' through C_ret, O_val, C_prim, O_var; no hook) with 1. Its
first step raises with no handler, allocating the exception over do's closure, and finishes (`fx_next`). Every
end that Ends' or EndsSrc' admits asks SMs of that final machine. FunRel' fails there for every store
(`fx_no_funrel`), and the machine has no further step, so at n = 1 neither disjunct holds. The fix belongs to
emit-spec: SMs must keep `m_next` fresh (every key at or above it unused). This does NOT refute
`sim'_statement`: O'_raise asks SM of the machine before the allocation. Mutant `ShenJitEmitSimFreshNext`
gives the witness a fresh pointer, and `fx_next` must then fail. The implications below stay as proved. Their
conclusions are false at `cx_E`, so `raise_resolve_statement` is false there too; each conclusion becomes a
target only once SMs is repaired.

| Theorem | From | To |
|---|---|---|
| `call_preservation'_of_preservation'` | `preservation'_statement` | `call_preservation'_statement` (the entry state is MS'-related: `entered_ms'`) |
| `preservation'_of_sim'` | `sim'_statement`, `raise_resolve_statement` | `preservation'_statement` (induction on n, inside it on the source measure; IO events through `env_ok` shifted along the environment) |
| `call_preservation'_of_sim'` | the same two | `call_preservation'_statement` |
| `call_preservation_src'_of_cp'` | `call_preservation'_statement`, `clo_scoped_statement` | `call_preservation_src'_statement` |
| `call_preservation_src_old_of_cp'` | `call_preservation'_statement`, `clo_scoped_statement`, `old_reflect'_statement` | `call_preservation_src_old_statement` (JitKRef's `call_preservation_src_statement` at mu = [] with `GvalsRel [] s m` added; not the 4a7346e text verbatim) |

The composition (`call_preservation_src'_of_cp'`) runs the emitted body's run, which
`call_preservation'` relates to the machine, back through b1 and b0 with `adequacy_tr` (KRef adequacy for
any IO trace, from environments whose values are VRel-reflexive; `JitKRefGround.adequacy_of_fundamental`
asks first-order values and silent runs), and composes with `GVal_trans` and `GStore_trans`. The arguments
are VRel-reflexive by `vrh_refl`: a vector through mu is in the identity world because `HeapRel` puts its
cell in the store; a closure needs `clo_scoped_statement`, because `VRh_lam` constrains only the captured
entries of its environment (the rest need not be `vok`, so `vrefl` does not apply) and `KRef_refl` needs the
body scoped.

Two new premises, each NOT proved:
- `clo_scoped_statement`: a body `CloOK` accepts is scoped in its parameters and capture names. With the
  hooks opaque, Comp gives this only through each family's own rule (the Clo hook's capture reads), so it
  is a per-family lemma through `Comp_ind'`.
- `raise_resolve_statement`: what `O'_raise` leaves open, resolved to a machine step with a related state,
  or to a final error on both sides. The no-handler half needs `SMs` stable under the exception's
  allocation; the handler half meets the slot-1 gap below at `KD'_trap`.

NOT proved: `sim'_statement` from the seven `sim_X_statement` (so the acceptance's
`call_preservation_src'_of_sims` is not reached). Two gaps in the generic Ret cases, both in
`rocq/JitEmitKont.v`, which is emit-spec's:
- **Slot 1.** EvalCtx asks `cv = [] \/ ~ w (fp + 1)` of the w its continuation is at. No frame whose body
  runs at an inner `w1` (`KD'_let`, `KD'_lett`, `KD'_trap`, `KD'_do1`, `KD'_do1t`, `KD'_hbind`, `TK'_if`,
  `TK'_cond`, `TK'_and`, `TK'_or`) carries that for `w1`; a body whose destination is slot 1 even needs
  `w1 (fp + 1)` (`KC'_slot`). `ms'_slot1_frame` (closed) is an MS'_ret state at `cv = [Z]` whose let frame's
  body goes to slot 1, and `evalctx_slot1_void` (closed) shows that no EvalCtx at a `cv <> []` has a slot-1
  destination. A generic proof would have to re-relate that state at another cv, which needs Comp at that
  cv, which the hooks need not give. The frames would need `cv = [] \/ ~ w1 (fp + 1)`, or a destination
  other than slot 1 with `2 <= top`. This does NOT show `sim'_statement` false: with the hooks empty no code
  reads a capture, and a concrete state can be re-related at `cv = []`. Truth UNKNOWN.
- **`KD'_hbind`.** The machine is at Comp of `chain (EVar x) ass`, an `EApp` only the App hook derives,
  while the source is already at Ret with `KHead` frames over rho (not `(x, v) :: rho`).
  `sim_App_statement` speaks of Eval states only.

Also NOT done: the instantiation at proved `sim_X` (emit-assembly; the hooks are empty and may not be
inverted outside their files); `old_reflect_core_statement` (UNKNOWN, not attempted); `env_ok` necessity for
`call_preservation'` and `call_preservation_src'`, which is not demonstrable while the hooks are empty:
`C_prim` goes through `pmap`, which has no IO primitive, so nothing a call enters asks for IO (the analogue
of `env_ok_needed` needs a family rule reaching get-time).

Fifteen closed statements added (`Audit_Jit` 723). Six mutants (`ShenJitEmitSimFreshNext` above, and five each dropping or weakening one new premise
or theorem hypothesis: `ShenJitEmitSimCloScoped`, `ShenJitEmitSimVrhDom`, `ShenJitEmitSimAdequacyRefl`,
`ShenJitEmitSimRaiseStar`, `ShenJitEmitSimSlot1Any`). The `scripts/report.py` pin is 274 (268 + 6), computed;
`make report` was not run. The evidence is in [STATUS](STATUS.md).

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

**At 0.6, after `=` against a symbol constant was admitted: 174 of 955 definitions accepted** on the erased witness, 781 rejected, none failing erase, none unreadable, all front end unchecked; the source-body judge accepts 148, none lost on the witness (`NORM_DIR=/tmp/p2-T02-capture/witness JIT_OUT=/tmp/p2-eq-guard-merge-norm scripts/check-shen-jit-norm.sh` in `buri-lps`, branch `p2/eq-guard-merge`, exit 0, log sha256 `94659a70a4376134860069f7be23f9a151a27cf24f6d2f7d035f3c0612287aab`; witness set the same `e45add98...b69dd1`). Before that change:

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

**Stage 0 residuals and the four decision items** (10 November 2026, `r1-residual-ledger`; regenerated the same day
after `=` against a symbol constant was admitted, `eq-guard-merge`).
`tests/shen-jit/stage0-residuals.txt` lists every stage 0 definition the Rocq source judge does not accept: 807, as
the source judge accepts 148 of 955 (the count `stage0-accepted.txt` pins; no full-pipeline judge exists yet, so the
full-pipeline validated count is UNKNOWN). `tests/shen-jit/stage0_residuals.py` writes it from `judge_split.sh`'s
Rocq verdict files, run on branch `p2/eq-guard-merge` (on `p2/int` 335348c) on the pinned stage 0 set (`ec9b3872...`)
and norm witness (`e45add98...b69dd1`); src, nf and tf come to 148, 150 and 174 (111, 112 and 133 at `p2/int`
2e45d67, as in `spikes/pass-split/CENSUS.md`, before the change). The file records those hashes, the verdict-file
hashes and the scripts' hashes; its own sha256 is
`9044ef21fa22c35c7726d69495d400fbf9819839d92823a67c15b63dd993179e`. Compared by name with the 844 rows at 2e45d67, 37
rows are gone (the 37 newly accepted definitions) and none is new. Evidence kinds stay apart in it: the src, nf and tf
columns are Rocq verdicts; the first blocker is a census label from a syntactic walk of the norm witness (Comp gaps,
`=` outside `pguard`, calls of `shen-jit.eval-kl`), checked only in that no definition Rocq accepts on nf gets an emit
label; the ledger, reason and decision columns are bookkeeping. By first label: `OB-JIT-LOWER-FRAGMENT` 368,
`OB-JIT-LOWER-OPTIMIZATIONS` 343, `OB-JIT-NAN-IDENTITY` 59, `OB-JIT-PORT-PRIMS` 26, `OB-JIT-LOWER-GENERAL` 6,
`OB-JIT-IDENTITY-MODEL` 5 (at 2e45d67: 463, 306, 43, 24, 3 and 5; the definitions first blocked by `=` against a
symbol now show their next label).

The four decision items are Reuben's decision. Each has an open ledger entry and, until he decides, defaults to a named
residual. The counts are definitions any of whose labels touch the item (census):

| item | ledger entry | definitions | options |
|---|---|---|---|
| port primitives | `OB-JIT-PORT-PRIMS` | 178 | wire `jit_port_prims_proposed` (adds a hash parameter to the rules), or named exceptions; the operators with no carrier (byte buffers, Prolog variables and the rest of `jit_port_prims_residual`) stay residual either way. `jit_port_prims_proposed` is not wired. |
| eval-kl | `OB-JIT-LOWER-GENERAL` | 16 | prove it, or exclude it as a named exception |
| identity primitives | `OB-JIT-IDENTITY-MODEL` | 48 | model identity, or named exceptions (`same?`, `tagged?`, `deref`, `deref=`) |
| `=` on two possibly-NaN operands | `OB-JIT-NAN-IDENTITY` | 206 | a proved static non-real judgment in Rocq, a NaN identity rule, or a named limit |

For NaN `=`, a Rocq non-real judgment means extending `JitLowerRel.pguard` and redoing the `Comp` simulation, so it is
not cheap and was not attempted here; `feature_census.py`'s `NONREAL` set is a census and decides nothing. `=` against
a symbol constant is no longer a residual label: a symbol is never a NaN, and `pguard` now admits symbol constants
(`OB-JIT-SYM-INJECTIVE`). Of the 152 definitions first blocked by it at 2e45d67, 37 are now accepted by the source
judge and 115 are filed under their next census label.
