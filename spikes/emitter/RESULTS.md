# Spike 7: what the emitter costs, by two routes, on one opcode

Result: **route B, checking the emitter's output, finished for the `move` opcode, and route A, proving
the emitter, stopped after two small rungs.** On per-opcode cost, B looks about 2 to 20 times cheaper. That
doesn't settle the question: B leaves two obligations nobody has measured, whole-function layout and
showing that the unproved emitter can't damage anything else. Shen/JIT is not verified by any of this.

Evidence kind: Rocq theorems about the exact bytes of the check build in Theorem's RISC-V model, replayed
with `rocqchk`, and suite runs under `qemu-riscv64`. Nothing has run on RISC-V hardware.

## The opcode

`(move D S)`, chosen because it has real operand variety at moderate size: a source in CACHE, a home
register or the frame, a destination in a home register or the frame, compressed and full encodings,
and a store and a CACHE write that depend on the emitter's analysis.

| Measure | Value |
|---|---|
| Opcodes in `ops.h` | 21, plus 52 `case P_` lines in `jit.c` for primitives |
| Moves seen in contract, kernel and extension suites | 13,179 |
| Forms seen | 17 by operand class and length; no constant source appeared |
| Emit-specific code for `move` | About 320 instructions: `store_result` 233, `operand_kind` and `operand_offset` 87, plus its case in `compile_code` |
| Emit-specific code overall | About 13,500: `emit_prim` 5,098, `compile_code` 3,654, `emit_slow_paths` 2,309, `emit_fused` 1,129, `emit_eq` 496, `emit_exit_test` 482, `emit_type_test` 373 |

So `move` is one of the simpler opcodes, about 1/42 of the emit-specific code by size. It has no branch,
label, slow path, allocation or call, which are the hard parts of the others.

## Route B: check the output

`overlay/check_move.c` holds `spike_check_move`, a leaf of 150 RV64 instructions with no stores or calls.
`apply_hook.py` marks each move's bytes with SLJIT labels. After `sljit_generate_code`, and before the code
can run, a gate calls the checker. Reject stops the process.

**Proved:** `check_move_contract` in `coq/MoveContract.v`, on the checker's bytes in the check build. For all
values of the operands and any memory, in the model's real `step`, the function returns to `ra`, with memory
unchanged and every register outside t0-t2 and a0-a7 unchanged, and a0 = 0, 2, or 1. If a0 = 1:

```coq
in_domain h c d s k /\
exists store, (store = false -> k = 1) /\
  e = a + 2 * Z.of_nat (length (move_template h c d s k store)) /\
  emit_at mem a (move_template h c d s k store)
```

That is: [a, e) holds exactly the halves of the template, and a store can be missing only if the value
stays in CACHE.

`coq/MoveDecode.v` checks each encoding in the template against the model's own decoder across the whole
domain, so the template isn't just a copy of the checker's formulas. A compressed form is checked with the
following halfword all zeros and all ones, not for every following halfword.

**Premises of the contract:** overlay misses the text and rodata (`mem_clear`), `ra` even, `0 <= a <= e`,
`e + 32 < 2^64`, and every halfword in [a, e) readable.

### Running it

| Suite under `qemu-riscv64` | Result | Moves accepted | Rejected | Out of domain, unchecked |
|---|---|---|---|---|
| Contract and extension runs | 157/0 and 123/0 | 2,888 and 1,094 (which is which isn't recorded) | 0 | 0 |
| Kernel | 154/0 | 9,137 | 0 | 60 |

Both runs of each gave the same counts. The gate does fire: with the emitter changed to read the wrong slot
(`build.sh checkbad`), stage 1 aborted with `spike-check: move 11 2 ... rejected: 6 bytes`.

**Overhead:** nothing measurable. Five alternating kernel runs took 2,529-3,281 ms on the base build and
2,491-3,217 ms with the checker, on a loaded machine. Only one opcode is checked, so this can't be scaled.

**Labels change no code size:** across the 493 functions of a contract run, the generated sizes in base and
check builds are identical (`SHEN_JIT_PERF_MAP`). That compares sizes only. Bytes can't be compared directly,
since the binaries' helper addresses differ.

### What the checker needs from the emitter

| Input | Source | Trusted? |
|---|---|---|
| Start and end of each move's bytes | SLJIT labels, read after code generation | Not proved correct. The contract covers whatever range it's given, so a gap between ranges is unchecked |
| `dst`, `src` | Bytecode words | Bytecode correctness is Phase 2's job. The checker doesn't decode bytecode, and the hook passes the words |
| `cached` | The emitter's analysis state | **Untrusted hint.** Reading CACHE is right only if CACHE holds that slot, which needs a dataflow check over the function |
| `keep` and leaving out the store | The emitter's `read_soon`, `dead_store`, `consumed_next` | **Untrusted hint.** Leaving out a store is right only if the slot is dead, which needs a liveness check |
| `homes` | The emitter's `home_count` | **Untrusted hint.** Needs a function-level check |

Move needs no relocations, slow paths or label targets, so this spike says nothing about those.

### Gaps in route B

- **The emitter still runs unproved in the same address space.** A bug in `jit.c` or SLJIT could overwrite
  the heap, the checker's inputs, or code already checked. Checking output removes the functional obligation,
  not memory safety. This could cost as much as route B saves, and I didn't measure it.
- **Whole-function layout is unproved**; see below.
- **Hints above are unchecked**, so the template shows the right bytes *given* those facts.
- **Semantics:** the template is tied to decoded instructions, but I didn't prove a spike 4 style step
  theorem from `emit_at` to slot updates. Spike 4's proof used concrete bytes, so that remains to be done.
- **Domain:** offsets above 2047 and constant sources return 2 and pass unchecked, 60 of 13,179 moves in
  these suites. That is an allowlist; it isn't complete coverage. Every other opcode is unchecked too.
- **Availability:** a checker that rejects valid code stops the process. Rejections were 0 here.
- **Not proved:** the gate function `spike_check_move_gate`, the hook, and that it's reached for every move.
- **Cache coherence and overwriting code**, as in spike 1.

## Route A: prove the emitter

SLJIT works in two phases: `sljit_emit_*` records instructions into buffers, then `sljit_generate_code` copies
them to executable memory, resolving labels and jumps. The contract reached only pieces of phase one.

| Rung | Statement | Instructions covered | Hand lines |
|---|---|---|---|
| 1. `operand_kind` on slot operands | `operand_kind_slot`: returns the SLJIT kind per `kind_of`. The constant path through `ra_at` isn't covered | 17 of 38 | 173 |
| 2. `push_inst16` with room in the chunk | `push_inst16_fast`: the exact memory afterward, including the halfword at `b + 16 + u`, the used count and size, and restored registers. The `malloc` path isn't covered | 28 of 40 | 186 |
| **Total** | | **45** | **359**, plus 81 of adapted spike 5 memory lemmas |

That is 8.0 lines per instruction, on easy code. Both rungs pass `rocqchk` with only primitive assumptions.
Their premises include exact field offsets from the compiled code and, for rung 2, explicit disjointness of
stack, compiler and buffer.

**Stopped here. Not reached for `move`:**

| Remaining | Instructions |
|---|---|
| `sljit_emit_op1` call closure, with `emit_op` 444, `getput_arg` 470, `push_mem_inst` 416, `load_immediate` 534, `load_immediate32` 306, and `emit_single_op` 4,047 (one switch case is used) | 8,132, including libc `malloc` and its callees |
| `store_result` adds `read_soon`, `dead_after`, `reads_slot` and more | 9,575 in closure |
| `sljit_generate_code`, the phase that makes the final bytes: a copy loop with labels and jumps, all inlined | 860 |
| The `move` case inside `compile_code`, plus the compiler state invariant across the whole function | Part of 3,654 |

No contract connects anything from the bytecode to final bytes. The closure over-approximates, since a whole
function counts even if one case is used.

## Comparison

| | Route A: prove emitter | Route B: check output |
|---|---|---|
| State for one opcode | 2 rungs, nothing end to end | Whole checker contract |
| Instructions proved | 45 of about 10,000 reachable | 150 of 150 |
| Hand lines | 359 + 81 | 1,703 Rocq + 119 C |
| Lines per instruction | 8.0 (leaf code) | 11.4 |
| Wall time | 14 min | 44 min of proof, plus 12 min on the checker and wiring |
| Failed compile rounds | 7, including one 300 s tactic hang | About 19, all small |
| Check time | `rocqchk` 50-59 s per rung | `rocqchk` 103 s, build about 30 s |
| Mutants rejected | 2 of 2 | 13 of 13 (6 on bytes, 7 on the spec) |

Hand lines for route B are `MoveContract` 840, `MoveCompare` 581, `MoveStep` 138, `MoveDecode` 86,
`MoveTemplate` 45, `MoveAudit` 13. They reuse spike 5's `GcStep` and `GcTac`, adapted and not counted.
`MoveStep` and most of `MoveCompare` should carry over to other opcodes. A rejected mutant only shows this
proof script fails on it, not that its statement is false.

## Projection

Measured inputs only. Both are floors for the per-opcode functional part, not a budget.

| Route | Assumption | Scale | Lines per unit | Total lines |
|---|---|---|---|---|
| B, low | Comparer reused; each form costs `move`'s contract, template and decode | 42 by emit-code size | 971 | About 41k |
| B, high | No reuse; each of 21 + 52 cases costs what `move` cost | 73 | 1,703 | About 124k |
| A, low | All of `jit.c` and SLJIT at the rung rate | 34,875 instructions | 8.0 | About 280k |
| A, high | The same at spike 5's rate | 34,875 instructions | 25.3 | About 880k |

**Why these can mislead:**

- `move` is simpler than most opcodes, so B's cost per opcode is likely understated.
- Route A's figure counts lines per emitter instruction. It leaves out the relation from every emitter state
  to the bytes it produces, which is the actual theorem and likely the larger part.
- Route B leaves out layout, the hints, and emitter memory safety.
- Route A's sample is 45 instructions of the easiest code.

## What one opcode can't show: whole-function layout

To conclude anything about a function, on top of per-opcode templates, a checker must:

1. Walk the bytecode itself and account for every byte of the function, with no gaps or overlaps.
2. Re-derive `cached`, `homes`, liveness and pair facts by dataflow, instead of taking hints.
3. Check entry, frame and arity sequences, and branches between templates, including SLJIT's relaxed forms.
4. Check slow paths placed after the body, shared stubs, and return to the right place with state restored.
5. Check calls, handlers and the return-address sites the runtime uses for backtraces.
6. Handle inlined bodies, fused tests and exit tests, where one template spans several bytecodes.
7. Handle absolute addresses and immediates, whose values come from runtime state like constant cells.

Item 2 means re-implementing part of the emitter's analysis in proved code, which is a real cost.

## Recommendation

**Prefer route B for the next spike, but don't treat this as the answer yet.** The evidence separates the routes
on the cost of per-opcode correctness: B finished a whole opcode end to end, and A got 45 instructions into a
path of thousands. **It doesn't separate them on total cost**, because of B's memory-safety gap and layout work.

Before funding Phase 3, I'd measure the two things most likely to change this:

1. A function-level checker on one small function with a branch, an allocation and a slow path.
2. What it takes to show the emitter can't harm anything outside its buffers. Options are a no-crash and
   frame proof of the emitter, or running it isolated from what it could damage.

## Not run

- GC stress, `test-native`, `test-ffi`, `test-stlib`, `fuzz-native`, and `tests/cli.sh` with the checker.
- Route A rungs past 2; a spike 4 style semantic theorem for the template.
- A check that the `rocqchk` failure case of `check.sh` (exit 5) fires. It can't be triggered without
  corrupting a `.vo`.

## Checks

`check.sh` binds to the check build's SHA-256 and the checker's bytes, builds the audit, requires the `.vo`
files, replays with `rocqchk`, and reads the assumptions. Its last clean run printed `ALL_OK`, with only
`PrimInt63` and `PrimString` assumptions in the nine audited statements.

`gatetest.sh` showed each case fires: wrong binary exit 2, wrong checker bytes exit 3, broken proof exit 4,
smuggled axiom exit 6, `Admitted` exit 7, and clean exit 0 before and after. While writing this, the first version
of the gate failed its own clean case, because an up-to-date `dune` prints no audit output. It now compiles
the audit again for its output.

## Pins

| Item | Value |
|---|---|
| Shen/JIT | `715bf60`, spike 2's arena patch plus `apply_hook.py` |
| Check build `runtime` SHA-256 | `4a6666d7fec18851a9665be3159b6bc49840a6d1e2530c96ba94edc284fe8dff` |
| `spike_check_move` bytes SHA-256 | `97641237ffbaa8eac69194259af409506fc874d4cdc164116807e90fb7202be3`, at `0x36b9c`, 0x1aa bytes |
| Base build `runtime` | `048fadf7a0d50652...`. It differs from spike 2's `de349ea0...` from the same sources. I didn't investigate why; the two trees have different paths in a `-g` build |
| Model and prover | Theorem's model `5e13f6b0`, Rocq 9.3.0, OCaml 5.2.1, zig 0.13 (clang 18) |

## Reproduce

In `buri-lps`, with spike 2's tree at `/lps/s7/sj` and `/lps/s7/jit.c.base` from it, and `cp -a /work /work-s7`:

```sh
bash spikes/emitter/build.sh check
bash spikes/emitter/suites.sh check
bash spikes/emitter/check.sh       # route B
bash spikes/emitter/check-a.sh     # route A
bash spikes/emitter/gatetest.sh
bash spikes/emitter/mutate.sh
```

`/work-s7` and `/work-s7m` are still in the container. Agent token use isn't visible from inside the agent.

Total agent usage for this spike, as reported to the parent session: 671,808 tokens across two network-interrupted runs. Parent-session replay of `check.sh`: `ALL_OK`, exit 0.
