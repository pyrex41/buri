# Spike 8: the three risks of checking the emitter's output

Result: **the checker route held up on all three risks for the code it covers, and none of them
blocked it.** A generic theorem now says that whatever bytes a function-level checker accepts follow
their bytecode on every path, up to named helper contracts. The checker takes nothing from the
emitter's analysis, and one real function from the 0.3 build is covered end to end. The open costs
are elsewhere: proving the in-process C checker, calls, and the many opcodes and slow paths this
domain doesn't reach. Nothing here verifies Shen/JIT.

Evidence kind: Rocq theorems in Theorem's unmodified RISC-V and Linux process model, replayed with
`rocqchk`, plus suite runs under `qemu-riscv64`. Nothing has run on RISC-V hardware.

## Setup

Shen/JIT 0.3 (`b4ccf2dff97031ee624692bb32d2addd18cacb39`), with spike 2's static code arena. Two
changes were needed at 0.3: the `heap.c` hunk of spike 2's patch moved, and `emit_sqrt` no longer
compiles for RISC-V (it has arm64 and x86-64 arms only; `setup.sh` adds an `fsqrt.d` arm). That second
change touches hand-written native code, which the claim excludes; it's here only so the build links.
`shen-jit-0.3-rv64-checker.patch` shows the resulting tree, minus `local.mk`, which git ignores and
spike 2's patch carries.

## Risk 2 and 3: the function-level checker and its theorem

### What the checker does

`coq/CfDefs.v` holds the checker as a Rocq function, `check_all`. For each bytecode instruction it
symbolically runs that instruction's machine code from a canonical state (what CACHE holds, which
frame slots are current, which slots are known pairs, how much heap room is reserved) and compares
the result with what the bytecode requires. It follows branches to labels and slow paths placed after
the body, the allocator call through `auipc`/`jalr`, the raise check that branches to the shared
unwind stub, and the jump back to restart the instruction.

Its other inputs are the bytecode words, the runtime's constant table (values and cell addresses), the
frame size and helper addresses, all read from the runtime, and two **certificates**: the byte offset of
each instruction and the canonical state before each one. A wrong certificate makes the check fail.
The emitter's `cached`, `homes`, `keep` and byte ranges, which spike 7 trusted, are gone. The bytecode
itself has to be trusted or come from the lowerer that Phase 2 proves, and it must be read from memory
the emitter couldn't have changed: that is risk 1 again.

Domain: `move`, `const`, `cons` with its allocation slow path, `hd` and `tl` of slots known to be
pairs, `=` against an identity-compared constant fused with its `jump-if-false`, `cons?` fused the
same way, `label`, `jump` and `return`. Other forms are rejected.

### What is proved

`run_sim` and `step_sim` in `coq/CfTop.v`, for every function `check_all` accepts:

- **`step_sim`:** from any accepted point, in a machine state related to a bytecode state by `Rel`,
  the model's real `RiscvSemantics.step` goes:
  - for `BNext j st'`, to the code of instruction `j`, related to `st'`; or, for `cons`, to the
    allocator call (`AtAlloc` below);
  - for `BReturn v`, to the return address from slot 0, with `a0 = v`, the heap pointer in `s3`, and
    callee-saved registers preserved;
  - never to `BOther`: accepted code doesn't reach an undefined bytecode state from a related state.
- **`run_sim`:** the same, composed over any bytecode run.
- **`AtAlloc`:** the frame pointer, frame top and heap pointer are published to the VM, `a0 = vm`,
  `a1` holds the words reserved, and `ra` points into this code. For **every** return from the
  allocator that satisfies its contract (`After`, which allows any new bytecode state `st2`), the
  machine either jumps to the unwind stub when the status is 26, or comes back to the same `cons`
  related to `st2`.

**Premises:**

| Premise | What it says |
|---|---|
| `Rel` | Register roles (`s0` frame, `s1` VM, `s2` CACHE, `s3` heap pointer), current slots readable, heap words and constant cells readable, code bytes in the writable and executable segment, layout disjointness, writable regions, pair facts, reserved room |
| `After` | The allocator's contract on return: registers, frame, heap and cells as `Rel` needs, with `st2` unconstrained. **That `st2` means the same as `st` (the collector's job, spike 5's `scan_iso`) is not proved here** |
| `Hkeq` | The kernel's `=` is word equality when one side has an identity tag (symbol, special, procedure) |
| `Htrue`, `Hfalse` | `true` and `false` aren't pairs (proved for the real values in `CfInstance.v`) |
| `WfK` | Immediate constants fit in a word (proved for the real function) |

The bytecode semantics (`bnext` in `CfDefs.v`) is a spike artifact for this subset. It isn't Phase 1's
`JitBytecode.v` and isn't connected to KLambda.

### One real function

`coq/CfInstance.v` applies both theorems to `shen.invoke` from the 0.3 kernel, compiled by the real
JIT in the capture harness (`capture/`):

```text
(prim 4 = (const 0) 3) (jump-if-false 4 0) (prim 5 cons 2 (const 0)) (prim 4 cons (const 1) 5)
(return 4) (label 0) (prim 4 cons 2 3) (return 4)
```

The code has a fused `=`, three conses, two room checks with slow paths calling `h_alloc` and
branching to the shared unwind stub, a label reached from the branch, a symbol constant loaded through
a computed cell address, and two returns. `cap_accepted` proves `check_all` accepts these exact bytes,
and `cap_parse` that the bytecode list is what `parse` reads from the code object's words. The theorems
`cap_run` and `cap_step` follow with no further premise beyond `Rel`, `After` and `Hkeq`.

Bytes SHA-256 `369db3d9b9d3cd92232435b4cc942d986011b0af3f251537a3d084c4c4582ce6`, 240 bytes at `0x156230`, bound by `check.sh` to the dump, to
`shen.invoke.bin` from the same run, and to the capture binary's SHA-256.

### Running the C checker

`overlay/check_fn.c` implements the same checker in C, called after `sljit_generate_code` and before
the code can run (`apply_hook.py`). It computes its own canonical states and can dump them. For
`shen.invoke` the dumped states are the Rocq certificate, with slot 0 added to the current slots and
pair facts dropped. **The theorem is about the Rocq function, not this C code**, and the two differ in
details. They agree on this one function by computation.

### Suites under `qemu-riscv64` with the C checker

Two runs each, same counts both times. The checker ran in reporting mode: a rejection is counted and
the code still runs.

| Suite | Result | Functions compiled | In the checker's domain | Accepted | Rejected |
|---|---|---|---|---|---|
| Contract | 157 passed, 0 failed | 493 | 30 | 21 | 9 |
| Kernel | 154 passed, 0 failed | 2,452 | 41 | 21 | 20 |
| Extensions | 123 passed, 0 failed | 1,005 | 53 | 14 | 39 |

"In the domain" is by opcode only, so it includes forms the checker doesn't handle. Every rejection
in these runs is valid code the checker can't yet follow, not an emitter bug:

| Reason | Contract | Kernel | Extensions |
|---|---|---|---|
| `hd` or `tl` of a slot not known to be a pair (the tag check's slow path to `h_prim`) | 8 | 8 | 8 |
| `=` against a fixnum (has a slow path) | 1 | 1 | 1 |
| "indirect jump", in test functions such as `belongs-in?` and `ppm.match-cons`; cause not found | 0 | 11 | 30 |

### Emitter bugs, function by function

`capture/domain_run.sh` compiles each of the 49 kernel functions in the domain by opcode through the
real JIT with the checker linked, for the correct build and three deliberately wrong ones. Six
produced no checker record in the harness and aren't counted.

| Build | Accepted | Rejected | Rejection reasons beyond the correct build's |
|---|---|---|---|
| Correct | 29 | 14 | None |
| `cons` writes its first operand to both fields | 17 | 26 | 12 "cons wrote the wrong thing" |
| A needed result store is dropped | 27 | 16 | 2 "store to the wrong slot" |
| The room check reserves two words too few | 17 | 26 | 11 "h_alloc arguments", 1 "room check wrong" |

The first two bugs also stop stage 1, so the suites catch them too. The room bug passes the contract
suite, 157 to 0, because it only matters when the heap is nearly full; the checker finds it in 12
functions. The correct build's 14 rejections are 10 `hd` or `tl` slow paths, 2 instructions outside the
block runner's forms, 1 fixnum `=`, and 1 string `=` with several branches.

## Risk 1: the emitter shares the address space

The unproved emitter runs in the same process before the checker. It could corrupt the heap, the
bytecode the checker reads, the checker's own state, or code already checked. Copying its output into
checker-owned memory before checking delivers nothing on its own, because the emitter has already run
by then.

| Design | Theorem it would deliver | Proof cost | Runtime cost | Status |
|---|---|---|---|---|
| (a) Emitter in a separate process, as a TCP peer | For every byte string the peer sends, the runtime either rejects it or installs code that refines its bytecode | No emitter proof at all. The runtime's accept, read and copy code is in scope, as it is anyway | One round trip per compile; measured 3.2 µs on loopback here, against 2,452 compiles in the kernel suite | Supported by the model, see below; not built |
| (b) Prove the emitter only writes what it may | The checker's inputs and the heap are untouched while it runs | Static closure of `compile_code`: 110 functions, 37,493 instructions, plus 3,727 in libc. 2,413 stores through computed pointers, 926 to its own stack, 25 indirect calls. At 8.0 to 25.3 lines per instruction (spike 7 rung 2, spike 5) that's about 0.33M to 1.0M lines | None | Not sampled this spike; the rates are earlier spikes' |
| (c) Sandbox the emitter (software fault isolation), and prove a validator that every store and indirect jump in the emitter's binary is masked | The emitter writes only its sandbox | A store-masking validator, likely of the size of this spike's block checker; 2,413 store sites and 25 indirect calls to mask | Typical SFI overhead for the emitter only; not measured | No RV64 SFI toolchain at hand |

**Why (a) fits the model.** Theorem's model runs one process. `clone` is modeled only as the parent sees
it (`Sys/Kernel/Fork.v`), and the child never runs. Sockets are modeled on the accepting side: the
environment offers an infinite, universally quantified queue of connections, each with an arbitrary
script of bytes (`State.NetQueue`, `Sys/Net/Socket.v`). An emitter process that connects to the runtime
is exactly such a peer, so a statement over all inputs already covers every possible emitter, correct
or not. `connect` from the runtime side is unmodeled, so the runtime must listen.

**What (a) leaves open.** The socket reads and writes become observable events in the process's trace,
so the refinement claim must permit or hide them. The bytecode and address map the runtime sends are
its own output. Phase 1's statement of the claim would need that change. No prototype was built.

## Costs

| Item | Lines | Notes |
|---|---|---|
| Checker definition (`CfDefs.v`) | 684 | Includes the bytecode subset and the word reader |
| Generic soundness (`CfStep`, `CfRun`, `CfSound`, `CfStepSim`, `CfCases`, `CfCons`, `CfTop`) | 2,222 | About 150 of `CfStep` adapted from spike 4 |
| Instance for `shen.invoke` (`CfInstance.v`) and audit | 79 | `CfCaptured.v` (30) is generated |
| C checker | 634 | 3,739 RV64 instructions compiled; about 3,500 without the reporting functions, still including the dump code |

Marginal cost per bytecode form, measured as the case proof plus its clause in `check_at`:

| Form | Lines |
|---|---|
| `label` | 13 |
| `move` | 21 |
| `hd`, `tl` | 27 each |
| `return`, `jump` | 29 and 30 |
| `cons?` fused | 48 |
| `=` fused, with the identity premise | 65 |
| `cons` with room check, allocator call and resume | about 410 |

Wall time from start to the gate first passing was about 1 hour, with about 45 compile rounds, most
of them argument-order and name fixes rather than proof difficulty. Tokens aren't visible inside
this agent.

## Projection

From measured numbers only. Assumptions are labeled; none of this is a budget.

**The checker's soundness in Rocq, for all of Shen/JIT's compiled forms:**

| Part | Assumption | Low | High |
|---|---|---|---|
| About 47 more primitive forms in `emit_prim` | Low: each reuses one generic "slow path to a raising helper" lemma at about 40 lines. High: each costs what `cons` did | 1.9k | 19k |
| Calls: `call`, `call-sealed`, `call-value`, the three tail calls, `closure` | 300 to 1,500 each; they need a frame and window invariant across calls and GC roots, none of which this spike touched | 2.1k | 10.5k |
| About 18 other opcodes (handlers, entry dispatch, loops, raw and real registers, inline) | 50 to 300 each | 0.9k | 5.4k |
| More RV64 instruction forms in the block runner | About 30 forms at 20 to 40 lines | 0.6k | 1.2k |
| Infrastructure: register homes, memory caches, handler stack, inlined bodies, entry check | | 2k | 8k |
| **Total** | | **about 7.5k** | **about 44k** |

**The C checker's binary:** about 3,500 instructions today, at 11.4 (spike 7) to 25.3 (spike 5) lines
per instruction: 40k to 89k lines. If it grows two to four times to cover the whole domain, 75k to 340k.
**This is now the largest single item on the checker route.**

**Compared with route A** (spike 7, prove the emitter): 280k to 880k lines for functional correctness,
plus design (b) above for memory safety if the emitter stays in-process.

**Coverage today:** in the 0.3 kernel, 49 of 941 functions (5.2%) and 692 of 39,634 bytecode
instructions (1.7%) are in this domain by opcode, and 29 of the 43 the harness exercised were accepted.
Calls are common: `call-sealed` 2,298, `tail-call-sealed` 626 and `closure` 540 of the 39,634
instructions.

## Recommendation

**Fund Phase 3 by the checker route, in stages.** The three risks that spike 7 left open didn't
break it:

- **Risk 2:** certificates replace trusted inputs, and wrong ones are rejected (mutants below).
- **Risk 3:** layout composes across branches, labels, slow paths and shared stubs, for a real function.
- **Risk 1:** design (a) removes the emitter from the proof entirely, inside the existing model.

Per-form marginal cost is small (13 to about 410 lines), so the Rocq side looks bounded.

Do these first, because each could change the answer:

1. **The C checker binary.** Prove `decode` and `run_block` (about 900 instructions) on the binary
   and measure the rate, or find a way to produce the in-process checker from the Rocq definition.
2. **One call form.** `call-sealed` with its frame window and GC roots, to see whether calls stay
   within the per-form range above.
3. **The peer split.** A prototype of design (a) and a draft of the refinement statement that permits
   its socket events.

**What would change my mind:**

- **Stop at bytecode** if the C checker's binary proves at well over 25 lines per instruction, or a
  call form costs more than about 2,000 lines, or Phase 1's claim can't permit the peer's socket I/O
  and no in-process isolation is affordable.
- **Direct proof** only if the emitter's own structure turned out to be provable at near spike 7's
  leaf rate across its whole closure, which nothing so far suggests.

## Checks

| Check | Result |
|---|---|
| `check.sh` | `ALL_OK`, exit 0: capture binary and bytes bound, 7 audited statements, `rocqchk` exit 0 in 87 s |
| Assumptions of `run_sim`, `step_sim`, `cap_run`, `cap_step`, `cap_accepted`, `cap_parse`, `cap_length` | Only `PrimString.get`, `PrimString.length`, `PrimString.string` |
| `Admitted` or axioms in `coq/` | None |

`gatetest.sh` showed each gate fires from a modified copy of the spike:

| Case | Exit | Message |
|---|---|---|
| Clean, before | 0 | `ALL_OK` |
| Wrong capture binary | 2 | `FAIL capture binary` |
| Dump bytes changed, instance regenerated | 3 | `FAIL dump bytes differ from shen.invoke.bin` |
| Instance edited by hand | 3 | `FAIL instance differs from the dump` |
| Ill-typed proof step | 4 | `FAIL build` |
| `rocqchk` given a missing file | 5 | `FAIL rocqchk` |
| Extra axiom in the audit (`classic`) | 6 | `FAIL assumptions: classic` |
| `Admitted` in a source file | 7 | `FAIL Admitted or axiom in sources` |
| Clean, after | 0 | `ALL_OK` |

The `rocqchk` case only shows the exit code is wired: it gives `rocqchk` a missing file, not a corrupted
proof. Two earlier versions of the broken-proof case didn't fire, because the edited proofs were still
correct: `reflexivity` closes `check_all ... = true` by conversion, and `tag3 v_true` and
`tag3 v_false` are both 2, so swapping them type-checks.

`mutate.sh` checks that each mutant fails to build, then that the unmodified spike builds again. A
rejected mutant only shows that this proof script, or the checker run by `vm_compute`, fails on it.

| Mutant | What changed | Where it failed |
|---|---|---|
| `b-tag-off-by-one` | `addi a0,s3,3` becomes `+4` after a `cons` | `cap_accepted` |
| `b-cons-field-order` | The tail is stored at offset 0 | `cap_accepted` |
| `b-room-too-small` | The room check reserves 16 bytes instead of 32 | `cap_accepted` |
| `b-eq-branch-inverted` | `bne` becomes `beq` in the `=` test | `cap_accepted` |
| `b-alloc-wrong-words` | The allocator is asked for 2 words, not 4 | `cap_accepted` |
| `b-hp-not-reloaded` | After the allocator, `s2` is loaded instead of `s3` | `cap_accepted` |
| `b-return-wrong-value` | `a0` gets `s1` instead of CACHE | `cap_accepted` |
| `b-fp-not-published` | The frame pointer is stored at offset 24, not 16 | `cap_accepted` |
| `b-raise-check-wrong-status` | The raise check compares with 25 | `cap_accepted` |
| `c-cache-kept-at-alloc` | The certificate keeps CACHE at the allocation | `cap_accepted` |
| `c-cut-shifted` | One instruction's byte offset moved by 2 | `cap_accepted` |
| `c-slot-claimed-current` | The certificate claims a slot the code didn't store is current | `cap_accepted` |
| `s-no-hp-check` | `post_ok` no longer checks the heap pointer | `CfSound.v` |
| `s-no-room-zero-at-resume` | `check_resume` no longer requires no reserved room | `CfCons.v` |
| `s-hd-without-pair` | `hd` no longer requires a known pair | `CfCases.v` |
| `s-no-frame-kept-at-call` | `check_slow` no longer checks the frame at the call | `CfCons.v` |

16 of 16 rejected, and the unmodified spike built again afterwards. The `s-` mutants weaken the
checker's definition, and each breaks a soundness proof, so these checks are load-bearing.

## Not done or not run

- **No theorem connects the C checker to the Rocq checker.** Only the Rocq checker is proved.
- **Not covered by the theorem:**
  - the entry and arity check (`check_entry` is defined but not proved)
  - the unwind stub, the allocator's semantic contract, cache coherence, and reuse of code memory
  - helper addresses: they come from the runtime and aren't checked against its symbol table
- **Out of domain:** the hd and tl tag-check slow path to `h_prim` (10 of 14 rejections in the
  harness), `=` against fixnums or strings, calls, loops and handlers.
- **Not run with the checker:** GC stress, `test-native`, `test-ffi`, `test-stlib`, `fuzz-native`,
  and `tests/cli.sh`.
- **Design work not done:** no prototype of design (a), no frame-proof sample for (b), no SFI build
  for (c).
- **Not exercised:** six in-domain kernel functions in the harness (the hook printed no record for
  them); I didn't find out why.
- **Strict mode isn't usable yet:** every rejection of valid code outside the supported forms would
  stop the process.

## Pins

| Item | Value |
|---|---|
| Shen/JIT | `b4ccf2dff97031ee624692bb32d2addd18cacb39` (0.3), spike 2's arena patch, `setup.sh` changes, `apply_hook.py` |
| Capture binary SHA-256 | `2d5ba69525d4d96ac413b3148542d4c7d329263023aa1ec627d9f7e3aa1ac833` |
| Model and prover | Theorem's model `5e13f6b0`, Rocq 9.3.0, OCaml 5.2.1, zig 0.13 (clang 18) |

## Reproduce

In `buri-lps`, with `/work` holding the built model:

```sh
bash spikes/emitter-risks/setup.sh          # 0.3 tree at /lps/s8/sj, stage 0, /work-s8
bash spikes/emitter-risks/build.sh check    # the checker build
bash spikes/emitter-risks/suites.sh check
EXTRA_OBJ=spikes-overlay/spike8.o SPIKE_DUMP=shen.invoke SPIKE_DUMP_OUT=/lps/s8/cap/shen.invoke.dump \
  bash spikes/emitter-risks/capture/capture.sh shen.invoke 2
bash spikes/emitter-risks/check.sh
bash spikes/emitter-risks/gatetest.sh
bash spikes/emitter-risks/mutate.sh
bash spikes/emitter-risks/capture/domain_run.sh check   # and checkbad-slot, checkbad-store, checkbad-room
python3 spikes/emitter-risks/stores.py /path/to/base/runtime
```

`/work-s8` and `/work-s8m` are left in the container.

Total agent usage for this spike, as reported to the parent session: 753,206 tokens, 79 minutes. Parent-session replay of `check.sh`: `ALL_OK`, exit 0.
