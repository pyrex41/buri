# Spike 5: what binary-level functional proofs of the runtime cost

Phase 0, spike 5 of the Shen/JIT verification plan. The sample is the Cheney collector in
`src/runtime/heap.c`, compiled by spike 2's build.

**Result: measured, but on only 172 of 71,321 runtime instructions (0.24%).** Four rungs have
machine-checked statements, with narrowing premises listed below. Nothing here verifies the
collector, and the sample says little about the emitter, which is the largest unknown.

Evidence kind: Rocq theorems about the exact bytes of the runtime, in Theorem's unmodified RISC-V
and Linux process model, replayed with `rocqchk`. Nothing has run on RISC-V hardware.

## Image

| Item | Value |
|---|---|
| `runtime` SHA-256 (spike 2) | `de349ea06fc770e1dcf735f416a1713c93715aa7371528001918bdd635dcbd38` |
| `shen-jit` SHA-256 (runtime + heap image) | `603b0d582310b3a82540148fd3f434a452c0cd1a43f2aa4504e595705db25d8d` |
| Proof image SHA-256 | `20c5c4e346153345955ae2ee50d44ce9a1bface1597b8489742c15c6bfe89031` |
| Model | Theorem's `rocq-linux-process-semantics` `5e13f6b0`, Rocq 9.3.0 |

The proof image is `runtime` with only `p_memsz` of its one `PT_LOAD` set to `p_filesz` (3 bytes
differ; `mkimage.py` checks that). That drops the 64 MiB arena and `.bss` from the snapshot. Text and
rodata are byte-identical, but **the theorems are about this image's segment list, not the 64 MiB
one**. Carrying them to the full image hasn't been done; it would need reasoning about fetch and
rodata reads, which are the same bytes.

## Collector size

Whole-function counts from `disasm.sh`, excluding padding `nop`s:

| Function | Instructions | Proved here |
|---|---|---|
| `vm_collect` (with `collect_into`, sweeps, root loops inlined) | 825 | 0 |
| `drain` (with `scan`, `scan_values` inlined) | 260 | 27 |
| `copy_value` | 204 | 113 |
| `obj_words` | 32 | 32 |

## What's proved

Each is a contract over all states meeting its premises, not a concrete run. All are about
`msteps`, Theorem's chain of machine steps. Top statements are in the named files, and the premises
below are the important ones.

| Rung | Theorem | Statement |
|---|---|---|
| 1 | `obj_words_contract` | For every header word, returns to an even return address with a0 equal to `obj_words_Z`, a transcription of `value.h`. Changes only a0-a3 and no memory. |
| 2 | `copy_value_contract` | Every call meeting `cv_rel` runs to its return address with the stated result and memory, keeps callee-saved registers, and keeps the memory invariant. The cases are non-pointer, already forwarded, pair with non-pair tail, pair with a list spine, and any other object of a valid type. |
| 3 | `scan_contract` | A scan over a run of **pairs only**, following the relation `scan_pairs`, runs to the loop's exit with exactly the relation's memory. Calls `copy_value` through rung 2. |
| 4 | `scan_iso` | For a heap of **pairs and non-pointers only**: at the end of the scan, forwarding is an injective map onto all of to-space; each copy holds the images of the original's values; each original holds its forwarding address; and everything reachable from a forwarded root is forwarded. |

`witness_machine` and `witness_iso` apply rungs 3 and 4 to a concrete one-cell heap with a
self-pointing tail, so the premises aren't vacuous for that heap. It exercises the forwarded and
non-pointer cases of `cv_rel`. The other cases have no witness.

### Premises and exclusions

- **Memory:** the overlay doesn't touch text or rodata (`mem_clear`), the frame, semispaces and Copy
  struct are writable, and semispaces are disjoint and below the stack with the Copy struct above it.
  The stack-above-heap order is an assumption about layout, not a proved fact.
- **`copy_value`:** the pointer is in from-space, so `reach_large` and the `copy_large` branch
  aren't covered. Object types are 1-11; the invalid-type path isn't covered.
- **Relations:** rungs 2 and 3 show that the machine follows relations written from the C code.
  The relations carry their own premises, such as to-space having room. Nothing proves a real
  collection satisfies them, except what rung 4 derives for pairs.
- **Rung 3:** the header arm of `scan_values`, `T_CODE` constants and large objects aren't covered.
- **Rung 4:** the root loop in `collect_into` isn't proved on the binary. Roots appear only as
  cells already forwarded when the scan starts. Symbol and code sweeps, stream closing, and
  semispace flipping aren't covered.

**Whole collection wasn't reached.** A full contract still needs `vm_collect`'s 825 instructions,
the 233 uncovered in `drain`, 91 in `copy_value`, a graph model with every object type, and the
stack, global cell and handler roots.

## Checks

| Check | Result |
|---|---|
| `dune build .../GcAudit.vo` | exit 0 |
| `rocqchk` on `GcAudit`, which imports every rung | exit 0, 105 s |
| `Print Assumptions` on 8 statements | Only `PrimInt63`, `PrimString`, `PrimArray` primitives; no custom axiom |
| `Admitted` in the example | 0 |

### Mutations

| Mutant | Kind | Where it failed |
|---|---|---|
| `code-words`: code object size 11 | spec | `Rung1ObjWords.v`, `bveq` |
| `header-type-shift`: type field off by one bit | spec | `Rung1ObjWords.v`, rewrite |
| `forward-marker`: `V_FORWARD` = 35 | spec | `Rung2Spine.v`, type mismatch |
| `nonptr-tag-list`: tag 1 treated as non-pointer | spec | `Rung2Paths.v`, rewrite |
| `spine-write-order`: swapped copied words | spec | `Rung2Spine.v`, timeout |
| `pair-moved-tag`: wrong tag on the moved pointer | spec | `Rung2Spine.v`, type mismatch |
| `object-next-offset`: cursor 8 too far | spec | `Rung2Spine.v`, timeout |
| `saved-reg-order`: swapped frame slots | spec | `Rung2Frame.v`, incomplete proof |
| `scan-skips-slot`: second slot not scanned | spec | `Rung3Scan.v`, type mismatch |
| `inv-show-unscanned`: scanned words not imaged | spec | `Rung4Graph.v`, type mismatch |
| `iso-drops-tail`: reachability ignores the tag test | spec | `Rung4Graph.v`, hypothesis name |
| `ow-jump-table`: first table entry zeroed | bytes | `Rung1ObjWords.v`, `bveq` |
| `ow-li-3`: `li a0,4` for `li a0,3` | bytes | `Rung1ObjWords.v`, `bveq` |
| `cv-forward-marker`: marker 33 | bytes | `Rung2Spine.v`, type mismatch |
| `cv-wrong-cursor`: new cursor computed from the wrong registers | bytes | `Rung2Spine.v`, type mismatch |
| `cv-loop-step`: loop step changed | bytes | `Rung2Spine.v`, type mismatch |
| `scan-wrong-slot`: result stored through the wrong register | bytes | `Rung3Scan.v`, rewrite |

All 17 were rejected, and the unmodified proofs compiled before and after. `iso-drops-tail` failed
because the script names a hypothesis the mutant removes, so it's weak evidence.

A rejected mutant only shows this proof script doesn't go through for it, not that its statement is
false. Several failures are timeouts or `bveq`'s misleading "runaway-large" message.

Gates tested both ways:

- `mutate.sh`'s baseline compiled, and all mutants failed. It also fired for real: my first `ow-li-3`
  patch wrote the original bytes, so it reported `MUTANT_ACCEPTED`. It now refuses any patch that
  doesn't change bytes. A broken `sed` reported `MUTANT_NOT_APPLIED`.
- `mkimage.py` and `disasm.sh` reject a `runtime` with changed bytes, and accept the real one. My
  first negative test wrote a zero over a zero and passed, so I redid it with a real change.

## Rates

Lines are hand-written Rocq, including specs and comments. Generated fetch and decode facts aren't
counted. Clock is the host's, mostly single-threaded on a loaded machine, and includes writing,
compiling and fixing. **Tokens aren't visible to me while running**, so use the harness's total for
this agent, which covers the entire spike rather than any rung.

| Part | Instructions | Lines | Lines per instruction | Clock | Failed compiles (about) |
|---|---|---|---|---|---|
| Shared library: step lemmas, tactics, memory (`GcStep`, `GcTac`, `GcMem`) | n/a | 576 | n/a | in rung 1 | 4 |
| 1: `obj_words`, leaf with jump table | 32 | 308 | 9.6 | 12 min, with library | 9 |
| 2: `copy_value`, memory, two loops, one inlined jump table | 113 | 2,007 | 17.8 | 41 min, 10 of them lost to one hang | 18 |
| 3: pair scan, calls through rung 2 | 27 | 442 | 16.4 | 6 min | 7 |
| 4: graph invariant, no new instructions | 0 | 772 | n/a | 20 min | 9 |
| Witness: non-vacuity | 0 | 249 | n/a | 5 min | 7 |
| **Total** | **172** | **4,354** | **25.3** | **85 min from start to witness** | **about 54** |

Compile: each rung file takes under 25 s, and `Rung2Spine.v` is the largest. Full example check
with `rocqchk` is 105 s.

**What reuse did.** Rung 3 cost 6 minutes because it inherited the library and rung 2's contract. The
library needed 576 lines because Theorem's step lemmas assume 4-byte instructions and this build uses
RVC. Its proof library's block executor (`SymTac`) assumes read-only code, so I stepped one instruction
at a time rather than using it. Mirroring it would likely cut proof-check time and maybe lines.

## Projection

From measured rates only. In-scope instructions are spike 2's table, minus linked-but-excluded `ffi.c`,
`thread.c`, and `profile.c` (3,938): **51,336** runtime plus **16,994** libc and compiler-rt.

| Scenario | Instructions | Rate | Lines | Agent-hours at the observed 3,070 lines/hour |
|---|---|---|---|---|
| Low: runtime only, at the leaf rate; libc assumed by premise | 51,336 | 9.6 | about 490k | about 160 |
| Middle: runtime only, at the overall rate | 51,336 | 25.3 | about 1.3M | about 420 |
| High: runtime and all libc, at the overall rate | 68,330 | 25.3 | about 1.7M | about 560 |

**Treat these as floors for what they cover, not estimates of the whole job.** They assume this
sample's rate extends to all other code. Line and hour totals assume no extra coordination and that a
loaded single agent's rate holds. 3,070 lines/hour is 4,354 lines over 85 minutes.

What the sample can't tell us:

- **The emitter.** `jit.c` (18,253) and `sljitLir.c` (16,622) are half the in-scope code. Their
  correctness isn't about the emitter's own steps; it's a simulation between bytecode and whatever
  code they emit. Nothing here measures that, and rung 4's invariant is the only related data.
- **Code size vs. paths.** Effort follows paths, not instructions. Here, 11 object types and a few
  tags were cheap because they were small. A primitive with many cases, or the emitter's many per-opcode
  paths, could cost far more per instruction.
- **libc.** `malloc`, `printf` and `strtod`-style code may be harder or be replaced by premises, and
  only the reachable part matters. I measured none of it.
- **Floating point and the model's edges.** Nothing here touches `Fpu.v`, syscalls, or the image
  loader's relocation.
- **Graph complexity.** Rung 4 has one object shape. Each added shape (closures, code objects with
  constant slots, large objects, weak symbol sweep) adds to the invariant, and rung 4's 772 lines for
  pairs alone suggest this grows quickly. No rate here covers the full object model.
- **Sampling bias.** I picked the collector because it's small and has clear specs. It isn't a random
  sample.

**Different measure, for reference:** Theorem quotes about 600k proof lines per 18k instructions, or
33 lines per instruction, for no-crash proofs of whole binaries. Those lines are largely machine-emitted
and cover every path of each binary, so the two rates aren't comparable. Mine are hand-written, for a
stronger functional claim, on a small and favorable part of a binary.

## Reproduce

In the `buri-lps` container, with spike 2's `runtime` at `/lps/runtime`:

```sh
bash spikes/gc-rate/setup.sh
bash spikes/gc-rate/regen.sh
bash spikes/gc-rate/build.sh theories/Examples/gc_rate_ns/GcAudit.vo
bash spikes/gc-rate/mutate.sh
bash spikes/gc-rate/disasm.sh /lps/runtime OUT_DIR   # disassembly and function counts
```

| File | Contents |
|---|---|
| `coq/GcStep.v`, `GcTac.v`, `GcMem.v` | Library: any-size step lemmas, tactics, words in memory |
| `coq/Rung1ObjWords.v` | Rung 1 |
| `coq/Rung2Frame.v`, `Rung2Paths.v`, `Rung2Pointer.v`, `Rung2ObjSize.v`, `Rung2Spine.v` | Rung 2 |
| `coq/Rung3Scan.v` | Rung 3 |
| `coq/Rung4Graph.v`, `Rung4Witness.v` | Rung 4 and its witness |
| `coq/GcAudit.v` | Assumption audit |
| `gen_code.py`, `mkimage.py`, `regen.sh` | Image and fetch/decode facts |

Total agent usage for this spike, as reported to the parent session: 746,039 tokens, 98 minutes.

## Parent-session replay

Compiling `Rung4Witness.v` and `GcAudit.v` directly with `rocq compile` against a copy of the build tree
succeeded, and `rocqchk` on `GcAudit.vo` exited 0 in 94 s. I had to do it that way because in `/work-s5`,
after `mutate.sh`, `dune build theories/Examples/gc_rate_ns/GcAudit.vo` exited 0 and left no
`GcAudit.vo` or `Rung4Witness.vo`. I didn't find out why, so don't treat a zero dune exit as evidence in
this tree without checking that the `.vo` exists.
