# Spike 4: the real emitter's bytes against bytecode behavior

Result: **passed for one captured code object.** In Theorem's unmodified model, the exact
bytes Shen/JIT's emitter produced for a three-bytecode function refine a small bytecode
semantics, on the fast path, the allocation path up to the allocator call, and the error path
up to the helper call. Shen/JIT is not verified by this. The emitter, the helpers and the
semantics' link to KLambda are all unproved.

Evidence kind: Rocq theorem, replayed with `rocqchk`, about Theorem's RISC-V process model and
bytes captured from a run under `qemu-riscv64`.

## The code object

```text
(code sl.f 2 6 () ((prim 4 hd 2) (prim 5 cons 4 3) (return 5)) () ())
```

It emits 148 bytes at `0x5c140`; the dump is the 192-byte arena block, including trailing zeros.

| Path | Instructions | Ends at |
|---|---|---|
| Return | 20 | The frame's return address, with the new pair in `a0` |
| Allocation | 18 | `jal h_alloc` (`0x27860`), after publishing `fp`, `top` and `hp` |
| Error, `hd` of a non-pair | 14 | `jal h_prim` (`0x277c0`), with the primitive number and argument set up |

That is 36 distinct instructions, most of them compressed.

## What is proved

`slice_refines` in `coq/SliceProof.v`. For any `segs`, `fp`, `vm`, `st`, `regs`, `m` and `rom` with
`Rel st regs m`:

```coq
exists ms, steps segs (mkst regs (at_ 0) m rom) ms /\ Outcome rom regs (brun slice_prog st) ms
```

- `steps` is a chain of Theorem's `RiscvSemantics.step`, the same trusted step as spike 1.
- `Rel` fixes the registers (`s0` FP, `s1` VM, `s2` cached slot 2, `s3` HP, `a2` argument count),
  the slots, heap limit and heap in memory, layout disjointness, writability, and the captured
  bytes in one writable and executable segment.
- `Outcome` says what the machine state must be for each bytecode result, including the returned
  value, HP, what was published to the VM, the slots and heap afterwards, and which registers are
  preserved.
- `BStuck` maps to `False`, so the theorem also shows a related state never gets stuck.

`coq/SliceWitness.v` shows `Rel` is satisfiable and that concrete related states reach all three
outcomes, so the theorem doesn't hold just because its premise is impossible.

## What is not proved

**The emitter (`jit.c` and SLJIT).** The bytes are captured, so this says nothing about any other
code object, or about whether the emitter produces these bytes on another run. This is the main
gap, and the plan's hardest layer: 18,253 + 16,622 instructions in spike 2's count.

**These helper contracts, all unproved obligations:**

| Obligation | What is needed |
|---|---|
| `h_alloc` (`0x27860`) | With `a0 = vm`, `a1 = words`, and `fp`, `top`, `hp` published: returns to `ra`, preserving `s0`, `s1` and the roots' values under relocation, with room for `words`, or returns `26` after raising |
| `h_prim` (`0x277c0`) | With `a1 = 11` and `args[0] = x`: raises the error for `hd` of a non-pair, or runs a quiet handler, and returns its status |
| Return after `h_alloc` (`0x84` to `0x92`) | Reloads HP and slot 4, then restarts the allocation; these instructions are not stepped |
| Return after `h_prim` (`0x5e` to `0x6e`) | Tests for `26` and otherwise continues; not stepped |
| Unwind stub (`-0xae`) and arity stub (`-0x9a`) | Shared stubs, not stepped; `Rel` assumes the argument count is 2 |

**Other limits:**
- **Semantics:** `SliceBytecode.v` is a hand-written spike artifact for three instructions, not
  connected to Búri's `KLSemantics.v` or to the lowerer.
- **Reaching `Rel`:** no theorem shows a real process start reaches this relation. The evidence
  that it matches is sampled: three runs in `capture.c` (return, error, and an allocation that ran
  one real collection).
- **Fixed addresses:** code sits at `0x5c140` and helpers at capture-binary addresses, not the
  release binary's. The proof isn't position-independent.
- **Machine state:** Theorem's `mkst` fixes no pending syscall, no LR reservation, and a constant
  FP state, so only such states are covered.
- **Coherence:** as in spike 1, the model doesn't require a cache flush, so nothing here covers it.
- **GC:** the relation doesn't say which values are roots.

## What the proof revealed

- **The emitted test isn't literally the spec's test.** It computes `x - 3` and tests the low three
  bits for zero. `tag_taken` proves this equals `tag3 x = 3`.
- **Slot 5 is never written to memory.** The code keeps it in `CACHE`, so the relation after a
  return can only require slots 0-4. `docs/design.md` describes this; the proof forces it to be
  stated.
- **`WxExec`'s lemmas assume 4-byte instructions.** Most emitted code is compressed, so
  `SliceStep.v` restates them with the length as a parameter.
- **`decide` on bit vectors can exhaust memory at `Qed`.** A `vm_refl_bv` check on memory reads
  passed while tactics ran, then reached 11.7 GB in the kernel check. Comparing as numbers
  (`zs_inj`) takes 0.05 s. Anything at larger scale should use this form.

## Checks

| Check | Result |
|---|---|
| `check.sh`, fresh capture (bytes, helpers, build, `rocqchk`, assumptions, no `Admitted`) | `ALL_OK` |
| Bytes | SHA-256 `9c5e80dd29631be8e07bb723f1930e2c038a339eabd314c69fa7df27370e1367`, same on re-capture |
| Helper addresses | Match `h_prim` and `h_alloc` in the capture binary's symbol table |
| Assumptions of `slice_refines` and `w_rel` | Only `PrimInt63` and `PrimString` primitives |
| Capture runs under QEMU | `hd=1 tl=5`; error raised; `hd=3 tl=6` with 1 collection |

`gatetest.sh` shows each gate fires from a modified copy of the spike:

| Case | Exit | Message |
|---|---|---|
| Wrong bytes hash | 2 | `FAIL bytes` |
| Wrong helper address | 3 | `FAIL helper H_ALLOC` |
| Unjustified axiom | 6 | `FAIL assumptions: tag_low` |
| `Admitted` in a file | 7 | `FAIL Admitted` |

`mutate.sh` starts with an unchanged control, which must build. Nine mutants were then rejected,
and the restored proof built again:

| Mutant | Rejected at | Failure |
|---|---|---|
| `word-reads-wrong-slot` (table updated) | `SliceProof.v:526` | Type error |
| `word-table-unchanged` | `SliceFacts.v:33` | Decode fact fails |
| `result-tag-wrong` (table updated) | `SliceProof.v:536` | Type error |
| `tag-test-wrong` (table updated) | `SliceProof.v:285` | Type error |
| `spec-tag-wrong` | `SliceProof.v:71` | Type error |
| `tag-branch-swapped` (table updated) | `SliceProof.v:291` | Rewrite pattern not found |
| `limit-branch-swapped` (table updated) | `SliceProof.v:408` | Rewrite pattern not found |
| `spec-branch-swapped` | `SliceProof.v:595` | Type error |
| `alloc-wrong-words` (table updated) | `SliceProof.v:432` | `bveq` |

A rejected mutant only shows this proof script doesn't go through for it, not that its statement
is false. The two branch-swap failures are especially weak evidence: the script stopped on a
pattern match, not on a contradiction.

## Measures

| Measure | Value |
|---|---|
| Hand-written proof | 851 lines (`SliceProof.v` 612, `SliceStep.v` 239) |
| Hand-written spec and witness | 263 lines (`SliceBytecode.v` 74, `SliceWitness.v` 189) |
| Generated | 99 lines (`SliceCode.v`, `SliceFacts.v`) |
| Instructions covered | 36 |
| Lines per instruction | About 24 for proof alone, about 31 with spec and witness |
| Clean build of the example | 22 s on 3 jobs, with the model already built |
| `rocqchk` of `SliceProof` and `SliceWitness`, including their closure | 73-98 s |
| Wall time | About an hour, not measured precisely |
| Tokens | Not visible to me |

**Don't project cost from these.** The paths are straight lines with hand-picked values, and
`path_alloc` and `path_return` repeat a long prefix by copy. The ratio is near Theorem's reported
33 lines per instruction, but theirs is mostly machine-emitted over whole binaries, so that's a
coincidence rather than a confirmation. The real unknowns are unmeasured here: templates that hold
for every operand, and a proof about the emitter.

## Pins

| Item | Value |
|---|---|
| Model | `theorem-labs/rocq-linux-process-semantics` `5e13f6b0f82936aa5d006438e07e265c5d9fcfc4`, unmodified |
| Prover | Rocq 9.3.0, OCaml 5.2.1 |
| Shen/JIT | `715bf60`, spike 2's arena objects (`runtime` SHA-256 `de349ea0...`) |
| Compiler | `zig cc` 0.13.0, as in spike 2 |
| Capture binary SHA-256 | `c79e39ab4f569be00d7c450ab22439322fda89a4ccf88342c735e82876c5a85d` |

## Reproduce

Inside the `buri-lps` container from `spikes/jit-in-model/setup.sh`, with spike 2's built tree copied
to `/lps/s4/sj`:

```sh
cp -a /work /work-s4 && mkdir -p /work-s4/theories/Examples/jit_slice
bash spikes/jit-slice/check.sh
bash spikes/jit-slice/mutate.sh
bash spikes/jit-slice/gatetest.sh
```

Run these one at a time, since they share `/work-s4`. `gen_capture.py` writes `coq/SliceCode.v`, and
`gen_facts.py` writes `coq/SliceFacts.v`. `gen_facts.py`'s table is hand-maintained from a decode
listing; Rocq checks every entry against the bytes.

## Reproducibility caveat

Copying spike 2's tree isn't scripted, and `capture.sh` assumes it. The first gate run also needed
a recreated `/work-s4`, because I deleted a build directory and ran two scripts concurrently. Those
invalid results were discarded, and everything above comes from the clean runs afterwards.

Total agent usage for this spike, as reported to the parent session: 499,587 tokens, 39 minutes.
