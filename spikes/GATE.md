# Shen/JIT Phase 0 gate

Recommendation: **narrow, and keep the full goal open.** Fund Phases 1 and 2 (the spec and
KLambda to bytecode), and run one more spike on the emitter before funding Phase 3.

This is a decision about further work. Nothing in these spikes verifies Shen/JIT.

## What Phase 0 showed

| Spike | Result | Limit |
|---|---|---|
| 1. Write-then-run in Theorem's model | Passed, unmodified model, 14 instructions | Cache sync not modeled; no reuse of code memory |
| 2. RV64 static arena build | Go under QEMU: contract 157/0, kernel 154/0 | Heap image file and flush path unresolved; REPL out of scope |
| 3. KLambda semantics on Rocq 9.3 | Passed, 10 files, one import line each | 10 of Búri's 179 Rocq files; text comparison only |
| 4. Real emitted bytes | Passed, 36 instructions, one code object | Helpers and emitter unproved; addresses fixed to one binary |
| 5. Collector cost | 172 of 71,321 instructions; four rungs checked | Pairs only at rungs 3 and 4; about 1,149 collector instructions left |
| 6. AArch64 | 21 Sail theorems; can't yet express running stored code | No process model; extra self-patching proofs |

No spike hit a stop condition. The model accepts the JIT shape without extension, and the proof
rate on the code we sampled was usable.

## Measured cost

| Spike | Instructions | Hand lines | Lines per instruction | Agent tokens | Tokens per instruction |
|---|---|---|---|---|---|
| 4. Emitted code | 36 | 851, plus 263 of spec and witness | 24 (31 with both) | 499,587 | 13,877 |
| 5. Collector | 172 | 4,354 | 25.3 | 746,039 | 4,337 |

Token figures are the totals the harness reported per agent. I don't know how they treat cached
context, so use them as a relative measure, not a bill.

## Projection

Runtime code alone, from spike 5's figures:

| | Instructions | Lines | Agent-hours | Tokens at spike 5's rate |
|---|---|---|---|---|
| Low (libc assumed, leaf rate of 9.6) | 51,336 | about 490k | about 160 | about 220M |
| High (libc included, 25.3) | 68,330 | about 1.7M | about 560 | about 300M |

**Treat these as floors, not a budget.** Samples this small don't extrapolate well, and the collector
is a favorable sample picked for its size. They exclude:

- **The emitter's real cost.** `jit.c` and `sljitLir.c` hold 34,875 instructions, about half of the
  code. Their proof isn't just about those instructions: it must show that everything they can emit
  simulates its bytecode. No spike measured this, and it could dominate the whole project.
- Lowerer and bytecode proofs, the heap image, composition, and the Shen frontend.
- Many-path primitives, libc, floating point, and retries at scale.

So the total is unknown. All we can say is that the known part is in the range of Anthropic's
reported "hundreds of millions of tokens" per large proof, and that the unmeasured part is the
hardest.

## Why narrow

Phases 1 and 2 are worth doing whichever way the emitter goes. They produce a Rocq spec of Shen/JIT's
behavior and a preservation proof down to bytecode, and that survives even if binary proofs stop. They
also shouldn't need Theorem's machinery, which makes them the cheapest real result available.

Committing to Phase 3 now would mean funding its biggest cost without having measured it.

## Spike 7: the emitter

Compare two routes on one opcode, over all its operand forms:

1. **Prove the emitter.** Contract on the real `jit.c` and SLJIT code path for that opcode: for every
   operand, the emitted bytes meet the template.
2. **Check its output.** A small proved checker validates emitted bytes against templates before they
   run, and stops on a mismatch. Then `jit.c` and SLJIT drop out of the trusted base, as Búri already
   does for captured compiler output. The cost is a runtime check and a further difference from the
   stock build, which makes the question for Bruno harder.

Bound it to about the same cost as spikes 4 and 5.

**Next gate:** fund Phase 3 only if one route has a measured cost that projects to something you're
willing to pay.

## Decisions for Reuben

- Approve the narrowed plan: Phases 1 and 2, plus spike 7.
- Whether to ask Bruno Deferrari now. A checker route changes what we'd ask, so I'd wait for spike 7.
- AArch64 stays a later decision. It would multiply binary-level cost, so it should follow the
  emitter measurement.
