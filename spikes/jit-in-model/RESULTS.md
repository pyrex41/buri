# Spike 1: running code written at runtime, in Theorem's process model

Result: **passed for this one program.** Theorem's unmodified model can prove a
program that writes instructions and runs them, with no model extension. This says
nothing yet about Shen/JIT itself, whose emitter, runtime and GC are unproved.

Evidence kind: Rocq theorem, replayed with `rocqchk`, about Theorem's RISC-V and Linux
process model. It is not evidence about real hardware.

## What is proved

`omni_strong_universal` and `strong_universal` in `coq/Proof.v`, checked by the generated
`Checker.v` against Theorem's trusted statement. For every valid process input, stack
placement and launch, the source (which stores two instruction words in its own segment,
calls them, and exits with their result) has the same observable behavior as an ordinary
binary with immutable code: no output, exit 42.

The stores are what make this work. `image_arena_is_zero` shows the arena's bytes in the
image are zero, and `image_arena_word_illegal` shows that word doesn't decode.
`gen_fetch_addi` and `gen_fetch_ret` fetch the real instructions from the stores, for any
earlier memory.

## What is not proved

- **Cache coherence.** `step_fencei_wx` shows `fence.i` only advances the PC in this model,
  and any store is visible to the next fetch. So the theorem can't tell a correct program
  from one that omits the fence. Real hardware needs this as a separate obligation.
- **Executable `mmap`.** The arena is an ELF segment because the model doesn't model
  `PROT_EXEC` pages. This is a layout change from stock Shen/JIT.
- **Reusing arena memory.** Nothing here overwrites code that has already run. Shen/JIT's
  collector frees and reuses code memory, which needs its own invariant.
- **General code.** This is 12 fixed instructions plus 2 generated ones, stepped one at a
  time. Shen/JIT's generated code depends on its input, so the method must scale to a
  simulation over all emitted code. This spike doesn't show that it does.
- **Trust.** The result trusts the model, the Rocq kernel, and the snapshot tool that turns
  ELF files into memory images.

## Checks

| Check | Result |
|---|---|
| `dune build theories/Examples/jit_write_run_ns` | exit 0 |
| `rocqchk` on `Checker` | exit 0 |
| Theorem's assumption check, `check()` from `.github/check_assumptions.py`, on this example only | No errors; only `PrimInt63`, `PrimString` and `PrimArray` primitives appear |
| `Admitted` in the example | 0 |
| QEMU run of both binaries | exit 42 and 42 |

Five mutants were rejected by `mutate.sh`:

| Mutant | Failure |
|---|---|
| `wrong-generated-result` | `bveq` |
| `second-store-removed` | type error at the `exact`/apply step |
| `first-store-removed` | type error at the `exact`/apply step |
| `call-wrong-address` | `bveq` |
| `target-exits-43` | `bveq` |

A rejected mutant only shows that this proof script doesn't go through for that binary. It
isn't a proof that the mutant's statement is false. `bveq` reports a false closed goal as
"runaway-large", which is its timeout wording rather than a size problem I measured.

## Pins

| Item | Value |
|---|---|
| Model | `theorem-labs/rocq-linux-process-semantics` `5e13f6b0f82936aa5d006438e07e265c5d9fcfc4`, unmodified apart from adding this example and its `dune` stanza |
| Prover | Rocq 9.3.0, OCaml 5.2.1 |
| Assembler and linker | Ubuntu 24.04 `gcc-riscv64-linux-gnu`, flags in `build.sh` |
| Source binary SHA-256 | `67bc1dfaa4184d1972ff4ae79b961946df49a5c640c9027d6249862b200de1df` |
| Target binary SHA-256 | `3764ebc9166cb613fbe0ee981289fad3c23bcd68e00c311c7d88051c0380d6c8` |
| Source segment hex SHA-256 | `3073c4d68cca05543fb6c046b80867349656902c2c20e2121b59be1be2895cb4` |
| Target segment hex SHA-256 | `bd2c6b86908ff2f132e516995845363e61173011f399ccac7ba43ae17f18de41`, `b9d319081acf73c7e4d4cdd79d2b236b1564187c68de1f58cb0ba318abb98c39` |

Two builds are byte-identical once stripped. Before stripping, symbol-table contents
varied between builds.

## Cost

About 405 lines of proof by hand (`defs` 41, `source` 258, `target` 54, `Proof` 52). The
model and proof library took under an hour to build on 6 CPUs under heavy machine load.
The example compiles in seconds, and `rocqchk` took about 1.5 minutes. This is too small to
project a rate for the gate; spike 5 is the measurement for that.

## Reproduce

Inside a container set up by `setup.sh` (it expects the model clone at `/lps/src` and builds it at `/work`):

```sh
cp spikes/jit-in-model/coq/*.v /work/theories/Examples/jit_write_run_ns/
bash spikes/jit-in-model/build.sh
dune build theories/Examples/jit_write_run_ns
bash spikes/jit-in-model/mutate.sh
```

The `dune` stanza, a copy of `rwx_flag_ns`'s with the name changed and
`--source-text 0x10078:0x100a8`, must be added by hand. No script does that yet.
