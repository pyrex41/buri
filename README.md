# Búri

Machine-checked proofs that real implementations of [Shen](https://shenlanguage.org) run programs the way the
language says they should, down to the machine code that executes. AI agents write the proofs;
[Rocq](https://rocq-prover.org) checks every one, and an independent checker replays them. Nothing counts because an
agent says it is correct.

It is not a test suite. Tests show a program behaved on the inputs someone tried. A proof covers every input.

## Where it is

**No Shen implementation is verified yet.** The lead track is [Shen/JIT](https://github.com/tizoc/shen-jit), a small
native JIT whose exact RISC-V binary looks reachable. It is in Phase 2: proving that Shen/JIT's lowerer, which
compiles KLambda to bytecode, preserves meaning, by checking its output for all 955 kernel definitions.

| Shen/JIT, Phase 2 (`p2/int`, 12 Nov 2026) | |
|---|---|
| Pinned upstream | v0.6 (`934cfa5`), kernel 43.4; re-pin to v0.7 or later is next |
| Kernel definitions accepted by the source judge | 148 of 955 (not re-measured since the new checkers landed) |
| KRef fundamental property (the central lemma) | proved |
| Audited Shen/JIT statements | 915, no new axioms (counted; lane re-run pending) |
| Proof mutations that must be rejected | 306 |

The other tracks (Shen-Scheme on Chez, Shen-CL on SBCL, an Arm foundation) have narrower results. What each number
means, and what it does not, is in [STATUS](docs/STATUS.md) and [TRUST](docs/TRUST.md). The next piece of work is
laid out in [TODO.md](TODO.md).

## Run

```sh
make bootstrap   # pinned toolchain under .tools/, no sudo
make check       # Shen tests and all proofs
make report      # every gate, with hashes, into _build/report.json
```

`make check-shen-jit` runs the Shen/JIT lane (Rocq 9 proofs and the comparison with the pinned binary). It needs the
container from `spikes/jit-in-model/setup.sh` and the binary from `ports/shen-jit/build.sh`. Details and platforms
are in [BUILD](docs/BUILD.md).

## Reading on

| To learn | Read |
|---|---|
| What Búri aims for and how it works | [OVERVIEW](docs/OVERVIEW.md) |
| What is proved, tested or assumed right now | [STATUS](docs/STATUS.md), [TRUST](docs/TRUST.md) |
| The Shen/JIT track: scope, claim, results | [SHEN-JIT](docs/SHEN-JIT.md), [spikes/GATE.md](spikes/GATE.md) |
| Decisions taken, word for word | [docs/decisions/](docs/decisions/) |
| The whole plan and its ledgers | [END-TO-END-PLAN](docs/END-TO-END-PLAN.md), [spec/](spec/) |
| How to work on it | [AGENTS.md](AGENTS.md) |

## Bugs found upstream

Writing precise semantics finds real bugs. Of nine filed, eight are fixed.

| Project | Fixed | Open |
|---|---|---|
| Shen-Scheme | [#46](https://github.com/tizoc/shen-scheme/issues/46), [#47](https://github.com/tizoc/shen-scheme/issues/47), [#48](https://github.com/tizoc/shen-scheme/issues/48) | |
| Shen-CL | [#68](https://github.com/Shen-Language/shen-cl/issues/68), [#69](https://github.com/Shen-Language/shen-cl/issues/69) | [#70](https://github.com/Shen-Language/shen-cl/issues/70) |
| shen-sources | [#118](https://github.com/Shen-Language/shen-sources/issues/118) | |
| Shen/JIT | [#1](https://github.com/tizoc/shen-jit/issues/1), [#12](https://github.com/tizoc/shen-jit/issues/12) | |

## License

Third-party licences for the pinned implementations are in [LICENSES/](LICENSES/).
