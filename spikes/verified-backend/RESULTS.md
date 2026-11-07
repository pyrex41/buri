# Spike 10: a verified Shen on an off-the-shelf verified back end

**Question.** Is building a verified Shen on top of an existing verified compiler much cheaper than Búri's
current route? The current route proves the exact Shen/JIT binary, using a proved checker over the
RISC-V bytes it emits and a template for each opcode.

**Answer, in short.** Probably yes, but only on one route (CakeML) and only for a different claim. At my
high estimate the CakeML track is about 14 times smaller than the lowest floor of the current route's
projections, and about 5 times smaller if my estimate is 3 times too low. The current route's figures are
themselves floors. The claim becomes "a verified Shen binary"
rather than "the Shen/JIT binary is verified". It also rests on a different trusted base: HOL4, CakeML's
RISC-V ISA model and FFI oracle, and a HOL4-to-Rocq statement match.

What I measured on the CakeML route:

- **Front end.** Each construct costs about what Búri's Phase 2 costs. The saving lies entirely below
  the front end, because CakeML's back end, garbage collector and bignums are already proved.
- **Speed.** Kernel code compiled ahead of time this way ran about 5-12 times slower than Shen/JIT on one
  microbenchmark under QEMU with direct calls, and about 7-8 times slower in one run that called through
  redefinable function cells. That is a floor. User code reaching `eval-kl` would run either in an
  interpreter whose speed I didn't measure (UNKNOWN), or at compiled speed after about 22 ms per
  definition with CakeML's `Eval` on x64.
- **Runtime eval.** CakeML's runtime compilation (`Eval`) is implemented only for x64 today, so `eval-kl`
  on RISC-V is the open problem on this route.

CertiRocq, Bedrock2 and CompCert with VST don't give that saving today. See
[Judgment](#part-3-judgment).

Nothing here verifies any Shen. Evidence kinds are labelled: **measured** (run here, at the stated
commit), **read** (from a primary source, cited), or **projected** (arithmetic on measured or read
numbers). Nothing was run on RISC-V hardware.

## Part 1: facts from primary sources

Repository facts are as of 7 November 2026, at the commits named. Paper facts are as published.

### CakeML

| Fact | Status | Source |
|---|---|---|
| Release v3479 (26 August 2026), built on HOL `trindemossen-2-v6` = `a390cba`. Master is active: `79f649e`, 6 November 2026. Recent releases: v3304 (April), v3400 (June), v3479 (August) | Read | [releases](https://github.com/CakeML/cakeml/releases/tag/v3479) |
| BSD 3-Clause licence. HOL4 also uses a BSD-style licence | Read | `LICENSE` in each repo |
| **RISC-V 64 target.** `compiler/encoders/riscv` proves `riscv_encoder_correct` and `target_ok riscv_target` against HOL4's **L3-derived** RISC-V model (`examples/l3-machine-code/riscv`), with `riscv_ok`: virtual memory off, an old privileged-spec CSR layout (`mcpuid`, `mstatus.VM`). `compiler/backend/riscv/proofs` proves `riscv_backend_config_ok`, `riscv_machine_config_ok`, `riscv_init_ok`, and instantiates the generic `compile_correct` as `riscv_compile_correct` | Read, at `e8eca63` | those files |
| **The compiler's own binary is verified, but not on RISC-V.** Bootstrapped binaries come with end-to-end theorems (`cake_compiled_thm`) for **x64, arm8 and ag32 only**. `compiler/bootstrap/compilation/` has no `riscv` directory, and the release ships `cake-x64-64`, `cake-x64-32` and `cake-arm8-64` | Read | `compiler/bootstrap/compilation/`, release assets |
| Running the verified arm8 `cake` with `--target=riscv` gives RISC-V code. I found no packaged theorem for that composition: the arm8 binary's theorem, plus `compile_correct` (`compiler/proofs`), plus the RISC-V config lemmas. It looks composable, but **I did not check it**. The covered path today is in-logic compilation, as the Scheme front end's theorem does (below) | Read; composition UNKNOWN | as above |
| The exported `.S` gives the code as `.byte` directives (6,492 lines in my benchmark), plus a small hand-written preamble and FFI glue. So `gcc`/`as` only place bytes. `basis_ffi.c` is unverified C | Measured | `exp/bench-riscv.S` |
| **Verified GC.** The collector is written in the compiler's own intermediate languages and verified as part of the compiler proof. It is copying, with a non-generational Cheney default and an optional generational collector (`--gc=genN`) | Read | `compiler/backend/gc`; `cake --help` |
| The top-level theorem is `machine_sem mc ffi ms ⊆ extend_with_resource_limit (semantics ...)`. Its premises include `installed bytes ...` (the loader put the bytes and data where expected) and an FFI oracle | Read | `compiler/proofs/compilerProofScript.sml` |
| **Runtime eval (`Eval`).** Sewell et al., "Cakes That Bake Cakes: Dynamic Computation in CakeML", PLDI 2023 (PACMPL 7, [doi:10.1145/3591266](https://doi.org/10.1145/3591266)). The paper says: "Eval is currently only supported on a small subset of CakeML target architectures (x64) and operating systems (Linux-based)". It also says "permissions and caches are not modeled in CakeML's target memory model, so their implementations are not verified", that code added at run time is never reclaimed, and that the code buffer must be RWX. The release Makefile still says "At present, EVAL is only supported on Linux + x64". The generic theorem `compile_correct_eval` (in `backendProof`) isn't tied to x64. The arm8 bootstrap theorem instantiates it with `compile_inc_progs_for_eval arm8_config`. No build glue for RISC-V exists | Read | paper §1, §4.2.4; `Makefile`; `backendProofScript.sml:4486`; `arm8BootstrapProofScript.sml` |
| Candle uses `Eval` for a verified REPL: Abrahamsson, Myreen, Kumar, Sewell, ITP 2022 (LIPIcs 237), and JAR 69(4) 2025, [doi:10.1007/s10817-025-09743-8](https://doi.org/10.1007/s10817-025-09743-8). In the Cakes paper's test, loading Candle's basis took 4,356 `Eval`s in 98 s on an x86-64 i7-7700K, about 22 ms per `Eval`. HOL Light itself took 74.94 s | Read | paper §6 |
| Scale: "over 320,000 lines", of which the compiler is "over 220,000". A full build is "~20 hours" and "~16 GB" RAM | Read | paper §5; `build-instructions.sh` |
| **A verified Lisp-like front end already exists.** `compiler/scheme` is a Scheme-to-CakeML compiler (CPS, with a tagged value type including `call/cc`). Its theorem `scheme_to_machine_code_value_terminates` and two siblings take a Scheme program's semantics down to `machine_sem`, for any target whose config is ok. It is mostly one author (Pascal Lasnier), December 2024 to December 2025, with 164 commits on 62 distinct commit days | Read, at `e8eca63` | `compiler/scheme/proofs/scheme_to_machine_code_correctScript.sml`; `git log` |
| CakeML evaluates right to left; KLambda evaluates left to right | Read | `how-to.md` |

### Bedrock2 (mit-plv)

| Fact | Status | Source |
|---|---|---|
| A C-like language whose only data type is the machine word, with a program logic and a verified compiler to bare-metal RISC-V (`riscv-coq`). There are end-to-end theorems to the Kami processor for the IoT lightbulb demo | Read | [README](https://github.com/mit-plv/bedrock2) at `757f17c` (21 September 2026) |
| The README states as a design decision that function pointers, recursive functions ("we might add them later") and non-terminating programs (except the top-level loop) are not supported. **No GC, no runtime and no dynamic memory management** | Read | README |
| Rocq 9.2 and master in CI. MIT licence. Last release v0.0.9 (October 2025). Rupicola (MIT, active) compiles Gallina to Bedrock2 relationally, one program at a time, also without a GC | Read | `.github/workflows`; [rupicola](https://github.com/mit-plv/rupicola) |

### CertiCoq, now CertiRocq

| Fact | Status | Source |
|---|---|---|
| Renamed CertiRocq. Release `v0.9.1+9.1` (18 March 2026) for **Rocq 9.1**; main `943b52a` (3 November 2026). `rocq-certirocq.opam` pins `coq >= 9.1 & < 9.2~`, CompCert 3.17, MetaRocq (an unreleased `9.1` branch, per `INSTALL.md`) and WasmCert. MIT licence | Read | [repo](https://github.com/CertiRocq/certirocq) |
| Targets Clight (then any C compiler, or CompCert) and WebAssembly | Read | README |
| **The end-to-end proof is incomplete.** The composed theorem in `theories/Compiler/correctness.v`, `metarocq_to_anf_correct`, ends at **λANF**, not Clight. `metarocq_anf_pipeline` there is `Admitted`, with 3 more `admit`s. `theories/Codegen/LambdaANF_to_Clight_correct.v` has 5 `Admitted` and 20 `admit`. `toplevel_theorems.v` has 1 `Admitted` and `LambdaANF_to_Clight.v` has 1. I found no theorem in the repo that composes erasure, λANF, Clight and CompCert | Measured by grep, at `943b52a` | those files |
| **GC.** The runtime collector `runtime/gc_stack.c` is C. CertiGraph's `CertiGC` verifies a `gc_stack.c` in VST, at CertiGraph `38e6429` (5 November 2026). **These are not the same file**: they differ in non-comment code, including `forward_remset`. So the GC CertiRocq ships isn't the verified one at these commits | Measured (diff) | `CertiGraph/CertiGC/GC_Source/gc_stack.c` and `certirocq/runtime/gc_stack.c` |
| Primitive ints, floats and strings are supported. An "unverified" GMP binding for `nat` was added in 0.9.1 | Read | release notes; `correctness.v` |
| Rocq compatibility: Búri's `Observation`, `KLSyntax`, `KLValue` and `KLSemantics` compile unchanged under Rocq **9.1.1**, apart from the usual `Coq`→`Stdlib` import rewrite. They took 1, 6, 1 and 1 s. There is no CertiRocq for Coq 8.18 or Rocq 9.3: the previous release, `v0.9+8.19`, is for 8.19 | Measured / read | `buri-vb-certirocq` |

### CompCert with a VST-proved interpreter

| Fact | Status | Source |
|---|---|---|
| CompCert v3.18 (30 August 2026) has a RISC-V back end (`riscV/`). Its theorem is down to its own `Asm` semantics; the assembler and linker are outside it | Read | [repo](https://github.com/AbsInt/CompCert) |
| **Licence:** "INRIA Non-Commercial License Agreement ... for educational, research or evaluation purposes only, but prohibits any commercial use"; commercial use needs an AbsInt Software Usage Agreement. Only some files (`lib/`, `common/`, parts of `cfrontend/` including `Clight.v`, `cparser/`) are also LGPL | Read | `LICENSE` |
| VST: the opam distribution is BSD-2. Latest v2.17 (September 2026), plus 3.x betas | Read | VST `LICENSE` |
| The route needs a KLambda interpreter and GC written in C, proved in VST against `KLSemantics`, then compiled by CompCert. All of it is in Rocq, so no cross-prover boundary. But every line of the runtime and GC is a new VST proof | Read / judgment | |

### Other verified compilers for Lisp-like or dynamically typed languages

| System | Target | State | Source |
|---|---|---|---|
| CakeML Scheme front end | Any CakeML target, RISC-V included | Active; see above | `compiler/scheme` |
| Jitawa (Myreen and Davis, ITP 2011): a verified Lisp runtime with a JIT and a copying GC, about 7,500 lines of machine code. It hosts Milawa, proved sound to machine code (JAR 2015) | **x86 only** | Not maintained, as far as I can tell (UNKNOWN). It is the closest precedent for proving a JIT's machine code, which is Búri's current route | [project page](https://www.cl.cam.ac.uk/~mom22/jitawa/), [ITP talk](https://www.cl.cam.ac.uk/~mom22/talks/2011-itp-jitawa-talk.pdf) |
| PureCake (lazy, Haskell-like, to CakeML) | Via CakeML | Statically typed, so not a fit | CakeML ecosystem |
| CertiRocq's verified Wasm back end | Wasm | Not RISC-V | release notes |
| I found none that targets RISC-V without going through CakeML | | | |

## Part 2: the capped experiment

### Definitions chosen

All are in stage 0's accepted set at 0.4. The decoded names come from the stage 0 run's logs in
`buri-lps:/tmp/p4/s0`, and the counts match `tests/shen-jit/stage0-accepted.txt`. Bodies are from
`/lps/p4/sj/build/stage0/*.forms`, renamed `vb.*` so they don't collide with sealed kernel names.

| Definition | Covers |
|---|---|
| `shen.magless` | `let`, `if`, `*`, `>`, self tail call |
| `shen-jit.lower.size` | `cond`, `cons?`, `hd`, `tl`, `+`, two non-tail recursive calls |
| `shen.abs` | `if`, `>`, `-` |
| `shen.digit?` | `and`, `>=`, `<=` |
| `reverse` and `length`, with `shen.reverse-help` and `shen.length-h` | a call that is a tail call to another function, `cond`, `=` on `()`, `cons`, `simple-error` |

The helpers aren't in the accepted set: they use `=` and `simple-error`. A driver (`exp/driver.kl`) builds
a 1,024-leaf tree and a 200-element list on every iteration and sums all six results.

### Route 1: KLambda translated to CakeML source, compiled by the verified compiler

`exp/kl2cml.py` is an **unverified** prototype of the code generator this route would prove, shaped like
CakeML's verified `scheme_to_cake`. It uses one tagged type
`datatype kv = KInt int | KSym string | KStr string | KBool bool | KNil | KCons kv kv` and an exception
`KlErr`. Each primitive is a checked CakeML function. Each `defun` becomes a CakeML function in one
`fun ... and ...` group. Arguments that aren't atoms are bound left to right with `let val`, so CakeML's
right-to-left order is never observable.

**Profile.** This prototype refines neither `agreed_rules` nor `jit_rules` exactly. Integers are CakeML
bignums, as in `agreed_rules` and unlike `jit_rules`' 62-bit range. Calls are direct, which assumes
Phase 2's FunRel premise and no redefinition. Under-application raises `"arity"`, where
`KLSemantics.call_named` returns `VPartial`. A real track would fix a `cake_rules` instance of `KLPort`'s
options.

**Measured:**

| Step | Result |
|---|---|
| Tool setup | Downloading and building `cake` from `cake-arm8-64.tar.gz` (SHA-256 `07aa0156...be99a`) on the macOS arm64 host took 12 s. The bootstrapped binary carries arm8's `cake_compiled_thm`, but that theorem covers the arm8 Linux machine, not macOS |
| Compile, KLambda to CakeML to RISC-V | `kl2cml` under 0.1 s, `cake --target=riscv` 0.8 s, `.S` 601 KB. Linked with `zig cc` (riscv64-linux-musl) and the release's `basis_ffi.c` |
| Agreement | Every program that ran gave the same results, wherever two of them were run at the same n: 536872138 at n=1, 5368721425 at n=10, 53687218750 at n=100, 107374447500 at n=200, 268436193750 at n=500, 1073746275000 at n=2000 and 1610620912500 at n=3000. The programs were the CakeML binary, the pinned Shen/JIT binary (SHA-256 `5eb9f433...51872`), Búri's `KLSemantics.next` under `vm_compute` (n=1, 10, 100) and its CertiRocq build (n=10). This is sampled agreement, not proof |

**Speed.** Timings use `qemu-riscv64` user mode in `buri-lps`. Each figure is the minimum of 7 runs for the
n=200/2000 pair and of 5 for the n=500/3000 pair, with the CertiRocq build container paused (`docker
pause`; the HOL container was idle). The slope is the time per extra iteration between the two n, so
start-up cancels out:

| Binary | n=200 | n=2000 | Slope (ms/iter) | n=500 | n=3000 | Slope (ms/iter) |
|---|---|---|---|---|---|---|
| Shen/JIT 0.4, named build | 82 | 527 | 0.247 | 106 | 418 | 0.125 |
| CakeML, as translated | 101 | 2,793 | 1.496 | 455 | 4,359 | 1.562 |
| CakeML, first-order arithmetic (`KL2CML_FO=1`) | 93 | 2,882 | 1.549 | 440 | 4,194 | 1.502 |
| CakeML, `--gc=gen5000` | 119 | 3,502 | 1.879 | 738 | 5,951 | 2.085 |
| CakeML, first-order and `--gc=gen5000` | 110 | 2,967 | 1.587 | 679 | 4,955 | 1.710 |

A second session on an idle machine (load average 0.19), adding a variant that makes every named call
through a mutable function cell (`KL2CML_CELLS=1`), as KLambda's redefinable function namespace needs:

| Binary | n=200 | n=2000 | Slope (ms/iter) | n=500 | n=3000 | Slope (ms/iter) |
|---|---|---|---|---|---|---|
| Shen/JIT 0.4, named build | 82 | 563 | 0.267 | 107 | 848 | 0.296 |
| CakeML, as translated | 100 | 2,611 | 1.395 | 442 | 4,096 | 1.462 |
| CakeML, function cells | 207 | 3,845 | 2.021 | 727 | 5,819 | 2.037 |

All times are in ms. **On steady-state slope, CakeML's code is about 5 to 12 times slower than Shen/JIT on
this benchmark with direct calls, and about 7 to 8 times slower through function cells in the one session
that measured both.** The range comes from Shen/JIT's own variation: its slope was 0.125 to 0.296 across
the four pairs, while CakeML's held at 1.4 to 1.6. Notes:

- The first-order variant and the generational collector don't close the gap, so it isn't my
  translation's use of closures in arithmetic.
- CakeML shows an unexplained knee. Up to about n=200 it runs at about 0.5 ms per iteration, then about
  1.5. Heap size (`CML_HEAP_SIZE` 8, 64 and the default) didn't move it. I didn't find the cause.
- Both programs ran under QEMU user mode on an arm64 host. QEMU may penalize self-modifying JIT code
  differently from static code. This is one microbenchmark; no hardware run.
- Earlier runs, made while the HOL and CertiRocq builds were using about 9 of the 10 CPUs, gave
  similar CakeML slopes and noisier Shen/JIT ones. I discarded them.

### Route 2: Búri's own semantics compiled by CertiRocq

`exp/kl2rocq.py` writes a Rocq file. It loads the same KLambda forms as `KLValue` data, turns them into
syntax with `KLSemantics.parse` (as `eval-kl` does), and drives `KLSemantics.next` with a fuel of 2^40
steps. Since the interpreter **is** Búri's specification, `eval-kl` comes free. If CertiRocq's theorem
were complete, the result would be a binary proved to refine `KLSemantics` with no statement match
at all.

**Measured** in `buri-vb-certirocq`, a fresh `ubuntu:24.04` arm64 container. The C was compiled natively
with `gcc -O2`, **not** for RISC-V and not under QEMU:

| Step | Result |
|---|---|
| Setup | `opam install --deps-only`, which builds Rocq 9.1.1, MetaRocq, CompCert 3.17 and WasmCert: 1 h 13 min. `make -j10` (theories): 24 min 37 s. `make plugin`: 25 s. About 1 h 40 min in all, with no failures |
| Búri sources under Rocq 9.1.1 | `Observation`, `KLSyntax`, `KLValue` and `KLSemantics` compile unchanged, apart from the import rewrite |
| CertiRocq compile, n=10 | 54 s for `rocq compile` with `CertiRocq Compile result`, giving 4.1 MB of C. Then 13 s of `gcc` |
| CertiRocq compile, n=100 | 293 s, with the same 4.1 MB of C, on two runs on a quiet machine. The compile time depends on the input constant, which suggests compile-time evaluation in the pipeline. I didn't find the cause |
| CertiRocq compile, 1,000 extra definitions (`exp/pad1000.kl`) | With the default stack, `Error: Stack overflow.` at `CertiRocq Compile`. With `ulimit -s unlimited`, it hadn't finished after **30 minutes** (1.7 GB) and I stopped it. **Blocked** at this cap. So a kernel-sized store hasn't been compiled by CertiRocq |
| Result | n=10 gave `5368721425`, decoded from the printed `positive`, the same as every other run |
| Run time | n=10: 137-233 ms. n=100: 2,995-3,372 ms. Slope about 32 ms per iteration, native arm64 |

So CertiRocq's code runs about 11 times faster than `vm_compute` on the same specification. Even natively,
it is about **130 to 260 times slower than Shen/JIT running under QEMU emulation**, and the true gap on
equal footing is larger. That is with a store of 26 functions. With about 1,000, `vm_compute` became
86 times slower again (below), and I couldn't compile that case at all.

**Speed of the specification as an interpreter.** Measured under `vm_compute` on Rocq 9.3, native arm64,
as an upper bound on what any faithful compilation of `next` gives:

| Store | Per iteration | vs Shen/JIT under QEMU |
|---|---|---|
| The 12 test functions and 14 primitive entries | 0.36 s (n=1 0.36 s, n=10 3.6 s, n=100 38 s) | about 2,500 times slower |
| The same, plus 1,000 dummy `defun`s, as the real kernel has about 1,000 | 31 s (n=1) | about 200,000 times slower |

The cause is the specification's representation. `call_named` scans `gfuns`, an association list,
comparing names as `list N` with `text_eqb`, on every call, primitive calls included. Environments are
association lists, and `Z` is binary `positive`. CertiRocq keeps these as boxed inductives, unless you use
its unverified GMP binding. An interpreter fast enough to use would be a new program, proved to refine
`KLSemantics`, and writing that proof is the same per-construct work as any other route.

### Route 1's proof cost

**What exists to compare against (measured line counts, CakeML `e8eca63`):**

| Scheme front end | Lines |
|---|---|
| AST, values, semantics (`scheme_ast`, `scheme_values`, `scheme_semantics`) | 666 |
| Code generator and basis glue (`scheme_to_cake`, `scheme_compiler`) | 556 |
| Semantic properties (`scheme_semanticsProps`) | 992 |
| Simulation proof (`scheme_to_cakeProof`) | 2,479 |
| &nbsp;&nbsp;infrastructure: environments, value and continuation relations, `letrec` initialisation (lines 1-844) | about 845 |
| &nbsp;&nbsp;`application_preservation`: procedures, 10 primitives, `call/cc` and throw (845-1649) | about 805 |
| &nbsp;&nbsp;`step_preservation`: the 9 expression forms and continuations (1686-2142) | about 457 |
| &nbsp;&nbsp;multi-step, termination, exceptions, divergence (2143-2479) | about 336 |
| Top level and machine code (`scheme_compileCorrect`, `scheme_to_machine_code_correct`, `scheme_to_cake_env`) | 745 |
| **Total** | **5,758** |

That is about 19 constructs (9 forms and 10 primitives) for about 4,200 lines of proof: about 66 lines per
construct for the core cases, or about 220 with infrastructure. Búri's Phase 2 cost 100-400 lines per
construct, and about 600 for calls and tail calls. So **the front end costs about the same per construct
on both routes**. The difference lies entirely below the front end.

### A first rung of the proof, measured

`hol/klfragScript.sml` is a self-contained HOL4 theory over CakeML v3479's `semantics`:

- a KLambda fragment with integer and boolean literals, variables, `if`, `let` and `+`;
- a left-to-right big-step semantics for it;
- a code generator to CakeML AST over a tagged type `KI | KB` and an exception `KlErr`, shaped like
  `kl2cml`;
- **`cg_correct`.** For every expression, environment and CakeML state: if the source result isn't
  stuck, the variables avoid four reserved names, the constructor environment declares the type, and the
  environments are related, then CakeML's own `evaluate` returns the same state together with a related
  value, or raises the related exception.

Holmake reports it `OK` (not `CHEATED`). Its tags are only `DISK_THM`.

| Measure | Value |
|---|---|
| Lines | 197 in all: syntax and semantics 32, code generator 32, relations and side conditions 42, proof and 2 helper lemmas 67 |
| Per construct | 6 constructs, about 11 proof lines each, about 33 with everything |
| Effort | About 30 minutes of interactive work, 6 debugging rounds through a saved-heap REPL (`hol/dbg.sh`) |
| Check time | 40 s wall, 0.78 GB, for `Holmake` of the theory, mostly loading CakeML's semantics |

**What this rung leaves out, which is most of the work:**

- calls, tail calls and the clock;
- closures and partial application;
- `trap-error`, the store and `set`/`value`;
- the remaining primitives;
- `eval-kl`;
- the relation to `rocq/KLSemantics.v` itself.

It is cheap because none of the hard parts are in it. Phase 2 spent half its step proof on calls and tail
calls, and the Scheme proof spends 805 lines on application. Read it as "the HOL and CakeML machinery
works at Búri's rate for easy constructs", not as a rate for the whole front end.

| Setup step, measured | Wall time |
|---|---|
| Poly/ML 5.9.1 and HOL `a390cba`, `bin/build`, fresh `ubuntu:24.04` arm64 container | 42 min (HOL alone 33 min 6 s, 1.8 GB peak) |
| CakeML `e8eca63`: `Holmake scheme_to_cakeProofTheory scheme_compileCorrectTheory` and their dependencies (semantics, its proofs, part of basis) | 17 min 43 s, 2.1 GB peak. `scheme_to_cakeProof` alone took 497 s |
| Not built: `backendProof` and the bootstrap, which the in-logic compilation theorem needs | The paper and build notes give about 20 h and 16 GB |

## Part 3: judgment

### The routes, side by side

| | Current route: prove the exact Shen/JIT binary | CakeML (KLambda compiled to CakeML) | CertiRocq (`KLSemantics` as an interpreter) | Bedrock2 | CompCert with a VST interpreter |
|---|---|---|---|---|---|
| What is verified | The named Shen/JIT binary | A new Shen binary | A new Shen binary | n/a | A new Shen binary |
| Back end, GC, bignums | To prove: emitter checker, runtime, GC | **Already proved** | Partly proved: λANF stage done, Clight stage with `Admitted`, GC not the shipped file | No GC or runtime | CompCert proved. GC and runtime are new VST proofs |
| Spec link to `KLSemantics` | Native Rocq | HOL4 copy plus a statement match | **Native: the spec is the program** | Native Rocq | Native Rocq |
| Machine model | Theorem's Linux/RV64GC process model | CakeML's L3 RISC-V, `installed`, FFI oracle | CompCert `Asm`, unconnected | `riscv-coq` | CompCert `Asm` |
| Speed vs Shen/JIT | 1× | Compiled kernel code about 5-12× slower (7-8× with function cells), measured. User code through `eval-kl`: UNKNOWN under option (b) | CertiRocq build: about 130-260× slower, measured, natively against Shen/JIT under QEMU, with 26 functions. With 1,000 functions it wouldn't compile within 30 min. `vm_compute`: 2,500× to 200,000× | n/a | Unknown |
| `eval-kl` | The JIT, which needs the lowerer proof or the checker | Unsolved on RISC-V (below) | Free | n/a | Free (interpreter) |
| Licence | Shen/JIT and kernel BSD | BSD-3 (CakeML), HOL4 BSD-style | MIT, but CompCert non-commercial if used | MIT | **CompCert non-commercial** |

### How `eval-kl` would work

- **CakeML route, three options.**
  - (a) **CakeML `Eval`.** The binary carries the KLambda-to-CakeML code generator, the CakeML compiler
    (bootstrapped, as Candle's REPL does) and the compiled kernel. `eval-kl` generates CakeML AST and
    calls `Eval`. `compile_correct_eval` is generic, but `Eval` runs only on x64 Linux today. A RISC-V port
    needs code-buffer glue, RWX memory and `fence.i` cache maintenance, and the paper says that part is
    unverified even on x64. Code added at run time is never reclaimed. Latency is about 22 ms per `Eval`
    on x64, from Candle's figure.
  - (b) **A verified KLambda interpreter inside the binary, for code that arrives through `eval-kl`.**
    It would be written in HOL4 and turned into CakeML by the proof-producing translator. The kernel stays
    compiled ahead of time. This avoids `Eval` and its unverified cache flush, but code passed to `eval-kl`
    then runs at interpreter speed. Shen's `eval`, `load` and `define` all go through `eval-kl`, so most
    user programs would be interpreted.
  - (c) Ahead-of-time compilation of the whole program, with no runtime `eval-kl`. That isn't Shen.

  I'd try (b) first for a verified result and treat (a) as a performance upgrade.
- **CertiRocq route.** `rule_eval_kl` parses data into syntax inside the specification, so `eval-kl` is
  just another step. That is this route's one real advantage.
- **The current route.** Runtime lowering needs either the general proof over `lower.shen`
  (`OB-JIT-LOWER-GENERAL`, not estimated) or the Phase 2 checker run on every lowering and proved at
  binary level. Then the emitter checker and the checker's own C binary are also on the path.

### Joining Búri's Rocq specification and Theorem's model

- **CakeML.** The theorem lives in HOL4, about `machine_sem` on CakeML's machine. It states refinement
  as a set of behaviours under `extend_with_resource_limit`. Joining Búri needs three things:
  1. **A HOL4 copy of `KLSemantics`** and what it uses: 1,116 lines of Rocq across `Observation`,
     `KLSyntax`, `KLValue` and `KLSemantics`. Then
     a **trusted statement match**: a written argument, or a mechanical translation that both sides
     check, that the copy equals `rocq/KLSemantics.v` under one port profile, and that CakeML's
     `extend_with_resource_limit` matches `Observation.v`'s `refines_res`. No HOL4-to-Rocq tool does
     this today; I'd treat it as a reviewed trusted step and keep it small.
  2. **The machine model.** CakeML's bottom is the L3-derived RISC-V model, with virtual memory off and
     an old privileged-spec CSR layout. The program is placed by an `installed` premise, and system
     calls go through a C FFI (`basis_ffi.c`, unverified) modelled by an oracle. None of that is
     Theorem's Linux process model. Either accept CakeML's model as the trusted bottom for this track,
     which is a weaker claim than the zlib-style one in `docs/SHEN-JIT.md`, or prove correspondences:
     the L3 model against Theorem's RV64 semantics for the instructions CakeML emits, ELF load against
     `installed`, and each FFI entry point against Linux system calls. That second option is a project
     of its own and I haven't estimated it.
  3. **IO.** Búri's request/response IO and CakeML's basis file-system oracle would need a relation for
     streams, `open`, `close`, `read-byte`, `write-byte` and `get-time`.
- **CertiRocq.** Native Rocq, so `KLSemantics` and `refines_res` join directly. But there is no complete
  theorem to join. The end-to-end composition stops at λANF, Clight has `Admitted` lemmas, and CompCert's
  `Asm` isn't Theorem's model either.

### Expected slowdown against Shen/JIT

- **CakeML, compiled ahead of time:** about 5-12× with direct calls, and 7-8× through function cells
  (one session), on the one microbenchmark measured (`let`, `if`, `cond`, arithmetic, pairs, calls),
  under QEMU user mode. **That is a floor for kernel code.** The prototype still leaves out `VPartial` and
  a 62-bit range check, if the profile wants one.
- **User code, which arrives through `eval`, `define` and `load`:** under option (b) it runs in the
  verified interpreter, whose speed is UNKNOWN. Under option (a) it runs at compiled speed after about
  22 ms per definition, from the x64 figure, once `Eval` exists on RISC-V.
- **CertiRocq or any faithful interpreter of `KLSemantics`:** the CertiRocq build was about 130-260×
  slower with 26 functions. That figure is native arm64 against Shen/JIT under QEMU, so the real gap is
  larger. Under `vm_compute` the gap was 2,500× with 26 functions and 200,000× with 1,000. A fast
  interpreter would be a new program needing its own proof.

### Shen-specific pieces that remain to prove on either route

Neither back end gives these:

- **Value encoding.** The tagged type, symbols as interned values, strings, vectors (`absvector`),
  streams, exceptions as values, closures and `VPartial`.
- **Primitives.** On a new-binary route, the target is KLambda's primitive set: 36 in Búri's
  `KLSyntax.prim`, not Shen/JIT's 120. Shen/JIT's extra `shen-jit.*` primitives exist only because its
  kernel port uses them, and a CakeML Shen would run the standard kernel KLambda. Each primitive needs a
  CakeML implementation and a case in the simulation. By the Scheme proof's rate (805 lines for
  application of 10 primitives plus procedures and `call/cc`), that is perhaps 40-120 lines each.
  Floats need binary64. CakeML has `Double`/`Float64` with HOL4 IEEE semantics, and Búri's profile leaves
  inexact arithmetic as a parameter, so this is a profile choice, not a gap.
- **Errors.** `simple-error`, `trap-error`, and system errors with messages.
- **Arity and partial application.** Under-application gives `VPartial`, over-application applies the
  result, and arity errors follow the profile.
- **Global function cells and redefinition** (`defun` at run time), `set` and `value`, and the
  `do`/`thaw` conventions.
- **Equality.** `=`, including cyclic and deep structures. `OB-JIT-NAN-IDENTITY` doesn't arise if the
  new binary's profile gives reals identity.
- **The kernel image.** Compiling the standard kernel's roughly 1,000 definitions ahead of time, and
  relating the initialised store to `KLSemantics`' store after initialisation.

On the current route the same list applies. In addition, the lowerer's rewrites (inlining, folding,
goto labels, the one-slot `cons` chain), which keep 897 of 950 stage 0 definitions out of the Phase 2
relation, all need proofs. **A new-binary route translates the kernel's KLambda directly and has no
optimizing lowerer to validate, so those rewrites drop out entirely.**

### Cost, projected from measured inputs only

Every figure here is a projection. Lines are hand-written proof and definition lines.

| CakeML track item | Basis | Lines |
|---|---|---|
| HOL4 copy of `KLSemantics` and what it uses, statement-match document, profile choice | 1,116 lines of Rocq to copy: `Observation` 399, `KLSyntax` 116, `KLValue` 214, `KLSemantics` 387. Part of `Observation` is generic behaviour/refinement machinery that CakeML's semantics already has in its own form | 1.5k-3k |
| Code generator and simulation for all KLambda forms: calls and tail calls with the clock, closures, partial application, `trap-error`, store, `defun` | Scheme: about 4.2k lines of proof for 19 constructs including `call/cc`. Phase 2: 100-400 lines per construct, 600 for calls. Rung 1 above: about 11 per easy construct | 6k-12k |
| 36 primitives, value encoding, equality | 40-120 per primitive, plus the encoding | 3k-7k |
| IO relation (FFI oracle to Búri's request/response) | No direct sample; judgment | 2k-5k |
| `eval-kl` by option (b): an interpreter in HOL4, translated, and its simulation | About the same as the code generator again | 5k-10k |
| Kernel image, initialisation, top-level composition (as in `scheme_to_machine_code_correct`) | Scheme: 745 lines for composition; plus the kernel | 2k-4k |
| **Total** | | **about 20k-41k lines** |

Against this, the current route's own projections, all floors and all from earlier spikes:

- runtime alone: 490k-1.7M lines (spike 5);
- emitter checker: 41k-124k (spike 7);
- the checker's C binary: 40k-89k;
- plus function-level layout, emitter memory safety, the lowerer, and the image, none of them estimated.

The current route's lowest floor is about 571k lines (490k + 41k + 40k). Against my high estimate of 41k,
the CakeML track is about 14 times smaller. If my estimate is 3 times too low (123k), it is about 5 times
smaller. Those current-route figures are floors that leave out the unestimated items. The difference is
exactly what CakeML has already proved: the back end, GC, register allocation and bignums.
Machine time is real but bounded: about 1 h to set up HOL4 and the needed CakeML theories, about 20 h
once for `backendProof` and the bootstrap, and the in-logic compilation of a kernel-sized program
(UNKNOWN; the Scheme theorem takes `compile ... = SOME` as a premise).

### Licensing

| Component | Licence | Note |
|---|---|---|
| CakeML | BSD-3-Clause | Compatible with Búri and with the kernel's BSD licence |
| HOL4 | BSD-style | |
| CertiRocq, MetaRocq, Bedrock2, Rupicola, CertiGraph | MIT | |
| VST | BSD-2 (opam distribution) | |
| CompCert | INRIA Non-Commercial, or a paid AbsInt licence | Blocks commercial use unless licensed. Some files (`Clight.v` and more) are also LGPL. This matters for CertiRocq too, if it is linked through CompCert |
| Theorem's process model | MIT | |

### Recommendation

**Go on a small parallel CakeML track, with a gate. No-go on CertiRocq, Bedrock2 and CompCert with VST as
the verified back end today.**

- **Why go.** The measured front-end cost per construct matches Phase 2's, and everything below the front
  end, which dominates the current route's projections, is already proved in CakeML. One easy rung was
  proved here in 30 minutes. The measured speed is a floor for compiled kernel code only. There is a direct precedent: a verified Scheme front end to machine code,
  roughly one person-year by its commit history.
- **What it changes.** The claim becomes "a verified Shen binary": a new implementation, not Shen/JIT.
  README says Búri aims at "real implementations", so that is Reuben's call, not a technical one. The
  trusted base gains HOL4, CakeML's machine model, `basis_ffi.c` and a statement match. It loses
  Theorem's Linux model unless the model correspondence is funded.
- **Why not CertiRocq.** Its composed theorem stops at λANF, with `Admitted` lemmas in the Clight stage.
  The shipped GC isn't the verified one. Its build of `KLSemantics` ran 130-260 times slower than Shen/JIT with 26 functions, even with that
  comparison tilted in its favour, and wouldn't compile with 1,000 functions within 30 minutes.
  It is tied to Rocq 9.1 exactly. Its native Rocq link and free `eval-kl` are real advantages, worth
  revisiting if CertiRocq's Clight proof closes.
- **Why not Bedrock2.** It has no GC, recursion or dynamic memory, so everything Búri would need stays
  to be proved.
- **Why not CompCert with VST.** The GC and the interpreter would be new VST proofs, at per-line rates
  like the current route's, and the licence is non-commercial.

**Proposed gate (about 2-3 agent-weeks, projected).**

1. A HOL4 copy of the Phase 2 fragment of `KLSemantics`, with calls and tail calls, the clock and arity
   errors.
2. A code generator and simulation proof for exactly the Phase 2 fragment, with in-logic compilation of
   the 53 accepted stage 0 definitions to RISC-V through `compile_correct`.
3. A written statement-match argument for that fragment.
4. One run of the result under QEMU against Shen/JIT on the same definitions.

**Infrastructure risk in step 2.** In-logic compilation needs `backendProof` built, which the build notes
put at about 20 h and 16 GB. This machine's Docker VM has 16 GB in total, shared with other agents, so step
2 may need a bigger host. The fallback is the verified arm8 `cake` with `--target=riscv`; discharging the
composition marked UNKNOWN in Part 1 would then be part of the gate.

Fund the full track only if calls and tail calls come in under about 1,000 lines and the in-logic
compilation of those 53 definitions finishes in hours, not days. `eval-kl` stays the main open design
risk. Keep the current route's Phases 1-2 running: the KLambda-level work (port options, value relation,
stage 0 tooling) carries over either way.

## Reproduce

Files in `spikes/verified-backend/`:

| File | What |
|---|---|
| `setup-hol.sh` | Poly/ML 5.9.1, HOL `a390cba`, CakeML `e8eca63` in a fresh `ubuntu:24.04` container (`buri-vb-hol`) |
| `setup-certirocq.sh` | opam, OCaml 4.14.2, CertiRocq `943b52a`, MetaRocq `51b14e4` (`buri-vb-certirocq`) |
| `exp/defs.kl`, `exp/driver.kl` | The definitions and the driver |
| `exp/kl2cml.py` | Unverified KLambda-to-CakeML prototype (`KL2CML_FO=1` for the first-order variant, `KL2CML_CELLS=1` for function cells; the cells variant's `main.cml` calls `(!c_vb_2ebench)`) |
| `exp/kl2rocq.py` | Emits a Rocq file running the same forms on `KLSemantics.next` |
| `exp/main.cml` | CakeML driver: reads n from the command line |
| `exp/bench-riscv.S`, `exp/gen.cml`, `exp/bench.cml` | The base variant: generated CakeML, full program, and the CakeML compiler's RISC-V output. The other variants regenerate with `KL2CML_FO=1` and `--gc=gen5000` |
| `exp/bench.sh` | Timing, in `buri-lps` |
| `exp/certirocq-run.sh` | CertiRocq compile, gcc and timing |
| `exp/pad1000.kl` | 1,000 dummy definitions, for the store-size test |
| `hol/klfragScript.sml`, `hol/Holmakefile` | The fragment proof |
| `hol/dbg.sh` | Replays a tactic prefix from a saved heap (development aid) |

```sh
# CakeML route (host: macOS arm64; buri-lps for RISC-V linking and QEMU)
curl -LO https://github.com/CakeML/cakeml/releases/download/v3479/cake-arm8-64.tar.gz   # sha256 07aa0156...be99a
tar xzf cake-arm8-64.tar.gz && make -C cake-arm8-64 cake
python3 exp/kl2cml.py exp/defs.kl exp/driver.kl > gen.cml && cat gen.cml exp/main.cml > bench.cml
cake-arm8-64/cake --target=riscv < bench.cml > bench-riscv.S
# in buri-lps, with /opt/zig-linux-aarch64-0.13.0/zig:
zig cc -target riscv64-linux-musl -O2 -include sys/time.h -c basis_ffi.c -o ffi.o
zig cc -target riscv64-linux-musl -c bench-riscv.S -o bench.o
zig cc -target riscv64-linux-musl -static bench.o ffi.o -lm -o bench-cake
bash exp/bench.sh 7 200 2000          # pause other containers first

# The spec as an interpreter (buri-lps, Rocq 9.3, Búri built in /tmp/p4)
python3 exp/kl2rocq.py 1 VbRun1.v exp/defs.kl exp/driver.kl [exp/pad1000.kl]
sed -i 's/^From Coq Require/From Stdlib Require/' VbRun1.v; echo 'Time Eval vm_compute in result.' >> VbRun1.v
rocq compile -Q /tmp/p4 Buri VbRun1.v

# HOL fragment proof (buri-vb-hol)
cd hol && CAKEMLDIR=/opt/cakeml Holmake      # klfragTheory OK

# CertiRocq (buri-vb-certirocq, after setup-certirocq.sh; Búri sources compiled in /root/buri91)
bash exp/certirocq-run.sh 10            # and 100
```

**Containers left running:** `buri-vb-hol` (HOL4, CakeML and the fragment proof under `/root/klfrag`) and
`buri-vb-certirocq` (the CertiRocq switch). Both are about 14 GB-capped. Remove them with
`docker rm -f buri-vb-hol buri-vb-certirocq` when they're no longer needed. The `buri-lps` scratch files
are in `/tmp/vb`.

Agent token use isn't visible from inside the agent.
