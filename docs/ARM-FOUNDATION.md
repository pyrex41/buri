# ARM proof foundation: first E2E-20 research gate

Experiment date: 1 November 2026, on branch `wave-a/arm` from commit `8c94540`.
This is a research report for package 20 of [END-TO-END-PLAN](END-TO-END-PLAN.md).
Sections 1-9 are the first (Wave A) experiment, which proved no theorem.
**Section 10 is the Wave B update** (branch `wave-b/arm-proofs`): the first
byte-level lemma checked against the sail-arm Armv9.4 Coq model, a working
Coq 8.19.0 Islaris environment, and an Islaris proof of the Chez fixnum fast
path. Both proofs live outside `scripts/prove` in separate toolchains, so the
repository proof gate and audit count are still unchanged. Where section 10
contradicts an earlier "not built"/"not proved" statement, section 10 is
current. Each result names its evidence kind:

* **emulated run**: qemu-user executed the native code. The result is a sample.
  It is not evidence about the ISA model.
* **byte capture**: exact bytes read from a live code object. These are ground
  data about one relocated instance.
* **sampled agreement**: two byte captures compared. Agreement on one function
  does not show equivalence.
* **isla trace**: isla symbolic execution of the Sail model on exact opcode
  bytes. Rocq has not checked it. It trusts isla, z3 and the Sail-to-IR
  translation.
* **Coq elaboration**: a Sail-generated Coq model elaborated by `coqc`. This
  shows the model can be loaded; it is not a theorem about any instruction.
* **model theorem** (section 10): a Coq theorem about the sail-arm Armv9.4 Coq
  model text itself, checked by `coqc` in the separate model toolchain.
* **Islaris theorem** (section 10): an Iris/Islaris theorem checked by `coqc`
  8.19.0 about isla-generated traces. It is relative to the traces; the step
  "trace = architecture" is isla's, not Coq's.

No toy ISA, handwritten model or disassembly-text agreement is used as
evidence. Listings from objdump and from Chez's `$assembly-output` or SBCL's
disassembler are kept only as reading aids next to the bytes.

## 1. Exact pins used

| Component | Pin |
|---|---|
| Host | x86_64 Linux, 4 cores, no aarch64 hardware, no binfmt_misc |
| nixpkgs | `nixpkgs-26.11pre1105041.885ba4d038f1` (rev `885ba4d038f10c3d17d7a92e8c3cc185b99c9158`), see [nix/arm/tools.nix](../nix/arm/tools.nix) |
| Emulator | qemu-user 11.1.2 `qemu-aarch64` (`c48d79c1...`) |
| Shen-Scheme | v0.52: tag commit `fa071737`. The repository's reviewed source is `8d261518`, a descendant; its diff from the tag touches only `simple-error`/string handling and tests, not `+` |
| Chez for Shen-Scheme | **10.3.0**, from shen-scheme's `Makefile` (`csversion ?= 10.3.0`, archive sha256 `d237d987...`). Configuration: `--threads --disable-curses --disable-iconv --disable-x11`, machine `tarm64le` |
| Chez build | `nix/arm/build-chez-10.3.0-aarch64.sh`. Stage 1 builds ta6le from the pb boot files and runs `make bootquick XM=tarm64le`; stage 2 runs `configure --cross --force -m=tarm64le` with nixpkgs gcc 16.2.0 for aarch64. Hashes are in [ports/arm/README](../ports/arm/README.md). Nixpkgs ships Chez **10.4.1**, so it is not the pin |
| Shen-CL | `4844072dde0208c3e4b99dcbfea58e4fdfd812e8` (the CL-PORT pin), kernel 43.1 release archive `900eedef...`. Precompiled to Lisp by the x86_64 Shen-Scheme v0.52 |
| SBCL | nixpkgs aarch64-linux SBCL **2.6.8** (`/nix/store/dz3b75gd...-sbcl-2.6.8`, Hydra build). It is not an upstream sbcl.org tarball, and the repository has no SBCL version pin to compare against |
| Sail ARM model | sail-arm `7d0581642d0e3aaca367bbc5650aca7c53057543`, `arm-v9.4-a` (from Arm's 2023-03 ASL) |
| Isla | isla `e9b5d945394277656593a0d429466d7fa0a2b4b3`, built here with nixpkgs rustc/cargo 1.99.0 and z3 5.1.0 (z3-sys 0.5.0). Upstream tests Rust 1.70 and Z3 4.12.6 |
| Isla IR | isla-snapshots `d8b31014643035a3b11071e56ef30001de3f52ab`, `armv9p4.ir.gz` (gunzipped sha256 `02918f81...`) with isla's `configs/armv9p4.toml` |
| Coq model probe | the sail-arm v9.4 Coq snapshot, compiled with nixpkgs Coq 8.18.0 (OCaml 4.14.4), stdpp 1.10.0 and coq-sail-stdpp tag `0.19`. This is a separate toolchain; the repository's Debian Coq 8.18.0 is untouched |

## 2. Native artifacts (work item 1): done

The test function `(define buri-arm-add X Y -> (+ X Y))` has a fixnum fast path
and a generic-arithmetic runtime call. Both ports produced native code from
their actual generated host code (`ports/arm/`):

* **Shen-Scheme to Chez 10.3.0 tarm64le.** The port emits
  `(define (kl:buri-arm-add V3015 V3016) (+ V3015 V3016))`. A live x86_64
  Shen-Scheme v0.52 evaluates it with optimize-level 0 and debug-level 1, with
  type recovery and interrupt traps on, `current-eval = compile`, and `+` bound
  to Chez's primitive. These are all Chez defaults. Plain tarm64le Chez 10.3.0
  then compiled the same form to a 152-byte code object: 34 instruction words
  plus 4 return-point data words. It ran under qemu (emulated run).
  * Sampled agreement on x86_64: the code object built inside a real Shen-Scheme
    v0.52 process equals plain Chez 10.3.0 ta6le output, except for 3 relocated
    absolute addresses. **There is no aarch64 Shen-Scheme process yet.** The
    aarch64 bytes therefore come from plain Chez under Shen-Scheme's observed
    parameters. Building Shen-Scheme itself for aarch64 with this Chez is the
    next step.
  * Chez 10.4.1 gave the same tarm64le code apart from relocated immediates
    (sampled agreement, one function).
* **Shen-CL to SBCL 2.6.8 arm64.** Shen-CL was built under qemu on aarch64 SBCL
  in about 3 minutes and produced a 284 MB image. The port emits
  `(DEFUN buri-arm-add (V2264 V2265) (shen-cl.add V2264 V2265))`, and `shen-cl.add`
  is inlined. The result is a 680-byte code component: 32 header bytes plus 162
  instruction words with the float and type paths open-coded. Runtime policy is
  speed, safety and debug all 1. The `boot.lsp` proclamation `(speed 3)
  (safety 3) (debug 0)` does not apply to code evaluated at run time, which is a
  real configuration fact for E2E-23. Byte capture and emulated run.

Chez relocation note: every runtime call is a `movz/movk x10` sequence holding
the library entry's **absolute address**, followed by `br x10`. The stored bytes
are therefore one relocated instance (ASLR-dependent). A proof artifact has to
be the code template plus its relocation entries, plus a theorem that relocation
instantiates them. Content-addressing the bytes alone is not enough.

## 3. Runtime-call inventory (work item 4)

The data below come from byte captures and the code objects' own relocation
and constant tables. The code addresses belong to one qemu process.

| Port | Call or trap | What it is | How it is reached |
|---|---|---|---|
| Chez | library `+` (libspec `+` 34838, 348 bytes) | generic arithmetic for overflow, non-fixnum, flonum, bignum and error | tail `br x10` at `+0x80` after the `b.vs` overflow branch or the tag test `tst x30,#7` |
| Chez | library `event` (libspec 32817, 352 bytes) | interrupt/GC/timer poll | at `+0x24`, `subs x22,x22,#1` decrements the trap counter on the slow path; at zero it calls `event` with an explicit return point (`adr x30`, live mask data at `+0x54`) |
| Chez | library `doargerr` (176, 180 bytes) | wrong-argument-count error | `cmp x23,#2; b.ne` at entry |
| Chez | return | through the frame return address `ldur x10,[x20]; br x10` (x20 = `%sfp`) | no `ret`; the return protocol is Chez-specific |
| SBCL | `SB-KERNEL:TWO-ARG-+` (5,512 bytes) | generic `+` for mixed and non-fixnum operands | static-fdefn table relative to the NULL register (`ldr lr,[NULL,#1009]; br lr`) |
| SBCL | `SB-KERNEL:%DOUBLE-FLOAT` (260 bytes) | coercion (`shen-cl.double-precision`) | FDEFN constant, `blr` |
| SBCL | `SB-VM::ALLOC-TRAMP` (asm routine) | slow-path heap allocation when the TLAB is exhausted | literal-pool `blr` |
| SBCL | inline TLAB allocation in the pseudo-atomic section | bignum (header 273) and double-float (header 285) boxing, `dmb ishst` publication barrier | inline |
| SBCL | `brk #9` | pending-interrupt trap (GC/signal safepoint) taken via SIGTRAP into the C runtime | inline |
| SBCL | `brk #15` | invalid-argument-count trap | inline |

Conservative static reachability (`*.closure`): SBCL reaches 26 code
components, 65,740 text bytes, through boxed constants. This excludes assembly
routines and the C runtime. For Chez the walk **stops at the three library
entries**, because code objects in the boot heap keep no relocation tables at
run time. **Incompatibility for E2E-24:** a Chez runtime closure cannot be
computed from a running image. It has to come from build-time objects (the
cross compiler with relocations retained) or from decoding machine code.
Neither count includes libc, the Chez kernel C code (`S_get_more_room`,
`S_call_help`) or the SBCL C runtime (GC, signal handlers). Every trap path
above (`event`, `brk #9`) enters the C runtime.

## 4. ISA model evaluation (work item 2)

### sail-arm Coq export

sail-arm `7d058164` includes Coq snapshots: `arm-v9.4-a/snapshots/coq/armv9.v`
(42 MB, 843,405 lines, 33,663 top-level definitions) and `armv9_types.v`
(23,230 lines). They need coq-sail-stdpp, and `coq-sail-arm.opam` says `coq >=
8.15`. The probe found:

* coq-sail `0.17.1` (the Sail version the model's README last tested) **fails**
  with stdpp 1.10. It imports `stdpp.unstable.bitvector`, which moved to
  `stdpp.bitvector`.
* coq-sail `0.19` (`coq >= 8.18`, `stdpp-bitvector >= 1.10`) **builds** with
  Coq 8.18.0 and stdpp 1.10.0. `armv9_types.v` elaborates in 2 min 55 s at
  1.3 GB RSS, and `arm_extras.v` elaborates too.
* `armv9.v` **elaborates** with Coq 8.18.0, coq-sail-stdpp 0.19 and stdpp
  1.10.0. It took 24 min 16 s wall time at 6.4 GB maximum RSS (`armv9.vo` is
  59 MB), using `-R . SailArm` because the snapshot uses unqualified
  `Require Import armv9_types`. The authoritative Armv9.4-A model is therefore
  **loadable in this repository's Coq version** (Coq elaboration evidence).
  It is not loadable in the repository's *installation*, which has no stdpp
  or coq-sail. Bitvector guards compute under `vm_compute`: `uint` of the word
  gives `2868969495`, and the guard tests reduce to booleans.
* coq-sail HEAD needs Rocq >= 9.0, which is incompatible with this repository's
  Coq 8.18.
* The snapshot's decoder is `__DecodeA64 (pc : Z) (opcode : mword 32) : M unit`,
  a monadic program in the Sail concurrency-interface monad. A byte-decoding
  theorem therefore has to reason about an `M` computation, not a pure
  function. This is feasible, but it is not a `vm_compute` one-liner.

### Islaris

Islaris `c978e10f` requires **Coq exactly 8.19.0** (or dev),
`coq-lithium dev.2024-09-11.0.7945a29d`, stdpp-bitvector/unstable,
coq-record-update 0.3.3, dune exactly 3.9.1, and the ott-generated `isla-lang`
pinned at `bda86c9f`. It is tested against isla `b8e614bd` and isla-snapshots
`b58da917`, with the Armv8.5 `aarch64.ir`, which isla-snapshots HEAD no longer
ships under that name. Results:

* **Coq version incompatible** with the repository's 8.18. A separate switch is
  required.
* **Blocked here by egress policy:** the Islaris dependencies are installed from
  `opam.ocaml.org`, `coq.inria.fr` (opam released repo) and
  `gitlab.mpi-sws.org` (Iris dev repo, where lithium lives). The session proxy
  refuses all three (HTTP 403 CONNECT); the refusals were not retried. Nixpkgs
  has no lithium package. Its Coq 8.19 set is Coq 8.19.2 with stdpp 1.12.0 and
  Iris 4.4.0, not Islaris's dev pins.
* Islaris was therefore **not built** and **no Islaris proof was attempted**. Its
  frontend also expects the isla `b8e614bd` trace grammar; whether the newer
  isla `e9b5d945` output parses is **unknown** (not tested).

### Isla on the exact bytes: done

isla-footprint was built and ran on every Chez instruction word and on an SBCL
fragment: entry, fixnum fast path with inline bignum allocation, return and
`ALLOC-TRAMP` call. Each word was passed as its exact bytes in memory order:
`-x` with the default little endianness takes byte order, so word `0xab010017`
is passed as `170001ab`. Islaris's flags `--simplify-registers --tree -s` were
used. **All 72 words produced traces with rc=0**: 34 Chez words and 38 SBCL
words, listed in `ports/arm/isla/STATUS` with all traces in
`all-traces.tar.xz`. Each took 19-89 s, 2,942 s in total, and the traces are
35-1,576 lines. Every run warned `No primop emulator_read_tag/emulator_write_tag`:
MTE tag-memory primitives are missing from isla, so the MTE paths are not
modeled. The `brk #9` and `brk #15` traces end in
`sail_take_exception (Exception_SoftwareBreakpoint)` as an
**abstract primop**: what follows the exception (vector entry, EL change) is
not modeled under this config.

What the traces show (isla trace evidence): the encodings decode in the Sail
Armv9.4 model to the expected semantics. `170001ab` reads R0 and R1, does a
64-bit add, and writes R23 plus PSTATE.N/Z/C/V through AddWithCarry. Loads and
stores (`ldur`, `str`, `ldp`) carry the model's full translation and fault
paths: `Exception_DataAbort` with `Fault_Alignment` and `Fault_AddressSize`
under the default config, as well as the `read-mem` success path. Branches
write `_PC`. The default config is EL0-agnostic with the MMU off, and adds
roughly 400 `assume-reg` lines per instruction. A Linux-process (EL0, MMU on)
specification needs `armv9p4_mmu_on.toml` or Islaris-style register
constraints, and **every one of those constraints is a premise of the claim**.

Answer to the gate question. For isla, the exact extracted bytes **can** be
decoded, and their semantics stated in the authoritative Sail model. That
holds for the straight-line fragment of both functions, including faults.
**Rocq has not checked these semantics.** A Coq statement over the same model
is now *possible*, since the model elaborates, but it **has not been
proved**. The first attempt was `ports/arm/coq/BuriDecodeProbe.v`. It stated
`__DecodeA64 0 0xab010017 = execute_..._add_sub_shiftedreg 23 64 1 0 true 0
LSL false` and ended in `Abort`. Reducing guard by guard exposed **why that
statement has the wrong shape**: the Sail decoder is effectful. Its guards are
`and_boolM` over `read_reg SEE` (the ASL "SEE" decode state), and taken branches
run `write_reg SEE _` before the `decode_*`/`execute_*` call. isla shows the
same `read-reg |SEE|` / `write-reg |SEE|` events. The two other approaches
tried do not scale on this 59 MB model: strong normalisation
(`lazy -[execute]`) was killed at 8.2 GB, and `f_equal; vm_compute` was killed
at 8.2 GB after 10 min. A byte-decoding theorem must therefore be a statement
about the monadic program, or a Hoare triple using coq-sail's `Hoare.v`, under
a premise on `SEE`. It must be proved by guided stepping, not whole-term
computation.

## 5. Trust-boundary audit draft (work item 3)

| Step | What it assumes | Witness needed before a result is relied on |
|---|---|---|
| Arm ASL to Sail (asl_to_sail, 2023-03 ASL snapshot from Arm) | the translation preserves ASL meaning; the Arm ASL is the architecture; handwritten `mem.sail`, `interface.sail`, `impdefs.sail`, `reset.sail` and `devices.sail` make implementation-defined choices | foundation, recorded per pin. The handwritten glue and every IMPLEMENTATION DEFINED choice must be listed and matched to the target CPU (E2E-01) |
| Sail to Coq (`sail -coq`, coq-sail library) | the Coq backend's monadic embedding (concurrency interface, `M`, undefined values) reflects Sail semantics; generated termination measures are sound | the backend is not verified. The Coq text **is** the model; the trusted step is "Sail source = Coq text". Mitigation: pin the snapshot hash; Coq elaboration checks well-typedness only |
| coq-sail library (bitvectors, `mword`, monad) | definitions and lemmas inside Coq | checked by coqc and coqchk; it has to carry no axioms (`Print Assumptions` audit to do) |
| Sail to isla IR (`isla-sail`, Jib) | IR semantics = Sail semantics; the snapshot was built from the stated sail-arm revision (not re-derived here) | regenerate the IR from pinned sail-arm and sail; **the IR snapshot's provenance is currently trusted on its README** |
| isla symbolic execution | the isla interpreter faithfully executes the IR; path splitting is exhaustive; simplification (`-s`, `--simplify-registers`) preserves meaning; config register assumptions are stated | Islaris's approach is to treat isla traces as *untrusted*. Coq checks trace-to-Sail-semantics adequacy only for Islaris's own trace language, and for the trace it is given. **Islaris's adequacy theorem is about its own operational semantics of traces, not about the Coq Sail model**, so the link "trace = Sail model" remains an isla trust assumption. Each trace needs a checked witness: either a Coq proof that the trace refines the Coq `__DecodeA64`/execute for that opcode, or a verified isla |
| z3 (SMT) | path-feasibility pruning and simplification are correct; an UNSAT pruned path is truly infeasible | a pruned path is a claim that it is unreachable, so it needs proof certificates (z3 proof objects or a recheck in Coq) or a non-pruning mode with all paths kept. z3 5.1.0 is not the tested 4.12.6 |
| Islaris trace to Coq (frontend, isla-lang ott) | the printer/parser emits the same trace | the Coq-side trace is the object proved about, so a printer bug cannot create unsoundness *relative to the trace*. It can still break the link to the real opcode, so decoding has to be bound to bytes |
| Config/constraints (`armv9p4*.toml`, `//@constraint`) | initial register state, EL, MMU and feature flags | each is a premise and has to appear in the claim; it must be discharged by OS/loader theorems (E2E-26/27/31) |
| Byte extraction (this report) | `foreign-ref`/`sap-ref` read the live code object; GC was disabled or objects locked | harness data (trusted to capture). Package 26 must replace it with loader-image binding |
| qemu-user | none for proof: execution samples only | not evidence |

## 6. Incompatibilities and missing mechanisms found

1. **Chez version.** Nixpkgs has 10.4.1, but shen-scheme v0.52 pins 10.3.0.
   The single-derivation nix cross build fails: Chez's host-side pb bootstrap
   configures vendored zlib with the cross CC. A two-stage manual build works
   (`nix/arm/build-chez-10.3.0-aarch64.sh`). Linking uses Chez's vendored
   zlib/lz4.
2. **No aarch64 Shen-Scheme yet.** Byte agreement between Shen-Scheme and plain
   Chez is only an x86_64 sample.
3. **Relocated absolute addresses in Chez code.** The proof object must be
   template plus relocations (see section 2).
4. **Boot-heap code has no runtime relocation tables** in Chez, so dependency
   closure needs build-time data.
5. **SBCL runtime policy** differs from the build-time proclamation.
6. **Islaris requires Coq 8.19.0 and Iris/lithium dev pins.** It cannot share
   the repository's Coq 8.18. Its dependencies are unreachable through this
   session's egress (opam.ocaml.org, coq.inria.fr and gitlab.mpi-sws.org
   refused).
7. **coq-sail versions are coupled to stdpp and Coq versions.** 0.17.1 does not
   work with stdpp 1.10, 0.19 does, and HEAD needs Rocq 9.
8. **isla toolchain drift.** Isla's documented Rust and Z3 versions (1.70 /
   4.12.6) differ from what built here (1.99.0 / 5.1.0). Islaris tests an older
   isla and snapshot.
9. **Runtime traps go through signals.** SBCL's `brk #9/#15` and Chez's
   `event` enter the C runtime, so an ISA-level proof of these functions
   needs an exception-level/OS model (E2E-27) for the trap path.
10. The Sail model's `mem.sail`/`interface.sail` give a sequential memory
    interface under isla's default config. The concurrency interface is present
    in the Coq snapshot, but no weak-memory (E2E-28) link was exercised.
11. **The decoder is effectful** (`read_reg`/`write_reg SEE`), so "decode
    bytes" is a monadic statement with a state premise. Whole-term evaluation
    of the 59 MB model exceeds 8 GB.
12. **isla gaps:** the MTE tag primitives `emulator_read_tag/write_tag` are
    missing, and `sail_take_exception` is abstract. Fault and trap paths
    therefore stop at "exception taken", with no vector or EL semantics.

## 7. Size and scalability estimates (from observed numbers only)

* isla: 19-89 s per opcode (one thread, with other jobs sharing 4 cores). Each
  trace with `--tree -s` is 35 to 1,576 lines, and memory accesses are the
  largest because of translation and fault paths. That is 2,942 s (about 0.8 h) of CPU
  for the 72 words traced. The SBCL function alone is 162 instruction words. The
  SBCL constant-reachability closure (66 KB, about 16k instruction words) would
  take about 7 CPU days of isla at the observed 41 s average, **before** any
  proof. Many words repeat, so tracing should be cached per distinct opcode, and
  parametric (`--partial`) traces should be produced per encoding class.
* Coq model: `armv9_types.v` elaborates in 3 min at 1.3 GB. For `armv9.v`,
  24 min and 6.4 GB on one core. A proof module that imports
  it pays that once per build, and `coqchk` of the 59 MB `.vo` has not been
  measured.
* Code per Shen `+`: Chez emits 34 instructions and reaches 3 library entries
  (880 bytes) before the C runtime. SBCL emits 162 instructions with float
  paths open-coded. The SBCL encoding is roughly 4.8 times as large, and the
  difference comes from Shen-CL's inline `shen-cl.add`.
* Islaris proof effort: **not measured** (not built).

## 8. Recommended pin for E2E-01 (provisional)

* **Architecture model:** sail-arm `7d058164` `arm-v9.4-a`. Use its Coq
  snapshot as the authoritative model text and the isla `armv9p4.ir` snapshot
  `d8b31014` as an untrusted trace generator. Re-derive both from pinned Sail
  before relying on them.
* **Profile:** AArch64 little-endian, EL0 Linux process, base A64 integer and
  load/store with LSE off unless needed. Initially exclude SVE/SME, MTE and PAC
  (the snapshot enables them in `armv9p4.toml`; the release charter must
  disable them or prove they are unused).
* **Toolchains:** Chez 10.3.0 tarm64le threaded (the shen-scheme v0.52
  configuration) and aarch64 SBCL 2.6.8 from nixpkgs `885ba4d`. Shen-CL
  `4844072d` with kernel 43.1.
* **Proof stack:** Coq 8.18.0, coq-sail-stdpp 0.19 and stdpp 1.10.0 for the Sail
  model. Islaris only in a separate Coq 8.19.0 environment, after its
  dependencies become reachable. Any Islaris result must be bridged to the Coq
  Sail model before it counts for E2E-20.

## 9. Next steps

1. Build Shen-Scheme v0.52 for aarch64 on the 10.3.0 tarm64le Chez (main.c
   cross-compiled, runtime boot built under qemu) and recapture `buri-arm-add`
   in-process.
2. Make the Chez closure walk use build-time objects with relocations retained,
   and inventory the C kernel entry points (`S_call_help`, `S_get_more_room`).
   Do the same for SBCL assembly routines and C runtime callees.
3. Prove the first byte-level decode lemma in the elaborated Coq model, in the
   monadic form described in section 4: for `0xab010017`, the decoder under
   `SEE`-premise P reduces to `write_reg SEE _ >> execute_..._add_sub_shiftedreg
   23 64 1 0 true 0 LSL false`. Then prove its execute effect on
   R0/R1/R23/PSTATE. Add stdpp 1.10 and coq-sail-stdpp 0.19 to the pinned
   toolchain before any such module enters `scripts/prove`, and audit
   coq-sail's `Print Assumptions`.
4. Get Islaris dependencies through an allowed channel (vendored opam repository
   or nix derivations for lithium `7945a29d` and Coq 8.19.0). Then reproduce
   one example and prove the Chez fixnum fast path (`+0x00`-`+0x20`). The
   precondition is tagged fixnums, and the postcondition is the return to the
   frame's return address with x23 holding the tagged sum.
5. Write the trace-to-Coq-model bridge obligation as a stated (not assumed)
   Rocq theorem shape, and decide whether the bridge is per opcode (checked
   witness) or a verified isla.
6. Choose and record the EL0/MMU-on configuration and the register constraints
   as explicit premises in the release charter.

## 10. Wave B: first checked byte-level proofs (branch `wave-b/arm-proofs`)

Two independent results, in two separate toolchains. Neither file is in
`scripts/prove`; each has its own opt-in check. The repository's Coq 8.18.0
pins (`scripts/rocq`, `rocq-packages.lock`) are untouched.

### 10.1 Model theorem: ADDS X23, X0, X1 in the sail-arm Armv9.4 Coq model

File `ports/arm/coq/BuriArmAdds.v`, checked by `scripts/check-arm.sh`. The
toolchain is the Wave-A one: nixpkgs `885ba4d` Coq 8.18.0
(`/nix/store/z93aiwvy...-coq-8.18.0`), stdpp 1.10.0, coq-sail tag `0.19`
(commit `6918e8f3d63494d9a0c3b7e8d57fa689527cdfc7`, `src-stdpp`), and the
sail-arm `7d058164` snapshot (`armv9.v` `5169ce7f4d10...`, `armv9_types.v`
`3586eb0f632f...`, `arm_extras.v` `a82f366aadeb...`) compiled with
`-R . SailArm`. The word is the captured Chez word at `kl:buri-arm-add+0x14`,
bytes `17 00 01 ab`. The check script re-reads those bytes from
`ports/arm/chez/chez1030-buri-arm-add.bin` (whose sha256 it checks against
`ports/arm/SHA256SUMS`) and requires the theorem's `Definition` line to name
exactly that word. It then checks the model file hashes, compiles the proof,
audits `Print Assumptions`, and requires a one-bit mutant word (`0xab010018`,
Rd = 24) to be rejected by the decode proof (`Unable to unify`).

| Theorem | Statement | Evidence kind |
|---|---|---|
| `chez_0014_decode` | for every `pc`, `__DecodeA64 pc 0xab010017 = (read_reg SEE >>= fun see => if see <? 15 then write_reg SEE 15 >> execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 23 64 1 0 true 0 ShiftType_LSL false else throw (Error_Undefined tt))` | model theorem, universal over `pc`; an exact equation of `iMon` trees, so it fixes every behaviour of the decoder on this word |
| `chez_0014_execute` | that execute call equals the explicit program `adds_x23_x0_x1` (read R0, R1; four read/write pairs on PSTATE setting N, Z, C, V from the model's `AddWithCarry`; write R23) | model theorem, closed equation |
| `chez_0014_adds_trace` | for all `pc`, SEE value `see < 15`, X0, X1 and PSTATE `p`, `Interface.iTrace_match (__DecodeA64 pc 0xab010017)` accepts the trace "read SEE = see; write SEE := 15; read X0; read X1; read PSTATE = p; write PSTATE.N; ...; write PSTATE.V; write X23 := fst (AddWithCarry X0 X1 0)", each PSTATE re-read returning the last written value | model theorem (universal); `iTrace_match` is coq-sail's own "this trace is a behaviour" relation, used with sequential register reads |
| `chez_0014_sum` | `uint (fst (AddWithCarry x0 x1 0)) = (uint x0 + uint x1) mod 2^64` | closed lemma |

Premises, all explicit: `SEE < 15` (the ASL decode-retry register). This
snapshot never resets SEE between instructions; `initialize_registers` sets
it to an undefined integer, so the premise is a real one that a fetch/execute
theorem must discharge. No feature or configuration register is read on this
path: the equation shows the decode and execute of this word read only SEE,
R0, R1 and PSTATE. `pc` is not used.

How it was proved (the Wave-A blocker): `hnf` stops at the decoder's first
`if`, and strong normalisation exceeds 8 GB. A guided tactic instead decides
each closed Boolean guard with `vm_compute`, rewrites it to `true`/`false`, and
reduces only `and_boolM`/`bind`/`returnM`/`iMon_bind`. Guards that do not
match return `Ret false` without reading SEE, so the 73 guards of
`__DecodeA64_DataProcReg` collapse to the single matching one. The decode
proof takes about 8 s, the whole file 24 s at 1.06 GB maximum RSS, after
the 14 s load of `armv9.vo`. `coqchk` of the file (which would recheck the
59 MB model) was not run.

Assumption audit: `chez_0014_execute` and `chez_0014_sum` are closed under
the global context. Every statement that mentions `__DecodeA64` depends on
`ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec`
and `FunctionalExtensionality.functional_extensionality_dep`, and
`Print Assumptions __DecodeA64` lists exactly those three. They are Coq
standard-library axioms of the Reals library, reached because the model's
floating-point decoders use Coq `R` through coq-sail's `Real.v`; Buri adds no
axiom. Any theorem about this model's decoder inherits them, so they are part
of the trusted base of this result, together with the Sail-to-Coq
translation, coq-sail 0.19 and the Coq 8.18.0/stdpp 1.10.0 kernel.

Not shown: other words; the fetch/execute loop around `__DecodeA64`
(`ExecuteA64`, `__SetThisInstrDetails`, PC update); memory, faults or
branches in this model; `coqchk`; any relation between this model and the
isla traces of section 10.3.

### 10.2 Coq 8.19.0 Islaris environment: built

`nix/arm/islaris.nix` (opt-in, `nix-build nix/arm/islaris.nix -A env`) builds
everything on the nixpkgs `885ba4d` tarball. Coq is
`coq_8_19.override { version = "8.19.0"; }`; its source came from the nixpkgs
release table (hash `sha256-ixsYCvCX...`). The dev pins come by exact git commit
through `builtins.fetchGit`. GitHub git reads are allowed through the proxy;
GitHub archive downloads and the opam/MPI GitLab hosts are refused. Each
commit was found in a GitHub mirror and matches the 8-hex suffix in Islaris's
opam version strings, which are the only published identifiers for these dev
packages; opam archive checksums could not be fetched to compare.

| Package | Pin | Mirror |
|---|---|---|
| coq | 8.19.0 (tag commit `a360913f`) | nixpkgs fetch, built 6 min 12 s |
| coq-stdpp (+bitvector, unstable) | `a1a12e00fba07f2e41ccd74a8b593b88e48fc2c3` = dev.2024-09-10.3.a1a12e00 | github `rocq-iris/stdpp` (also nixpkgs' mirror for released stdpp) |
| coq-iris | `6f24ed4baa4d61967a95bac834eab2c66f3b76fa` = dev.2024-09-10.1.6f24ed4b | github `rocq-iris/iris` |
| coq-lithium | `7945a29d1647970709a9b5ad2ffc53c757e130cc` = dev.2024-09-11.0.7945a29d ("update Iris", M. Sammler, 2024-09-11) | github `UIC-verif-group/refinedC` (refinedc tree; `dkxb/refinedc` stops at 2024-07) |
| coq-record-update | tag v0.3.3 `50e45e9f4ed52840427c3bfddc9037a645d9bf19` | github `tchajed/coq-record-update` |
| isla-lang | `bda86c9f0bd28bbaa2481f50ddc986ede342805a` (Islaris pin-depends) | github `rems-project/isla-lang` |
| islaris | `c978e10f50db5c40f0fdf113f5f76a779782c6f9` | github `rems-project/islaris` |

Store paths of the build: `coq-8.19.0` `nyvwdj1l...`, stdpp `66q2ls2d...`,
iris `8wwxidam...`, lithium `24bfzrrm...`, record-update `lwq2x6l2...`,
islaris `il53cd0n...`. Deviations from Islaris's opam file are recorded, not
hidden. Dune is nixpkgs 3.23.1 (Islaris pins 3.9.1) and ott is 0.34. Lithium is
built with `coq_makefile` from `theories/lithium/*.v`, not with refinedc's dune
file. Islaris's opam-only `coqc` timing wrapper and its sail/pkvm/riscv example
trees are dropped. `isla_lang.v` comes from the vendored isla-lang dune rule,
not from `opam var`. As a sanity check, Islaris's own unmodified
`examples/example.v` with its committed traces checks in this environment
(`ports/arm/islaris/check-islaris-example.sh`, 27 s).

Isla for Islaris: Islaris is tested against isla `b8e614bd` and the Armv8.5
snapshot `aarch64.ir`. isla `b8e614bda4a20e42c37d8b216853653133d04322` was
built here with the same nixpkgs rustc/cargo 1.99.0 and z3 5.1.0 (binary
`dd996a77...`). isla-snapshots `d8b31014` still ships the Armv8.5 IR as
`armv8p5.ir` (sha256 `4ece4410a43c...`), which contains Islaris's
`isla_footprint_no_init`. The Wave-A isla `e9b5d945` also runs on it.

### 10.3 Islaris theorem: the Chez fixnum fast path

Files: `ports/arm/islaris/buri_chez_add.dump` (annotated dump of Chez
`+0x00..+0x23`), the generated traces `ports/arm/islaris/instructions/buri_chez_add/`
(isla `b8e614bd`) and `.../buri_chez_add-isla-e9b5d945/` (isla `e9b5d945`), and
the proof `ports/arm/islaris/buri_chez_add.v`. `gen-traces.sh` first checks
that the dump's opcode column equals the captured bytes `+0x00..+0x23`, then
runs the Islaris frontend in dump mode. That mode is Islaris's own pipeline:
`isla-footprint -f isla_footprint_no_init -C etc/aarch64_isla_coq.toml
--simplify-registers --tree -s`, followed by Islaris's trace simplification and
Coq printing. Regeneration gives identical `.v` traces. The raw `.isla` files
differ only in struct-field order. The two isla versions give traces that
differ in SMT expression shape (the N flag of `cmp`/`adds`/`tst`). The proof
checks against both trace sets (`check-islaris.sh ENV DIR`, 33 s, 1.18 GB).

`buri_chez_add_fast_path` (Islaris theorem, universal over a, b, fp, ra and
the prior X10/X30): with the nine instructions at `0x7f8d409bcb50..+0x20`, and
`instr _ None` at the two slow-path targets `+0x24` and `+0x84`, the
precondition below gives `instr_body 0x7f8d409bcb50`. The precondition is
`reg_col sys_regs`, `reg_col CNVZ_regs`, X23 = 2, X0 = a, X1 = b,
`InGuardedPage = false`, X20 = fp with `fp ↦ₘ ra`, `fp < 2^52`, `fp mod 8 = 0`,
`(a | b) & 7 = 0` and `-2^63 ≤ sa + sb < 2^63`. Under it, control reaches `ra`
with X23 = a + b, X30 = a | b, X10 = ra, and X0, X1, X20 and the slot
unchanged. The three slow-path branches are proved infeasible from the premises
in the proof. `Print Assumptions` reports **Closed under the global context**.

What this does and does not establish:

* Islaris's adequacy relates `instr_body` to Islaris's operational semantics
  **of the traces**. The traces are isla output over the Armv8.5 Sail IR, not
  the Armv9.4 model of 10.1. They are produced under Islaris's register
  constraints (EL2, `SCTLR_EL2 = 0x4000002`, MMU off, `HCR_EL2`, `SCR_EL3`,
  `CFG_ID_AA64PFR0_EL1_*`, `TCR_EL2`, debug registers), which appear as
  `AssumeReg` premises inside `sys_regs`. **The Chez code runs at EL0 under
  Linux with the MMU on. This theorem is about EL2 with the MMU off.**
  Relating the two is an E2E-27/E2E-31 obligation.
* Isla and z3 path pruning are trusted, isla `b8e614bd` was built with rustc
  1.99 and z3 5.1.0 (not its tested 4.12.6), and the IR snapshot's provenance
  rests on the isla-snapshots README. The trace-to-model bridge (section 9
  item 5) is still open. Section 10.1 shows that a direct model proof is
  feasible per opcode, but no bridge theorem connects the two.
* The base address is the captured instance's. The fragment is
  position-independent, but the theorem is stated for that address.
* `instr_pre ra Q` is the continuation hypothesis; the Chez return protocol
  (what the caller at `ra` expects) is not modelled.

### 10.4 What remains open for E2E-20

The exit criterion needs byte-level proofs for a branch, call, load/store,
fault, allocation stub and atomic against the selected ISA model. Section 10.3
covers a branch, a load and an indirect branch only in Islaris over Armv8.5
traces. Section 10.1 covers one data-processing word in the Armv9.4 model.
No fault, call, allocation stub, atomic or memory-model result exists. The
SBCL code is not yet covered. Package 20 stays in progress.

### 10.5 Wave C: the fast-path premises as Shen-value facts (E2E-21)

`ports/arm/islaris/buri_chez_add_shen.v` (Islaris theorem, same Coq 8.19
toolchain, `check-islaris-shen.sh`) restates 10.3 for X0/X1 holding Chez
fixnum words of Shen integers x, y. The premise `(a|b)&7 = 0` follows. The
no-overflow premise holds exactly when x + y is a fixnum, so it is a real Shen
premise, not a consequence of x and y being integers. The fixnum encoding and
the register numbers come from constants extracted from the pinned Chez
sources and build output. Everything else listed in 10.3 stays assumed: EL2
with the MMU off, the Armv8.5 traces, the base address and the continuation.
See [REPRESENTATION](REPRESENTATION.md) section 4.
