# E2E-20 first ARM experiment: provenance of the stored artifacts

These files are **inert captured data and harness scripts** for the first-wave
experiment of [END-TO-END-PLAN](../../docs/END-TO-END-PLAN.md) package 20. They
are not proof evidence. Findings, failures and the recommended pin are in
[ARM-FOUNDATION](../../docs/ARM-FOUNDATION.md). Large binaries are not stored;
their sha256 and reproduction commands are below.

The function is the smallest Shen function with a runtime-call slow path:

```shen
(define buri-arm-add X Y -> (+ X Y))
```

Kernel 43.1 turns it into `(defun buri-arm-add (V1 V2) (+ V1 V2))`.

| Port | Generated host code (captured from the real port) |
|---|---|
| Shen-Scheme v0.52 | `(define (kl:buri-arm-add V3015 V3016) (+ V3015 V3016))` |
| Shen-CL 4844072d | `(DEFUN buri-arm-add (V2264 V2265) (shen-cl.add V2264 V2265))`; `shen-cl.add` is declaimed inline |

## Chez side (`chez/`)

* `chez1030-buri-arm-add.{hex,bin}`: the exact 152 code bytes of the code object
  that **plain Chez Scheme 10.3.0 tarm64le** (threaded, the shen-scheme v0.52
  pin) produced for the form above in its interaction environment. The
  parameters are optimize-level 0 and debug-level 1, with the interrupt trap on.
  These are the Chez defaults, and they are exactly the values a running x86_64
  Shen-Scheme v0.52 reports
  (`scripts/shen-scheme-params.shen`). Offsets 0x54-0x63 are return-point data
  words (code-top-link and live mask), not instructions. The four `movz/movk`
  groups embed **process-specific absolute addresses** of library entries: the
  bytes are one relocated instance, and `*.relocs` gives the relocation targets.
  The run used qemu-aarch64. Its results were `(+ 1 2)=3`, fixnum overflow to a
  bignum `1152921504606846976`, `1.5+2=3.5` and a non-number error, all through
  the library slow path. This is emulator execution, not model evidence.
* `chez1030-buri-arm-add.chez-asm`: Chez's own `$assembly-output` listing.
  `chez1030-buri-arm-add.objdump` is a GNU objdump listing. Both are **reading
  aids only**: no claim is based on disassembly text.
* `chez1041-buri-arm-add.hex`: the same experiment on nixpkgs Chez 10.4.1. Its
  bytes differ from 10.3.0 only inside the relocated `movz/movk` immediates
  (offsets 0x40-0x4c, 0x70-0x7c, 0x84-0x90). This is sampled agreement for one
  function; it is not a version-equivalence claim.
* `shen-scheme-ta6le-buri-arm-add.hex` vs `chez1030-ta6le-buri-arm-add.hex`: on
  x86_64, compare the code object made **inside a real Shen-Scheme v0.52
  process** (`scripts/shen-in-situ.shen`) with plain host-built Chez 10.3.0 ta6le.
  The 123 bytes are identical except for the three relocated 8-byte absolute
  addresses. This is one sampled agreement on the host architecture. It supports
  using plain tarm64le Chez as a stand-in for an aarch64 Shen-Scheme process, but
  it does not prove that. No aarch64 Shen-Scheme build exists yet.
* `chez1030-buri-arm-add.closure`: the code objects reachable through relocation
  tables (`scripts/chez-closure.ss`). The walk ends at the library entries `+`,
  `event` and `doargerr` because **boot-heap code objects have empty relocation
  tables at run time**. The listing therefore cannot be a runtime closure; see
  ARM-FOUNDATION.

## SBCL side (`sbcl/`)

* `sbcl-buri-arm-add.{hex,bin}`: the 680 text bytes of the code component
  produced inside **Shen-CL (shen-cl master 4844072d, kernel 43.1) built and run
  on nixpkgs aarch64 SBCL 2.6.8 under qemu-aarch64**. The simple-fun entry is at
  offset 0x20, and offsets 0x00-0x1f are header and data words. `*.constants`
  lists the boxed constants and `*.policy` the compiler policy at dump time:
  all 1, not the `(speed 3) (safety 3) (debug 0)` proclaimed in `boot.lsp`.
  `*.sbcl-disasm` is SBCL's listing, a **reading aid only**. It ran with results
  3, the bignum `4611686018427387904`, `1152921504606846976` and 3.5.
* `sbcl-buri-arm-add.closure`: 26 code components and 65,740 text bytes are
  reachable through boxed constants from the function and from `TWO-ARG-+`.
  The count excludes assembly routines (`ALLOC-TRAMP`) and the C runtime (GC,
  trap handlers).

## isla traces (`isla/`)

`isla/STATUS` records one result per instruction word. Each traced word ran
`scripts/isla94` (isla-footprint) on its exact bytes in memory order against
the Sail Armv9.4-A IR. The run covered every Chez instruction word and an SBCL
fragment: the entry, the fixnum fast path with bignum allocation, the return
and the allocation-trampoline call. Selected traces are stored. They are
**symbolic-execution output of isla + z3 over the Sail model**. They are
unchecked by Rocq, so they are not theorems.

## Coq model probe (`coq/`)

`build-sail-arm-coq.sh` and `build-armv9-coq.sh` elaborate the sail-arm v9.4
Coq snapshot with a separate nixpkgs Coq 8.18.0, stdpp 1.10.0 and
coq-sail-stdpp 0.19 (the `armv9.v` step took 24 min at 6.4 GB). Both scripts
contain scratch paths, so adjust `A=` before use. `BuriDecodeProbe.v` records
the first decode-lemma attempt. It ends in `Abort`, it is not in
`scripts/prove`, and it **is not a theorem**. The header comment explains why
the pure equation was the wrong shape.

## Reproduction (x86_64 Linux + nix; no aarch64 hardware)

```
nix build -f nix/arm/tools.nix qemu-user sbcl-aarch64 aarch64-binutils   # pinned nixpkgs 885ba4d
nix/arm/build-chez-10.3.0-aarch64.sh WORK                                # Chez 10.3.0 ta6le + tarm64le
# Chez: (from ports/arm/scripts)
qemu-aarch64 WORK/target/csv10.3.0/tarm64le/bin/tarm64le/scheme \
  -b .../petite.boot -b .../scheme.boot -q --script chez-dump.ss . chez1030-buri-arm-add
# Shen-CL: precompile shen-cl 4844072d with shen-scheme v0.52 (load scripts/build.shen, (build)),
# extract ShenOSKernel-43.1.tar.gz (sha256 900eedef...) as kernel/, then
qemu-aarch64 SBCL/bin/sbcl --non-interactive --load boot.lsp
qemu-aarch64 bin/sbcl/shen script cl-add.shen
# isla: rems-project/isla e9b5d945, cargo build --release --bin isla-footprint (nixpkgs rustc 1.99.0, z3 5.1.0)
mk-opcodes.py chez1030-buri-arm-add.hex 0:54,64:98 > chez.list
ISLA94=scripts/isla94 isla-batch.sh chez.list traces/
```

| Input | Identity |
|---|---|
| shen-scheme source tag v0.52 | commit `fa0717374d907545c997ba0e38526f02b720a2ab` (tag object `cdd6118b`); Makefile `csversion 10.3.0` |
| Chez release `csv10.3.0.tar.gz` | sha256 `d237d9874c6e8b0ccf7758daa8286a6e825528b13ce3b2bca56eb1f73cddbc2c` (matches shen-scheme's pin) |
| built tarm64le `scheme` / `petite.boot` / `scheme.boot` | `219003131938590d5828635e1ae5bd5e57feb8080bdb4c1dfdfa7f2f8f4be390` / `59c038098cc74ab26bf6882ef0fed136cffd73188743b858e2bbbc144366dad6` / `43adf79b6b4446c18c688b6d5a174279488d5816d29e3d77abb3467abd8b7a46` |
| shen-scheme v0.52 linux-x64 binary (host) | archive `aa711f57...`; `bin/shen-scheme` `18ad5cfc776c9adc9d2121b9ba39b0c50c04c53a195c493f42a1f4b1b3a5ff97` |
| shen-cl | `4844072dde0208c3e4b99dcbfea58e4fdfd812e8` (same as CL-PORT pin) |
| ShenOSKernel-43.1.tar.gz | sha256 `900eedef44f440af78f9395ed06e689ce1604546fc309f5bc7c8bc84cc651920` |
| aarch64 SBCL 2.6.8 | `/nix/store/dz3b75gd6bnc5lqbyw5a6879xyg7fkqp-sbcl-2.6.8`; `sbcl.core` `44fce5d1bc32b823102b43dbeb225bbd8635800b12577704710d3682f936fef4` |
| Shen-CL aarch64 image `bin/sbcl/shen` (not stored, 284 MB) | `dcc978393967a65a43025f903fd4a2b2e486631279749013113c3bff636549cd` |
| qemu-user 11.1.2 `qemu-aarch64` | `/nix/store/1wjkglafi3l64ry9nf206l0ayykisrdr-qemu-user-11.1.2`; `c48d79c124d2df4fdd816436c72596f296b61f73c34ae9beb72415a5f07826a4` |
| Chez 10.4.1 aarch64 (comparison only) | `/nix/store/flhpgw6a287rgmshz8np06gyzwq61ls6-chez-scheme-10.4.1` |
| isla | `e9b5d945394277656593a0d429466d7fa0a2b4b3`; binary `056b41473c2b121618c1012d5c7ffd440c2efd1f517cf8601f28775191038a90` (z3-sys 0.5.0 against z3 5.1.0) |
| isla-snapshots | `d8b31014643035a3b11071e56ef30001de3f52ab`; `armv9p4.ir.gz` `d8c547ee...`, gunzipped `02918f81...` |
| sail-arm | `7d0581642d0e3aaca367bbc5650aca7c53057543`; `arm-v9.4-a/snapshots/coq/armv9.v` `5169ce7f...` (843,405 lines) |

`SHA256SUMS` covers every stored file.

## Wave B proofs (`coq/BuriArmAdds.v`, `islaris/`)

Unlike the files above, these are **checked proofs**, each in its own
toolchain and outside `scripts/prove` (see ARM-FOUNDATION section 10):

* `coq/BuriArmAdds.v`: theorems about the sail-arm Armv9.4 Coq model on the
  captured word `0xab010017` (Chez `+0x14`). Checked by `scripts/check-arm.sh`,
  which binds the word to the stored bytes and rejects a mutant word. It
  supersedes the aborted `coq/BuriDecodeProbe.v`, which is kept as a record.
* `islaris/buri_chez_add.v`: an Islaris (Coq 8.19.0) proof of the Chez fixnum
  fast path `+0x00..+0x23`. Traces in `islaris/instructions/` are Islaris
  frontend output over isla `b8e614bd` (and, for comparison, `e9b5d945`) on
  the Armv8.5 IR. They are regenerated by `islaris/gen-traces.sh`, which
  first checks that the dump opcodes equal the captured bytes. Checked by
  `islaris/check-islaris.sh ISLARIS_ENV TRACES_DIR` with the environment
  from `nix-build nix/arm/islaris.nix -A env`.

| Input | Identity |
|---|---|
| coq-sail | tag `0.19`, commit `6918e8f3d63494d9a0c3b7e8d57fa689527cdfc7` (`src-stdpp`) |
| isla (Islaris-tested) | `b8e614bda4a20e42c37d8b216853653133d04322`; binary `dd996a770a5caaa62a672b41527d86b9ca40a7462d8a024f0ff117d93dff7e67` (rustc 1.99.0, z3 5.1.0) |
| Armv8.5 IR | isla-snapshots `d8b31014` `armv8p5.ir`, sha256 `4ece4410a43c32b58737957d55920b485ade5171bb53deddebb9c7d61df77075` (Islaris's `aarch64.ir`) |
| Coq 8.19 env | `nix/arm/islaris.nix`; pins and store paths in ARM-FOUNDATION 10.2 |

## Wave C (`coq/BuriArmDecode.v`, `coq/BuriArmBridge*.v`, `islaris/el0/`)

These are checked by `scripts/check-arm.sh` Part B in one Coq 8.19.0 that
loads Islaris and the sail-arm model, built with
`nix-build nix/arm/sail-model.nix -A env` (see ARM-FOUNDATION section 11).

* `coq/BuriArmDecode.v` holds exact decode equations for twelve more captured
  words. Every `Definition *_word_XXXX` line is bound to the stored bytes.
  The words are the Chez fast path, the Chez store at +0x2c, and the SBCL
  `ret` (+0x210), `blr x10` (+0x2a0) and `brk #15` (+0x264). SBCL `.bin`
  offset + 0x1f0 = `.sbcl-disasm` address.
* `coq/BuriArmBridgeValues.v` and `coq/BuriArmBridge.v` hold the
  trace-to-model bridge for ADDS at +0x14 against `islaris/instructions/buri_chez_add/a14.v`.
* `islaris/etc/mk-el0-config.sh` derives
  `islaris/etc/aarch64_isla_coq_el0_linux.toml` (EL0, MMU on) from Islaris's
  config. `islaris/gen-el0-traces.sh` regenerates `islaris/el0/*.isla`.
  `islaris/el0/STATUS` gives one outcome per word, including the
  resource-exhausted `ldur`. The `*.el2-to-el0.diff` files show what changes
  for the branches. These traces are unchecked isla output.
* `scripts/sha256sums.py` regenerates `SHA256SUMS`.
