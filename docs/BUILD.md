# Pinned and reproducible builds (E2E-03)

**What this shows and what it doesn't.** Reproducibility gives *identity* evidence:
independent builds from the same pinned inputs produce the same bytes. It does
not show that Shen-Scheme, Chez, Coq, OCaml, glibc or any other tool preserves
semantics. Theorem validity comes only from `coqc`/`coqchk` running under
`make prove`. Python and Nix orchestrate the builds and package the bytes. Neither
decides whether a theorem holds. Steps 20–32 of END-TO-END-PLAN.md still have to
close the semantic gap.

## Routes

| Route | Command | Toolchain | Hermetic |
|---|---|---|---|
| Bootstrap (canonical, host) | `make bootstrap test prove manifest` | `scripts/bootstrap`, `scripts/bootstrap-rocq` download and check the pinned archives into `.tools/` | No. Uses the host's `/lib64` loader, glibc, libgmp, `/bin/sh`, python3 and make |
| Nix | `nix build .#gates` (also `nix flake check`) | `flake.nix` with nixpkgs pinned in `flake.lock` | Yes. Non-fixed-output steps run in the Nix sandbox with no network, no `/usr`, no `/lib64` and no `/home` (probe result below) |
| Earthly | `earthly -P +gates`, `+test`, `+host`, `+compare` | `Earthfile`, base images pinned by digest | `+gates` and `+test` call the Nix route. `+host` runs the bootstrap route on Ubuntu 24.04 and needs network. Only `+test` has been executed (see Results) |

`nix develop` gives a shell with the same pinned tools and links `.tools` to the
Nix tool tree. It does this only when `.tools` is missing or is already a link,
so an existing bootstrap directory is never overwritten.

## Pinned inputs

* **nixpkgs:** the nixos-24.11 channel release `nixos-24.11.719113.50ab793786d9`
  (git revision `50ab793786d9de88ee30ec4e4c24fb4236fc2674`), fetched as the
  `releases.nixos.org` `nixexprs.tar.xz` tarball. `flake.lock` pins it with
  `narHash sha256-EjLqzTANsT+CbWv85OOvz6B6C/B/Oj2tS3WBQNHmNKE=`. The proxy here
  blocks the GitHub API and archive endpoints for NixOS/nixpkgs, so the channel
  tarball is used instead. nixpkgs provides only the launcher and runtime pieces
  (glibc 2.40, gmp 6.3.0, bash, coreutils, make and python3), plus `dpkg` for
  unpacking.
* **Shen-Scheme v0.52 linux-x64:** a *prebuilt binary*, pinned by the archive
  sha256 `aa711f57…d8c9`. This digest is the one in `scripts/bootstrap` and in
  `toolchain.lock.json`. The flake fails to evaluate if either copy disagrees.
  The archive is unpacked unmodified. Nothing here rebuilds Shen-Scheme or Chez
  Scheme from source (see open obligations below).
* **PR 117 typechecker overlay:** `t-star.shen` from shen-sources
  `ec16a9fa4fc2e87e2aa336fb1ae30e8ac2266394`, sha256 `480e26c6…9168`. This matches
  `scripts/bootstrap` and is checked again by `scripts/shen` at every launch.
* **Coq 8.18.0 / OCaml 4.14.1:** the six Ubuntu snapshot `.deb` files listed in
  `rocq-packages.lock`. The flake reads that file directly, so the list exists in
  one place only. Each `.deb` is a fixed-output fetch from
  `snapshot.ubuntu.com/ubuntu/20260828T000000Z`, extracted unmodified with
  `dpkg-deb -x`.

### How pinned binaries are launched under Nix

The upstream ELF executables expect `/lib64/ld-linux-x86-64.so.2`, and the Nix
sandbox does not have that path. The Nix route does not patch the executables.
It runs them through `${glibc}/lib/ld-linux-x86-64.so.2 --library-path
${gmp}/lib:${glibc}/lib <unmodified binary>`, which keeps every payload byte
identical to the bootstrap route. Two details:

* `scripts/shen` clears `SHEN_SCHEME_HOME`. When Shen-Scheme starts through an
  explicit loader, `/proc/self/exe` names the loader, so the Shen launcher sets
  `SHEN_SCHEME_HOME` to the pinned `lib/shen-scheme` directory. A host install
  finds that same directory relative to its own binary.
* `scripts/shen` and `scripts/rocq` are unchanged. `.tools` is a link to the Nix
  derivation `dotTools`, which has the same layout: `host-path`,
  `t-star-pr117.shen`, `rocq/usr/bin/*`, `rocq/usr/lib`, `rocq/etc`. It also
  contains a `launcher.json` that tells the manifest where the payloads are.

The runtime libraries do differ between routes: host Ubuntu glibc 2.39 and
libgmp versus nixpkgs glibc 2.40 and gmp 6.3.0. The manifest records the loader
and every resolved library with its hash.

### nixpkgs Coq is a different binary

`.#coq-nixpkgs` (nixpkgs `coq_8_18`) reports `8.18.0 compiled with OCaml
4.14.2`. The deb build reports OCaml 4.14.1. Tested on the same input files
(`Arithmetic.v`, `Equality.v`, `Lambda.v`), it produces different `.vo` bytes
from the deb Coq. Its standard library `.vo` files are separate builds as well.
It cannot be made byte-identical, so it is offered for comparison only and no
gate uses it. The deb route is canonical.

## Build manifest

`make manifest` writes `_build/manifest.json` after a gate run, and
`make manifest-compare A=x.json B=y.json` compares two manifests. The Nix gate
derivation writes the manifest inside the sandbox. A manifest records:

* `sources`: the sha256 of every file in the tree, excluding `.git`, `.tools`,
  `_build`, `result*` and ignored build products;
* `tools`: per-file hashes and a tree digest for the Shen-Scheme payload and the
  extracted Coq payload, the overlay hash, the declared archive and deb hashes,
  and `coqc --version`;
* `tools._launch`: the route, the launcher files, and the dynamic loader and
  shared libraries actually resolved for `shen-scheme` and `coqc`, with hashes;
* `commands`: `make -n test prove`, each `scripts/rocq` invocation (with flags)
  in `scripts/prove`, and the `ulimit`/`export`/`exec` lines of `scripts/rocq`
  and `scripts/shen`;
* `environment`: the variables that can change tool behaviour (`SHEN_SCHEME_*`,
  `OCAML*`, `COQ*`, `LC_ALL`, `LANG`, `TZ`, `SOURCE_DATE_EPOCH`,
  `PYTHONHASHSEED`, …), with PATH, TMPDIR and HOME kept for information only;
* `outputs`: hashes of every `.vo`, `.glob`, generated `.v`, capture and log file
  under `_build`.

The comparer prints each differing key. Keys under a `_`-prefixed section
(`_launch`, `_orchestration`, `_git`, informational environment) are expected to
differ between routes, and each one is printed with its explanation. Any other
difference is reported as an `IDENTITY-DIFF` and makes the comparison fail.

Limitation: on the host route, `make manifest` runs as a separate process after
`make prove`. Its `environment` section therefore records the manifest process's
environment, not a capture taken during the gates. The Nix route writes the
manifest in the same build environment as the gates.

## Results

**Sandbox probe** (a derivation built with the pinned nixpkgs on this machine):
inside the build there was no `/home`, no `/usr/lib/x86_64-linux-gnu`, no
`/lib64` loader and no network (a `curl` to cache.nixos.org failed). `/bin/sh` is
the sandbox busybox. Stack limits were soft 8192 KiB and hard unlimited, so
`ulimit -s 65536` in `scripts/rocq` succeeds.

**Run 1: commit `b7ed1aa`.** Two independent builds of the same commit, run at
the same time on one machine:

* A: the host bootstrap route in a clean git worktree (`rm -rf _build; make test
  && make prove && make manifest`). Tools came from `scripts/bootstrap*`, with
  the host loader, glibc 2.39 and libgmp.
* B: `nix build .#gates` in the Nix sandbox, using the pinned nixpkgs glibc 2.40
  and gmp 6.3.0 through the explicit loader. It took 28 minutes on a shared
  4-core machine.

Both gates passed: every `BURI_SUITE_OK`, `BURI_GATE_TESTS_OK 22`, `BURI_ROCQ_OK
357 audited theorems …; coqchk replay passed`, and every proof mutation
rejected.

| Compared | Entries | Equal |
|---|---|---|
| Source files | 234 | all (tree `3234a5fd…3a93`) |
| Shen-Scheme payload files | 18 | all |
| Coq payload files (six extracted debs) | 3581 | all |
| PR 117 overlay, `coqc --version` | 2 | all |
| `.vo` proof objects (gate modules and mutation files) | 228 | **all**: digest `dde51250…2fc8` |
| `.glob` files | 147 | all |
| Generated `.v` proof inputs | 166 | all |
| Captures, `.bits`, `.sexp`, sources | 124 | all |
| Other logs: Rocq module logs, mutation logs, `Audit.log`, `rocq-version.log` | 148 | all, raw bytes |
| Shen test/export logs | 32 | equal only after masking `run time: … secs` lines |
| coqc `.aux` files | 147 | **differ** |

The nondeterminism found, with its explanation:

1. **coqc `.aux` files.** These hold the absolute path of the compiled `.v` file
   (`/home/user/…/_build/rocq/X.v` against `/build/source/_build/rocq/X.v`) and
   wall-clock timings for proof steps. Neither coqchk nor any gate reads them. The
   manifest keeps them under `outputs/_volatile/coq_aux` and reports them as
   explained differences.
2. **Shen-Scheme logs.** These contain `run time: N secs` wall-clock lines.
   Their raw hashes are kept under `outputs/_volatile/logs_raw`. Their hashes
   with that one line pattern masked (`outputs/logs_normalized`) are compared as
   identity entries.
3. **Environment.** The Nix gate sets `LC_ALL=C` and `TZ=UTC`, and stdenv sets
   `SOURCE_DATE_EPOCH=315532800` and `PYTHONHASHSEED=0`. The host run set none of
   these. All outputs above still agree. The comparer reports this as a distinct
   outcome, `BURI_MANIFEST_SAME_BYTES_DIFFERENT_ENVIRONMENT` (exit 3), not as
   identical.
4. **The `make -n` record** in run 1 picked up a `make[1]: Entering directory`
   line from the nested make. The manifest now clears `MAKEFLAGS` and
   `MAKELEVEL` and passes `--no-print-directory`. The route differences in
   loader, glibc and libgmp, `/bin/sh`, python and make are recorded and
   explained.

`.vo` files are byte-identical across different absolute build directories,
different glibc builds, and the host and sandbox environments. **This is
identity evidence.** It shows the same Coq binary produced the same proof
objects from the same sources. It says nothing about whether Coq is correct.

**Run 2: commit `4495d2f`, with the fixed manifest tooling.** The same two
routes were run again. Both gates passed with 71 rejected mutations each. The Nix
build took 43 minutes under load. `make manifest-compare` returned
`BURI_MANIFEST_SAME_BYTES_DIFFERENT_ENVIRONMENT 4754 identity entries equal; 4
environment differences; 217 explained route differences` (exit 3). There were
zero identity differences. The four environment differences are `LC_ALL`, `TZ`,
`SOURCE_DATE_EPOCH` and `PYTHONHASHSEED`, as described above. Digests that both
builds share:

* source tree `eb5e2183…aeba8` (238 files)
* proof objects `dde51250e0db874ef1bdaeb7010ee3b4b777ccb43c20ddbf42aeadefc26e2fc8`
  (228 `.vo`). This is unchanged from run 1 because no Rocq input changed.
* generated captures `7804576a…cfbe`
* Coq payload tree `a00171bc…` (3581 files); Shen payload tree `2bc53d74…`

**Earthly (executed for `+test` only).** No Docker daemon was running at first.
`dockerd` was started locally, and `earthly` v0.8.15 came from the pinned nixpkgs
(`nix run --inputs-from . nixpkgs#earthly`). The buildkitd container did not
trust this environment's TLS-intercepting proxy. That was worked around by
running a local buildkitd image with the proxy CA appended
(`--buildkit-image`), and by placing the proxy CA at `ci-extra-ca.crt`
(git-ignored and excluded from the hashed sources) for the Earthfile's optional
CA hook. With those, `earthly -P +test` on commit `f91af6b` succeeded. The Nix
sandbox ran inside the container with `sandbox-fallback = false`. The test
manifest it exported compared `BURI_MANIFEST_IDENTICAL 3956 identity entries
equal; 19 explained route differences` against `nix build .#test` on the host.
The derivation output paths differ (`4sjx…-buri-test` in the container's Nix
2.24.14, `mc6dyf…-buri-test` on the host's Nix 2.34.6). Host Nix gives the same
`.drv` for `git+file:` and `path:` evaluation of that tree, so the version
difference is the likely cause, but this has not been isolated. `+gates`,
`+host` and `+compare` are written but were **not executed**: each repeats the
>40-minute prove run on this shared machine. `+host` also needs network for
`make bootstrap` and has an untested `apt-get --snapshot` step.

## Target systems

The flake declares `lib.targetSystems = { x86_64-linux = "pinned-binaries";
aarch64-linux = "declared-unbuilt"; }`. On aarch64-linux it currently has only a
dev shell (python3 and make, for the manifest tooling). No pinned Shen-Scheme
linux-arm64 release asset exists, and `rocq-packages.lock` pins amd64 debs only.
ARM work is kept separately under `nix/arm/`.

## Open obligations (E2E-03 is not complete)

1. Rebuild Shen-Scheme v0.52 and its Chez Scheme from pinned source (source
   revision `8d261518db17fbfec32d1b268b40ed216b925c74`, which was reviewed in
   `toolchain.lock.json`). Then explain any difference from the release
   binary's bytes. Today the binary is an input trusted by hash.
2. Rebuild Coq 8.18.0 / OCaml 4.14.1 from source, or reproduce the Ubuntu deb
   build. Pin the runtime libc and libgmp debs from the same snapshot so that
   the two routes' runtimes match.
3. Pin `/bin/sh`. The Nix sandbox's `/bin/sh` comes from the host `nix.conf`
   (`sandbox-paths`, busybox 1.36.1). The repository scripts use `#!/bin/sh`,
   and patching their shebangs would change the hashed sources.
4. Produce the Scheme and CL artifacts for a declared ARM profile, and record
   which compiler built each file (the plan's E2E-03 deliverable). Shen-CL/SBCL
   (`make check-cl-port`) is not part of these routes.
5. E2E-35 binding: the manifest is not yet a signed release bundle, and no
   admission protocol consumes it.

## Registering Rocq modules and audit counts

`scripts/prove` no longer carries hard-coded module lists or a theorem total.

- Ordinary modules are listed one per line in `rocq/modules.d/*.list`. Files are
  concatenated in C-locale name order, so a lane whose modules import another
  lane's must use a file name that sorts after it. `00-base.list` holds every
  module merged through Wave B, in its original order.
- Audit modules are `rocq/Audit.v` or `rocq/Audit_<lane>.v`. Each has an explicit
  expected count of `Closed under the global context` lines in
  `rocq/audit.d/<module>.count`. Audit modules compile after all listed modules.
  Each audit log must contain no `Axioms:` line and exactly its expected count.
- The gate fails closed when:
  - a `rocq/*.v` file is unregistered;
  - a module is registered twice;
  - a listed module has no source;
  - an audit count has no module;
  - an audit module is listed in `modules.d`;
  - a count file is malformed.
- The printed total and the report's `audited_theorems` are the sum of the count
  files. Every count stays explicit, so deleting an audited theorem still fails.
- `make prove` also requires the `BURI_ROCQ_OK` line before running mutations,
  so a zero exit without the success line is a failure.

A new lane adds its own `.list` file, its own `Audit_<lane>.v` and its own
`.count` file. It does not edit `scripts/prove`, `rocq/Audit.v` or the report's
theorem total.
