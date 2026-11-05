# E2E-21 pinned representation inputs

These files are **inert captured data**. They are not proof evidence. The
specification and the theorems built on them are in
[REPRESENTATION](../../docs/REPRESENTATION.md). `SHA256SUMS` covers every
input file. `scripts/package-repr-layout.py` checks each upstream file
against its own copy of the upstream hash. It then generates
`rocq/ChezLayout.v` and `rocq/SbclLayout.v`, which `scripts/prove`
regenerates and diffs.

## Chez Scheme 10.3.0 (`chez/`)

* `cmacros.ss`, `arm64.ss`, `arm64.def`, `types.h` are unchanged copies of
  `s/cmacros.ss`, `s/arm64.ss`, `s/arm64.def` and `c/types.h` at tag
  `v10.3.0`, commit `adfaf9e6`. They are byte-identical to the files in
  `csv10.3.0.tar.gz` (sha256 `d237d987…`). Licence: Apache-2.0, see
  `LICENSES/Chez-Scheme.txt`.
* `tarm64le-equates.h` and `tarm64le-machine.def` are **build-time
  outputs**, not upstream files. They are `boot/tarm64le/equates.h` and
  `xc-tarm64le/s/machine.def` from the run of
  `nix/arm/build-chez-10.3.0-aarch64.sh` whose `scheme`, `petite.boot` and
  `scheme.boot` hashes are pinned in `ports/arm/README.md`. The same
  `equates.h` (sha256 `980e7c82…`) appears in four places: the host
  cross-compilation tree, the host boot directory, the target boot directory
  and the target `tarm64le/boot/tarm64le` directory used to compile the
  kernel. To regenerate them, rerun that script and copy the two files.
* `chez-layout-sample.ss` and `chez-10.3.0-tarm64le-sample.capture` are a
  **sampled** (emulated) reading of live object words. The capture was made
  with:

  ```
  qemu-aarch64 WORK/target/csv10.3.0/tarm64le/bin/tarm64le/scheme \
    -b .../petite.boot -b .../scheme.boot -q --script chez-layout-sample.ss
  ```

  qemu-user 11.1.2 is pinned in `ports/arm/README.md`. Heap addresses vary
  between runs; only residues and offsets are recorded.

## SBCL 2.6.8 (`sbcl/`)

* `early-objdef.lisp`, `early-vm.lisp`, `arm64-parms.lisp` and
  `arm64-vm.lisp` are `src/compiler/generic/early-objdef.lisp`,
  `src/compiler/generic/early-vm.lisp`, `src/compiler/arm64/parms.lisp` and
  `src/compiler/arm64/vm.lisp` from `sbcl-2.6.8-source.tar.bz2` (sha256
  `ad5126dfdfba5db27ee77bcc25893020fe522d0b7653d45b4c4795ade3ddc23d`, the
  nixpkgs source of the pinned aarch64 SBCL). Licence: public domain and
  BSD-style, see SBCL's `COPYING`.
* `sbcl-layout.lisp` and `sbcl-2.6.8-arm64-image.capture` are an **image
  capture** of `sb-vm` constants and feature lists. The capture was made
  with:

  ```
  qemu-aarch64 /nix/store/dz3b75gd…-sbcl-2.6.8/bin/sbcl \
    --core …/lib/sbcl/sbcl.core --noinform --non-interactive --no-sysinit \
    --no-userinit --load sbcl-layout.lisp
  ```
* `arm64-type-vops.lisp`, `arm64-pred.lisp`, `generic-type-vops.lisp`,
  `type-vop-macros.lisp` and `genesis.lisp` are `src/compiler/arm64/type-vops.lisp`,
  `src/compiler/arm64/pred.lisp`, `src/compiler/generic/type-vops.lisp`,
  `src/compiler/type-vop-macros.lisp` and `src/compiler/generic/genesis.lisp`
  from the same tarball, unchanged.
* `sbcl-type-tests.lisp` and `sbcl-2.6.8-arm64-type-tests.capture` are an
  **image capture** of the arm64 code the pinned image emits for
  `(lambda (x) (op x))` for each host operation of `CLContracts.cl_host_ops`:
  the raw instruction words read from the code objects, with the disassembly
  as comments. The capture was made with the same command as above, loading
  `sbcl-type-tests.lisp`. `scripts/package-sbcl-type-tests.py` packages it
  into `rocq/SbclTypeTests.v`.
