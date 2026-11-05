# Tools used by the E2E-20 ARM experiment (docs/ARM-FOUNDATION.md).
# Pinned to the nixpkgs revision the experiment actually used:
#   nixpkgs-26.11pre1105041.885ba4d038f1 (rev 885ba4d038f10c3d17d7a92e8c3cc185b99c9158)
# Every attribute below was substituted from cache.nixos.org on an x86_64-linux
# host; the aarch64 entries are native aarch64-linux builds run under qemu-user.
# Building these establishes byte identity only, never semantics.
#
#   nix build -f nix/arm/tools.nix <attr>
{ nixpkgs ? builtins.fetchTarball {
    url = "https://releases.nixos.org/nixpkgs/nixpkgs-26.11pre1105041.885ba4d038f1/nixexprs.tar.zst";
    sha256 = "sha256-RcsCCbI6YtyC9Be5c0XiwLMHJivUaGWSNHjJt0Q3NBE=";
  }
}:
let
  host = import nixpkgs { system = "x86_64-linux"; };
  a64 = import nixpkgs { system = "aarch64-linux"; };
  cross = host.pkgsCross.aarch64-multiplatform;
in {
  # qemu-user 11.1.2: runs the aarch64 binaries (emulation, not an ISA model).
  qemu-user = host.qemu-user;
  # Official-in-nixpkgs aarch64 SBCL 2.6.8 used to build Shen-CL.
  sbcl-aarch64 = a64.sbcl;
  # Chez 10.4.1 aarch64: NOT the shen-scheme v0.52 pin (10.3.0); used only as a
  # cross-version comparison.  The 10.3.0 build is nix/arm/build-chez-10.3.0-aarch64.sh.
  chez-aarch64-10_4_1 = a64.chez;
  # Cross toolchain for the Chez 10.3.0 kernel and objdump reading aids.
  aarch64-gcc = cross.buildPackages.gcc;
  aarch64-binutils = cross.buildPackages.binutils;
  # isla build inputs (cargo build of rems-project/isla e9b5d945).
  inherit (host) cargo rustc z3 gcc gnumake;
  # Separate Coq used only for the sail-arm Coq snapshot probe; the
  # repository's pinned Coq 8.18.0 (rocq-packages.lock) is untouched.
  coq_8_18 = host.coqPackages_8_18.coq;
  stdpp_coq_8_18 = host.coqPackages_8_18.stdpp;
}
