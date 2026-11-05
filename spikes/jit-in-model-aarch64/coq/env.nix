# Same pins as nix/arm/islaris.nix and nix/arm/sail-model.nix (Coq 8.19.0, stdpp
# a1a12e00, coq-sail 6918e8f3, sail-arm 7d058164 by sha256), but for the host's
# system: those files hardcode x86_64-linux and this spike ran on aarch64-linux.
# Islaris itself is not built: this spike is model theorems only.
{ nixpkgs ? builtins.fetchTarball {
    url = "https://releases.nixos.org/nixpkgs/nixpkgs-26.11pre1105041.885ba4d038f1/nixexprs.tar.zst";
    sha256 = "sha256-RcsCCbI6YtyC9Be5c0XiwLMHJivUaGWSNHjJt0Q3NBE=";
  }
, system ? builtins.currentSystem
}:
let
  pkgs = import nixpkgs { inherit system; };
  inherit (pkgs) stdenv;
  coq = pkgs.coq_8_19.override { version = "8.19.0"; };
  contrib = "lib/coq/8.19/user-contrib";
  stdpp = stdenv.mkDerivation {
    pname = "coq-stdpp"; version = "pinned";
    src = builtins.fetchGit { url = "https://github.com/rocq-iris/stdpp"; rev = "a1a12e00fba07f2e41ccd74a8b593b88e48fc2c3"; allRefs = true; };
    nativeBuildInputs = [ coq coq.ocamlPackages.ocaml coq.ocamlPackages.findlib pkgs.which pkgs.python3 ];
    dontConfigure = true;
    buildPhase = "patchShebangs .; make -j$NIX_BUILD_CORES";
    installPhase = "make install COQLIBINSTALL=$out/${contrib} COQPLUGININSTALL=$out/lib/ocaml COQDOCINSTALL=$out/share/doc";
  };
  coq-sail = stdenv.mkDerivation {
    pname = "coq-sail-stdpp"; version = "0.19";
    src = builtins.fetchGit { url = "https://github.com/rems-project/coq-sail"; rev = "6918e8f3d63494d9a0c3b7e8d57fa689527cdfc7"; allRefs = true; };
    nativeBuildInputs = [ coq coq.ocamlPackages.ocaml ];
    dontConfigure = true;
    buildPhase = ''
      export COQPATH=${stdpp}/${contrib}
      sh prepare-stdpp-src.sh
      cd src-stdpp
      make -j$NIX_BUILD_CORES HAVE_OPAM_BBV=no BBV_DIR= all
    '';
    installPhase = ''
      mkdir -p $out/${contrib}/SailStdpp
      cp *.v *.vo *.glob $out/${contrib}/SailStdpp/
    '';
  };
  rev = "7d0581642d0e3aaca367bbc5650aca7c53057543";
  snap = name: sha256: pkgs.fetchurl { url = "https://raw.githubusercontent.com/rems-project/sail-arm/${rev}/arm-v9.4-a/snapshots/coq/${name}"; inherit sha256; };
  model = stdenv.mkDerivation {
    pname = "sail-arm-v9.4-coq"; version = builtins.substring 0 8 rev;
    dontUnpack = true;
    nativeBuildInputs = [ coq ];
    buildPhase = ''
      export COQPATH=${stdpp}/${contrib}:${coq-sail}/${contrib}
      ulimit -s unlimited
      ulimit -v 8388608
      mkdir -p SailArm && cd SailArm
      cp ${snap "armv9_types.v" "3586eb0f632fb642a39bbe5a526b2ffb34267725440fc9e9981e61a6de31a998"} armv9_types.v
      cp ${snap "arm_extras.v" "a82f366aadebfd12aaef4f7e6cdb5088c40b7a90ad4781e03b7baff9991b278c"} arm_extras.v
      cp ${snap "armv9.v" "5169ce7f4d10ab1a37bb77dd6a41114838c65fc0ceea4e9ef9cd1e73d8d1e68a"} armv9.v
      for f in armv9_types arm_extras armv9; do coqc -R . SailArm $f.v; done
    '';
    installPhase = ''
      mkdir -p $out/${contrib}
      cp -r . $out/${contrib}/SailArm
    '';
  };
in { inherit coq stdpp coq-sail model;
  env = pkgs.buildEnv { name = "a64-spike-env"; paths = [ coq stdpp coq-sail model ]; pathsToLink = [ "/bin" "/lib" ]; };
}
