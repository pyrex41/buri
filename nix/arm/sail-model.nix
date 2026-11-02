# The sail-arm Armv9.4-A Coq model and coq-sail, compiled with the SAME Coq
# 8.19.0 + stdpp as the Islaris environment (nix/arm/islaris.nix), so that
# one Coq file can state a theorem about both an Islaris trace and the model
# (ports/arm/coq/BuriArmBridge.v).  Opt-in; not the repository toolchain.
#
#   nix-build nix/arm/sail-model.nix -A coq-sail     # ~30 s
#   nix-build nix/arm/sail-model.nix -A model        # ~7 min, 6.4 GB peak RSS (armv9.v)
#   nix-build nix/arm/sail-model.nix -A env          # islaris env + coq-sail + model
#
# Pins:
#   coq-sail   tag 0.19 = 6918e8f3d63494d9a0c3b7e8d57fa689527cdfc7, github rems-project/coq-sail,
#              src-stdpp prepared exactly as its prepare-stdpp-src.sh does
#   sail-arm   7d0581642d0e3aaca367bbc5650aca7c53057543, arm-v9.4-a/snapshots/coq/*.v
#              fetched as single files from raw.githubusercontent.com by sha256
#              (the full repository is >1 GB of other snapshots)
# The model is compiled with `-R . SailArm` (the snapshot uses unqualified
# `Require Import armv9_types`) and `ulimit -s unlimited`.
{ nixpkgs ? builtins.fetchTarball {
    url = "https://releases.nixos.org/nixpkgs/nixpkgs-26.11pre1105041.885ba4d038f1/nixexprs.tar.zst";
    sha256 = "sha256-RcsCCbI6YtyC9Be5c0XiwLMHJivUaGWSNHjJt0Q3NBE=";
  }
}:
let
  isl = import ./islaris.nix { inherit nixpkgs; };
  inherit (isl) pkgs coq stdpp;
  inherit (pkgs) stdenv;
  contrib = "lib/coq/8.19/user-contrib";

  coq-sail-src = builtins.fetchGit {
    url = "https://github.com/rems-project/coq-sail";
    rev = "6918e8f3d63494d9a0c3b7e8d57fa689527cdfc7";
    allRefs = true;
  };
  rev = "7d0581642d0e3aaca367bbc5650aca7c53057543";
  snap = name: sha256: pkgs.fetchurl {
    url = "https://raw.githubusercontent.com/rems-project/sail-arm/${rev}/arm-v9.4-a/snapshots/coq/${name}";
    inherit sha256;
  };
  model-src = {
    "armv9_types.v" = snap "armv9_types.v" "3586eb0f632fb642a39bbe5a526b2ffb34267725440fc9e9981e61a6de31a998";
    "arm_extras.v" = snap "arm_extras.v" "a82f366aadebfd12aaef4f7e6cdb5088c40b7a90ad4781e03b7baff9991b278c";
    "armv9.v" = snap "armv9.v" "5169ce7f4d10ab1a37bb77dd6a41114838c65fc0ceea4e9ef9cd1e73d8d1e68a";
  };

  coq-sail = stdenv.mkDerivation {
    pname = "coq-sail-stdpp";
    version = "0.19";
    src = coq-sail-src;
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

  model = stdenv.mkDerivation {
    pname = "sail-arm-v9.4-coq";
    version = builtins.substring 0 8 rev;
    dontUnpack = true;
    nativeBuildInputs = [ coq ];
    buildPhase = ''
      export COQPATH=${stdpp}/${contrib}:${coq-sail}/${contrib}
      ulimit -s unlimited
      # Fail this build, not a neighbour, if armv9.v exceeds 7 GiB.
      ulimit -v 7340032
      mkdir -p SailArm && cd SailArm
      cp ${model-src."armv9_types.v"} armv9_types.v
      cp ${model-src."arm_extras.v"} arm_extras.v
      cp ${model-src."armv9.v"} armv9.v
      for f in armv9_types arm_extras armv9; do coqc -R . SailArm $f.v; done
    '';
    installPhase = ''
      mkdir -p $out/${contrib}
      cp -r . $out/${contrib}/SailArm
    '';
  };
in {
  inherit coq-sail model;
  env = pkgs.buildEnv { name = "islaris-sail-env"; paths = [ isl.env coq-sail model ]; };
}
