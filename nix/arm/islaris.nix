# Separate Coq 8.19.0 + Iris + Lithium + Islaris environment for E2E-20.
#
# This is NOT the repository's proof toolchain.  The repository pins Debian
# Coq 8.18.0 (scripts/rocq, rocq-packages.lock) and nothing here changes it.
# Islaris c978e10f requires Coq exactly 8.19.0 and Iris/Lithium dev pins that
# opam serves from opam.ocaml.org / gitlab.mpi-sws.org, which this session's
# egress proxy refuses.  Every dev pin below is instead fetched by exact git
# commit from a GitHub repository (builtins.fetchGit, pinned rev).  A git
# commit id fixes the whole tree by hash; the opam "dev.<date>.<n>.<sha8>"
# version strings name the same commit prefix, which is the only published
# hash for these dev packages (opam's archive checksums were unreachable).
#
#   nix-build nix/arm/islaris.nix -A islaris      # theories + frontend
#
# Pins (see docs/ARM-FOUNDATION.md section 10):
#   nixpkgs     885ba4d038f1 (same tarball as tools.nix)
#   coq         8.19.0  (nixpkgs release table hash sha256-ixsYCvCX...)
#   stdpp       a1a12e00fba07f2e41ccd74a8b593b88e48fc2c3  (coq-stdpp dev.2024-09-10.3.a1a12e00), github rocq-iris/stdpp
#   iris        6f24ed4baa4d61967a95bac834eab2c66f3b76fa  (coq-iris dev.2024-09-10.1.6f24ed4b), github rocq-iris/iris
#   lithium     7945a29d1647970709a9b5ad2ffc53c757e130cc  (coq-lithium dev.2024-09-11.0.7945a29d),
#               refinedc tree mirrored at github UIC-verif-group/refinedC
#   record-upd  50e45e9f4ed52840427c3bfddc9037a645d9bf19  (tag v0.3.3), github tchajed/coq-record-update
#   isla-lang   bda86c9f0bd28bbaa2481f50ddc986ede342805a  (islaris pin-depends), github rems-project/isla-lang
#   islaris     c978e10f50db5c40f0fdf113f5f76a779782c6f9, github rems-project/islaris
# Deviations from Islaris's opam file, recorded rather than hidden: dune is
# nixpkgs 3.23.1 (Islaris pins 3.9.1), ott is nixpkgs 0.34 (>= 0.31 required).
{ nixpkgs ? builtins.fetchTarball {
    url = "https://releases.nixos.org/nixpkgs/nixpkgs-26.11pre1105041.885ba4d038f1/nixexprs.tar.zst";
    sha256 = "sha256-RcsCCbI6YtyC9Be5c0XiwLMHJivUaGWSNHjJt0Q3NBE=";
  }
}:
let
  pkgs = import nixpkgs { system = "x86_64-linux"; };
  inherit (pkgs) lib stdenv;

  coq = pkgs.coq_8_19.override { version = "8.19.0"; };
  ocamlPackages = coq.ocamlPackages;
  ocaml = ocamlPackages.ocaml;
  dune = ocamlPackages.dune_3;

  git = url: rev: builtins.fetchGit { inherit url rev; allRefs = true; };
  srcs = {
    stdpp = git "https://github.com/rocq-iris/stdpp" "a1a12e00fba07f2e41ccd74a8b593b88e48fc2c3";
    iris = git "https://github.com/rocq-iris/iris" "6f24ed4baa4d61967a95bac834eab2c66f3b76fa";
    refinedc = git "https://github.com/UIC-verif-group/refinedC" "7945a29d1647970709a9b5ad2ffc53c757e130cc";
    record-update = git "https://github.com/tchajed/coq-record-update" "50e45e9f4ed52840427c3bfddc9037a645d9bf19";
    isla-lang = git "https://github.com/rems-project/isla-lang" "bda86c9f0bd28bbaa2481f50ddc986ede342805a";
    islaris = git "https://github.com/rems-project/islaris" "c978e10f50db5c40f0fdf113f5f76a779782c6f9";
  };

  contrib = "lib/coq/8.19/user-contrib";
  coqpath = deps: lib.concatMapStringsSep ":" (d: "${d}/${contrib}") deps;

  # A coq_makefile-built library.  `files` overrides the _CoqProject.
  coqLib = { pname, src, deps ? [ ], pre ? "", make ? "make -j$NIX_BUILD_CORES", install ? "make install" }:
    stdenv.mkDerivation {
      inherit pname src;
      version = "pinned";
      nativeBuildInputs = [ coq ocaml ocamlPackages.findlib pkgs.which pkgs.python3 ];
      dontConfigure = true;
      buildPhase = ''
        export COQPATH=${coqpath deps}
        patchShebangs .
        ${pre}
        ${make}
      '';
      installPhase = ''
        export COQPATH=${coqpath deps}
        ${install} COQLIBINSTALL=$out/${contrib} COQPLUGININSTALL=$out/lib/ocaml COQDOCINSTALL=$out/share/doc
      '';
    };

  stdpp = coqLib { pname = "coq-stdpp"; src = srcs.stdpp; };
  record-update = coqLib {
    pname = "coq-record-update"; src = srcs.record-update;
    make = "make -j$NIX_BUILD_CORES NO_TEST=1";
  };
  iris = coqLib {
    pname = "coq-iris"; src = srcs.iris; deps = [ stdpp ];
    make = "./make-package iris -j$NIX_BUILD_CORES";
    install = "./make-package iris install";
  };
  lithium = coqLib {
    pname = "coq-lithium"; src = srcs.refinedc; deps = [ stdpp iris record-update ];
    pre = ''
      { echo "-Q theories/lithium lithium"
        echo "-arg -w -arg -notation-overridden"
        echo "-arg -w -arg -redundant-canonical-projection"
        ls theories/lithium/*.v; } > _CoqProject.lithium
      coq_makefile -f _CoqProject.lithium -o Makefile.lithium
    '';
    make = "make -f Makefile.lithium -j$NIX_BUILD_CORES";
    install = "make -f Makefile.lithium install";
  };

  # Islaris theories (isla, isla.aarch64) plus the frontend, in one dune
  # workspace with isla-lang vendored.  Only the parts needed here are built.
  islaris = stdenv.mkDerivation {
    pname = "islaris";
    version = "c978e10f";
    src = srcs.islaris;
    nativeBuildInputs = [ coq ocaml dune pkgs.ott ocamlPackages.findlib ocamlPackages.menhir pkgs.which ];
    buildInputs = with ocamlPackages; [ cmdliner pprint integers menhirLib ];
    dontConfigure = true;
    postPatch = ''
      mkdir -p vendor && cp -r ${srcs.isla-lang} vendor/isla-lang && chmod -R u+w vendor
      echo ${pkgs.ott}/share/ott > vendor/isla-lang/ott.path.txt
      substituteInPlace vendor/isla-lang/dune \
        --replace-fail '(with-stdout-to %{target} (system "opam var ott:share"))' '(copy ott.path.txt %{target})'
      substituteInPlace theories/dune \
        --replace-fail '(action (with-stdout-to %{target} (system "opam var isla-lang:share"))))' '(action (with-stdout-to %{target} (echo "unused\n"))))' \
        --replace-fail '(copy "%{read-lines:isla-lang.share}/isla_lang.v" %{target})' '(copy ../vendor/isla-lang/lang.v %{target})'
      # Root dune env wraps coqc in an opam-only timing script; drop it.
      rm dune
      # Not needed for this experiment; keeps the build to the core theories.
      rm -rf sail sail-riscv pkvm_handler examples instructions theories/riscv64
      printf 'let version : string = "c978e10f"\n' > frontend/version.ml
      sed -i '/(rule/,$d' frontend/dune
    '';
    buildPhase = ''
      export COQPATH=${coqpath [ stdpp iris lithium record-update ]}
      export HOME=$TMPDIR
      dune build --profile release -j $NIX_BUILD_CORES @theories/all @theories/aarch64/all frontend/main.exe 2>&1 | tail -40
      test -f _build/default/frontend/main.exe
    '';
    installPhase = ''
      mkdir -p $out/${contrib} $out/bin $out/etc
      cp -r _build/default/theories $out/${contrib}/isla
      cp _build/default/frontend/main.exe $out/bin/islaris
      cp -r etc/* $out/etc/
    '';
  };
in {
  inherit coq stdpp iris record-update lithium islaris pkgs;
  env = pkgs.buildEnv { name = "islaris-env"; paths = [ coq stdpp iris record-update lithium islaris ]; };
}
