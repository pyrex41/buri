{
  # Pinned, hermetic build environment for the Buri gates (END-TO-END-PLAN E2E-03).
  #
  # Identity evidence only: a reproducible build shows that the same pinned
  # inputs produce the same bytes. It never shows that any compiler, checker or
  # runtime preserves semantics. Theorem validity is decided by Coq/coqchk run by
  # `make prove`, never by this file or by the manifest tooling.
  #
  # Pinned inputs (all fixed-output, verified by hash before use):
  #   * nixpkgs: nixos-24.11 channel release 719113, git revision
  #     50ab793786d9de88ee30ec4e4c24fb4236fc2674 (narHash in flake.lock).
  #     Supplies only the launcher/runtime: glibc, gmp, python3, make, coreutils.
  #   * Shen-Scheme v0.52 linux-x64 release archive. This is a PREBUILT BINARY
  #     pinned by sha256 (the same digest as scripts/bootstrap and
  #     toolchain.lock.json); it is not rebuilt from source here. The from-source
  #     rebuild of shen-scheme and Chez Scheme is an open obligation (docs/BUILD.md).
  #   * PR 117 typechecker overlay t-star.shen at shen-sources commit
  #     ec16a9fa4fc2e87e2aa336fb1ae30e8ac2266394 (sha256 as in scripts/bootstrap).
  #   * Coq 8.18.0 / OCaml 4.14.1: the canonical route. The exact Ubuntu snapshot
  #     .deb files listed in rocq-packages.lock (sha256 per line), extracted
  #     unmodified. Their ELF executables are launched through nixpkgs' glibc
  #     dynamic loader with nixpkgs gmp, instead of the host's /lib64 loader,
  #     libc and libgmp. The executable bytes are identical to the deb route.
  #   * `coq-nixpkgs` (nixpkgs coq_8_18) is exposed for comparison only. It is a
  #     different binary (different OCaml build and patch level) and is NOT used
  #     by any gate.
  description = "Buri: pinned toolchain and hermetic gate builds";

  inputs.nixpkgs.url =
    "https://releases.nixos.org/nixos/24.11/nixos-24.11.719113.50ab793786d9/nixexprs.tar.xz";

  outputs = { self, nixpkgs }:
    let
      lib = nixpkgs.lib;
      nixpkgsRevision = "50ab793786d9de88ee30ec4e4c24fb4236fc2674";
      toolchain = builtins.fromJSON (builtins.readFile ./toolchain.lock.json);
      bootstrapScript = builtins.readFile ./scripts/bootstrap;

      # Target systems. Only x86_64-linux has pinned binary inputs today.
      # aarch64-linux is declared but intentionally not built: there is no
      # pinned Shen-Scheme linux-arm64 release asset and rocq-packages.lock pins
      # amd64 debs only. ARM experiments live under nix/arm/ (separate workstream).
      targetSystems = {
        x86_64-linux = "pinned-binaries";
        aarch64-linux = "declared-unbuilt";
      };

      # Source given to hermetic builds: the flake's tracked tree, minus local
      # tool links and build products.
      source = lib.cleanSourceWith {
        src = self;
        filter = path: type:
          let base = baseNameOf path; in
          !(base == ".tools" || base == "_build" || base == ".git" || base == "ci-extra-ca.crt"
            || lib.hasPrefix "result" base);
      };

      forX86 = f: f (import nixpkgs { system = "x86_64-linux"; });

      x86 = forX86 (pkgs:
        let
          shenSha = toolchain.host_archive_sha256."linux-x64";
          overlaySha = toolchain.overlay_sha256;
          _sameShenHash = assert lib.hasInfix shenSha bootstrapScript; true;
          _sameOverlayHash = assert lib.hasInfix overlaySha bootstrapScript; true;

          shenArchive = assert _sameShenHash; pkgs.fetchurl {
            name = "shen-scheme-v0.52-linux-x64-bin.tar.gz";
            url = "${toolchain.host}/releases/download/${toolchain.release}/shen-scheme-${toolchain.release}-linux-x64-bin.tar.gz";
            sha256 = shenSha;
          };

          tStarOverlay = assert _sameOverlayHash; pkgs.fetchurl {
            name = "t-star-pr117.shen";
            url = "https://raw.githubusercontent.com/Shen-Language/shen-sources/${toolchain.required_kernel_commit}/${toolchain.overlay_path}";
            sha256 = overlaySha;
          };

          # One fixed-output fetch per line of rocq-packages.lock.
          debLines = builtins.filter (l: l != "")
            (lib.splitString "\n" (builtins.readFile ./rocq-packages.lock));
          rocqDebs = map (line:
            let
              fields = lib.splitString " " line;
              hash = builtins.elemAt fields 0;
              path = builtins.elemAt fields 1;
            in pkgs.fetchurl {
              name = baseNameOf path;
              url = "${toolchain.rocq.snapshot}/${path}";
              sha256 = hash;
            }) debLines;

          loader = "${pkgs.glibc}/lib/ld-linux-x86-64.so.2";
          libraryPath = "${pkgs.gmp}/lib:${pkgs.glibc}/lib";

          # Shen-Scheme: archive extracted unmodified under dist/; bin/shen-scheme
          # is a launcher. scripts/shen clears SHEN_SCHEME_HOME, so the launcher
          # sets it to the pinned library directory: the same directory the
          # binary would find relative to its own path on a host install.
          shenHost = pkgs.runCommand "buri-shen-scheme-v0.52" { } ''
            mkdir -p $out/dist $out/bin
            tar xzf ${shenArchive} --no-same-owner -C $out/dist
            real=$out/dist/shen-scheme-v0.52-linux-bin/bin/shen-scheme
            test -x "$real"
            cat > $out/bin/shen-scheme <<EOF
            #!${pkgs.runtimeShell}
            export SHEN_SCHEME_HOME=$out/dist/shen-scheme-v0.52-linux-bin/lib/shen-scheme
            exec ${loader} --library-path ${libraryPath} $real "\$@"
            EOF
            chmod +x $out/bin/shen-scheme
          '';

          # Coq: the six pinned debs extracted unmodified under payload/, with
          # launchers in usr/bin for every ELF executable.
          rocqTree = pkgs.runCommand "buri-coq-8.18.0-ubuntu-debs"
            { nativeBuildInputs = [ pkgs.dpkg pkgs.file ]; } ''
            mkdir -p $out/payload $out/usr/bin
            ${lib.concatMapStringsSep "\n" (d: "dpkg-deb -x ${d} $out/payload") rocqDebs}
            ln -s $out/payload/usr/lib $out/usr/lib
            ln -s $out/payload/usr/share $out/usr/share
            ln -s $out/payload/etc $out/etc
            for tool in $out/payload/usr/bin/*; do
              name=$(basename "$tool")
              if file -b "$tool" | grep -q '^ELF'; then
                cat > $out/usr/bin/$name <<EOF
            #!${pkgs.runtimeShell}
            exec ${loader} --library-path ${libraryPath} $tool "\$@"
            EOF
                chmod +x $out/usr/bin/$name
              else
                ln -s "$tool" $out/usr/bin/$name
              fi
            done
          '';

          launcher = builtins.toJSON {
            schema = "buri-launcher-1";
            route = "nix";
            nixpkgs_revision = nixpkgsRevision;
            loader = loader;
            library_path = lib.splitString ":" libraryPath;
            shen_payload = "${shenHost}/dist/shen-scheme-v0.52-linux-bin";
            shen_executable = "${shenHost}/dist/shen-scheme-v0.52-linux-bin/bin/shen-scheme";
            rocq_payload = "${rocqTree}/payload";
          };

          # The `.tools` layout scripts/shen and scripts/rocq already expect.
          dotTools = pkgs.runCommand "buri-dot-tools" { } ''
            mkdir -p $out
            printf '%s\n' ${shenHost}/bin/shen-scheme > $out/host-path
            cp ${tStarOverlay} $out/t-star-pr117.shen
            ln -s ${shenHost} $out/host
            ln -s ${rocqTree} $out/rocq
            cat > $out/launcher.json <<'EOF'
            ${launcher}
            EOF
          '';

          gateTools = with pkgs; [
            bash coreutils diffutils findutils gnugrep gnused gawk gnumake python3
          ];

          gate = name: targets: pkgs.stdenvNoCC.mkDerivation {
            name = "buri-${name}";
            src = source;
            nativeBuildInputs = gateTools;
            dontConfigure = true;
            dontFixup = true;
            # Fixed locale and time zone; the gates must not depend on them.
            LC_ALL = "C";
            TZ = "UTC";
            buildPhase = ''
              runHook preBuild
              ln -s ${dotTools} .tools
              ${lib.concatMapStringsSep "\n" (t: "make ${t}") targets}
              make manifest-test
              python3 scripts/build-manifest.py write _build/manifest.json
              runHook postBuild
            '';
            installPhase = ''
              mkdir -p $out
              cp -r _build $out/_build
            '';
          };

          gates = gate "gates" [ "test" "prove" ];
          testGate = gate "test" [ "test" ];
        in {
          packages = {
            inherit shenArchive tStarOverlay shenHost rocqTree dotTools gates;
            test = testGate;
            coq-nixpkgs = pkgs.coq_8_18;
            default = gates;
          };
          checks = {
            test = testGate;
            prove = gates;
          };
          devShells.default = pkgs.mkShell {
            packages = gateTools ++ [ pkgs.git ];
            LC_ALL = "C";
            TZ = "UTC";
            BURI_NIX_TOOLS = "${dotTools}";
            shellHook = ''
              if [ -L .tools ] || [ ! -e .tools ]; then
                ln -sfn ${dotTools} .tools
                echo "buri: .tools -> ${dotTools} (pinned nix toolchain)"
              else
                echo "buri: existing .tools directory kept (bootstrap route); nix tools at $BURI_NIX_TOOLS"
              fi
            '';
          };
        });

      # aarch64-linux: declared target, nothing pinned to build yet. Only the
      # manifest tooling (pure Python) is meaningful there.
      aarch64 = let pkgs = import nixpkgs { system = "aarch64-linux"; }; in {
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [ coreutils gnumake python3 git ];
          shellHook = ''
            echo "buri: aarch64-linux is a declared, unbuilt target; no pinned Shen-Scheme or Coq binaries exist for it." >&2
          '';
        };
      };
    in {
      lib = { inherit targetSystems nixpkgsRevision; };
      packages.x86_64-linux = x86.packages;
      checks.x86_64-linux = x86.checks;
      devShells.x86_64-linux = x86.devShells;
      devShells.aarch64-linux = aarch64.devShells;
    };
}
