VERSION 0.8
# Build orchestration for E2E-03. Earthly only sequences steps and exports
# bytes; it decides nothing. Theorem validity is decided by coqc/coqchk inside
# `make prove`. Reproducibility is identity evidence, never semantic evidence.
#
# Targets:
#   +tools     pinned Nix toolchain (flake.nix: dotTools), fixed-output fetches only
#   +test      `make test` in the Nix sandbox (no network), exports its manifest
#   +gates     `make test` and `make prove` in the Nix sandbox, exports the
#              manifest and proof objects
#   +host      canonical bootstrap route on a pinned Ubuntu 24.04 image (needs
#              network for `make bootstrap`; not hermetic)
#   +compare   compares the +gates and +host manifests
#
# Nix's build sandbox needs namespaces inside the container: run with
#   earthly -P +gates
# Base images are pinned by digest.

FROM nixos/nix:2.24.14@sha256:4411619b45575be9fb47063c0878e2d9ef86988678b23c01bf3dd1b967d753fc
WORKDIR /buri

nix-env:
    # Optional extra CA for TLS-intercepting egress proxies. Normal CI has no
    # such file; the image's bundle is then used unchanged.
    COPY --if-exists ci-extra-ca.crt /etc/ssl/certs/ci-extra-ca.crt
    RUN cat /nix/var/nix/profiles/default/etc/ssl/certs/ca-bundle.crt > /etc/ssl/certs/buri-ca.crt && \
        if [ -f /etc/ssl/certs/ci-extra-ca.crt ]; then cat /etc/ssl/certs/ci-extra-ca.crt >> /etc/ssl/certs/buri-ca.crt; fi
    ENV NIX_SSL_CERT_FILE=/etc/ssl/certs/buri-ca.crt
    ENV SSL_CERT_FILE=/etc/ssl/certs/buri-ca.crt
    RUN printf 'experimental-features = nix-command flakes\nsandbox = true\nsandbox-fallback = false\n' >> /etc/nix/nix.conf

tools:
    FROM +nix-env
    # Only the files the toolchain derivations read, so this layer caches.
    COPY flake.nix flake.lock toolchain.lock.json rocq-packages.lock ./
    COPY scripts/bootstrap scripts/bootstrap
    RUN --privileged nix build --no-link --print-out-paths 'path:.#dotTools'

test:
    FROM +tools
    COPY . .
    RUN --privileged nix build -L --out-link /result 'path:.#test' && cp /result/_build/manifest.json /manifest.json
    SAVE ARTIFACT /manifest.json AS LOCAL _build/earthly/test-manifest.json

gates:
    FROM +tools
    COPY . .
    RUN --privileged nix build -L --out-link /result 'path:.#gates' && cp -rL /result/_build /out
    SAVE ARTIFACT /out/manifest.json AS LOCAL _build/earthly/nix-manifest.json
    SAVE ARTIFACT /out/rocq AS LOCAL _build/earthly/nix-rocq

host:
    FROM ubuntu:24.04@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852
    # Package index from the same Ubuntu snapshot as rocq-packages.lock.
    RUN apt-get update --snapshot 20260828T000000Z && \
        apt-get install -y --no-install-recommends --snapshot 20260828T000000Z \
            ca-certificates curl make python3 && \
        rm -rf /var/lib/apt/lists/*
    WORKDIR /buri
    COPY . .
    RUN make bootstrap && make test && make prove && make manifest
    SAVE ARTIFACT _build/manifest.json AS LOCAL _build/earthly/host-manifest.json

compare:
    FROM +host
    COPY +gates/manifest.json /nix-manifest.json
    RUN python3 scripts/build-manifest.py compare _build/manifest.json /nix-manifest.json
