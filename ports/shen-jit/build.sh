#!/bin/bash
# The named build of the Shen/JIT lane (docs/SHEN-JIT.md), at the frozen pin: static, ET_EXEC, musl, RV64GC shen-jit with a static RWX code arena.
# Run inside a fresh ubuntu:24.04 linux/arm64 container, with this directory readable:
#   docker run --rm --platform linux/arm64 -v "$PWD":/ports ubuntu:24.04 bash /ports/build.sh [OUT]
# OUT defaults to /tmp/shen-jit-rv64. The binary needs qemu-riscv64 (or RISC-V) to run.
# The hash depends on OUT, since -g records the build directory: the named binary (toolchain.lock.json)
# is built with OUT=/lps/p4/sj, and the same command in a fresh container gives the same bytes.
set -euo pipefail
SPIKE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:-/tmp/shen-jit-rv64}
COMMIT=d3348cefbb2b209992039c1c0f55751241750364
ZIG=zig-linux-aarch64-0.13.0
ZIG_SHA256=041ac42323837eb5624068acd8b00cd5777dac4cf91179e8dad7a7e90dd0c556

export DEBIAN_FRONTEND=noninteractive
command -v qemu-riscv64 >/dev/null && command -v git >/dev/null || {
  apt-get update -qq >/dev/null
  apt-get install -y -qq qemu-user make curl xz-utils git ca-certificates >/dev/null 2>&1
}
if [ ! -x /opt/$ZIG/zig ]; then
  curl -fsSL -o /opt/zig.tar.xz https://ziglang.org/download/0.13.0/$ZIG.tar.xz
  echo "$ZIG_SHA256  /opt/zig.tar.xz" | sha256sum -c -
  tar -C /opt -xf /opt/zig.tar.xz
fi
export ZIG_GLOBAL_CACHE_DIR=/tmp/zg ZIG_LOCAL_CACHE_DIR=/tmp/zl
CC_RV=/usr/local/bin/cc-rv64
cat > $CC_RV <<EOF
#!/bin/sh
exec /opt/$ZIG/zig cc -target riscv64-linux-musl -mcpu=baseline_rv64 -fno-sanitize=undefined -fno-pie -no-pie "\$@"
EOF
chmod +x $CC_RV

rm -rf "$OUT"; git config --global --add safe.directory '*'
git clone -q https://github.com/tizoc/shen-jit.git "$OUT"; cd "$OUT"; git checkout -q $COMMIT
git apply "$SPIKE/shen-jit-rv64-arena.patch"

# Stage 0 with the pinned native host, checked against the repository's manifest.
make deps >/dev/null
make build/stage0/.done >/dev/null
( cd build && grep ' stage0/' ../generated.sha256 | sha256sum -c --quiet - )
echo "stage 0 matches generated.sha256"

$CC_RV -std=c11 -O2 -g ${SPIKE_ARENA_CFLAGS:-} -c spikes-overlay/arena.c -o spikes-overlay/arena.o
make -j"$(nproc)" build/runtime CC=$CC_RV >/dev/null 2>&1
( cd build
  qemu-riscv64 ./runtime --stage1 stage0 shen-jit.img
  cat runtime shen-jit.img > shen-jit; chmod +x shen-jit
  sha256sum runtime shen-jit.img shen-jit )
