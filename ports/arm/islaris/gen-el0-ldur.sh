#!/bin/bash
# Wave D retry of the EL0 ldur footprint (el0/STATUS, ARM-FOUNDATION 12.5): the EL0 config
# plus Islaris's own dump constraint on X20, under the host lock and a 7 GiB cap; peak RSS
# is measured with GNU time.  Extra isla arguments (e.g. -T 1) are passed through.
#   gen-el0-ldur.sh OUTDIR [ISLA ARGS...]
#   ISLA_BIN  isla b8e614bd isla-footprint   ISLA_IR85  isla-snapshots d8b31014 armv8p5.ir
#   XBIN      aarch64-linux-gnu binutils      GNU_TIME   GNU time binary
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=$1; shift; mkdir -p "$out"
: "${ISLA_BIN:?}" "${ISLA_IR85:?}" "${XBIN:?}" "${GNU_TIME:?}"
export PATH="$XBIN:$PATH"
s=$(date +%s)
flock /tmp/buri-heavy.lock prlimit --as=$((7*1024*1024*1024)) -- "$GNU_TIME" -f "maxrss_kb=%M elapsed=%e" \
  timeout 900 "$ISLA_BIN" -A "$ISLA_IR85" -f isla_footprint_no_init -C "$here/etc/aarch64_isla_coq_el0_linux.toml" \
  --simplify-registers --tree -s -x -i 8a0240f8 \
  --reset-constraint '= (bvand R20 0xfff0000000000007) 0x0000000000000000' "$@" > "$out/a1c.isla" 2> "$out/a1c.err"
echo "a1c 8a0240f8 rc=$? secs=$(( $(date +%s) - s )) lines=$(wc -l < "$out/a1c.isla")"
tail -2 "$out/a1c.err"
