#!/bin/bash
# Regenerate the EL0 / MMU-on isla footprints in el0/ (see el0/STATUS).
#   gen-el0-traces.sh OUTDIR
#   ISLA_BIN   isla b8e614bd isla-footprint     ISLA_IR85  isla-snapshots d8b31014 armv8p5.ir
#   XBIN       aarch64-linux-gnu binutils       ISLARIS_SRC rems-project/islaris c978e10f
# One isla job at a time, each capped at 7 GiB address space and 15 min, so
# an overrun is recorded as resource exhaustion instead of hurting the host.
# On a shared machine: flock /tmp/buri-heavy.lock gen-el0-traces.sh OUTDIR
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=$1; mkdir -p "$out"
: "${ISLA_BIN:?}" "${ISLA_IR85:?}" "${XBIN:?}" "${ISLARIS_SRC:?}"
cfg="$out/aarch64_isla_coq_el0_linux.toml"
bash "$here/etc/mk-el0-config.sh" "$ISLARIS_SRC" > "$cfg"
cmp -s "$cfg" "$here/etc/aarch64_isla_coq_el0_linux.toml" || { echo 'EL0 config drifted' >&2; exit 1; }
export PATH="$XBIN:$PATH"
for nb in a0:ff0a00f1 a4:01040054 a8:1e0001aa ac:df0b40f2 a10:a1000054 a14:170001ab \
          a18:66000054 a1c:8a0240f8 a20:40011fd6; do
  n=${nb%%:*} op=${nb#*:} s=$(date +%s)
  ( ulimit -v 7340032; timeout 900 "$ISLA_BIN" -A "$ISLA_IR85" -f isla_footprint_no_init -C "$cfg" \
      --simplify-registers --tree -s -x -i "$op" ) > "$out/$n.isla" 2> "$out/$n.err"
  echo "$n $op rc=$? secs=$(( $(date +%s) - s )) lines=$(wc -l < "$out/$n.isla")"
done
