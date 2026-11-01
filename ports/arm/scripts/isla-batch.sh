#!/bin/sh
# Run isla-footprint (Islaris flags: --simplify-registers --tree -s) on each
# "offset bytes" line of LIST, writing OUTDIR/<offset>-<bytes>.trace and a
# status line per instruction to OUTDIR/status.
# usage: isla-batch.sh LIST OUTDIR
list=$1; out=$2
mkdir -p "$out"
: > "$out/status"
while read -r off bytes; do
  start=$(date +%s)
  "${ISLA94:?set ISLA94 to an isla-footprint wrapper, see ports/arm/README.md}" "$bytes" \
    --simplify-registers --tree -s > "$out/$off-$bytes.trace" 2> "$out/$off-$bytes.err"
  rc=$?
  end=$(date +%s)
  echo "$off $bytes rc=$rc secs=$((end-start)) lines=$(wc -l < "$out/$off-$bytes.trace")" >> "$out/status"
done < "$list"
