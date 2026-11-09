#!/bin/sh
# Kernel-check every generated stage 0 module, one at a time, single-threaded and nice'd.
export PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=1
cd "$(dirname "$0")/.."
for f in gen/Stage0Gen/S0_*.lean; do
  m=$(basename $f .lean)
  s=$(date +%s)
  out=$(nice -n 19 lake build Stage0Gen.$m 2>&1)
  rc=$?
  e=$(date +%s)
  echo "$m rc=$rc wall=$((e-s))s $(echo "$out" | grep -m1 'error' | cut -c1-150)"
done
