#!/bin/sh
# Verify one module, nice'd, with checked dependencies cached. Usage: ./check.sh Buri.X.fst [extra F* options]
# Prints wall-clock and CPU time; appends a line to timings.log.
set -u
here=$(cd "$(dirname "$0")" && pwd)
FSTAR=${FSTAR:-$HOME/opt/fstar-v2026.10.25/fstar-run}
f=$1; shift
mkdir -p "$here/_cache"
start=$(date +%s)
/usr/bin/time -p nice -n 19 "$FSTAR" --cache_checked_modules --cache_dir "$here/_cache" --odir "$here/_out" \
  --include "$here" --include "$here/stage0" "$here/$f" "$@" 2> "$here/_cache/last.err"
rc=$?
end=$(date +%s)
grep -v '^real\|^user\|^sys' "$here/_cache/last.err" >&2
cpu=$(awk '/^user/{u=$2} /^sys/{s=$2} END{print u+s}' "$here/_cache/last.err")
echo "$f rc=$rc wall=$((end-start))s cpu=${cpu}s $*" | tee -a "$here/timings.log"
exit $rc
