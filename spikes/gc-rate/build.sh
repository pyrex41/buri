#!/bin/bash
# In buri-lps: copies the proofs to /work-s5 and builds the named targets (default all),
# printing per-file compile time.
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
here=$(cd "$(dirname "$0")" && pwd); ex=/work-s5/theories/Examples/gc_rate_ns
cp "$here"/coq/*.v "$ex"/
cd /work-s5
s=$(date +%s)
timeout ${LIMIT:-1500} dune build ${@:-theories/Examples/gc_rate_ns} -j3 > /tmp/s5.log 2>&1; rc=$?
echo "rc=$rc secs=$(( $(date +%s)-s ))"
grep -vE 'deprecated|^Defined|Running as root|Warning: Use of|^$' /tmp/s5.log | head -${ERRLINES:-50} | cut -c1-${ERRW:-260}
exit $rc
