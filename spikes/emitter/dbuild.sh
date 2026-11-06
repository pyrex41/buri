#!/bin/bash
# In buri-lps: copies coq/ into the example and builds the named targets, memory-capped.
# A zero exit from dune is not evidence by itself: each target's .vo is checked to exist.
here=$(cd "$(dirname "$0")" && pwd); W=${W:-/work-s7}; ex=$W/theories/Examples/emitter_ns
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
cp "$here"/coq/*.v "$ex"/; cd $W; export OCAMLRUNPARAM=d=4; ulimit -v 9000000
s=$(date +%s); timeout ${LIMIT:-1200} dune build "$@" -j3 > /tmp/s7-$(basename $W).log 2>&1; rc=$?
echo "rc=$rc secs=$(( $(date +%s)-s ))"
for t in "$@"; do [ -f _build/default/$t ] || { echo "MISSING $t"; rc=9; }; done
grep -vE '^Warning.*deprecated|^\[.*deprecated|^Defined|Running as root|^$' /tmp/s7-$(basename $W).log | head -${ERRL:-30} | cut -c1-240
exit $rc
