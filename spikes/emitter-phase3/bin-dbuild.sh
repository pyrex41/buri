#!/bin/bash
# In buri-lps: copies coq-bin/ into the s9bin_ns example and builds the named targets, memory-capped, -j2.
# A zero exit from dune is not evidence by itself: each target's .vo is checked to exist.
here=$(cd "$(dirname "$0")" && pwd); W=${W:-/work-s9a}; ex=$W/theories/Examples/s9bin_ns
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
mkdir -p "$ex"; cp "$here"/coq-bin/*.v "$ex"/; cd $W; export OCAMLRUNPARAM=d=4; ulimit -v 9000000
log=/tmp/s9bin-$(basename $W).log
s=$(date +%s); timeout ${LIMIT:-1500} dune build "$@" -j2 > $log 2>&1; rc=$?
echo "rc=$rc secs=$(( $(date +%s)-s ))"
for t in "$@"; do [ -f _build/default/$t ] || { echo "MISSING $t"; rc=9; }; done
grep -vE "^Defined|Running as root|^$" $log | grep -E -B3 -A${ERRA:-25} "Error" | head -${ERRL:-60} | cut -c1-${ERRC:-300}
exit $rc
