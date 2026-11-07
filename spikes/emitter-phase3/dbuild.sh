#!/bin/bash
# In buri-lps: copies coq/ into the example and builds the named targets, memory-capped.
# A zero exit from dune is not evidence by itself: each target's .vo is checked to exist.
here=$(cd "$(dirname "$0")" && pwd); W=${W:-/work-s8}; ex=$W/theories/Examples/emitter_risks_ns
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
mkdir -p "$ex"; cp "$here"/coq/*.v "$ex"/; cd $W; export OCAMLRUNPARAM=d=4; ulimit -v 9000000
s=$(date +%s); timeout ${LIMIT:-1200} dune build "$@" -j3 > /tmp/s8-$(basename $W).log 2>&1; rc=$?
echo "rc=$rc secs=$(( $(date +%s)-s ))"
for t in "$@"; do [ -f _build/default/$t ] || { echo "MISSING $t"; rc=9; }; done
grep -vE "^Defined|Running as root|^$" /tmp/s8-$(basename $W).log | grep -v -E "Warning: Use of|Abbreviation|notation-for-abbreviation" | grep -E -A${ERRA:-22} "Error" | head -${ERRL:-40} | cut -c1-${ERRC:-240}
exit $rc
