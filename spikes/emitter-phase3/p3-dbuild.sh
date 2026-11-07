#!/bin/bash
# In buri-lps: copies coq-p3/ into /work-s9b's example emitter_p3_ns and builds the named targets, memory-capped.
# A zero exit from dune is not evidence by itself: each target's .vo is checked to exist.
here=$(cd "$(dirname "$0")" && pwd); W=${W:-/work-s9b}; ex=$W/theories/Examples/emitter_p3_ns
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
mkdir -p "$ex"; for f in "$here"/coq-p3/*.v; do cmp -s "$f" "$ex/$(basename $f)" || cp "$f" "$ex"/; done
for f in "$ex"/*.v; do [ -f "$here/coq-p3/$(basename $f)" ] || rm -f "$f"; done
cd $W; export OCAMLRUNPARAM=d=4; ulimit -v 9000000
s=$(date +%s); timeout ${LIMIT:-1800} dune build "$@" -j2 > /tmp/s9p3-$(basename $W).log 2>&1; rc=$?
echo "rc=$rc secs=$(( $(date +%s)-s ))"
for t in "$@"; do [ -f _build/default/$t ] || { echo "MISSING $t"; rc=9; }; done
grep -vE "^Defined|Running as root|^$" /tmp/s9p3-$(basename $W).log | grep -v -E "Warning: Use of|Abbreviation|notation-for-abbreviation" | grep -E -B2 -A${ERRA:-25} "Error" | head -${ERRL:-50} | cut -c1-${ERRC:-260}
exit $rc
