#!/bin/bash
# Sync the proof into the spike's own model tree and build targets. Run in buri-lps.
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
cp /buri/spikes/jit-slice/coq/*.v /work-s4/theories/Examples/jit_slice/
cd /work-s4
timeout ${T:-900} dune build ${*/#/theories/Examples/jit_slice/} -j3 2>&1 | grep -vE "Running as root|^Defined|deprecated" | head -${N:-40} | cut -c1-${W:-500}
