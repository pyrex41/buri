#!/bin/bash
# In buri-lps: (re)creates the emitter_ns image and fetch/decode facts in /work-s7.
# Usage: regen.sh [ADDR:HEX]   (mutation testing passes a byte patch)
set -euo pipefail
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
here=$(cd "$(dirname "$0")" && pwd); W=${W:-/work-s7}; ex=$W/theories/Examples/emitter_ns; R=/lps/s7/out/check/runtime; export W
mkdir -p "$ex"
python3 "$here/mkimage.py" $R /tmp/s7_rt ${1:-}
python3 $W/tools/elf_snapshot.py /tmp/s7_rt "$ex/SourceMemImage.v" --prefix SourceMemImage --module-name Source --namespace LinuxProcessSemantics.Examples.emitter_ns >/dev/null
RANGE=${RANGE:-36b9c:36d46,1e5a0:1e60c,2cf06:2cf64}
python3 "$here/gen_code.py" /tmp/s7_rt "$RANGE" "$ex/emitter_code.v"
