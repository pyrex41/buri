#!/bin/bash
# In buri-lps: (re)creates the gc_rate_ns image and fetch/decode facts in /work-s5.
# Usage: regen.sh [ADDR:HEXBYTES]  (mutation testing passes a byte patch)
set -euo pipefail
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
here=$(cd "$(dirname "$0")" && pwd); W=/work-s5; ex=$W/theories/Examples/gc_rate_ns
mkdir -p "$ex"
python3 "$here/mkimage.py" /lps/runtime /tmp/rt_trunc ${1:-} >/dev/null
python3 $W/tools/elf_snapshot.py /tmp/rt_trunc "$ex/SourceMemImage.v" --prefix SourceMemImage --module-name Source --namespace LinuxProcessSemantics.Examples.gc_rate_ns >/dev/null
python3 "$here/gen_code.py" /tmp/rt_trunc 10440:10456,14e00:14e4e,11bc0:11dc2,118e0:11bc0 "$ex/gc_rate_code.v" >/dev/null
