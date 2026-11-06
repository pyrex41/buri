#!/bin/bash
# Sets up /work-s5 in the buri-lps container (spikes/jit-in-model/setup.sh built /work), given
# spike 2's runtime at /lps/runtime. Then run regen.sh, build.sh, mutate.sh, disasm.sh.
set -euo pipefail
[ -d /work-s5 ] || cp -a /work /work-s5
mkdir -p /work-s5/theories/Examples/gc_rate_ns
