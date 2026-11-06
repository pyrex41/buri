#!/bin/bash
# Disassembles the collector from the pinned spike 2 binary, in the buri-lps container.
# Usage: disasm.sh RUNTIME_ELF OUT_DIR. Function boundaries are global/static C symbols;
# local labels (.L*, $d.*) don't start functions.
set -euo pipefail
elf=$1; out=$2; mkdir -p "$out"
echo "de349ea06fc770e1dcf735f416a1713c93715aa7371528001918bdd635dcbd38  $elf" | sha256sum -c --quiet -
riscv64-linux-gnu-objdump -d "$elf" > "$out/runtime.dis"
python3 - "$out/runtime.dis" <<'P' > "$out/functions.txt"
import re,sys
cur=None; c={}
for l in open(sys.argv[1]):
    m=re.match(r'^([0-9a-f]+) <(.*)>:$',l)
    if m:
        n=m.group(2)
        if not (n.startswith('.L') or n.startswith('$')): cur=(n,m.group(1))
        continue
    if cur and re.match(r'^ +[0-9a-f]+:\t[0-9a-f]+ ',l) and 'nop' not in l: c[cur]=c.get(cur,0)+1
for (n,a),k in sorted(c.items(),key=lambda x:-x[1]): print(k,a,n)
P
