#!/bin/bash
# Run in the buri-lps container. Each mutant must fail to compile; the unmodified
# binaries must compile again afterwards.
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
here=/buri/spikes/jit-in-model; ex=/work/theories/Examples/jit_write_run_ns; cd /work
try() { # name, sed expr, file relative to spike
  m=$(mktemp -d); cp -a "$here"/. "$m"/; sed -i "$2" "$m/$3"
  cmp -s "$m/$3" "$here/$3" && { echo "MUTANT_NOT_APPLIED $1"; return; }
  bash "$m/build.sh" >/tmp/mb.log 2>&1
  if timeout 900 dune build theories/Examples/jit_write_run_ns -j4 >/tmp/m.log 2>&1; then echo "MUTANT_ACCEPTED $1"
  else echo "rejected $1: $(grep -m1 -A1 '^Error' /tmp/m.log | tr '\n' ' ' | cut -c1-120)"; fi
  rm -rf "$m"
}
try wrong-generated-result 's/lui   a4, 0x2a00/lui   a4, 0x2b00/' program.S
try second-store-removed 's/sw    a4, 4(a5)/nop/' program.S
try first-store-removed 's/sw    a4, 0(a5)/nop/' program.S
try call-wrong-address 's/jalr  ra, 0(a5)/jalr  ra, 4(a5)/' program.S
try target-exits-43 's/li    a0, 42/li    a0, 43/' target/program.S
bash "$here/build.sh" >/tmp/mb.log 2>&1
timeout 900 dune build theories/Examples/jit_write_run_ns -j4 >/tmp/m.log 2>&1 && echo "restored-ok" || { echo RESTORE_FAILED; tail -5 /tmp/m.log; }
