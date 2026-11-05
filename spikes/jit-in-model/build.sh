#!/bin/bash
# Run inside the buri-lps container. Builds both binaries and snapshots them into
# Theorem's examples tree as the jit_write_run_ns example.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
ex=/work/theories/Examples/jit_write_run_ns
mkdir -p "$ex"
FLAGS="-static -nostdlib -nostartfiles -no-pie -march=rv64g_zifencei -mabi=lp64d -Wl,--build-id=none -s"
riscv64-linux-gnu-gcc $FLAGS ${SRCDEFS:-} -Wl,-T,"$here/rwx.lds" -Wl,--no-warn-rwx-segments -o /tmp/src.elf "$here/program.S"
riscv64-linux-gnu-gcc $FLAGS -Wl,-z,separate-code -o /tmp/tgt.elf "$here/target/program.S"
python3 /work/tools/elf_snapshot.py /tmp/src.elf "$ex/SourceMemImage.v" --prefix SourceMemImage --module-name Source --namespace LinuxProcessSemantics.Examples.jit_write_run_ns
python3 /work/tools/elf_snapshot.py /tmp/tgt.elf "$ex/TargetMemImage.v" --prefix TargetMemImage --module-name Target --namespace LinuxProcessSemantics.Examples.jit_write_run_ns
riscv64-linux-gnu-objdump -d /tmp/src.elf | grep -E '^ +[0-9a-f]+:'
riscv64-linux-gnu-objdump -d /tmp/tgt.elf | grep -E '^ +[0-9a-f]+:'
riscv64-linux-gnu-readelf -lW /tmp/tgt.elf | grep -E 'LOAD|Entry'
qemu-riscv64 /tmp/src.elf || echo "source exit=$?"
qemu-riscv64 /tmp/tgt.elf || echo "target exit=$?"
sha256sum /tmp/src.elf /tmp/tgt.elf
