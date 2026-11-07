#!/bin/bash
# Spike 10 timing, in buri-lps, under qemu-riscv64 user mode. Min of R runs, wall ms.
# Usage: bench.sh R N1 N2   (per-iteration slope = (t(N2)-t(N1))/(N2-N1))
set -u
cd /tmp/vb; R=$1; N1=$2; N2=$3
for n in $N1 $N2; do cat > b$n.shen <<S
(tc -)
(map (/. X (eval-kl X)) (read-file "/tmp/vb/defs.kl"))
(map (/. X (eval-kl X)) (read-file "/tmp/vb/driver.kl"))
(output "~A~%" (eval-kl [vb.bench $n 0]))
S
done
t1() { local best=999999999; for i in $(seq $R); do s=$(date +%s%N); "$@" > /tmp/vb/last.out 2>&1; e=$(( ($(date +%s%N)-s)/1000000 )); [ $e -lt $best ] && best=$e; done; echo $best; }
row() { local name=$1; shift; a=$(t1 "$@" $N1); ra=$(cat last.out); b=$(t1 "$@" $N2); rb=$(cat last.out)
  echo "$name n=$N1 ${a}ms [$ra] n=$N2 ${b}ms [$rb] slope=$(python3 -c "print('%.3f' % (($b-$a)/($N2-$N1)))") ms/iter"; }
sj() { qemu-riscv64 /lps/p4/sj/build/shen-jit script b$1.shen; }
row shen-jit sj
row cake-base qemu-riscv64 ./bench-cake
row cake-fo qemu-riscv64 ./bench-fo-riscv.exe
row cake-gen qemu-riscv64 ./bench-gen-riscv.exe
row cake-fo-gen qemu-riscv64 ./bench-fo-gen-riscv.exe
row cake-cells qemu-riscv64 ./bench-cells.exe
