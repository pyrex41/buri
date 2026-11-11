#!/bin/bash
# r21-image-lane measurements (census and test, not proof): docs/SHEN-JIT-IMAGE.md. In buri-lps:
#   bash spikes/image-decode/meas.sh TREE OUT   (TREE: this checkout; OUT: a fresh directory)
set -u
t=$1; o=$2; rm -rf "$o"; mkdir -p "$o"; cd "$o"
sj=/lps/p6/sj
sha256sum $sj/build/shen-jit > bin.sha
{ stat -c %s $sj/build/shen-jit; head -c 4657760 $sj/build/shen-jit | sha256sum; tail -c 783096 $sj/build/shen-jit | sha256sum; sha256sum $sj/build/runtime $sj/build/shen-jit.img; tail -c 8 $sj/build/shen-jit; echo; } > split.out
(cd $sj/build/stage0 && LC_ALL=C sha256sum *.forms *.sbc | sha256sum) > stage0.sha
python3 "$t/spikes/image-decode/census.py" $sj/build/shen-jit $sj/build/stage0 > census.out 2>&1; echo "census rc=$?"
python3 "$t/spikes/image-decode/sealgap.py" $sj/build/stage0 > sealgap.out 2>&1; echo "sealgap rc=$?"
python3 "$t/spikes/image-decode/fncells.py" $sj/build/shen-jit > fncells.out 2>&1; echo "fncells rc=$?"
cp "$t/spikes/image-decode/redef.shen" .
timeout 300 qemu-riscv64 $sj/build/shen-jit script redef.shen > redef.out 2> redef.err; echo "redef rc=$?"
sha256sum split.out census.out sealgap.out fncells.out redef.shen redef.out redef.err
