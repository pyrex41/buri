#!/bin/bash
# Reproduces docs/SHEN-JIT-IMAGE.md's measurements in buri-lps. Measurement, not a lane check.
#   run.sh SJ_DIR OUT     (SJ_DIR: the pinned build, e.g. /lps/p6/sj; OUT: a fresh directory)
# Wrap it in /lps/bin/rocq-slot. ImgData.v (the image's 97887 words and the 955 .sbc trees) takes
# about 18 minutes to compile and about 1.3 GB.
set -u
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
sj=$1; out=$2
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
rm -rf "$out"; mkdir -p "$out"; cd "$out"
sha256sum "$sj/build/shen-jit"
(cd "$sj/build/stage0" && LC_ALL=C sha256sum *.forms *.sbc | sha256sum)
python3 "$here/census.py" "$sj/build/shen-jit" "$sj/build/stage0" > census.out || { echo CENSUS_FAILED; exit 3; }
python3 "$here/sealgap.py" "$sj/build/stage0" > sealgap.out || { echo SEALGAP_FAILED; exit 3; }
python3 "$here/image_to_rocq.py" "$sj/build/shen-jit" "$sj/build/stage0" ImgData.v || { echo READ_FAILED; exit 4; }
for f in Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitMeta JitProfile JitLowerRel JitLowerKont JitLowerStable JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitLowerStage0; do
  sed 's/^From Coq Require/From Stdlib Require/' "$root/rocq/$f.v" > $f.v
done
sed 's/^From Coq Require/From Stdlib Require/' "$root/rocq/JitImage.v" > JitImage.v   # moved to rocq/ (r21-image-lane)
for f in ImgRun ImgSum ImgMut; do
  sed 's/^From Coq Require/From Stdlib Require/' "$here/$f.v" > $f.v
done
sed -i 's/^From Coq Require/From Stdlib Require/' ImgData.v
printf 'From Buri Require Import JitImage.\nPrint Assumptions JitImage.JitImage.check_def_sound.\n' > Ax.v
for f in Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitMeta JitProfile JitLowerRel JitLowerKont JitLowerStable JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitLowerStage0 JitImage Ax ImgData ImgRun ImgSum ImgMut; do
  s=$(date +%s)
  timeout 3000 rocq compile -Q . Buri $f.v > $f.log 2>&1 || { tail -20 $f.log; echo ROCQ_FAILED $f; exit 6; }
  echo "$f $(( $(date +%s) - s ))s"
done
grep -q "Closed under the global context" Ax.log || { echo NOT_CLOSED; exit 7; }
grep -q "s_total = Some (955, 0)" ImgSum.log || { echo TALLY_NOT_955; exit 8; }
grep -q 'r_mutA = Some (26%nat, \["differ print"\])' ImgMut.log && grep -q 'r_mutB = Some (26%nat, \["differ print"\])' ImgMut.log || { echo MUTANT_SURVIVED; exit 9; }
sha256sum census.out sealgap.out ImgSum.log ImgMut.log Ax.log
echo IMAGE_DECODE_OK
