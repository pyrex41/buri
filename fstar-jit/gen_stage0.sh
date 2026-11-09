#!/bin/sh
# Regenerate stage0/ (the F* data for the judge) from the pinned Shen/JIT d3348ce.
#   SHEN_JIT_REPO  a clone of tizoc/shen-jit containing d3348ce, with .deps/ (make deps):
#                  .deps/shen-jit/shen-jit (bootstrap 0.1) and .deps/kernel/klambda (kernel 43.4)
# Exports d3348ce with git archive (no checkout), runs its stage 0 recipe, checks the outputs
# against d3348ce's generated.sha256, then runs stage0_to_fstar.py on each file.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
repo=${SHEN_JIT_REPO:?set SHEN_JIT_REPO}
work=$(mktemp -d)
git -C "$repo" archive d3348cefbb2b209992039c1c0f55751241750364 | tar -x -C "$work"
(cd "$work" && nice -n 19 make BOOTSTRAP="$repo/.deps/shen-jit/shen-jit" KERNEL_KL="$repo/.deps/kernel/klambda" build/stage0/.done > /dev/null)
(cd "$work/build" && grep stage0/ ../generated.sha256 | shasum -a 256 -c - > /dev/null) || { echo "stage0 differs from d3348ce's generated.sha256"; exit 1; }
mkdir -p "$here/stage0"
while read n a r u; do
  python3 -I "$here/stage0_to_fstar.py" "$work/build/stage0" "$n" "$here/stage0" "$a" "$r" "$u"
done < "$here/../tests/shen-jit/stage0-accepted.txt"
rm -rf "$work"
echo "stage0/ regenerated"
