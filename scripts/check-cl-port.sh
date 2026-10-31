#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
: "${SHEN_CL_SOURCE:?Set SHEN_CL_SOURCE to the Shen-CL checkout}"
: "${SBCL:=sbcl}"
: "${COQC:=coqc}"
expected=4844072dde0208c3e4b99dcbfea58e4fdfd812e8
actual=$(git -C "$SHEN_CL_SOURCE" rev-parse HEAD)
[ "$actual" = "$expected" ] || { echo "Wrong Shen-CL revision: $actual" >&2; exit 1; }
git -C "$SHEN_CL_SOURCE" diff --quiet HEAD -- src/primitives.lsp || { echo 'Modified port source' >&2; exit 1; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
cp rocq/CLPortGuard.v "$tmp/CLPortGuard.v"
"$COQC" -Q "$tmp" Buri "$tmp/CLPortGuard.v"
"$SBCL" --script ports/shen-cl-capture.lisp "$SHEN_CL_SOURCE/src/primitives.lsp" "$tmp/CLPortCapture.v"
cmp rocq/CLPortCapture.v "$tmp/CLPortCapture.v"
cmp ports/shen-cl-guard.sexp "$tmp/CLPortCapture.sexp"
"$COQC" -Q "$tmp" Buri "$tmp/CLPortCapture.v"
for mutation in swap host-truthiness changed-message; do
  "$SBCL" --script ports/shen-cl-capture.lisp "$SHEN_CL_SOURCE/src/primitives.lsp" "$tmp/CLPortMutant.v" "$mutation"
  if "$COQC" -Q "$tmp" Buri "$tmp/CLPortMutant.v" >"$tmp/rejection.log" 2>&1; then
    echo "Incorrectly admitted $mutation" >&2; exit 1
  fi
  grep -q 'Unable to unify "true" with "false"' "$tmp/rejection.log" || { cat "$tmp/rejection.log" >&2; exit 1; }
  echo "Rejected modified capture: $mutation"
done
