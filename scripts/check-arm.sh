#!/bin/bash
# Opt-in E2E-20 gate.  NOT part of `make prove`: the ARM proofs need separate
# toolchains (docs/ARM-FOUNDATION.md sections 10-11).  Acceptance is decided
# by coqc/coqchk; this script only binds inputs (hashes, captured bytes),
# orchestrates, and checks Print Assumptions output.  Two independent parts,
# each run when its toolchain is given:
#
# Part A (Wave B, Coq 8.18.0): ports/arm/coq/BuriArmAdds.v against the model
#   compiled with nixpkgs Coq 8.18.0 + stdpp 1.10.0.
#   SAIL_ARM_COQ   directory holding armv9_types.vo, arm_extras.vo, armv9.vo
#                  (sail-arm 7d058164 arm-v9.4-a/snapshots/coq, `-R . SailArm`)
#   COQ_SAIL       coq-sail tag 0.19 (6918e8f3) src-stdpp, compiled
#   COQ818 / STDPP818  nixpkgs store paths (defaults below)
#
# Part B (Wave C, Coq 8.19.0): BuriArmAdds.v, BuriArmDecode.v,
#   BuriArmBridgeValues.v and BuriArmBridge.v against the SAME model compiled
#   with the Islaris Coq 8.19.0 + stdpp, plus coqchk of the result.
#   ARM819_ENV     nix-build nix/arm/sail-model.nix -A env  (Coq 8.19.0,
#                  Islaris theories, SailStdpp and SailArm in user-contrib)
#   or ISLARIS_ENV (nix/arm/islaris.nix -A env) with COQ_SAIL819 and
#                  SAIL_ARM_COQ819 directories of a non-nix build.
#
# On a shared machine run it under a host-wide lock, e.g.
#   flock /tmp/buri-heavy.lock scripts/check-arm.sh
# (every heavy coqc/coqchk below is also capped at 7 GiB address space).
#
# What a pass trusts: the Sail-to-Coq translation of sail-arm 7d058164,
# coq-sail-stdpp 0.19, the named Coq kernels and stdpp, the Islaris opsem
# definitions (Part B bridge), and the three Coq-stdlib Reals axioms that the
# model's decoder depends on (EXPECT_DECODER_AXIOMS; no axiom is added by Buri).
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$(pwd)
check_sha() { echo "$1  $2" | sha256sum -c --quiet - || { echo "Unexpected $2" >&2; exit 1; }; }
ran=0

# Every `Definition {chez,sbcl}_word_XXXX : mword 32 := Ox"...".` line in
# a proof file must equal the stored captured bytes at that offset.
bind_words() {
  local f=$1 port off want got bin
  for bin in ports/arm/chez/chez1030-buri-arm-add.bin ports/arm/sbcl/sbcl-buri-arm-add.bin; do
    check_sha "$(grep " ./${bin#ports/arm/}\$" ports/arm/SHA256SUMS | cut -d' ' -f1)" "$bin"
  done
  grep -oE 'Definition (chez|sbcl)_word_[0-9a-f]{4} : mword 32 := Ox"[0-9A-F]{8}"\.' "$f" |
  while read -r _ name _ _ _ _ lit; do
    port=${name%%_*} off=$((16#${name##*_}))
    [ "$port" = chez ] && bin=ports/arm/chez/chez1030-buri-arm-add.bin || bin=ports/arm/sbcl/sbcl-buri-arm-add.bin
    b=($(od -An -tx1 -j "$off" -N 4 "$bin"))
    want=$(printf '%s%s%s%s' "${b[3]}" "${b[2]}" "${b[1]}" "${b[0]}" | tr a-f A-F)
    got=${lit#Ox\"}; got=${got%\".}
    [ "$want" = "$got" ] || { echo "Word mismatch in $f: $name is $got, captured $want" >&2; exit 1; }
    echo "  bound $name = 0x$want"
  done
}

# Assumption audit.  Arg 1: coqc log; arg 2: the .v file (its Print
# Assumptions lines give the order); arg 3: names that must be closed.
# Every other audited name must depend on exactly the decoder's Reals axioms.
audit() {
  python3 - "$1" "$2" "$3" <<'EOF'
import re, sys
text = open(sys.argv[1]).read()
order = re.findall(r'^Print Assumptions ([\w.]+)\.', open(sys.argv[2]).read(), re.M)
closed = set(sys.argv[3].split())
blocks = re.split(r'\n(?=Axioms:|Closed under the global context)', text)
audit = [b for b in blocks if b.startswith(('Axioms:', 'Closed under'))]
reals = {'ClassicalDedekindReals.sig_not_dec', 'ClassicalDedekindReals.sig_forall_dec',
         'FunctionalExtensionality.functional_extensionality_dep'}
def names(b):
    return (set(re.findall(r'^([A-Za-z_][\w.]*) :', b, re.M)) |
            set(re.findall(r'^([A-Za-z_][\w.]*)$', b, re.M))) - {'Axioms'}
if len(audit) != len(order):
    print('Assumption audit: %d blocks for %d Print Assumptions' % (len(audit), len(order)), file=sys.stderr); sys.exit(1)
bad = []
for n, b in zip(order, audit):
    want = 'closed' if n in closed else frozenset(reals)
    got = 'closed' if b.startswith('Closed') else frozenset(names(b))
    if got != want: bad.append((n, got))
if bad:
    print('Assumption audit mismatch:', bad, file=sys.stderr); sys.exit(1)
print('  audit %s: %d closed, %d with only the model decoder\'s Reals axioms'
      % (sys.argv[2].split('/')[-1], sum(n in closed for n in order), sum(n not in closed for n in order)))
EOF
}

model_hashes() {
  check_sha 5169ce7f4d10ab1a37bb77dd6a41114838c65fc0ceea4e9ef9cd1e73d8d1e68a "$1/armv9.v"
  check_sha 3586eb0f632fb642a39bbe5a526b2ffb34267725440fc9e9981e61a6de31a998 "$1/armv9_types.v"
  check_sha a82f366aadebfd12aaef4f7e6cdb5088c40b7a90ad4781e03b7baff9991b278c "$1/arm_extras.v"
  for v in armv9_types arm_extras armv9; do
    [ -f "$1/$v.vo" ] || { echo "Missing $1/$v.vo" >&2; exit 1; }
  done
}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
ulimit -s unlimited

# ------------------------------------------------------------------ Part A
if [ -n "${SAIL_ARM_COQ:-}" ]; then
  : "${COQ_SAIL:?Set COQ_SAIL to the compiled coq-sail 0.19 src-stdpp directory}"
  : "${COQ818:=/nix/store/z93aiwvyich2swj7qx9ahccwj15hzx8y-coq-8.18.0}"
  : "${STDPP818:=/nix/store/xz8bq0nyg9j6b37pja9qxvbj4w15wmqf-coq8.18-stdpp-1.10.0}"
  echo '== Part A: BuriArmAdds.v, Coq 8.18.0'
  (
  export PATH="$COQ818/bin:$PATH" COQPATH="$STDPP818/lib/coq/8.18/user-contrib"
  coqc --version | grep -q 'version 8.18.0' || { echo 'Need Coq 8.18.0' >&2; exit 1; }
  model_hashes "$SAIL_ARM_COQ"
  bind_words ports/arm/coq/BuriArmAdds.v
  Q=(-Q "$COQ_SAIL" SailStdpp -R "$SAIL_ARM_COQ" SailArm)
  mkdir -p "$tmp/a" && cp ports/arm/coq/BuriArmAdds.v "$tmp/a/"
  (cd "$tmp/a" && coqc "${Q[@]}" -Q . BuriArm BuriArmAdds.v) > "$tmp/a/out.log" 2>&1 \
    || { cat "$tmp/a/out.log" >&2; exit 1; }
  audit "$tmp/a/out.log" ports/arm/coq/BuriArmAdds.v 'chez_0014_execute chez_0014_sum'
  # A modified word must be rejected by the decode proof.
  sed 's/Ox"AB010017"/Ox"AB010018"/' ports/arm/coq/BuriArmAdds.v > "$tmp/a/BuriArmAddsMutant.v"
  if (cd "$tmp/a" && coqc "${Q[@]}" -Q . BuriArm BuriArmAddsMutant.v) > "$tmp/a/mut.log" 2>&1; then
    echo 'Incorrectly admitted modified word 0xab010018' >&2; exit 1
  fi
  grep -q 'Unable to unify' "$tmp/a/mut.log" || { echo 'Mutant failed for another reason' >&2; exit 1; }
  echo '  rejected modified word 0xab010018 (Rd=24)'
  )
  ran=1
fi

# ------------------------------------------------------------------ Part B
if [ -n "${ARM819_ENV:-}" ]; then
  ISLARIS_ENV=$ARM819_ENV
  : "${COQ_SAIL819:=$ARM819_ENV/lib/coq/8.19/user-contrib/SailStdpp}"
  : "${SAIL_ARM_COQ819:=$ARM819_ENV/lib/coq/8.19/user-contrib/SailArm}"
fi
if [ -n "${ISLARIS_ENV:-}" ]; then
  : "${COQ_SAIL819:?Set COQ_SAIL819 (coq-sail 0.19 src-stdpp built with Coq 8.19.0)}"
  : "${SAIL_ARM_COQ819:?Set SAIL_ARM_COQ819 (the model built with Coq 8.19.0)}"
  echo '== Part B: decode equations and trace-to-model bridge, Coq 8.19.0'
  (
  export PATH="$ISLARIS_ENV/bin:$PATH" COQPATH="$ISLARIS_ENV/lib/coq/8.19/user-contrib"
  coqc --version | grep -q 'version 8.19.0' || { echo 'Need Coq 8.19.0' >&2; exit 1; }
  model_hashes "$SAIL_ARM_COQ819"
  for f in BuriArmAdds BuriArmDecode; do bind_words "ports/arm/coq/$f.v"; done
  # The bridge consumes the exact trace file the Islaris theorem uses.
  tr=ports/arm/islaris/instructions/buri_chez_add/a14.v
  check_sha "$(grep " ./islaris/instructions/buri_chez_add/a14.v\$" ports/arm/SHA256SUMS | cut -d' ' -f1)" "$tr"
  W=$tmp/b; mkdir -p "$W/buri" "$W/instructions/buri_chez_add"
  cp ports/arm/coq/BuriArm{Adds,Decode,BridgeValues,Bridge}.v "$W/buri/"
  cp "$tr" "$W/instructions/buri_chez_add/"
  Q=(-w -notation-overridden -w -redundant-canonical-projection
     -Q "$COQ_SAIL819" SailStdpp -R "$SAIL_ARM_COQ819" SailArm
     -Q "$W/instructions" isla.instructions -Q "$W/buri" BuriArm)
  cd "$W"
  coqc "${Q[@]}" instructions/buri_chez_add/a14.v
  for f in BuriArmAdds BuriArmDecode BuriArmBridgeValues BuriArmBridge; do
    s=$(date +%s)
    # 7 GiB cap: an overrun fails this job instead of the OOM killer's choice.
    ( ulimit -v 7340032; coqc "${Q[@]}" "buri/$f.v" ) > "$f.log" 2>&1 || { cat "$f.log" >&2; exit 1; }
    echo "  $f.v checked in $(( $(date +%s) - s )) s"
  done
  audit BuriArmAdds.log buri/BuriArmAdds.v 'chez_0014_execute chez_0014_sum'
  audit BuriArmDecode.log buri/BuriArmDecode.v 'sbcl_0264_execute HaveBTIExt_reads_FeatureImpl DecodeShift_LSL'
  audit BuriArmBridgeValues.log buri/BuriArmBridgeValues.v 'isla_sum_model isla_N isla_Z isla_C isla_V'
  audit BuriArmBridge.log buri/BuriArmBridge.v 'a14_run'
  # coqchk re-checks the four files and everything they load, the 59 MB
  # model included (about 4 min, 1 GB).
  ( ulimit -v 7340032; coqchk -silent -o "${Q[@]:4}" BuriArm.BuriArmDecode BuriArm.BuriArmBridge ) > chk.log 2>&1 \
    || { tail -20 chk.log >&2; exit 1; }
  python3 - chk.log <<'EOF'
import re, sys
t = open(sys.argv[1]).read()
ax = set(re.findall(r'^\s+([\w.]+)\s*$', t.split('* Axioms:')[1].split('* Constants')[0], re.M))
model = {'SailArm.armv9.' + n for n in ['__SleepRequest', 'read_mem_', 'read_mem_ifetch_',
         'read_mem_exclusive_', 'write_mem_', 'write_mem_exclusive_']}
std = {'Coq.Logic.FunctionalExtensionality.functional_extensionality_dep',
       'Coq.Reals.ClassicalDedekindReals.sig_not_dec', 'Coq.Reals.ClassicalDedekindReals.sig_forall_dec',
       'Coq.Logic.Classical_Prop.classic', 'Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq'}
extra = ax - model - std
if extra or 'BuriArm' in ''.join(ax):
    print('coqchk: unexpected axioms in the global context:', sorted(extra), file=sys.stderr); sys.exit(1)
for k in ['type-in-type', 'unsafe (co)fixpoints', 'positivity is assumed']:
    seg = t.split(k)[1].split('*')[0]
    if '<none>' not in seg:
        print('coqchk: unsafe flag', k, file=sys.stderr); sys.exit(1)
print('  coqchk: libraries re-checked; context axioms are the model\'s 6 external memory/sleep')
print('  primitives and 5 Coq-stdlib axioms (none from Buri); per-theorem dependence is the audit above')
EOF
  # Mutants: a different word must break the decode equation, and a changed
  # trace must break the bridge.
  sed 's/Ox"54000401"/Ox"54000400"/' buri/BuriArmDecode.v > buri/BuriArmDecodeMutant.v
  python3 - buri/BuriArmDecodeMutant.v <<'EOF'
import sys; p = sys.argv[1]; s = open(p).read()
open(p, 'w').write(s[:s.index('Theorem chez_000c_decode')])   # skip the slow LoadStore proofs
EOF
  if ( ulimit -v 7340032; coqc "${Q[@]}" buri/BuriArmDecodeMutant.v ) > mut1.log 2>&1; then
    echo 'Incorrectly admitted modified word 0x54000400 (b.eq)' >&2; exit 1
  fi
  grep -q 'Unable to unify\|Tactic failure\|No matching clauses' mut1.log || { cat mut1.log >&2; echo 'Decode mutant failed for another reason' >&2; exit 1; }
  echo '  rejected modified word 0x54000400 at +0x04 (b.eq instead of b.ne)'
  mkdir -p mt/buri_chez_add
  sed 's/(Manyop (Bvmanyarith Bvadd) \[Unop (ZeroExtend 64%N)/(Manyop (Bvmanyarith Bvxor) [Unop (ZeroExtend 64%N)/' \
    instructions/buri_chez_add/a14.v > mt/buri_chez_add/a14.v
  cmp -s mt/buri_chez_add/a14.v instructions/buri_chez_add/a14.v && { echo 'Trace mutant did not change the trace' >&2; exit 1; }
  QM=("${Q[@]}"); QM[11]="$W/mt"
  coqc "${QM[@]}" mt/buri_chez_add/a14.v
  if ( ulimit -v 7340032; coqc "${QM[@]}" buri/BuriArmBridge.v ) > mut2.log 2>&1; then
    echo 'Incorrectly admitted a trace computing xor instead of add' >&2; exit 1
  fi
  grep -q 'Error' mut2.log || { echo 'Bridge mutant failed for another reason' >&2; exit 1; }
  echo '  rejected a14 trace with bvadd replaced by bvxor (bridge proof fails)'
  )
  ran=1
fi

[ "$ran" = 1 ] || { echo 'Nothing checked: set SAIL_ARM_COQ (Part A) and/or ARM819_ENV or ISLARIS_ENV (Part B)' >&2; exit 1; }
echo 'BURI_ARM_CHECK_OK'
