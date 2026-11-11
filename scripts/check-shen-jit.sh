#!/bin/bash
# Opt-in Shen/JIT lane gate (E2E-37), at the frozen pin; ports/shen-jit/build.sh makes the binary. NOT part of `make prove`, whose 8.18 run compiles the
# same rocq/Jit*.v sources. This run needs the Rocq in toolchain.lock.json's shen_jit entry
# and qemu-riscv64, so it runs in the container from spikes/jit-in-model/setup.sh.
#
#   SHEN_JIT_SRC  checkout of the pinned Shen/JIT, with build/stage0 (default /lps/p6/sj)
#   SHEN_JIT_BIN  the named binary (default /lps/p6/sj/build/shen-jit)
#
# Acceptance of theorems is decided by rocq and rocqchk. The differential part compares
# samples with the binary: agreement is test evidence, never proof. Passing does not
# verify Shen/JIT.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
src=${SHEN_JIT_SRC:-/lps/p6/sj}
bin=${SHEN_JIT_BIN:-/lps/p6/sj/build/shen-jit}
out=${JIT_OUT:-/tmp/p1}; export JIT_OUT="$out"
want=$(python3 -c "import json;print(json.load(open('$root/toolchain.lock.json'))['shen_jit']['binary_sha256'])")
got=$(sha256sum "$bin" | cut -d' ' -f1)
[ "$want" = "$got" ] || { echo "NOT_THE_NAMED_BINARY $got"; exit 3; }
python3 "$root/tests/shen-jit/check_tables.py" "$root" "$src" || exit 4
# Emit families (r21-emit-spec-land): outside its own rocq/JitEmitRule<X>.v no file inverts a Rule_X hook;
# downstream code uses JitEmitRel.Comp_ind' and the Rule_X_map / Rule_X_all lemmas only. A syntactic gate (it cannot
# see a destruct of an unnamed Comp hypothesis); Rocq still decides every theorem.
python3 -I - "$root" <<'EMIT_NOINV' || { echo "EMIT_INVERSION_FOUND"; exit 13; }
import re,sys,pathlib
root=pathlib.Path(sys.argv[1]); bad=[]
FAM='(?:Eq|Store|Prim|DoFold|Clo|App|Trap)'
def strip(s):
    out=[];d=0;i=0;q=False
    while i<len(s):
        c=s[i]
        if not d and c=='"': q=not q
        if not q and s.startswith('(*',i): d+=1;i+=2;continue
        if not q and d and s.startswith('*)',i): d-=1;i+=2;continue
        out.append(c if not d and not q else (c if c=='\n' else ' ')); i+=1
    return ''.join(out)
ctors=set()
for f in root.glob('rocq/JitEmitRule*.v'):
    t=strip(f.read_text())
    for m in re.finditer(r'Inductive\s+(Rule[TO]?_'+FAM+r')\b.*?:=(.*?)\.(?:\s|$)',t,re.S):
        ctors|=set(re.findall(r'\|\s*([\w\']+)',m.group(2)))
        b=m.group(2).strip()
        if b and not b.startswith('|'): ctors.add(re.match(r'[\w\']+',b).group(0))
for f in sorted(root.glob('rocq/*.v')):
    if re.match(r'JitEmitRule.*\.v$',f.name): continue
    t=strip(f.read_text()); imp=re.search(r'Require\s+(?:Import|Export)?[^.]*\bJitEmitRel\b',t) is not None
    def hit(rule,m): bad.append(f'{f.name}:{t.count(chr(10),0,m.start())+1}: {rule}: {m.group(0)!r}')
    for m in re.finditer(r'\bRule[TO]?_'+FAM+r'_(?:ind|rect|rec|sind|case)\b',t): hit('generated scheme of a Rule hook',m)
    for m in re.finditer(r'\bJitEmitRel\.(?:Comp|CompT|CompOp|CompOps|CompW|CompTA)_(?:ind|rect|rec|sind)\b(?!\')',t): hit('generated scheme of the nested Comp block (use Comp_ind\')',m)
    if f.name.startswith('JitEmit') or imp:
        for m in re.finditer(r'(?<![\w.])(?:Comp|CompT|CompOp|CompOps|CompW|CompTA)_(?:ind|rect|rec|sind)\b(?!\')',t): hit('generated scheme of the nested Comp block (use Comp_ind\')',m)
    if f.name!='JitEmitRel.v':
        for m in re.finditer(r'\b[CTO]_'+FAM+r'\b(?!\')',t): hit('hook constructor of Comp outside JitEmitRel.v',m)
    for c in ctors:
        for m in re.finditer(r'\b'+re.escape(c)+r'\b',t): hit('constructor of a Rule hook',m)
    for pm in re.finditer(r'\bProof\b(.*?)\b(?:Qed|Defined|Admitted|Abort)\s*\.',t,re.S):
        for m in re.finditer(r'\bRule[TO]?_'+FAM+r'\b(?!_(?:map|all|All)\b)',pm.group(1)):
            bad.append(f'{f.name}:{t.count(chr(10),0,pm.start(1)+m.start())+1}: Rule hook named in a proof script: {m.group(0)!r}')
    if f.name.startswith('JitEmit') or imp:
        for m in re.finditer(r'\bwith\s+end\b',t): hit('empty match outside the hook files',m)
for b in bad: print('EMIT_INVERSION', b)
print(f'emit non-inversion check: {len(bad)} violations, {len(ctors)} hook constructors') 
sys.exit(1 if bad else 0)
EMIT_NOINV
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
mkdir -p "$out"; cd "$out"
FILES="Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitMeta JitProfile JitLowerRel JitLowerKont JitLowerStable JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase JitKRefCompatClo JitKRefCompose JitLowerEquiv JitEqBudget JitEqBudgetStep JitEqBudgetWalk JitEqBudgetCore JitKRefPrim JitKRefCompatCtl JitKRefCompatCall JitLowerStage0 JitKRefFv JitKRefFund JitKTerm JitKTermGround JitKTermBase JitKTermCompatClo JitKTermPrim JitKTermCompatCtl JitKTermCompatCall JitKTermFv JitKTermFund JitKRefTerm JitKRefTermThm JitNorm JitNormStage0 JitFrontD JitFrontSugar JitFrontProlog JitEmitRuleEq JitEmitRuleStore JitEmitRulePrim JitEmitRuleDoFold JitEmitRuleClo JitEmitRuleApp JitEmitRuleTrap JitEmitRel JitEmitNestTest JitEmitKont JitEmitInv Audit_Jit"
for f in $FILES; do
  sed 's/^From Coq Require/From Stdlib Require/' "$root/rocq/$f.v" > "$f.v"
  d=$(diff "$root/rocq/$f.v" "$f.v" || true)   # diff exits 1 when the files differ
  other=$(printf '%s\n' "$d" | grep -E '^[<>]' | grep -vE '^[<>] From (Coq|Stdlib) Require' || true)
  [ -z "$other" ] || { echo "SPEC_DRIFT $f"; exit 5; }
  rm -f "$f.vo"
  rocq compile -Q . Buri "$f.v" > "$f.log" 2>&1 || { tail -20 "$f.log"; echo "ROCQ_FAILED $f"; exit 6; }
  [ -s "$f.vo" ] || { echo "NO_OUTPUT $f"; exit 6; }
done
expected=$(cat "$root/rocq/audit.d/Audit_Jit.count")
closed=$(grep -c '^Closed under the global context$' Audit_Jit.log || true)
[ "$closed" = "$expected" ] || { cat Audit_Jit.log; echo "AUDIT_MISMATCH $closed of $expected"; exit 7; }
rocqchk -silent -Q . Buri $(for f in $FILES; do echo "Buri.$f"; done) > chk.log 2>&1 || { tail -5 chk.log; echo "ROCQCHK_FAILED"; exit 8; }
echo "rocq-9: ${closed} audited statements closed, rocqchk passed"
# Stage 0 translation validation (E2E-38): each definition's form and code object are decoded in
# Rocq and JitLowerCheck decides them. The per-file counts must equal tests/shen-jit/stage0-accepted.txt,
# so a change in either direction fails. Acceptance is per definition; rejection proves nothing.
if [ -z "${SKIP_STAGE0:-}" ]; then
  s0="$out/s0"; mkdir -p "$s0"; got="$s0/counts.txt"; : > "$got"
  for f in $(cd "$src/build/stage0" && ls *.forms | sed 's/\.forms$//'); do
    id=$(echo "$f" | tr - _)
    python3 "$root/tests/shen-jit/stage0_to_rocq.py" "$src/build/stage0" "$f" "$s0/S0_$id.v" || { echo "STAGE0_READ_FAILED $f"; exit 11; }
    sed -i 's/^From Coq Require/From Stdlib Require/' "$s0/S0_$id.v"
    (cd "$s0" && rocq compile -Q "$out" Buri "S0_$id.v" > "S0_$id.log" 2>&1) || { tail -5 "$s0/S0_$id.log"; echo "STAGE0_ROCQ_FAILED $f"; exit 11; }
    c=$(tr '\n' ' ' < "$s0/S0_$id.log" | grep -oE "result_$id = *\([0-9]+, [0-9]+, [0-9]+" | sed 's/.*(//; s/,//g')
    [ -n "$c" ] || { echo "STAGE0_NO_RESULT $f"; exit 11; }
    echo "$f $c" >> "$got"
  done
  diff "$root/tests/shen-jit/stage0-accepted.txt" "$got" > "$s0/diff.txt" || { cat "$s0/diff.txt"; echo "STAGE0_CHANGED"; exit 12; }
  echo "stage0: $(awk '{a+=$2; r+=$3; u+=$4} END {print a " accepted, " r " rejected, " u " unreadable of " a+r+u " definitions"}' "$got"), as recorded"
else echo "stage0: NOT RUN (SKIP_STAGE0 set)"; fi
if [ -n "${SKIP_DIFF:-}" ]; then echo "differential: NOT RUN (SKIP_DIFF set)"; exit 0; fi
d="$out/d"; mkdir -p "$d"; cd "$d"
cat "$src/tests/kl/ops.kl" "$root/tests/shen-jit/ops-calls.kl" > ops-all.kl
sed 's/^From Coq Require/From Stdlib Require/' "$root/tests/shen-jit/JitDiffLib.v" > JitDiffLib.v
rm -f JitDiffLib.vo; rocq compile -Q "$out" Buri -Q . JitDiff JitDiffLib.v > lib.log 2>&1 || { tail lib.log; exit 9; }
SJ_BIN=$bin STAGE0=$src/build/stage0 bash "$root/tests/shen-jit/run_case.sh" ev "$src/tests/kl/eval-cases.kl" kl > log_ev.txt 2>&1 &
SJ_BIN=$bin STAGE0=$src/build/stage0 bash "$root/tests/shen-jit/run_case.sh" ops "$d/ops-all.kl" kl > log_ops.txt 2>&1 &
SJ_BIN=$bin STAGE0=$src/build/stage0 bash "$root/tests/shen-jit/run_case.sh" ct "$src/contract/examples.shen" contract > log_ct.txt 2>&1 &
wait
python3 "$root/tests/shen-jit/compare_known.py" "$root/tests/shen-jit/known-differences.txt" ev ops ct || { echo "DIFFERENTIAL_CHANGED"; exit 10; }
echo "BURI_SHEN_JIT_LANE_OK (not a verification of Shen/JIT)"
