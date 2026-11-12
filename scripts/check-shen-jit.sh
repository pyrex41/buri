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
python3 -I - "$root" <<'EMIT_NOINV' || { echo "EMIT_INVERSION_FOUND"; exit 14; }
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
FILES="Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitMeta JitProfile JitLowerRel JitLowerKont JitLowerStable JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase JitKRefCompatClo JitKRefCompose JitLowerEquiv JitEqBudget JitEqBudgetStep JitEqBudgetWalk JitEqBudgetCore JitKRefPrim JitKRefCompatCtl JitKRefCompatCall JitLowerStage0 JitKRefFv JitKRefFund JitKTerm JitKTermGround JitKTermBase JitKTermCompatClo JitKTermPrim JitKTermCompatCtl JitKTermCompatCall JitKTermFv JitKTermFund JitKRefTerm JitKRefTermThm JitNorm JitNormStage0 JitFrontD JitFrontSugar JitFrontProlog JitImage JitEmitRuleEq JitEmitRuleStore JitEmitRulePrim JitEmitRuleDoFold JitEmitRuleClo JitEmitRuleApp JitEmitRuleTrap JitEmitRel JitEmitNestTest JitEmitKont JitEmitInv JitKRefCallNoTableCex JitFrontCheck JitFrontChainTest JitFrontShare JitFrontInline Audit_Jit"
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
# Emit families, term level (r21-emit-spec-land): Rocq prints (Set Printing All) every constant of JitEmitRel and of each
# compiled module that directly requires a JitEmit module, outside the JitEmitRule<X>.v files; JitEmitRel's own Comp_ind' family and the
# block's generated schemes are exempt, as are those of JitEmitNestTest's copy (JitEmitRelDummy). No printed term may match on Comp, CompT or CompOp (such a match prints
# their hook constructors [CTO]_<X> as branches; JitLowerRel's Comp has no such constructors), match on a Rule hook, or use a Rule hook's or the Comp block's generated schemes. This
# sees what the syntactic gate cannot, such as a destruct of an unnamed Comp hypothesis. Test evidence, not proof.
python3 -I - "$out" "$FILES" <<'EMIT_TERM' || { echo "EMIT_TERM_INVERSION_FOUND"; exit 15; }
import re,sys,pathlib,subprocess
out=pathlib.Path(sys.argv[1]); files=sys.argv[2].split()
FAM='(?:Eq|Store|Prim|DoFold|Clo|App|Trap)'
KINDS={'def','prf','scheme','rec','corec','proj','inst','meth','coe','thm','lem','fact'}
BLK=['Comp','CompT','CompOp','CompOps','CompW','CompTA']
EXEMPT={(f,p,n) for f,p in [('JitEmitRel','JitEmitRel'),('JitEmitNestTest','JitEmitNestTest.JitEmitRelDummy')]
        for n in [b+"_ind'" for b in BLK]+[f'{b}_{s}' for b in BLK for s in ['ind','sind','rect','rec']]}
names=[]; mods=[]
for f in files:
    if f.startswith('JitEmitRule') or f=='Audit_Jit': continue
    g=(out/f'{f}.glob').read_text()
    if f!='JitEmitRel' and not re.search(r'^R\d+:\d+ Buri\.JitEmit\w* ',g,re.M): continue
    mods.append(f)
    for m in re.finditer(r'^(\w+) \d+:\d+ (\S+) (\S+)$',g,re.M):
        k,p,n=m.groups()
        if k in KINDS and (f,p,n) not in EXEMPT: names.append(f'Buri.{f}.{n}' if p=='<>' else f'Buri.{f}.{p}.{n}')
names=list(dict.fromkeys(names))
if 'JitEmitRel' not in mods or not names: print('emit term-level check: nothing to print'); sys.exit(1)
src='From Buri Require '+' '.join(mods)+'.\nSet Printing All. Set Printing Width 1000000.\n'+''.join(f'Print {q}.\n' for q in names)
(out/'EmitTermGate.v').write_text(src)
r=subprocess.run(['rocq','compile','-Q',str(out),'Buri',str(out/'EmitTermGate.v')],cwd=out,capture_output=True,text=True)
log=r.stdout+r.stderr; (out/'EmitTermGate.log').write_text(log)
if r.returncode: print(log[-2000:]); print('emit term-level check: printing failed'); sys.exit(1)
pats=[(r'(?:\||\bwith)\s+(?:[\w\']+\.)*[CTO]_'+FAM+r'\b(?!\')','match on Comp, CompT or CompOp (hook constructor branch)'),
      (r'\bin\s+\(?\s*@?(?:[\w\']+\.)*Rule[TO]?_'+FAM+r'\b(?!\')','match on a Rule hook'),
      (r'\bRule[TO]?_'+FAM+r'_(?:ind|rect|rec|sind)\b','generated scheme of a Rule hook'),
      (r'(?<![\w\'])(?:Comp|CompT|CompOp|CompOps|CompW|CompTA)_(?:ind|rect|rec|sind)\b(?!\')','generated scheme of the nested Comp block')]
bad=[]
for b in re.split(r'\n(?=\S)',log):
    head=b.split()[0] if b.split() else '?'
    for p,why in pats:
        for m in re.finditer(p,b): bad.append(f'{head}: {why}: {m.group(0).strip()!r}')
for x in bad: print('EMIT_TERM_INVERSION',x)
print(f'emit term-level non-inversion check: {len(bad)} violations, {len(names)} constants printed from {len(mods)} modules')
sys.exit(1 if bad else 0)
EMIT_TERM
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
# Heap image code objects (OB-JIT-IMAGE-CODE, docs/SHEN-JIT-IMAGE.md): the binary's image is read as
# bytes (the trusted reader, OB-JIT-IMAGE-READER, writes each as a Byte.byte constructor; Rocq joins
# them into words) and Rocq proves image_code_ok, closed: every one of
# the 24 files' stage 0 definitions, from the stage 0 step's own S0_<file> modules, loads to the code
# object its function cell holds in the image (JitImage.code_check_sound). image_mutants_caught
# proves two one-word mutants of print's code are caught. The census Rocq computes on the image is
# compared with tests/shen-jit/image-facts.txt. Needs the stage 0 step's modules.
if [ -z "${SKIP_STAGE0:-}" ] && [ -z "${SKIP_IMAGE:-}" ]; then
  python3 "$root/tests/shen-jit/stage0_to_rocq.py" --image "$bin" "$s0/Img.v" || { echo "IMAGE_READ_FAILED"; exit 13; }
  sed -i 's/^From Coq Require/From Stdlib Require/' "$s0/Img.v"
  (cd "$s0" && rocq compile -Q "$out" Buri Img.v > Img.log 2>&1) || { tail -20 "$s0/Img.log"; echo "IMAGE_ROCQ_FAILED"; exit 13; }
  # image_code_ok and image_mutants_caught must each print "Closed under the global context": no
  # axiom, parameter or primitive. Anything else before image_facts fails.
  pre=$(sed -n '1,/^image_facts =/p' "$s0/Img.log" | grep -v '^\[WARNING\]' | grep -v '^image_facts =$')
  [ "$pre" = "$(printf 'Closed under the global context\nClosed under the global context')" ] || { cat "$s0/Img.log"; echo "IMAGE_ASSUMPTIONS"; exit 13; }
  sed -n '/^image_facts =/,$p' "$s0/Img.log" | tr '\n' ' ' | tr -s ' ' | sed 's/ $//' > "$s0/image-facts.txt"; echo >> "$s0/image-facts.txt"
  diff "$root/tests/shen-jit/image-facts.txt" "$s0/image-facts.txt" > "$s0/image-diff.txt" || { cat "$s0/image-diff.txt"; echo "IMAGE_FACTS_CHANGED"; exit 13; }
  echo "image: image_code_ok proved, closed under the global context (every stage 0 code object of the 24 files equals its image function cell's), 2 image mutants caught, census as recorded"
else echo "image: NOT RUN (SKIP_STAGE0 or SKIP_IMAGE set)"; fi
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
