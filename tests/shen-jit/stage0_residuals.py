#!/usr/bin/env python3
"""Write tests/shen-jit/stage0-residuals.txt: every stage 0 definition the Rocq source judge does not
accept, with a first blocker, the open ledger entry it is filed under, and the decision items it touches.

Three kinds of data, kept apart in the output:
  rocq verdict  JitLowerStage0.judge on each definition, computed by Rocq (judge_split.sh, variants
                src, nf and tf: 1 accepted, 2 rejected, 0 unreadable). src is the source-judge count,
                the quantity scripts/check-shen-jit.sh pins in stage0-accepted.txt. It is not the
                full-pipeline "validated" count (no full-pipeline judge exists at this commit). nf and tf
                are verdicts on the untrusted erased witness: emit-side evidence only.
  census        labels from a syntactic walk of the norm witness: the constructs JitLowerRel.Comp has
                no rule for, in pass_census.blockers order, plus `=` operands outside JitLowerRel.pguard
                and calls to shen-jit.eval-kl. Untrusted: a label for the residual, not a reason Rocq
                gave. The script checks the walk against Rocq: every definition the judge accepts on
                nf must get no emit label.
  ledger        the open spec/obligations.json entry each label is filed under, and the decision items
                (Reuben's decision; default: named residual) any of the definition's labels touch.
This script decides nothing about validity. It reads the admitted primitives from JitLowerRel.pmap,
the KL primitive names from KLSyntax.prim_name and the port-primitive proposal and residual reasons
from JitProfile.v; it checks the verdict files against their tally lines and stage0-accepted.txt,
and that every ledger id it names is open or partial (decision entries: open).

    stage0_residuals.py STAGE0_DIR WITNESS_DIR JUDGE_DIR BASE_COMMIT OUT
"""
import hashlib, json, os, re, sys
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, here)
from stage0_to_rocq import tokens, parse
from pass_census import MARKER, FALLBACK
from feature_census import eq_kind

root = os.path.dirname(os.path.dirname(here))

def rocq(f):
    return open(os.path.join(root, 'rocq', f)).read()

def between(text, start, end):
    body = text[text.index(start):]
    return body[:body.index(end)]

# Read (not decided): KLSyntax.prim_name and JitLowerRel.pmap give the KL primitives Comp admits.
_names = dict(re.findall(r'\|\s*(P\w+)\s*=>\s*"([^"]*)"', between(rocq('KLSyntax.v'), 'Definition prim_name', 'end.')))
KL = set(_names.values())
ADMITTED = {_names[p] for p in re.findall(r'(P\w+)\s*=>\s*Some', between(rocq('JitLowerRel.v'), 'Definition pmap', 'end.'))}
assert '=' in ADMITTED and 'cons' in ADMITTED, ADMITTED
_prof = rocq('JitProfile.v')
PROPOSED = set(re.findall(r'\("([^"]+)",\s*\d+%nat', between(_prof, 'Definition jit_port_prim_core_table', 'Definition pp_lookup')))
NO_CARRIER = dict(re.findall(r'\("([^"]+)",\s*"([^"]*)"\)', between(_prof, 'Definition jit_port_prims_residual', '].')))
assert len(PROPOSED) == 18 and not PROPOSED & set(NO_CARRIER), (len(PROPOSED), PROPOSED & set(NO_CARRIER))
IDENTITY = {'shen-jit.same?', 'shen-jit.tagged?', 'shen-jit.deref', 'shen-jit.deref='}

DECISIONS = {
    'eval-kl': 'OB-JIT-LOWER-GENERAL',
    'identity': 'OB-JIT-IDENTITY-MODEL',
    'nan-eq': 'OB-JIT-NAN-IDENTITY',
    'port-prims': 'OB-JIT-PORT-PRIMS',
}
EQ_COMPUTED = '= on two computed operands (no safe constant: pguard)'
EQ_SYMBOL = '= against a symbol constant only (pguard)'
EVALKL = 'call shen-jit.eval-kl'
FRONT = 'none on the norm witness; nf accepted (front-side gap)'

def atom(x):
    return x[1] if x[0] == 'atom' else None

def labels(n, out):
    """pass_census.blockers (non-transparent) on norm witness node n, with the admitted set read from
    JitLowerRel.pmap and `=` checked against pguard (feature_census.eq_kind); also labels calls to
    shen-jit.eval-kl, which Comp admits as calls but which wait on the eval-kl decision."""
    l = n[1]
    tag = atom(l[0])
    def each(xs):
        for x in xs:
            labels(x, out)
    if tag == 'const':
        if l[1][0] == 'list' and l[1][1]:
            out.append('folded constant list')
    elif tag == 'var':
        pass
    elif tag in ('if', 'and', 'or'):
        each(l[1:])
    elif tag == 'let':
        x, v, b = atom(l[1]), l[2], l[3]
        if x == 'stage0.lower.inlining':
            out.append(MARKER); each([b])
        elif v[0] == 'list' and atom(v[1][0]) == 'freeze':
            out.append('let-bound freeze (goto label / thaw in place)'); each([v[1][1], b])
        else:
            each([v, b])
    elif tag == 'do':
        out.append('do'); each(l[1:])
    elif tag in ('lambda', 'freeze'):
        out.append(tag); each([l[-1]])
    elif tag == 'trap':
        out.append('trap'); each([l[1], l[3]])
    elif tag == 'prim':
        op = atom(l[1])
        if op == 'shen-jit.inlined?':
            out.append('shen-jit.inlined? guard')
        elif op == 'raise-cond':
            out.append('raise-cond (cond fall-through)')
        elif op == '=':
            k, _ = eq_kind(l[2][1])
            if k == 'eq-two-computed':
                out.append(EQ_COMPUTED)
            elif k == 'eq-symbol-const':
                out.append(EQ_SYMBOL)
        elif op not in ADMITTED:
            out.append('prim ' + op)
        each(l[2][1])
    elif tag == 'call':
        if atom(l[1]) == 'shen-jit.eval-kl':
            out.append(EVALKL)
        each(l[2][1])
    elif tag == 'apply':
        out.append('apply (thaw)' if len(l) == 2 else 'apply (dynamic call)'); each(l[1:])
    else:
        raise ValueError('not a normal form: %r' % (n,))
    return out

def classify(label):
    """(ledger id, decision item or None, reason) for a census label."""
    if label == EVALKL or label == 'prim eval-kl':
        return DECISIONS['eval-kl'], 'eval-kl', 'eval-kl: Reuben\'s decision (prove or exclude); default residual'
    if label == EQ_COMPUTED:
        return DECISIONS['nan-eq'], 'nan-eq', 'both operands may be NaN reals: Reuben\'s decision; default residual'
    if label.startswith('prim '):
        op = label[5:]
        if op in IDENTITY:
            return DECISIONS['identity'], 'identity', 'object identity: Reuben\'s decision; default residual'
        if op in KL:
            return 'OB-JIT-LOWER-FRAGMENT', None, 'KL primitive with no Comp rule'
        if op in PROPOSED:
            return DECISIONS['port-prims'], 'port-prims', 'candidate in jit_port_prims_proposed, unwired: Reuben\'s decision'
        if op in NO_CARRIER:
            return DECISIONS['port-prims'], 'port-prims', 'no source meaning: ' + NO_CARRIER[op]
        return DECISIONS['port-prims'], 'port-prims', 'port primitive not in JitProfile census'
    if label in (MARKER, 'shen-jit.inlined? guard', FRONT) or label.startswith('let-bound freeze'):
        return 'OB-JIT-LOWER-OPTIMIZATIONS', None, 'front rewrite with no checker rule'
    if label == FALLBACK:
        return 'OB-JIT-STAGE0', None, 'Rocq rejects the erased form with no census label: emit-side mismatch'
    return 'OB-JIT-LOWER-FRAGMENT', None, 'construct with no Comp rule'

def listing_hash(d, names):
    """sha256 of the `LC_ALL=C sha256sum NAMES` listing, names in the order given (the CENSUS.md
    method for `*.forms *.sbc`: each glob in C order, forms first)."""
    lines = ''.join('%s  %s\n' % (hashlib.sha256(open(os.path.join(d, n), 'rb').read()).hexdigest(), n)
                    for n in names)
    return hashlib.sha256(lines.encode()).hexdigest()

def concat_hash(d, names):
    """sha256 of the files' bytes concatenated in C order (the CENSUS.md method for witness sets)."""
    h = hashlib.sha256()
    for n in sorted(names):
        h.update(open(os.path.join(d, n), 'rb').read())
    return h.hexdigest()

def verdicts(judge, variant, f):
    lines = open(os.path.join(judge, variant, f + '.codes')).read().split('\n')
    head = lines[0].split()
    vs = [int(v) for v in lines[1].split()]
    assert head[0] == f, f
    assert (int(head[1]), int(head[2]), int(head[3])) == (vs.count(1), vs.count(2), vs.count(0)), \
        'tally line disagrees with verdicts: %s %s' % (variant, f)
    return vs, ' '.join(head[:4])

def count(d, k):
    d[k] = d.get(k, 0) + 1

def main(s0, wit, judge, base, out):
    files = sorted(f[:-6] for f in os.listdir(s0) if f.endswith('.forms'))
    pinned = [l for l in open(os.path.join(here, 'stage0-accepted.txt')).read().split('\n') if l.strip()]
    obs = {o['id']: o['status'] for o in json.load(open(os.path.join(root, 'spec', 'obligations.json')))['obligations']}
    rows, tallies, total, acc = [], [], 0, 0
    per_ledger, per_first, per_decision, nf_tot = {}, {}, {}, [0, 0]
    for f in files:
        V = {v: verdicts(judge, v, f) for v in ('src', 'nf', 'tf')}
        tallies.append(V['src'][1])
        forms = parse(tokens(open(os.path.join(s0, f + '.forms')).read()))
        norms = parse(tokens(open(os.path.join(wit, f + '.norm')).read()))
        n = len(V['src'][0])
        assert n == len(V['nf'][0]) == len(V['tf'][0]) == len(forms) == len(norms), f
        for i in range(n):
            total += 1
            s, nf, tf = V['src'][0][i], V['nf'][0][i], V['tf'][0][i]
            name = atom(forms[i][1][1])
            assert atom(norms[i][1][0]) == name, (f, i, name)
            lb = labels(norms[i][1][2], [])
            emit = [b for b in lb if b != EVALKL]
            if nf == 1:
                # Census against Rocq: what the judge accepts on the erased norm has no emit label.
                assert not emit, 'census labels a definition Rocq accepts on nf: %s %s %r' % (f, name, emit)
            if tf == 1:
                # Likewise on tf, which erases the inlining marker.
                assert not [b for b in emit if b != MARKER], 'census labels a definition Rocq accepts on tf: %s %s %r' % (f, name, emit)
            if s == 1:
                acc += 1
                nf_tot[0] += nf == 1
                continue
            if not lb:
                lb = [FRONT] if nf == 1 else [FALLBACK]
            first = lb[0]
            led, _, why = classify(first)
            ds = sorted({d for d in (classify(b)[1] for b in lb) if d})
            assert obs.get(led) in ('open', 'partial'), 'ledger id not open: %s' % led
            count(per_ledger, led); count(per_first, first)
            for d in ds:
                count(per_decision, d)
            rows.append('\t'.join([f, str(i), name if s == 2 else 'Unparsed', str(s), str(nf), str(tf),
                                   first, led, why, ','.join(ds) or '-']))
    assert tallies == pinned, 'Rocq src verdicts differ from tests/shen-jit/stage0-accepted.txt'
    for v in DECISIONS.values():
        assert obs.get(v) == 'open', 'decision entry not open: %s' % v
    C = lambda ext: sorted((f + ext for f in files), key=lambda x: x.encode())
    codes = {v: listing_hash(os.path.join(judge, v), C('.codes')) for v in ('src', 'nf', 'tf')}
    s0h = listing_hash(s0, C('.forms') + C('.sbc'))
    normh = concat_hash(wit, [f + '.norm' for f in files])
    shas = {p: hashlib.sha256(open(os.path.join(here, p), 'rb').read()).hexdigest()
            for p in ('stage0_residuals.py', 'pass_census.py', 'feature_census.py')}
    resid = total - acc
    hdr = [
        '# Stage 0 residuals: every definition the Rocq source judge (rocq/JitLowerStage0.v, judge, on <f>.forms)',
        '# does not accept. Generated by tests/shen-jit/stage0_residuals.py from judge_split.sh output; do not edit.',
        '# Source judge accepts %d of %d stage 0 definitions (as stage0-accepted.txt pins); residual %d.' % (acc, total, resid),
        '# Full-pipeline validated count: UNKNOWN (no full-pipeline judge at this commit). Not "lower.shen proved".',
        '# Evidence kinds. src, nf, tf: Rocq verdicts (1 accepted, 2 rejected, 0 unreadable); nf and tf judge the',
        '# untrusted erased witness and are emit-side evidence only. first-blocker: census, the first label in',
        '# evaluation order from a syntactic walk of the norm witness (Comp gaps, = outside pguard, eval-kl calls);',
        '# untrusted, not a reason Rocq gave; checked only in that no nf-accepted (tf-accepted: no non-marker) definition gets an emit label.',
        '# ledger, reason, decisions: bookkeeping, the open spec/obligations.json entry the first label is filed under',
        '# and the decision items any label of the definition touches. Decision items are Reuben\'s decision, each',
        '# defaulting to a named residual: eval-kl OB-JIT-LOWER-GENERAL, identity OB-JIT-IDENTITY-MODEL,',
        '# nan-eq OB-JIT-NAN-IDENTITY, port-prims OB-JIT-PORT-PRIMS (JitProfile.jit_port_prims_proposed is not wired).',
        '# base commit: %s' % base,
        '# stage0 *.forms *.sbc, sha256 of the LC_ALL=C sha256sum *.forms *.sbc listing: %s' % s0h,
        '# norm witness *.norm, sha256 of the bytes concatenated in C order: %s' % normh,
        '# Rocq verdict files src/nf/tf *.codes, listing method: %s %s %s' % (codes['src'], codes['nf'], codes['tf']),
        '# script sha256: stage0_residuals.py %s pass_census.py %s feature_census.py %s' % (
            shas['stage0_residuals.py'], shas['pass_census.py'], shas['feature_census.py']),
        '# first-blocker (census) totals: ' + '; '.join('%s %d' % kv for kv in sorted(per_first.items(), key=lambda kv: (-kv[1], kv[0]))),
        '# ledger totals: ' + '; '.join('%s %d' % kv for kv in sorted(per_ledger.items(), key=lambda kv: (-kv[1], kv[0]))),
        '# decision items touched (definitions; census): ' + '; '.join('%s %d' % (k, per_decision.get(k, 0)) for k in sorted(DECISIONS)),
        '# file\tindex\tname\tsrc\tnf\ttf\tfirst-blocker\tledger\treason\tdecisions',
    ]
    with open(out, 'w') as o:
        o.write('\n'.join(hdr + rows) + '\n')
    print('source judge %d of %d; residual %d; wrote %s sha256 %s' % (
        acc, total, resid, out, hashlib.sha256(open(out, 'rb').read()).hexdigest()))

if __name__ == '__main__':
    main(*sys.argv[1:6])
