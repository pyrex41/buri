#!/usr/bin/env python3
"""Tables for spikes/pass-split/CENSUS.md, from the outputs of capture_passes.sh and judge_split.sh.

A census, not evidence: it counts verdicts the Rocq judge already gave (judge_split.sh) and
classifies rejected definitions by the first normal-form construct, in evaluation order, that
JitLowerRel.Comp has no rule for. The classification is syntactic and untrusted; only the verdicts
come from Rocq.

    pass_census.py STAGE0_DIR CAPTURE_DIR JUDGE_DIR
"""
import collections, os, sys
sys.path.insert(0, os.path.dirname(__file__))
from stage0_to_rocq import tokens, parse

# JitLowerRel.pmap: the primitives Comp admits.
ADMITTED = {'+', '-', '*', '>', '<', '>=', '<=', 'cons', 'hd', 'tl', 'cons?', 'number?', 'string?'}

FAMILIES = [
    ('share chains', ['share-chain']),
    ('sugar', ['cond', 'type', 'protect', 'thaw', 'trap-lambda', 'trap-other', 'lambda-app',
               'lambda-app-more', 'curried-apply', 'fn-sealed', 'fn-open', 'eval-kl']),
    ('prim folding', ['fold-cons', 'fold-plus', 'fold-minus']),
    ('sealed inlining', ['sealed-inline', 'inline-int-arg']),
    ('open inlining', ['open-inline']),
    ('freeze copying', ['let-frozen-copy', 'let-frozen-keep', 'frozen-late-hoist', 'inline-frozen']),
    ('is!/bind!', ['unified-now', 'bound-now', 'bound-now-frozen']),
    ('lambda copying', ['let-lambda']),
    ('(not a rewrite) dynamic application', ['dynamic-apply']),
]

def read(path):
    return parse(tokens(open(path).read()))

def atom(x):
    return x[1] if x[0] == 'atom' else None

MARKER = 'inlining marker (let stage0.lower.inlining)'
FALLBACK = 'none found (emit-side mismatch on admitted constructs)'

def blockers(n, transparent, out):
    """Append to out, in evaluation order, each construct of n that Comp has no rule for.
    transparent: treat the inlining marker as its body (as <f>.tforms erases it)."""
    l = n[1]
    tag = atom(l[0])
    def each(xs):
        for x in xs:
            blockers(x, transparent, out)
    if tag == 'const':
        v = l[1]
        if v[0] == 'list' and v[1]:
            out.append('folded constant list')
    elif tag == 'var':
        pass
    elif tag in ('if', 'and', 'or'):
        each(l[1:])
    elif tag == 'let':
        x, v, b = atom(l[1]), l[2], l[3]
        if x == 'stage0.lower.inlining':
            if not transparent:
                out.append(MARKER)
            each([b])
        elif v[0] == 'list' and atom(v[1][0]) == 'freeze':
            out.append('let-bound freeze (goto label / thaw in place)')
            each([v[1][1], b])
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
        elif op not in ADMITTED:
            out.append('prim ' + op)
        each(l[2][1])
    elif tag == 'call':
        each(l[2][1])
    elif tag == 'apply':
        out.append('apply (thaw)' if len(l) == 2 else 'apply (dynamic call)'); each(l[1:])
    else:
        raise ValueError('not a normal form: %r' % (n,))
    return out

def verdicts(judge, variant, f):
    lines = open(os.path.join(judge, variant, f + '.codes')).read().split('\n')
    head = lines[0].split()
    vs = [int(v) for v in lines[1].split()]
    assert int(head[1]) == vs.count(1) and int(head[2]) == vs.count(2) and int(head[3]) == vs.count(0), f
    return vs

def blocker_table(title, kept):
    """kept: one ordered blocker list per rejected definition."""
    first, uses, sole = collections.Counter(), collections.Counter(), collections.Counter()
    for bl in kept:
        bl = bl or [FALLBACK]
        first[bl[0]] += 1
        kinds = set(bl)
        for k in kinds:
            uses[k] += 1
        if len(kinds) == 1:
            sole[bl[0]] += 1
    print('## %s (definitions: %d)\n' % (title, len(kept)))
    print('| construct Comp has no rule for | first blocker | uses | sole blocker |')
    print('|---|---:|---:|---:|')
    for k, v in sorted(uses.items(), key=lambda kv: (-first[kv[0]], -kv[1], kv[0])):
        print('| %s | %d | %d | %d |' % (k, first[k], v, sole[k]))
    print()

def main(s0, cap, judge):
    files = sorted(f[:-6] for f in os.listdir(s0) if f.endswith('.forms'))
    wit, cnt = os.path.join(cap, 'witness'), os.path.join(cap, 'count')
    rows, kept_nf, kept_tf = [], [], []
    unread = collections.Counter()
    flags_defs = collections.Counter()
    tick_defs, tick_total = collections.Counter(), collections.Counter()
    fam_defs = collections.Counter()
    anomalies = []
    share_changed = 0
    no_rewrite = 0
    T = collections.Counter()
    for f in files:
        V = {v: verdicts(judge, v, f) for v in ('src', 'nf', 'tf')}
        norms = read(os.path.join(wit, f + '.norm'))
        forms = open(os.path.join(s0, f + '.forms')).read().split('\n')
        shares = open(os.path.join(wit, f + '.share')).read().split('\n')
        share_changed += sum(1 for a, b in zip(forms, shares) if a != b)
        census = read(os.path.join(wit, f + '.ncensus'))
        ticks = read(os.path.join(cnt, f + '.ticks'))
        assert len(V['src']) == len(V['nf']) == len(V['tf']) == len(norms) == len(census) == len(ticks), f
        r = collections.Counter()
        for i in range(len(norms)):
            a, b, t = V['src'][i] == 1, V['nf'][i] == 1, V['tf'][i] == 1
            r['n'] += 1
            r['src'] += a; r['nf'] += b; r['tf'] += t
            r['both'] += a and b; r['either'] += a or b
            r['src only'] += a and not b; r['nf only'] += b and not a
            r['tf only'] += t and not a
            for v in V:
                unread[v] += V[v][i] == 0
            name = atom(norms[i][1][0])
            for fl in census[i][1][1][1]:
                flags_defs[atom(fl)] += 1
            fired = set()
            for kv in ticks[i][1][1][1]:
                k, c = atom(kv[1][0]), int(atom(kv[1][1]))
                tick_defs[k] += 1; tick_total[k] += c; fired.add(k)
            for fam, keys in FAMILIES:
                if fired & set(keys):
                    fam_defs[fam] += 1
            no_rewrite += not (fired - {'dynamic-apply'})
            N = norms[i][1][2]
            bn, bt = blockers(N, False, []), blockers(N, True, [])
            if b and bn:
                anomalies.append((f, name, 'accepted on nforms with ' + bn[0]))
            if t and bt:
                anomalies.append((f, name, 'accepted on tforms with ' + bt[0]))
            if not b:
                kept_nf.append(bn)
            if not t:
                kept_tf.append(bt)
        rows.append((f, r)); T.update(r)
    cols = ['n', 'src', 'nf', 'tf', 'both', 'either', 'src only', 'nf only', 'tf only']
    print('## Split census (accepted per file)\n')
    print('src: the form as read (.forms); nf: erased normal form (.nforms); tf: erased normal form with')
    print('the inlining marker dropped (.tforms). both/either/only compare src with nf; tf only = accepted')
    print('on tf and not on src.\n')
    print('| file | defs | src | nf | tf | src and nf | src or nf | src only | nf only | tf only |')
    print('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for f, r in rows:
        print('| %s | %s |' % (f, ' | '.join(str(r[c]) for c in cols)))
    print('| **total** | %s |' % ' | '.join('**%d**' % T[c] for c in cols))
    print('\nunreadable (Unparsed): src %d, nf %d, tf %d\n' % (unread['src'], unread['nf'], unread['tf']))
    rej_src = T['n'] - T['src']
    print('Of the %d definitions rejected on src: %d accepted on nf, %d accepted on tf.\n'
          % (rej_src, T['nf only'], T['tf only']))
    blocker_table('Blockers on nf, definitions rejected on nf', kept_nf)
    blocker_table('Blockers on tf, definitions rejected on tf', kept_tf)
    print('## Normal-form facts (definitions)\n')
    print('| fact | definitions |')
    print('|---|---:|')
    for k in ['inlined?', 'inlining-marker', 'fresh', 'folded', 'shadow', 'applyhead', 'callshadow']:
        print('| %s | %d |' % (k, flags_defs[k]))
    print('\nshare output differs from the source form: %d definitions\n' % share_changed)
    print('## Rewrite families (count run)\n')
    print('| family | key | definitions | firings |')
    print('|---|---|---:|---:|')
    for fam, keys in FAMILIES:
        for k in keys:
            print('| %s | %s | %d | %d |' % (fam, k, tick_defs[k], tick_total[k]))
        print('| **%s** | any | **%d** | |' % (fam, fam_defs[fam]))
    print('\nno rewrite family fired (dynamic-apply aside): %d definitions' % no_rewrite)
    print('\nanomalies (accepted with a syntactic blocker): %d' % len(anomalies))
    for a in anomalies[:20]:
        print('  ', a)

if __name__ == '__main__':
    main(*sys.argv[1:4])
