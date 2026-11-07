#!/usr/bin/env python3
"""Census of what stage 0 definitions use, by construct, outside the Phase 2 relation.

Not evidence of anything proved: it reads the KLambda forms and counts definitions that use each
construct JitLowerRel.v does not admit, so that the cost of widening the relation can be estimated.
A definition is counted under every construct it uses.

    stage0_census.py STAGE0_DIR
"""
import collections, glob, os, sys
sys.path.insert(0, os.path.dirname(__file__))
from stage0_to_rocq import tokens, parse

ADMITTED_PRIMS = {'+', '-', '*', '>', '<', '>=', '<=', 'cons', 'hd', 'tl', 'cons?', 'number?', 'string?'}
SPECIAL = {'if', 'and', 'or', 'cond', 'let', 'type'}
KL_PRIMS = {'intern', 'pos', 'tlstr', 'cn', 'str', 'string?', 'n->string', 'string->n', 'set', 'value',
            'simple-error', 'error-to-string', 'cons', 'hd', 'tl', 'cons?', '=', 'eval-kl', 'absvector',
            'address->', '<-address', 'absvector?', 'write-byte', 'read-byte', 'open', 'close', 'get-time',
            '+', '-', '*', '/', '>', '<', '>=', '<=', 'number?'}

def uses(x, bound, out):
    if x[0] != 'list':
        return
    l = x[1]
    if not l:
        return
    h = l[0]
    if h[0] == 'atom':
        a = h[1]
        if a in bound:
            out.add('dynamic application')
        elif a in ('lambda', 'freeze'):
            out.add('closure (' + a + ')')
        elif a == 'trap-error':
            out.add('trap-error')
        elif a == 'do':
            out.add('do')
        elif a == 'thaw':
            out.add('thaw')
        elif a == 'defun':
            out.add('nested defun')
        elif a in KL_PRIMS and a not in ADMITTED_PRIMS:
            out.add('primitive ' + a)
        elif a not in SPECIAL and a not in KL_PRIMS and a.startswith('shen-jit.'):
            out.add('port primitive')
        if a == 'let' and len(l) == 4 and l[1][0] == 'atom':
            uses(l[2], bound, out); uses(l[3], bound | {l[1][1]}, out); return
        if a == 'lambda' and len(l) == 3 and l[1][0] == 'atom':
            uses(l[2], bound | {l[1][1]}, out); return
    else:
        out.add('dynamic application')
    for y in l[1:] if h[0] == 'atom' else l:
        uses(y, bound, out)

def main(d):
    per = collections.Counter(); only = collections.Counter(); total = 0
    for f in sorted(glob.glob(os.path.join(d, '*.forms'))):
        for form in parse(tokens(open(f).read())):
            l = form[1]
            params = {p[1] for p in l[2][1]} if l[2][0] == 'list' else set()
            out = set(); uses(l[3], params, out); total += 1
            for k in out: per[k] += 1
            if len(out) == 1: only[next(iter(out))] += 1
            if not out: only['(none of these)'] += 1
    print('definitions', total)
    for k, v in per.most_common(): print('uses %-34s %4d   sole blocker %4d' % (k, v, only[k]))
    print('uses none of these %4d' % only['(none of these)'])

if __name__ == '__main__':
    main(sys.argv[1])
