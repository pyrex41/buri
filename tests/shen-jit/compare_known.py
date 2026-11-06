#!/usr/bin/env python3
"""Compare Rocq's verdicts with tests/shen-jit/known-differences.txt. Anything not listed
must agree, and everything listed must still differ. Tests, not proof.

    compare_known.py KNOWN [--write] SET...
"""
import os, re, sys
BASE = os.environ.get('JIT_OUT', '/tmp/p1')
args = sys.argv[1:]
known_path = args.pop(0)
write = '--write' in args
if write: args.remove('--write')
now, total, agree = {}, 0, 0
for name in args:
    text = open(BASE + '/d/%s.out' % name, encoding='latin1').read()
    vs = re.findall(r'"((?:[^"]|"")*)"', text)
    caps = [l for l in open(BASE + '/d/cap_%s.txt' % name, encoding='latin1') if l.startswith(('@ok', '@err'))]
    if not vs or len(vs) != len(caps):
        print('VERDICT_COUNT_MISMATCH', name, len(vs), len(caps)); sys.exit(2)
    total += len(vs)
    for i, v in enumerate(vs):
        if v == 'agree': agree += 1
        else: now['%s %d' % (name, i)] = v.split(' ')[0] + (' ' + v.split(' ')[1] if v.startswith('stuck') else '')
if write:
    keep = {}
    try:
        for l in open(known_path):
            if l.strip() and not l.startswith('#'):
                k, _, rest = l.rstrip('\n').partition(' | ')
                keep[k] = rest
    except FileNotFoundError: pass
    with open(known_path, 'w') as f:
        f.write('# Differential differences at pin b4ccf2d: set index | kind | why. Tests, not proof.\n')
        for k in sorted(now, key=lambda s: (s.split()[0], int(s.split()[1]))):
            why = keep.get(k, '').split(' | ', 1)
            f.write('%s | %s | %s\n' % (k, now[k], why[1] if len(why) > 1 else 'UNEXPLAINED'))
    sys.exit(0)
known = {}
for l in open(known_path):
    if l.strip() and not l.startswith('#'):
        k, kind, why = l.rstrip('\n').split(' | ', 2)
        known[k] = kind
new = sorted(set(now) - set(known))
gone = sorted(set(known) - set(now))
changed = sorted(k for k in now if k in known and known[k] != now[k])
print('differential: %d cases, %d agree, %d known differences, %d new, %d gone, %d changed' % (total, agree, len(now) - len(new), len(new), len(gone), len(changed)))
for k in new[:20]: print('NEW_DIFFERENCE', k, now[k])
for k in gone[:20]: print('GONE', k)
for k in changed[:20]: print('CHANGED', k, known[k], '->', now[k])
sys.exit(1 if new or gone or changed else 0)
