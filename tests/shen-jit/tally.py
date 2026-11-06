#!/usr/bin/env python3
"""Summarize Run_*.v output against the capture. Tests, not proof."""
import os, re, sys, collections
BASE = os.environ.get('JIT_OUT', '/tmp/p1')
name = sys.argv[1]
text = open(BASE + '/d/%s.out' % name, encoding='latin1').read()
vs = re.findall(r'"((?:[^"]|"")*)"', text)
caps = [l for l in open(BASE + '/d/cap_%s.txt' % name, encoding='latin1') if l.startswith(('@ok', '@err'))]
print('verdicts', len(vs), 'captured', len(caps))
kinds = collections.Counter(v.split(' ')[0] + (' ' + v.split(' ')[1] if v.startswith('stuck') else '') for v in vs)
print(dict(kinds))
for i, (v, c) in enumerate(zip(vs, caps)):
    if v != 'agree' and len(sys.argv) > 2:
        tag, _, rest = c.strip().partition(' ')
        rest = bytes.fromhex(rest).decode('latin1') if tag == '@err' else rest
        got = v
        if v.startswith('diff-err '):
            got = 'err: ' + bytes.fromhex(''.join('%02x' % ord(ch) for ch in v[9:])).decode('latin1')
        print(i, '| real', tag, rest[:110], '| model', got[:110])
