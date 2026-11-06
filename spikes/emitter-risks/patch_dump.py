#!/usr/bin/env python3
"""Mutation helper: patch the captured bytes, or a field of the dump. usage: patch_dump.py IN OUT KIND ARGS..."""
import sys
lines = open(sys.argv[1]).read().splitlines()
d = {l.split(' ', 1)[0]: l for l in lines}
kind = sys.argv[3]
if kind == 'bytes':          # OFFSET HEX (little-endian instruction, 2 or 4 bytes)
    off, hexw = int(sys.argv[4], 16), sys.argv[5]
    b = [int(x) for x in d['bytes'].split()[1:]]
    w = int(hexw, 16); n = len(hexw) // 2
    for i in range(n): b[off + i] = (w >> (8 * i)) & 0xff
    d['bytes'] = 'bytes ' + ' '.join(map(str, b))
elif kind == 'state':        # WORDOFFSET C M P R
    st = d['states'].split()[1:]
    st = [x for x in st if not x.startswith(sys.argv[4] + ':')] + [':'.join(sys.argv[4:9])]
    d['states'] = 'states ' + ' '.join(st)
elif kind == 'cut':          # WORDOFFSET NEWCUT
    c = d['cuts'].split()[1:]; c[int(sys.argv[4])] = sys.argv[5]
    d['cuts'] = 'cuts ' + ' '.join(c)
open(sys.argv[2], 'w').write('\n'.join(d[l.split(' ', 1)[0]] for l in lines) + '\n')
