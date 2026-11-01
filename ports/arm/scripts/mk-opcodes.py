#!/usr/bin/env python3
"""Packaging only: turn a <prefix>.hex word dump into a list of
(offset, little-endian byte string) for selected offset ranges.
usage: mk-opcodes.py HEXFILE START:END[,START:END...] > list
Offsets are byte offsets from the dump's first byte (hex)."""
import sys
hexfile, ranges = sys.argv[1], sys.argv[2]
want = []
for r in ranges.split(','):
    a, b = r.split(':')
    want.append((int(a, 16), int(b, 16)))
for line in open(hexfile):
    if line.startswith('#'):
        continue
    off, word = line.split()
    off = int(off, 16)
    if any(a <= off < b for a, b in want):
        w = int(word, 16)
        print('%04x %s' % (off, w.to_bytes(4, 'little').hex()))
