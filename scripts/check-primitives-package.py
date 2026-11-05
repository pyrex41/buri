"""Independent literal correspondence check for rocq/PrimitiveSources.v.

Not semantic acceptance: it only confirms that every recorded byte span names
a blob-pinned source file and that the Coq string literal is exactly those
bytes, in order. Reading and admission are Rocq computations.
"""
from pathlib import Path
import hashlib
import re
import sys

target = Path(sys.argv[1]).read_text()
for profile in ('scheme', 'cl'):
    spans = re.findall(r'\("([^"]+)", "([0-9a-f]{40})", (\d+), (\d+)\)',
                       re.findall(r'Definition ' + profile + r'_spans [^\n]*\n(.*?)\]\.\n', target, re.S)[0])
    literal = re.findall(r'Definition ' + profile + r'_source : string := "(.*?)"\.\n', target, re.S)
    if not spans or len(literal) != 1:
        raise SystemExit('Malformed primitive source package: ' + profile)
    pieces = []
    for path, blob, start, end in spans:
        raw = Path(path).read_bytes()
        if hashlib.sha1(b'blob %d\0' % len(raw) + raw).hexdigest() != blob:
            raise SystemExit('Pinned blob mismatch: ' + path)
        pieces.append(raw[int(start):int(end)])
    if literal[0].replace('""', '"').encode('ascii') != b'\n\n'.join(pieces) + b'\n':
        raise SystemExit('Primitive source literal does not match pinned bytes: ' + profile)
print('primitive source package matches pinned bytes')
