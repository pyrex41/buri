"""Independent literal byte comparison for rocq/Prims2Sources.v.

No semantic acceptance: for every recorded span it re-reads the named file
(the patched one from PATCHED_OUT), re-checks its git blob id, and checks
that the Coq string literal is exactly those bytes (quotes doubled).
"""
from pathlib import Path
import hashlib
import re
import sys

out, module = sys.argv[1:]
text = Path(module).read_text()
spans = re.findall(r'Definition ([a-z_0-9]+)_span : string \* string \* nat \* nat := \("([^"]+)", "([0-9a-f]{40})", ([0-9]+), ([0-9]+)\)\.', text)
lits = dict(re.findall(r'Definition ([a-z_0-9]+)_source : string := "((?:[^"]|"")*)\n"\.', text))
if len(spans) != 8 or len(lits) != 8:
    raise SystemExit('Malformed prims2 package')
for name, path, blob, start, end in spans:
    p = Path(out) / path[len('patched:'):] if path.startswith('patched:') else Path(path)
    raw = p.read_bytes()
    if hashlib.sha1(b'blob %d\0' % len(raw) + raw).hexdigest() != blob:
        raise SystemExit('Blob mismatch: ' + path)
    src = raw.decode()[int(start):int(end)]
    if not src.startswith('(def'):
        raise SystemExit('Span does not open a definition: ' + name)
    if lits.get(name, '').replace('""', '"') != src:
        raise SystemExit('Literal does not match source bytes: ' + name)
