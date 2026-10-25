"""Byte lineage check for the extracted upstream pass, not semantic checking."""
from pathlib import Path
import hashlib
source = Path('ports/upstream/compiler.shen').read_bytes()
blob = hashlib.sha1(b'blob ' + str(len(source)).encode() + b'\0' + source).hexdigest()
if blob != '42ac753b8f305c578998b74693fc85b28112a814':
    raise SystemExit('Pinned upstream compiler blob mismatch')
text = source.decode()
a = text.index('(define merge-nested-lets\n')
b = text.index('\n(define', a + 1)
original = text[a:b].strip()
qualified = Path('ports/compiler-merge.shen').read_text().split('(tc -)\n', 1)[1].strip()
if qualified != original.replace('(define merge-nested-lets', '(define _scm.merge-nested-lets', 1):
    raise SystemExit('Extracted compiler pass differs beyond its qualified entry name')
