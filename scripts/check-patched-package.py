"""Independent literal byte comparison for the patched multiply package.

No semantic acceptance: it re-reads the patched primitives.lsp written by
`package-patched.py apply`, takes the recorded span, and checks that the Coq
string literal in the module is exactly those bytes (quotes doubled).
"""
from pathlib import Path
import re
import sys
out, module = sys.argv[1:]
text = Path(module).read_text()
span = re.findall(r'Definition patched_multiply_span : nat \* nat := \(([0-9]+), ([0-9]+)\)\.', text)
lit = re.findall(r'Definition patched_multiply_source : string := "((?:[^"]|"")*)\n"\.', text)
source = (Path(out) / 'shen-cl/primitives.lsp').read_text()
if len(span) != 1 or len(lit) != 1:
    raise SystemExit('Malformed patched multiply package')
start, end = int(span[0][0]), int(span[0][1])
if not source[start:end].startswith('(defun |shen-cl.multiply| (x y)\n'):
    raise SystemExit('Patched multiply span does not open the definition')
if lit[0].replace('""', '"') != source[start:end]:
    raise SystemExit('Patched multiply literal does not match source bytes')
