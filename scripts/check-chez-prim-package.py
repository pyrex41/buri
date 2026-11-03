"""E2E-22 (chezprim lane): independent literal-correspondence check of
rocq/ChezPrimRawInput.v against the raw capture (bytes only; never semantic
acceptance).

usage: check-chez-prim-package.py TRACE.raw.np Input.v
"""
from pathlib import Path
import re
import sys

LIT = r'"((?:[^"]|"")*)"'

trace, target = sys.argv[1:]
text = Path(target).read_text()
t = Path(trace).read_bytes().decode('ascii')
start = t.index('@@@ np-trace\n') + len('@@@ np-trace\n')
end = t.index('@@@ end\n', start)
body = text.split('Definition raw_sections : list (string * string * option string) := [\n', 1)[1]
assert body.endswith('].\n'), 'unexpected trailer'
body = body[:-3]
item = re.compile(r' \(' + LIT + r', ' + LIT + r', (?:None|\(Some ' + LIT + r'\))\)(?:;\n|$)', re.S)
pos, rebuilt = 0, ''
for m in item.finditer(body):
    if m.start() != pos:
        raise SystemExit('unparsed text between packaged sections')
    pos = m.end()
    name, pretty, raw = (g.replace('""', '"') if g is not None else None for g in m.groups())
    rebuilt += 'output of ' + name + ':\n' + pretty + ('' if raw is None else 'raw output:\n' + raw)
if pos != len(body):
    raise SystemExit('trailing text after packaged sections')
if rebuilt != t[start:end]:
    raise SystemExit('packaged sections do not reassemble the captured trace')
params = t[t.index('@@@ parameters\n') + len('@@@ parameters\n'):t.index('@@@ end\n')]
found = re.findall(r'Definition raw_parameters : string := ' + LIT + r'\.\n', text, re.S)
if len(found) != 1 or found[0].replace('""', '"') != params:
    raise SystemExit('parameters literal mismatch')
