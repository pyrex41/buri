"""E2E-22: independent literal-correspondence check of the Chez nanopass
packages (bytes only; never semantic acceptance).

usage:
  check-chez-np-package.py languages NP-LANGUAGES.ss Input.v
  check-chez-np-package.py capture TRACE.np CODE.hex CODE.relocs Input.v
"""
from pathlib import Path
import hashlib
import re
import sys

LIT = r'"((?:[^"]|"")*)"'


def lit(text, name):
    found = re.findall(r'Definition ' + re.escape(name) + r' : string := ' + LIT + r'\.\n', text, re.S)
    if len(found) != 1:
        raise SystemExit('missing or repeated literal ' + name)
    return found[0].replace('""', '"')


mode = sys.argv[1]
if mode == 'languages':
    src, target = sys.argv[2:]
    text = Path(target).read_text()
    raw = Path(src).read_bytes()
    if hashlib.sha256(raw).hexdigest() != 'db2c01ecfff979bf6b6c2ea2c493c0e2fbe9049f414a5c938f7114b2d48c9f2e':
        raise SystemExit('np-languages.ss is not the pinned Chez 10.3.0 v10.3.0 file')
    if lit(text, 'np_languages_source').encode('ascii') != raw:
        raise SystemExit('np-languages source literal does not match source bytes')
    spans = re.findall(r'\((\d+), (\d+)\)', text.split('Definition np_language_spans', 1)[1])
    body = raw.decode('ascii')
    for a, n in spans:
        if not body[int(a):int(a) + int(n)].startswith('(define-language '):
            raise SystemExit('span does not start a define-language form')
elif mode == 'capture':
    trace, hexfile, relocs, target = sys.argv[2:]
    text = Path(target).read_text()
    t = Path(trace).read_bytes().decode('ascii')
    start = t.index('@@@ np-trace\n') + len('@@@ np-trace\n')
    end = t.index('@@@ end\n', start)
    sec_text = text.split('Definition np_sections : list (string * string) := [\n', 1)[1]
    sec_text = sec_text.split('].\nDefinition arm_code_hex', 1)[0]
    pairs = re.findall(r' \(' + LIT + r', ' + LIT + r'\)(?:;\n|$)', sec_text, re.S)
    rebuilt = ''.join('output of ' + n.replace('""', '"') + ':\n' + b.replace('""', '"') for n, b in pairs)
    if rebuilt != t[start:end]:
        raise SystemExit('packaged sections do not reassemble the captured trace')
    params = t[t.index('@@@ parameters\n') + len('@@@ parameters\n'):t.index('@@@ end\n')]
    if lit(text, 'np_parameters') != params:
        raise SystemExit('parameters literal mismatch')
    if lit(text, 'arm_code_hex').encode('ascii') != Path(hexfile).read_bytes():
        raise SystemExit('hex literal mismatch')
    if lit(text, 'arm_code_relocs').encode('ascii') != Path(relocs).read_bytes():
        raise SystemExit('relocs literal mismatch')
else:
    raise SystemExit('unknown mode')
