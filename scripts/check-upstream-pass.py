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

# The order pass may only qualify names into its existing package namespace.
import re
helpers = ['merge-nested-lets','simple-scheme-expression?','has-computation?',
           'fresh-call-variable','order-call-inputs','order-call']
def extract(source, name):
    start = source.index('(define ' + name + '\n')
    depth = 0
    for i in range(start, len(source)):
        depth += (source[i] == '(') - (source[i] == ')')
        if depth == 0:
            return source[start:i+1]
    raise SystemExit('Unterminated upstream definition')
forms = []
for name in helpers:
    form = extract(text, name)
    form = re.sub(r'(?<=\()(' + '|'.join(re.escape(n) for n in helpers) + r')(?=[\s)])', r'_scm.\1', form)
    form = form.replace('(define ' + name + '\n', '(define _scm.' + name + '\n', 1)
    forms.append(form)
if Path('ports/compiler-order.shen').read_text() != '(tc -)\n' + '\n\n'.join(forms) + '\n':
    raise SystemExit('Extracted ordering helpers differ beyond package qualification')
primitive = Path('ports/upstream/primitives.scm').read_bytes()
identity = hashlib.sha1(b'blob ' + str(len(primitive)).encode() + b'\0' + primitive).hexdigest()
if identity != '92b8875a276848b473c59879f075f429ba44a7a0':
    raise SystemExit('Pinned upstream primitives blob mismatch')
pt = primitive.decode()
a = pt.index('(define (non-rational-/')
b = pt.index('\n\n', a)
if Path('ports/stock-division.scm').read_text() != pt[a:b] + '\n':
    raise SystemExit('Extracted stock division differs from upstream')

override = Path('ports/upstream/overrides.shen').read_bytes()
if hashlib.sha1(b'blob ' + str(len(override)).encode() + b'\0' + override).hexdigest() != '3f20b5f1b952c9c6aae3d32403da1f34095db433':
    raise SystemExit('Pinned upstream overrides blob mismatch')
read_body = extract(override.decode(), 'read-file-as-string')
if override.decode().count(read_body) != override.decode().count('(define read-file-as-string\n'):
    raise SystemExit('Repeated upstream read overrides disagree')
expected = '(tc -)\n' + read_body + '\n'
if Path('ports/io-read.shen').read_text() != expected:
    raise SystemExit('Extracted read wrapper differs from upstream')

# Kernel list helpers used by the order pass: exact bodies from the pinned
# Shen 43.1 sources/sys.shen; only defined names and self-references renamed.
kernel = Path('ports/upstream/sys.shen').read_bytes()
if hashlib.sha1(b'blob ' + str(len(kernel)).encode() + b'\0' + kernel).hexdigest() != '92aab80f04afe0b91a8f37eb835c245441b7ef09':
    raise SystemExit('Pinned Shen kernel sys.shen blob mismatch')
kt = kernel.decode()
kernel_helpers = ['occurrences', 'reverse', 'reverse-help', 'not']
kernel_forms = []
for name in kernel_helpers:
    if kt.count('(define ' + name + '\n') != 1:
        raise SystemExit('Kernel helper is not uniquely defined: ' + name)
    form = extract(kt, name)
    form = re.sub(r'(?<=\()(' + '|'.join(re.escape(n) for n in kernel_helpers) + r')(?=[\s)])', r'buri.kernel.\1', form)
    form = form.replace('(define ' + name + '\n', '(define buri.kernel.' + name + '\n', 1)
    kernel_forms.append(form)
if Path('ports/kernel-list.shen').read_text().split('(tc -)\n', 1)[1] != '\n\n'.join(kernel_forms) + '\n':
    raise SystemExit('Extracted kernel list helpers differ beyond buri.kernel. renaming')
