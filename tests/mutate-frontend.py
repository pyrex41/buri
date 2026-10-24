"""Construct adversarial captures. This code does not participate in acceptance."""
from pathlib import Path
import copy
import runpy

# Reuse the transport fixture parser, not a semantic verifier. Its existing
# native mutations are regenerated as part of this same adversarial gate.
wire = runpy.run_path('tests/mutate-wire.py')
read = wire['read']
g = read.__globals__
g['bits'] = Path('ports/encoder-kl.bits').read_text()
g['index'] = 0
raw = read()
assert g['index'] == len(g['bits'])
pack, unpack, encode = wire['pack'], wire['unpack'], wire['encode']
profile, tagged = unpack(raw)

def atom(s):
    return ('atom', '0', s.encode('ascii'))

def untag(d):
    fields = unpack(d)
    kind = fields[0][2].decode('ascii')
    if kind == 'nil':
        return []
    if kind == 'pair':
        return [untag(fields[1])] + untag(fields[2])
    if kind == 'sym':
        return ('sym', fields[1][2].decode('ascii'))
    if kind == 'num':
        return ('num', fields[1][2].decode('ascii'))
    if kind == 'text':
        return ('text', ''.join(chr(int(x[2])) for x in unpack(fields[1])))
    raise AssertionError(kind)

def tag(d):
    if isinstance(d, list):
        return pack([atom('nil')]) if not d else pack([atom('pair'), tag(d[0]), tag(d[1:])])
    kind, value = d
    if kind == 'text':
        payload = pack([('atom', '1', str(ord(c)).encode('ascii')) for c in value])
    else:
        payload = ('atom', '1' if kind == 'num' else '0', value.encode('ascii'))
    return pack([atom(kind), payload])

original = untag(tagged)
assert tag(original) == tagged and len(original) == 3

def replace_once(d, old, new, changed):
    if d == old and not changed[0]:
        changed[0] = True
        return new
    if isinstance(d, list):
        return [replace_once(x, old, new, changed) for x in d]
    return d

variants = {}
for name, old, new in [
    ('KLChangedDivisor', ('num', '2'), ('num', '3')),
    ('KLChangedTag', ('text', '011'), ('text', '010')),
]:
    changed = [False]
    variants[name] = replace_once(original, old, new, changed)
    assert changed[0]
v = copy.deepcopy(original)
v[0][2][0] = ('sym', 'UNBOUND')
variants['KLWrongBinder'] = v
v = copy.deepcopy(original)
v[0][2][1] = v[0][2][0]
variants['KLDuplicateParameters'] = v
variants['KLOmittedDefinition'] = original[:-1]
v = copy.deepcopy(original)
changed = [False]
v[0][3] = replace_once(v[0][3], ('sym', 'buri.wire-byte'), ('sym', 'buri.wire-string'), changed)
assert changed[0]
variants['KLWrongCallee'] = v
for name, value in variants.items():
    Path('_build/mutations', name + '.bits').write_text(encode(pack([profile, tag(value)])))
