"""Malformed native-capture fixtures; semantic acceptance stays in Rocq."""
from pathlib import Path
import copy
import runpy

h = runpy.run_path('tests/mutate-wire.py')
read, unpack, pack, encode = (h[k] for k in ['read', 'unpack', 'pack', 'encode'])
g = read.__globals__
g['bits'] = Path('ports/constructor.bits').read_text()
g['index'] = 0
raw = read()
assert encode(raw) == g['bits'] and g['index'] == len(g['bits'])
profile, tagged = unpack(raw)

def atom(s):
    return ('atom', '0', s.encode())

def untag(v):
    fs = unpack(v)
    k = fs[0][2].decode()
    if k == 'nil':
        return []
    if k == 'pair':
        return [untag(fs[1])] + untag(fs[2])
    if k == 'text':
        return (k, ''.join(chr(int(x[2])) for x in unpack(fs[1])))
    return (k, fs[1][2].decode())

def tag(v):
    if isinstance(v, list):
        return pack([atom('nil')]) if not v else pack([atom('pair'), tag(v[0]), tag(v[1:])])
    k, s = v
    payload = pack([('atom', '1', str(ord(c)).encode()) for c in s]) if k == 'text' else (
        'atom', '1' if k in ['num', 'bool'] else '0', s.encode())
    return pack([atom(k), payload])

def replace(v, old, new):
    if v == old:
        return copy.deepcopy(new)
    return [replace(x, old, new) for x in v] if isinstance(v, list) else v

original = untag(tagged)
assert tag(original) == tagged and len(original) == 10
variants = {}
for name, definition, old, new in [
    ('CtorLambda', 'kl:buri.sealed-definition', ('sym', 'lambda'), ('sym', 'wrong')),
    ('CtorAuthority', 'kl:buri.sealed-request', ('sym', 'only'), ('sym', 'except')),
    ('CtorBoolean', 'kl:buri.sealed-definition', ('bool', '1'), ('sym', 'true')),
    ('CtorExecutor', 'kl:buri.sealed-eval', ('sym', 'eval'), ('sym', 'evil')),
    ('CtorEntry', 'kl:buri.make-sealed-encoder', ('sym', 'kl:buri.sealed-program'), ('sym', 'evil')),
]:
    v = copy.deepcopy(original)
    d = next(d for d in v if d[1][0] == ('sym', definition))
    before = copy.deepcopy(d[2])
    d[2] = replace(d[2], old, new)
    assert d[2] != before
    variants[name] = v
v = copy.deepcopy(original)
d = next(d for d in v if d[1][0] == ('sym', 'kl:buri.sealed-program'))

def swap_append(v):
    if isinstance(v, list):
        if v and v[0] == ('sym', 'kl:buri.sealed-append'):
            assert len(v) == 3
            return [v[0], v[2], v[1]]
        return [swap_append(x) for x in v]
    return v

d[2] = swap_append(d[2])
assert v != original
variants['CtorAppendOrder'] = v
variants['CtorOmitted'] = original[:-1]
variants['CtorExtra'] = original + [original[-1]]
for name, v in variants.items():
    Path('_build/mutations', name + '.bits').write_text(encode(pack([profile, tag(v)])))
