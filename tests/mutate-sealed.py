"""Adversarial fixtures only; independent Rocq compilation decides rejection."""
from pathlib import Path
import copy
import runpy

h = runpy.run_path('tests/mutate-frontend.py')
read, unpack, pack, encode, tag, untag, replace = (
    h[k] for k in ['read', 'unpack', 'pack', 'encode', 'tag', 'untag', 'replace_once'])
g = read.__globals__
g['bits'] = Path('ports/sealed.bits').read_text()
g['index'] = 0
raw = read()
assert encode(raw) == g['bits'] and g['index'] == len(g['bits'])
profile, tagged = unpack(raw)
original = untag(tagged)
assert len(original) == 3 and tag(original) == tagged
variants = {}
for name, old, new in [
    ('SealedUnknown', ('sym', 'char->integer'), ('sym', 'unknown-helper')),
    ('SealedEval', ('sym', 'char->integer'), ('sym', 'eval')),
    ('SealedMutation', ('sym', 'char->integer'), ('sym', 'set!')),
    ('SealedDifferentHelper', ('sym', 'exact?'), ('sym', 'integer?')),
    ('SealedDifferentTarget', ('text', '011'), ('text', '010')),
]:
    v = copy.deepcopy(original)
    changed = [False]
    v[0] = replace(v[0], old, new, changed)
    assert changed[0]
    variants[name] = v
v = copy.deepcopy(original)
del v[0][1][0]
variants['SealedMissingHelper'] = v
v = copy.deepcopy(original)
v[2].append(('sym', 'eval'))
variants['SealedExtraImport'] = v
for name, v in variants.items():
    Path('_build/mutations', name + '.bits').write_text(encode(pack([profile, tag(v)])))
