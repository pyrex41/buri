"""Adversarial fixture construction only; never a proof acceptance step."""
from pathlib import Path
import copy
import runpy
helpers = runpy.run_path('tests/mutate-frontend.py')
read, unpack, pack, encode = (helpers[k] for k in ['read', 'unpack', 'pack', 'encode'])
tag, untag, replace = (helpers[k] for k in ['tag', 'untag', 'replace_once'])
g = read.__globals__
g['bits'] = Path('ports/observed-encoder.bits').read_text()
g['index'] = 0
raw = read()
assert g['index'] == len(g['bits']) and encode(raw) == g['bits']
profile, tagged = unpack(raw)
original = untag(tagged)
assert tag(original) == tagged and len(original) == 3
variants = {}
for name, index, side, old, new in [
 ('ObservedWrongTag', 2, 1, ('text', '011'), ('text', '010')),
 ('ObservedWrongDivisor', 0, 1, ('num', '2'), ('num', '3')),
 ('ObservedWrongCallee', 0, 1, ('sym', 'kl:buri.wire-byte'), ('sym', 'kl:buri.wire-string')),
 ('ObservedParallelLet', 0, 1, ('sym', 'let*'), ('sym', 'let')),
 ('ObservedChangedSource', 2, 0, ('text', '011'), ('text', '010')),
]:
    v = copy.deepcopy(original)
    changed = [False]
    # Mutate the body, preserving each function's signature.
    body = 3 if side == 0 else 2
    v[index][side][body] = replace(v[index][side][body], old, new, changed)
    assert changed[0]
    variants[name] = v
v = copy.deepcopy(original)
# The second sequential binding is an administrative temporary. Rename only
# the binder, leaving its use dangling; parameter/name spelling is not fixed.
v[0][1][2][3][1][1][0] = ('sym', 'UNBOUND')
variants['ObservedUnboundTemporary'] = v
variants['ObservedReorderedPairs'] = list(reversed(original))
variants['ObservedOmittedPair'] = original[:-1]
for name, value in variants.items():
    Path('_build/mutations', name + '.bits').write_text(encode(pack([profile, tag(value)])))
