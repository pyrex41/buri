"""Adversarial adapter AST fixtures; Rocq checks the actual semantic proofs."""
from pathlib import Path
import copy
import runpy
import subprocess
h = runpy.run_path('tests/mutate-constructor.py')
read, unpack, pack, encode, untag, tag, replace = (h[k] for k in
    ['read', 'unpack', 'pack', 'encode', 'untag', 'tag', 'replace'])
g = read.__globals__
g['bits'], g['index'] = Path('ports/adapter.bits').read_text(), 0
raw = read()
assert encode(raw) == g['bits'] and g['index'] == len(g['bits'])
profile, tagged = unpack(raw)
original = untag(tagged)
assert tag(original) == tagged
proof = Path('rocq/AdapterCorrect.v').read_text().replace(' NativeCodec AdapterInput.', ' NativeCodec.')
assert 'AdapterInput' not in proof
for name, definition, old, new in [
    ('AdapterWrongTag', 'kl:buri.kl-node', ('sym', 'num'), ('sym', 'sym')),
    ('AdapterWrongTail', 'kl:buri.kl-bytes', ('num', '1'), ('num', '0')),
    ('AdapterWrongChild', 'kl:buri.kl-node', ('sym', 'cdr'), ('sym', 'car')),
    ('AdapterWrongType', 'kl:buri.kl-node', ('sym', 'string?'), ('sym', 'symbol?')),
]:
    mutant = copy.deepcopy(original)
    d = next(d for d in mutant if d[1][0] == ('sym', definition))
    before = copy.deepcopy(d[2])
    d[2] = replace(d[2], old, new)
    assert before != d[2]
    bits, module = (Path('_build/mutations', name + suffix) for suffix in ['.bits', '.v'])
    bits.write_text(encode(pack([profile, tag(mutant)])))
    subprocess.run(['python3', 'scripts/package-adapter.py', str(bits), str(module)], check=True)
    with module.open('a') as out:
        out.write('\n' + proof)
