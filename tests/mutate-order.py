"""Adversarial ordering/fresh-name captures; acceptance is decided only by Rocq.

Each mutant changes the captured implementation AND restates the changed body
in the proof text, so the literal capture check still passes and only the
semantic proof can reject the mutant.
"""
from pathlib import Path
import copy
import runpy
import subprocess
h = runpy.run_path('tests/mutate-constructor.py')
read, unpack, pack, encode, untag, tag = (h[k] for k in ['read', 'unpack', 'pack', 'encode', 'untag', 'tag'])

def load(capture):
    g = read.__globals__
    g['bits'], g['index'] = Path('ports', capture + '.bits').read_text(), 0
    raw = read()
    assert encode(raw) == g['bits'] and g['index'] == len(g['bits'])
    profile, tagged = unpack(raw)
    return profile, untag(tagged)

def rewrite(node, match, change):
    """Apply change to the first list node satisfying match (depth first)."""
    if isinstance(node, list):
        if match(node):
            change(node)
            return True
        return any(rewrite(child, match, change) for child in node)
    return False

S = lambda s: ('sym', s)
def swap_cons(n):
    n[1], n[2] = n[2], n[1]
def swap_if(n):
    n[2], n[3] = n[3], n[2]

mutants = [
    # Keep branch conses the kept argument AFTER the accumulator: argument order is scrambled.
    ('OrderSwappedKeep', 'order-call', 'order_call', 'kl:_scm.order-call-inputs',
     lambda n: n == [S('cons'), [S('car'), S('V5977')], S('V5978')], swap_cons,
     'Call "cons" [Call "car" [Var "V5977"]; Var "V5978"]',
     'Call "cons" [Var "V5978"; Call "car" [Var "V5977"]]', ' OrderCallInput'),
    # Fresh loop accepts a candidate exactly when it already occurs (non-fresh capture).
    ('FreshAcceptsCollision', 'order-call', 'order_call', 'kl:_scm.fresh-call-variable',
     lambda n: len(n) == 4 and n[0] == S('if'), swap_if,
     '(If guard (Var "W5974") (Call "kl:_scm.fresh-call-variable" [Var "V5973"]))',
     '(If guard (Call "kl:_scm.fresh-call-variable" [Var "V5973"]) (Var "W5974"))', ' OrderCallInput'),
]
for name, capture, kind, definition, match, change, old, new, removed in mutants:
    profile, original = load(capture)
    mutant = copy.deepcopy(original)
    d = next(d for d in mutant if d[1][0] == S(definition))
    assert rewrite(d[2], match, change), name
    bits, module = (Path('_build/mutations', name + suffix) for suffix in ['.bits', '.v'])
    bits.write_text(encode(pack([profile, tag(mutant)])))
    subprocess.run(['python3', 'scripts/package-provenance.py', kind, str(bits), str(module)], check=True)
    proof = Path('rocq/OrderCallPass.v').read_text()
    assert proof.count(old) == 1, name
    with module.open('a') as out:
        out.write('\n' + proof.replace(old, new).replace(removed, ''))

# Kernel occurrence counting that ignores the cdr: names occurring later are missed.
profile, original = load('kernel-list')
mutant = copy.deepcopy(original)
d = next(d for d in mutant if d[1][0] == S('kl:buri.kernel.occurrences'))
target = [S('kl:buri.kernel.occurrences'), S('V5971'), [S('cdr'), S('V5972')]]
assert rewrite(d[2], lambda n: n == target, lambda n: n.__setitem__(slice(None), [S('quote'), ('num', '0')]))
bits, module = (Path('_build/mutations', 'OccurrenceDropsTail' + suffix) for suffix in ['.bits', '.v'])
bits.write_text(encode(pack([profile, tag(mutant)])))
subprocess.run(['python3', 'scripts/package-provenance.py', 'kernel_list', str(bits), str(module)], check=True)
with module.open('a') as out:
    out.write('\n' + Path('rocq/OrderCallPass.v').read_text().replace(' KernelListInput', ''))

# Statement-level: the composed theorem cannot be restated for reordered arguments.
source = Path('rocq/OrderCallPreserve.v').read_text()
old = '   (ev p op rho (Call f es) st out <-> ev p op rho target st out).'
assert source.count(old) == 1
Path('_build/mutations/PreserveReversedArgs.v').write_text(
    source.replace(old, '   (ev p op rho (Call f (rev es)) st out <-> ev p op rho target st out).'))
