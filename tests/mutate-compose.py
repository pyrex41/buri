"""Adversarial compiler-branch captures (E2E-15); acceptance is decided only by Rocq.

Each capture mutant changes the captured implementation of one emitter; the
literal capture check would accept the mutated bytes, so only the semantic
proofs in SchemeBranches.v can reject it. Two statement mutants restate the
composition and strictness theorems wrongly.
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
CE = S('kl:_scm.compile-expression')

def emit_if_true_compiles_else(params):
    t, a, b, s = params
    return (lambda n: n == [CE, a, s]), (lambda n: n.__setitem__(1, b))
def emit_let_body_unscoped(params):
    x, v, b, s = params
    return (lambda n: n == [CE, b, [S('cons'), x, s]]), (lambda n: n.__setitem__(2, s))
def cond_clause_unforced(params):
    cs, s = params
    test = [S('car'), [S('car'), cs]]
    return (lambda n: n == [CE, [S('kl:_scm.force-boolean'), test], s]), (lambda n: n.__setitem__(1, test))
def numeric_equality_as_equal(params):
    return (lambda n: n == [S('quote'), S('eqv?')]), (lambda n: n.__setitem__(1, S('equal?')))

mutants = [
    # A literal true test compiles the ELSE branch.
    ('EmitIfTrueCompilesElse', 'kl:_scm.emit-if', emit_if_true_compiles_else),
    # The let body is compiled without the bound variable in scope.
    ('EmitLetBodyUnscoped', 'kl:_scm.emit-let', emit_let_body_unscoped),
    # A cond clause test is compiled without force-boolean (Scheme truthiness).
    ('CondClauseUnforced', 'kl:_scm.emit-cond-clauses', cond_clause_unforced),
    # The numeric branch lowers = to equal? instead of eqv?.
    ('EqualityNumericEqual', 'kl:_scm.emit-equality-check', numeric_equality_as_equal),
]
proof = Path('rocq/SchemeBranches.v').read_text()
assert proof.count(' CompilerBranchesInput') == 1
for name, definition, make in mutants:
    profile, original = load('compiler-branches')
    mutant = copy.deepcopy(original)
    d = next(d for d in mutant if d[1][0] == S(definition))
    match, change = make(d[1][1:])
    assert rewrite(d[2], match, change), name
    assert mutant != original, name
    bits, module = (Path('_build/mutations', name + suffix) for suffix in ['.bits', '.v'])
    bits.write_text(encode(pack([profile, tag(mutant)])))
    subprocess.run(['python3', 'scripts/package-provenance.py', 'compiler_branches', str(bits), str(module)], check=True)
    with module.open('a') as out:
        out.write('\n' + proof.replace(' CompilerBranchesInput', ''))

# Statement-level mutants of the composition and strictness theorems.
compose = Path('rocq/SchemeCompose.v').read_text()
for name, old, new in [
    # Dropping the binding: the merged form is NOT the bare call.
    ('ComposeDroppedBinding',
     '   (ev p op rho (Let x a (Call f es)) st out <-> ev p op rho target st out).\nProof.\n intros cexp ordc ext ys1 ys2 gen N f args es x cv a st0',
     '   (ev p op rho (Call f es) st out <-> ev p op rho target st out).\nProof.\n intros cexp ordc ext ys1 ys2 gen N f args es x cv a st0'),
    # A true condition does not select the else-branch.
    ('StrictIfSwapped', '     ev p op rho (if bv then a else b) s1 o2 /\\ out = after e1 o2) \\/',
     '     ev p op rho (if bv then b else a) s1 o2 /\\ out = after e1 o2) \\/'),
]:
    assert compose.count(old) == 1, name
    Path('_build/mutations', name + '.v').write_text(compose.replace(old, new))
