"""Write altered copies of the stored Shen-CL lowering capture.

Byte packaging only: each mutant must be rejected by the Rocq admission
computation in scripts/proof-mutations. This script decides nothing.
"""
from pathlib import Path

source = Path('rocq/CLLoweringCapture.v').read_text()
guard = '(SBrack (SCons (SSym "true?") (SCons (SSym "Exp") SNil)))'
test = '(SParen (SCons (SSym "compile-expression") (SCons (SSym "Test") (SCons (SSym "Scope") SNil))))'
optimised = '(SParen (SCons (SSym "optimise-boolean-check") (SCons ' + test + ' SNil)))'


def emit_if_swapped(text):
    lines = text.split('\n')
    index = [i for i, line in enumerate(lines) if line.startswith('Definition captured_emit_if ')]
    assert len(index) == 1
    line = lines[index[0]]
    assert '"Then"' in line and '"Else"' in line
    lines[index[0]] = line.replace('"Then"', '"@@"').replace('"Else"', '"Then"').replace('"@@"', '"Else"')
    return '\n'.join(lines)


mutants = {}
assert source.count(guard) == 1
mutants['CLLowDroppedGuard'] = source.replace(guard, '(SSym "Exp")')
assert source.count(optimised) == 1
mutants['CLLowTruthiness'] = source.replace(optimised, test)
mutants['CLLowSwappedBranches'] = emit_if_swapped(source)
for name, text in mutants.items():
    assert text != source, name
    Path('_build/mutations', name + '.v').write_text(text)
