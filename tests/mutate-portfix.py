"""Port-fix lane mutants: an UNPATCHED capture (or a restated theorem) must
fail the patched theorems. Acceptance is decided only by Rocq; this script
writes the mutant modules into _build/mutations and prints their names.
"""
from pathlib import Path
import subprocess

out = Path('_build/mutations')
out.mkdir(parents=True, exist_ok=True)
names = []

def emit(name, text):
    (out / (name + '.v')).write_text(text)
    names.append(name)

# 1. The stock Shen-Scheme branch capture packaged as the "patched" profile:
#    the patched emitter theorems must fail on it.
subprocess.run(['python3', 'scripts/package-provenance.py', 'compiler_branches_patched',
                'ports/compiler-branches.bits', str(out / 'PortfixSchemeStockCapture.input.v')], check=True)
proof = Path('rocq/SchemePatched.v').read_text()
assert proof.count(' OrderCallPreserve CompilerBranchesPatchedInput') == 1
emit('PortfixSchemeStockCapture',
     (out / 'PortfixSchemeStockCapture.input.v').read_text() + '\n' + proof.replace(' OrderCallPreserve CompilerBranchesPatchedInput', ' OrderCallPreserve'))

# 2. Restating the patched literal path as eqv? (the stock lowering) fails.
old = '   (ev p op rho (Call "kl:=" [d1; d2]) st out <-> ev p op rho target st out).'
assert proof.count(old) == 1
emit('PortfixSchemeEqvStatement', proof.replace(old, old.replace('"kl:="', '"eqv?"')))

# 3. The stock EQ-rewrite guard in the reviewed patched optimise AST: the
#    qsafe-free soundness theorem must fail.
cl = Path('rocq/CLLoweringPatch.v').read_text()
old = 'Definition sym_guard := P [A "and"; P [A "="; cl_ "quote"; A "Quote"]; P [A "symbol?"; A "S"]].'
assert cl.count(old) == 1
emit('PortfixCLOptimiseStockGuard', cl.replace(old, 'Definition sym_guard := P [A "="; cl_ "quote"; A "Quote"].'))

# 4. The stock empty-clause rule in the reviewed patched emit-cond-clauses.
old = ''' B []; A "Scope"; A "->"; B [B [cl_ "t"; P [A "compile-expression"; B [A "simple-error"; SStr "condition failure"]; A "Scope"]]]]
 ++ cond_general).'''
assert cl.count(old) == 1
emit('PortfixCLCondStock', cl.replace(old, ''' B []; A "_"; A "->"; B []] ++ cond_general).'''))

# 5. The stock multiply bytes and body: the rejection theorem must fail.
mul = Path('rocq/CLMultiplyPatched.v').read_text()
src = Path('rocq/PatchedPrimitiveSources.v').read_text()
patched_clause = '        ((and (numberp x) (numberp y) (or (zerop x) (zerop y))) 0)\n'
assert src.count(patched_clause) == 1
stock_src = src.replace(patched_clause, '        ((or (zerop x) (zerop y)) 0)\n')
old = 'From Buri Require Import PortReader PatchedPrimitiveSources KLSyntax KLValue KLSemantics.'
assert mul.count(old) == 1
body_start = mul.index('Definition patched_multiply_body :=')
body_end = mul.index('Definition admission_of')
mutant = mul[:body_start] + 'Definition patched_multiply_body := W.multiply_body.\n' + mul[body_end:]
mutant = mutant.replace(old, 'From Buri Require Import PortReader KLSyntax KLValue KLSemantics.')
a = mutant.index('(* The patched body differs from the admitted stock body. *)')
b = mutant.index('(* Named SBCL classification contracts')
mutant = mutant[:a] + mutant[b:]
header = stock_src.split('Open Scope string_scope.\n', 1)[1]
mutant = mutant.replace('Module CLMultiplyPatched.\n', 'Module CLMultiplyPatched.\n' + header, 1)
emit('PortfixCLMultiplyStock', mutant)

print(' '.join(names))
