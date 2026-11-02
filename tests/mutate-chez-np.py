"""E2E-22 mutants: each changes one packaged datum and re-runs the Rocq check
that uses it; Rocq must refuse every one.  Prints the mutant names."""
from pathlib import Path
import re

out = Path('_build/mutations')
out.mkdir(parents=True, exist_ok=True)

capture = Path('rocq/ChezNpCaptureInput.v').read_text()
validate = Path('rocq/ChezNpValidate.v').read_text()
syntax = Path('rocq/ChezNpSyntax.v').read_text()
check = Path('rocq/ChezNpGrammarCheck.v').read_text()


def body(text):
    """Drop the module's own header comment and Require lines."""
    lines = text.split('\n')
    keep = [l for l in lines if not l.startswith('From ')]
    return '\n'.join(keep)


def with_capture(mutated_capture, theorem_tail):
    head = 'From Coq Require Import String List Bool ZArith.\n' \
           'From Buri Require Import ChezNpReader ChezNpCore ChezNpReloc.\n' \
           'Import ListNotations.\n'
    return head + body(mutated_capture) + '\n' + body(validate).split('(* ---- np-recognize-mrvs')[0] + theorem_tail


names = []

# 1. One instruction word of the captured tarm64le code object changed.
old = '0014 AB010017'
assert capture.count(old) == 1
tail = validate[validate.index('Definition code_record_of'):validate.index('(* The 152 captured bytes')]
Path(out / 'ChezNpWrongByte.v').write_text(with_capture(capture.replace(old, '0014 AB010016'), tail))
names.append('ChezNpWrongByte')

# 2. The printed np-recognize-mrvs output calls a different primitive.
m = re.search(r' \("np-recognize-mrvs", "((?:[^"]|"")*)"\)', capture, re.S)
assert m
sec = m.group(0)
assert sec.count(' + 3165690') == 1
mut = capture.replace(sec, sec.replace(' + 3165690', ' - 3165690'))
tail = validate[validate.index('(* The input of np-recognize-mrvs'):validate.index('Theorem mrvs_buri_arm_add_preserves')]
Path(out / 'ChezNpWrongMrvs.v').write_text(with_capture(mut, tail))
names.append('ChezNpWrongMrvs')

# 3. One generated L16 production differs from Rocq's own resolution.
old = '(Lst [(Atom "asm-return")])'
assert old in syntax
i = syntax.index('Definition grammar_L16')
mut = syntax[:i] + syntax[i:].replace(old, '(Lst [(Atom "asm-returns")])', 1)
head = 'From Coq Require Import String List.\n' \
       'From Buri Require Import ChezNpReader ChezNpGrammar ChezNpLanguagesInput.\n'
Path(out / 'ChezNpWrongGrammar.v').write_text(head + body(mut) + '\n' + body(check))
names.append('ChezNpWrongGrammar')

print(' '.join(names))
