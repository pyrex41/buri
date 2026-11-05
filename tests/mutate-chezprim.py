"""E2E-22 chezprim mutants: each changes one packaged raw pass output and
re-runs the Rocq check that uses it; Rocq must refuse every one.  Prints the
mutant names."""
from pathlib import Path
import re

out = Path('_build/mutations')
out.mkdir(parents=True, exist_ok=True)

capture = Path('rocq/ChezPrimRawInput.v').read_text()
LIT = r'"((?:[^"]|"")*)"'
item = re.compile(r' \(' + LIT + r', ' + LIT + r', (?:None|\(Some ' + LIT + r'\))\)(?:;\n|\]\.\n)', re.S)
raw = {}
for m in item.finditer(capture):
    raw.setdefault(m.group(1), m.group(3))  # Rocq-escaped raw text, first section of each name

HEAD = ('From Coq Require Import String List Bool ZArith.\n'
        'From Buri Require Import ChezNpReader ChezNpCore ChezPrimRaw ChezPrimExpand ChezPrimBlocks '
        'ChezPrimValidate.\n'
        'Import ListNotations.\nOpen Scope string_scope.\n')

names = []


def mutant(name, section, old, new, nth, claim):
    text = raw[section]
    assert text.count(old) >= nth, (name, old)
    i = -1
    for _ in range(nth):
        i = text.index(old, i + 1)
    mutated = text[:i] + new + text[i + len(old):]
    Path(out / (name + '.v')).write_text(
        HEAD + 'Definition mut_text : string := "' + mutated + '".\n'
        'Definition mut_datum : sexp := raw_or_nil (read_exactly mut_text).\n'
        'Theorem mutant : ' + claim + '.\nProof. vm_compute. reflexivity. Qed.\n')
    names.append(name)


# 1. np-suppress-procedure-checks output: the `+` call now shifts a
#    continuation attachment (an info field the stock printer hid).
mutant('ChezPrimRawAttach', 'np-suppress-procedure-checks', 'shift-attachment?= #f', 'shift-attachment?= #t', 2,
       'check_raw false false suppress_input mut_datum = true')
# 2. $np-expand-primitives output: the fixnum tag mask 7 becomes 3.
mutant('ChezPrimExpandMask', '$np-expand-primitives', '(immediate 7)', '(immediate 3)', 1,
       'check_expand_plus expand_in (body_w (clause_parts fname (Some mut_datum))) = true')
# 3. the overflow path calls library entry `-` instead of `+`.
mutant('ChezPrimExpandLib', '$np-expand-primitives', '#(libspec + 34838)', '#(libspec - 34838)', 1,
       'check_expand_plus expand_in (body_w (clause_parts fname (Some mut_datum))) = true')
# 4. the branch reads the carry flag instead of the overflow flag.
mutant('ChezPrimExpandFlag', '$np-expand-primitives', 'type= overflow', 'type= carry', 1,
       'check_expand_plus expand_in (body_w (clause_parts fname (Some mut_datum))) = true')
# 5. np-optimize-block-order! output: a block record field changed.
mutant('ChezPrimBlockField', 'np-optimize-block-order!', 'entry.26', 'entry.27', 1,
       'check_block_order block_in mut_datum = true')

print(' '.join(names))
