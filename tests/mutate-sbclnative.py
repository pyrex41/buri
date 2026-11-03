"""Write altered copies of the SBCL-native (E2E-21, CL side) modules.

Byte packaging only: each mutant is a truncated copy of rocq/SbclTests.v,
rocq/SbclValues.v or rocq/SbclHostOps.v in which either the captured code or
one theorem statement is changed. scripts/proof-mutations requires Rocq to
refuse every one; this script decides nothing. It prints lines NAME PATTERN
(spaces in PATTERN written as _).
"""
from pathlib import Path

out = Path('_build/mutations')
out.mkdir(parents=True, exist_ok=True)
gen = Path('rocq/SbclTypeTests.v').read_text()
tests = Path('rocq/SbclTests.v').read_text()
values = Path('rocq/SbclValues.v').read_text()
hostops = Path('rocq/SbclHostOps.v').read_text()


def swap(src, old, new):
    assert src.count(old) == 1, old
    return src.replace(old, new)


def upto(src, marker):
    """The module text before marker, closed."""
    i = src.index(marker)
    name = src[src.index('\nModule ') + 8:].split('.', 1)[0]
    return src[:i] + 'End ' + name + '.\n'


def through(src, start, section=''):
    """The module text through the Qed of the item starting at start, closed."""
    i = src.index(start)
    j = src.index('Qed.', i) + len('Qed.')
    name = src[src.index('\nModule ') + 8:].split('.', 1)[0]
    close = ('\nEnd ' + section + '.') if section else ''
    return src[:j] + close + '\nEnd ' + name + '.\n'


mutants = {}

# A capture whose consp CCMP tests NE instead of EQ: the consp window
# theorem must fail.
CCMP_EQ, CCMP_NE = '4200202596', '4200206692'
assert int(CCMP_EQ) == 0xFA5A0164 and int(CCMP_NE) == 0xFA5A1164
code_line = [l for l in gen.split('\n') if l.startswith('Definition code_consp :')][0]
mut_gen = swap(gen, code_line, code_line.replace(CCMP_EQ, CCMP_NE))
body = mut_gen[mut_gen.index('Module SbclTypeTests.'):]
inline = ('From Coq Require Import ZArith List.\nFrom Buri Require Import SbclLayout.\nImport ListNotations.\n'
          'Open Scope Z_scope.\nModule SbclTypeTests.\n' + body + 'End SbclTypeTests.\n')
t = swap(tests, 'From Buri Require Import SbclLayout SbclA64 SbclTypeTests.\n',
         'From Buri Require Import SbclLayout SbclA64.\n' + inline)
start = t.index('Theorem eq_window')
consp = t[t.index('Theorem consp_window'):]
consp = consp[:consp.index('Qed.') + len('Qed.')]
mutants['SbclCcmpCondition'] = (t[:start] + consp + '\nEnd SbclTests.\n', 'Error')

# The captured string test claimed to accept the symbol widetag range.
t = upto(tests, '(* ---------------------------------------------------------------- symbolic execution *)')
mutants['SbclStringRange'] = (swap(t, 'agrees (fun h => (225 <=? h) && (h <=? 237)) tv_stringp_codes',
                                   'agrees (fun h => (45 <=? h) && (h <=? 237)) tv_stringp_codes'),
                              'Error')

# NIL claimed not to be a CL symbol.
v = through(values, 'Theorem nil_dual', 'Rel')
mutants['SbclNilNotSymbol'] = (swap(v, 't_consp nilv = false /\\ t_symbolp m nilv = true /\\',
                                    't_consp nilv = false /\\ t_symbolp m nilv = false /\\'), 'Error')

# Shen false claimed to be CL false (NULL true on it).
v = through(values, 'Theorem kl_false_is_cl_true', 'Rel')
mutants['SbclFalseIsNil'] = (swap(v, 'kv (VBool false) w -> t_null w = false /\\ w <> nilv.',
                                  'kv (VBool false) w -> t_null w = true /\\ w <> nilv.'), 'Error')

# EQ claimed complete on every pair of equal values (false for strings,
# conses and numbers: distinct objects can represent one value).
h = through(hostops, 'Theorem eq_machine')
mutants['SbclEqComplete'] = (swap(h, '((symbolic a || symbolic b)%bool = true -> a = b -> r = true).',
                                  '(a = b -> r = true).'), 'Error')

for name, (text, pattern) in mutants.items():
    (out / (name + '.v')).write_text(text)
    print(name, pattern)
