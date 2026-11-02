"""Write altered copies of the packaged E2E-17 primitive wrapper sources.

Byte packaging only: each mutant restates the admission theorem of
rocq/SchemeWrappers.v or rocq/CLWrappers.v for a changed copy of the exact
pinned definition bytes. scripts/proof-mutations requires Rocq to refuse every
one; this script decides nothing. It prints the mutant names.
"""
from pathlib import Path
import re

packaged = Path('rocq/PrimitiveSources.v').read_text()


def literal(name):
    found = re.findall(r'Definition ' + name + r' : string := "(.*?)"\.\n', packaged, re.S)
    assert len(found) == 1, name
    return found[0]


scheme, cl = literal('scheme_source'), literal('cl_source')
mutations = {
    # kl:= compares numbers with eqv? (the compiled literal path) instead of =.
    'PrimEqvForNumbers': ('scheme', '(and (number? b) (= a b))', '(and (number? b) (eqv? a b))'),
    # assert-boolean checks the wrong predicate.
    'PrimAssertWrongPredicate': ('scheme', '(if (boolean? value)', '(if (symbol? value)'),
    # kl:= stops comparing list tails.
    'PrimEqDroppedTail': ('scheme', '(kl:= (cdr a) (cdr b))', '#t'),
    # shen-cl.equal? answers the opposite Shen Boolean.
    'PrimCLEqualSwapped': ('cl', "(if (|shen-cl.absequal| x y) '|true| '|false|)", "(if (|shen-cl.absequal| x y) '|false| '|true|)"),
    # absequal compares general numbers by identity.
    'PrimCLAbsequalEqNumbers': ('cl', '((numberp x) (and (numberp y) (= x y)))', '((numberp x) (and (numberp y) (eq x y)))'),
    # divide lets a CL ratio escape to Shen.
    'PrimCLDivideRatioEscape': ('cl', "(* (coerce 1.0 'double-float) div)", 'div'),
    # numeric-equal compares non-integer numbers by identity.
    'PrimCLNumericEqualEq': ('cl', '(and (numberp x) (numberp y) (= x y))', '(and (numberp x) (numberp y) (eq x y))'),
    # increment steps a non-fixnum (bignum) argument downwards.
    'PrimCLIncrementBignum': ('cl', '(1+ x)))', '(1- x)))'),
    # multiply returns 1 for a zero factor.
    'PrimCLMultiplyZero': ('cl', '((or (zerop x) (zerop y)) 0)', '((or (zerop x) (zerop y)) 1)'),
}
header = 'From Coq Require Import String List.\nFrom Buri Require Import SchemeWrappers CLWrappers.\nImport ListNotations.\nOpen Scope string_scope.\n'
for name, (port, old, new) in mutations.items():
    text = scheme if port == 'scheme' else cl
    old_lit, new_lit = old.replace('"', '""'), new.replace('"', '""')
    assert text.count(old_lit) == 1, name
    mutated = text.replace(old_lit, new_lit)
    if port == 'scheme':
        claim = 'SchemeWrappers.SchemeWrappers.admission_of mutated = (Some SchemeWrappers.SchemeWrappers.program, true)'
    else:
        claim = 'CLWrappers.CLWrappers.admission_of mutated = Some CLWrappers.CLWrappers.expected_program'
    Path('_build/mutations', name + '.v').write_text(
        header + 'Definition mutated : string := "' + mutated + '".\n'
        'Theorem mutant_admitted : ' + claim + '.\nProof. vm_compute. reflexivity. Qed.\n')
    print(name)
