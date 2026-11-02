"""Write altered copies of the E2E-21 representation modules.

Byte packaging only: each mutant is a copy of rocq/ChezWord.v or
rocq/ChezRepr.v in which either the pinned layout capture or one theorem
statement is changed. scripts/proof-mutations requires Rocq to refuse every
one with the expected error class; this script decides nothing. It prints
lines NAME PATTERN (spaces in PATTERN written as _).
"""
from pathlib import Path

layout = Path('rocq/ChezLayout.v').read_text()
word = Path('rocq/ChezWord.v').read_text()
repr_ = Path('rocq/ChezRepr.v').read_text()


def inline_layout(old, new):
    """The generated layout as an inline module (path ChezLayout.ChezLayout)."""
    assert layout.count(old) == 1, old
    body = layout.replace(old, new).replace('From Coq Require Import ZArith.\n', '')
    return 'From Coq Require Import ZArith.\nModule ChezLayout.\n' + body + 'End ChezLayout.\n'


def swap(src, old, new):
    assert src.count(old) == 1, old
    return src.replace(old, new)


WORD_IMPORT = 'From Buri Require Import ChezLayout.\n'


def lemma(name):
    start = repr_.index('Lemma ' + name + ' :')
    return repr_[start:repr_.index('Qed.', start) + len('Qed.')] + '\n'


def repr_with(old, new, name):
    """One ground lemma of ChezRepr.v checked against a changed capture."""
    return ('From Coq Require Import ZArith.\nFrom Buri Require Import ChezWord.\n' +
            inline_layout(old, new) +
            'Open Scope Z_scope.\nImport ChezLayout.ChezLayout ChezWord.ChezWord.\n' + lemma(name))


mutants = {}
# A captured equates.h claiming a 2-bit fixnum shift: the ground fixnum layout
# check must fail.
mutants['ReprFixnumShift'] = (
    swap(word, WORD_IMPORT, inline_layout('Definition fixnum_offset : Z := 3.', 'Definition fixnum_offset : Z := 2.')),
    'Unable to unify')
# A types.h capture whose TYPE macro does not subtract typemod.
mutants['ReprTypeMacro'] = (
    repr_with('Definition c_TYPE_is_minus_typemod : Z := 1.', 'Definition c_TYPE_is_minus_typemod : Z := 0.',
              'chez_sources_agree'),
    'Unable to unify')
# A sample whose second string element is not a Chez string-char.
mutants['ReprSampleChar'] = (
    repr_with('Definition sample_string_char1 : Z := 244502.', 'Definition sample_string_char1 : Z := 244480.',
              'chez_sample_agrees'),
    'Unable to unify')
# The naive premise "two Shen fixnums never overflow when added" is false:
# the no-overflow premise needs x + y in the fixnum range.
start = word.index('Theorem fx_add_no_overflow_iff')
stop = word.index('Qed.', start) + len('Qed.')
naive = '''Theorem fx_add_no_overflow_iff : forall x y, fx_range x -> fx_range y ->
  - half <= swrap (fx_enc x) + swrap (fx_enc y) < half.
Proof.
  intros x y Hx Hy; rewrite (fx_enc_signed x Hx), (fx_enc_signed y Hy).
  destruct chez_word_layout as (_ & HH & _ & _ & HP & HN).
  unfold fx_range in *; rewrite HH; rewrite HP, HN in *; lia.
Qed.'''
mutants['ReprNoOverflowNaive'] = (word[:start] + naive + word[stop:], 'Cannot find witness')

for name, (text, pattern) in mutants.items():
    Path('_build/mutations', name + '.v').write_text(text)
    print(name, pattern.replace(' ', '_'))
