"""Wave-D primitives-lane mutants (rocq/SchemeIntern.v, rocq/CLStrings.v).

Acceptance is decided only by Rocq: this script writes mutant modules into
_build/mutations and prints their names; tests/run-prims2-mutations.sh
requires each one to be refused.

- Byte mutants: a changed pinned definition (copied into the mutant together
  with the proof module) must fail admission by computed equality.
- Restatement mutants: a claim the captured bodies do not justify must be
  refused as a type mismatch against the real theorem.
"""
from pathlib import Path

out = Path('_build/mutations')
out.mkdir(parents=True, exist_ok=True)
names = []
sources = Path('rocq/Prims2Sources.v').read_text()
intern = Path('rocq/SchemeIntern.v').read_text()
strings = Path('rocq/CLStrings.v').read_text()
header = sources.split('Open Scope string_scope.\n', 1)[1]


def emit(name, text):
    (out / (name + '.v')).write_text(text)
    names.append(name)


def with_sources(proof, module, old, new):
    """The proof module with its Prims2Sources import replaced by a mutated copy."""
    assert sources.count(old) == 1, old
    mutated = sources.replace(old, new).split('Open Scope string_scope.\n', 1)[1]
    lines = proof.split('\n')
    req = [i for i, l in enumerate(lines) if l.startswith('From Buri Require Import') and 'Prims2Sources' in l]
    assert len(req) == 1
    lines[req[0]] = lines[req[0]].replace(' Prims2Sources', '')
    text = '\n'.join(lines)
    marker = 'Module %s.\n' % module
    assert text.count(marker) == 1
    return text.replace(marker, marker + 'Open Scope string_scope.\n' + mutated, 1)


# 1. The stock numeric branch put back into the patched kl:intern bytes.
emit('Prims2PatchedNumericBytes', with_sources(intern, 'SchemeIntern',
     '""false"") #f)\n        (else (string->symbol name))))',
     '""false"") #f)\n        (else (or (and (> (string-length name) 1) (char-numeric? (string-ref name 0)) (string->number name)) (string->symbol name)))))'))

# 2. The reviewed patched AST restated as the stock one.
old = 'Definition patched_body := bool_tests (Call "string->symbol" [nm]).'
assert intern.count(old) == 1
emit('Prims2PatchedAsStockAst', intern.replace(old, 'Definition patched_body := stock_body.'))

# 3. Stock kl:intern claimed to return the symbol 12 on the sampled host answer.
emit('Prims2StockTwelveSymbol', '''From Coq Require Import String List ZArith.
From Buri Require Import Native ObserverEffects SchemeIntern.
Import ListNotations Native.Native ObserverEffects.ObserverEffects SchemeIntern.SchemeIntern.
Open Scope string_scope.
Definition mutant : forall op, chez_intern_ops op ->
 SchemeWrappers.SchemeWrappers.yields op "string->number" [Text "12"] (Integer 12%Z) -> forall (ks : KLValue.KLValue.store) st n, n >= 8 ->
 eval_with n Pn op (rho "12") stock_body st = Out (Returned (Symbol "12")) st [] :=
 fun op C E ks st n Hn => proj1 (stock_intern_twelve op C E ks st n Hn).
''')

# 4. |pos| with (plusp n) for (minusp n): admission must fail.
emit('Prims2CLPosPlusp', with_sources(strings, 'CLStrings', '(minusp n) (>= n (length x))', '(plusp n) (>= n (length x))'))

# 5. |tlstr| without its non-empty guard: admission must fail.
emit('Prims2CLTlstrNoGuard', with_sources(strings, 'CLStrings',
     '(and (stringp x) (plusp (length x)))', '(stringp x)'))

# 6. |string->n| claimed to refine rule_string_to_n on every string.
emit('Prims2CLStringToNAll', '''From Coq Require Import String List.
From Buri Require Import CLLowering CLStrings.
From Buri Require CLWrappers CLContracts KLSemantics.
Import ListNotations CLStrings.CLStrings.
Definition mutant : forall h chr cchar, CLContracts.CLContracts.cl_host_ops h -> cl_string_ops h chr cchar ->
 forall k v ks n, n >= 7 -> rep_c k v ->
 refines ks (KLSemantics.KLSemantics.rule_string_to_n [k] ks) (CLWrappers.CLWrappers.ceval n h (env1 "S" v) string_to_n_body) :=
 fun h chr cchar HH SO k v ks n Hn R => string_to_n_refines h chr cchar HH SO k v ks n Hn R.
''')

# 7. |n->string| claimed to refine rule_n_to_string on every represented
#    argument, surrogates included.
emit('Prims2CLNToStringAll', '''From Coq Require Import String List.
From Buri Require Import CLLowering CLStrings.
From Buri Require CLWrappers CLContracts KLSemantics.
Import ListNotations CLStrings.CLStrings.
Definition mutant : forall h chr cchar, CLContracts.CLContracts.cl_host_ops h -> cl_string_ops h chr cchar ->
 forall k v ks n, n >= 8 -> rep_c k v ->
 refines ks (KLSemantics.KLSemantics.rule_n_to_string [k] ks) (CLWrappers.CLWrappers.ceval n h (env1 "N" v) n_to_string_body) :=
 fun h chr cchar HH SO k v ks n Hn R => n_to_string_refines h chr cchar HH SO k v ks n Hn R.
''')

print(' '.join(names))
