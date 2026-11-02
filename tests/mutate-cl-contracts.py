"""Write restated (false) claims about the captured Shen-CL contracts (E2E-16/17).

Byte packaging only: each mutant restates one CLContracts consequence in a
form the captured bodies do not justify and tries to prove it from the real
theorem. scripts/proof-mutations requires Rocq to refuse every one; this
script decides nothing. It prints the mutant names.
"""
from pathlib import Path

header = ('From Coq Require Import String List.\n'
          'From Buri Require Import CLLowering CLContracts.\n'
          'Import ListNotations.\nOpen Scope string_scope.\n')
world = 'CLContracts.CLContracts.captured_prim St h kern other'
given = ('forall St h kern other, CLContracts.CLContracts.cl_host_ops h -> '
         'CLContracts.CLContracts.cl_kernel_ops St kern -> ')
record = '(CLContracts.CLContracts.captured_contracts St h kern other H K)'
mutants = {
    # The former all-arity field: a wrong-arity cons? call is never emitted.
    'ClcAllArityRecord': (given + 'pred_refines St (' + world + ') "cons?" "CONSP"',
                          'exact (pc_cons St _ ' + record + ')'),
    # numeric-equal without the operand swap the optimizer performs.
    'ClcNumericUnswapped': (given + 'forall n v, args_refine St (' + world + ') EQUALP [VNum n; v] '
                            '"shen-cl.numeric-equal" [VNum n; v]',
                            'intros n v; exact (proj2 (pc_numeric St _ ' + record + ' n v))'),
    # EQ (identity) in place of EQUAL against a string literal.
    'ClcEqForStringLiteral': (given + 'forall x v, args_refine St (' + world + ') EQUALP [v; VStr x] '
                              '"EQ" [v; VStr x]',
                              'intros x v; exact (proj2 (pc_string_equal St _ ' + record + ' x v))'),
}
for name, (claim, proof) in mutants.items():
    Path('_build/mutations', name + '.v').write_text(
        header + 'Theorem mutant : ' + claim + '.\nProof. intros St h kern other H K. ' + proof + '. Qed.\n')
    print(name)
