"""Write E2E-07 proof mutants: false ground claims about the actual captured
shen/klambda.shen evaluator (Native run of the decoded capture), each the
negation of a behavior the implementation change or the extended refinement
relies on. scripts/proof-mutations requires Rocq to refuse every one; this
script only writes text and decides nothing. It prints the mutant names.
"""
from pathlib import Path

header = '''From Coq Require Import List String ZArith.
From Buri Require Import Native KLambdaEvaluatorCapture KLambdaEvaluatorGlobal.
Import ListNotations.
Import KLambdaEvaluatorCapture.KLambdaEvaluatorCapture.
Module G := KLambdaEvaluatorGlobal.KLambdaEvaluatorGlobal.
Open Scope string_scope.
Definition run_with ds e z := Native.Native.run 400 program "kl:buri.eval"
 [G.enc_defs ds; enc_term e; enc_env []; Native.Native.Integer z].
'''
sum_defs = '[("sum", ["x"; "y"], TPrim "+" [TVar "x"; TVar "y"])]'
mutants = {
    # Two function values compared as equal data (equality is undefined).
    'E2E07FunctionEqualityDefined':
        ('[]', 'TPrim "=" [TLambda "x" (TVar "x"); TLambda "x" (TVar "x")]', 'WRet (RBool false)'),
    # The superseded behavior: a closure against data is unsupported.
    'E2E07ClosureDataUnsupported':
        ('[]', 'TPrim "=" [TLambda "x" (TVar "x"); TLit (RInt 1)]', 'WUnsupported'),
    # The superseded behavior: thawing a closure is not-frozen (KLambda: XArity).
    'E2E07ThawClosureNotFrozen':
        ('[]', 'TThaw (TLambda "x" (TVar "x"))', 'WRaise "not-frozen"'),
    # The superseded behavior: applying a thunk is not-callable (KLambda: XArity).
    'E2E07ApplyThunkNotCallable':
        ('[]', 'TApply (TFreeze (TLit (RInt 1))) (TLit (RInt 2))', 'WRaise "not-callable"'),
    # A defined global reported unbound.
    'E2E07DefinedGlobalUnbound':
        (sum_defs, 'TGlobal "sum"', 'WRaise "unbound-function"'),
    # An under-saturated user call evaluated early instead of curried.
    'E2E07PartialCallsEarly':
        (sum_defs, 'TApply (TGlobal "sum") (TLit (RInt 3))', 'WRet (RInt 3)'),
}
for name, (ds, e, w) in mutants.items():
    Path('_build/mutations', name + '.v').write_text(
        header + 'Theorem mutant_claim : run_with ' + ds + ' (' + e + ') 20 = '
        'Native.Native.Returned (enc_verdict (' + w + ')).\nProof. vm_compute. reflexivity. Qed.\n')
    print(name)
