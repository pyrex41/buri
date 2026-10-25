"""Adversarial captured implementations and bridge statements; Rocq decides."""
from pathlib import Path
import copy
import runpy
import subprocess
h = runpy.run_path('tests/mutate-constructor.py')
read, unpack, pack, encode, untag, tag, replace = (h[k] for k in
 ['read','unpack','pack','encode','untag','tag','replace'])
g=read.__globals__; g['bits'],g['index']=Path('ports/equality-core.bits').read_text(),0
raw=read(); assert encode(raw)==g['bits'] and g['index']==len(g['bits'])
profile,tagged=unpack(raw); original=untag(tagged)
def bypass(node):
 if isinstance(node,list):
  if node and node[0]==('sym','if'):
   node[1]=('bool','1'); return True
  for child in node:
   if bypass(child): return True
 return False
for name in ['EqUncheckedTrans','EqWrongCongruence','EqMissingSym','EqExtraDefinition']:
 mutant=copy.deepcopy(original)
 if name=='EqUncheckedTrans':
  definition=next(d for d in mutant if d[1][0]==('sym','kl:buri.eq2-trans'))
  assert bypass(definition[2])
 elif name=='EqWrongCongruence':
  definition=next(d for d in mutant if d[1][0]==('sym','kl:buri.eq2-cong'))
  definition[2]=replace(definition[2],('sym','app'),('sym','wrong-app'))
 elif name=='EqMissingSym':
  mutant=[d for d in mutant if d[1][0]!=('sym','kl:buri.eq2-sym')]
 else:
  mutant.append(copy.deepcopy(mutant[0]))
 bits,module=(Path('_build/mutations',name+suffix) for suffix in ['.bits','.v'])
 bits.write_text(encode(pack([profile,tag(mutant)])))
 subprocess.run(['python3','scripts/package-provenance.py','equality_core',str(bits),str(module)],check=True)
 with module.open('a') as out:out.write('\n'+Path('rocq/EqualityCoreCorrect.v').read_text().replace(' EqualityCoreInput',''))
variants=[
 ('ReverseDroppedArgument','NativeReverse.v','rev (v::acc)++vs','rev acc++vs'),
 ('LoaderFakeActivationSuccess','ObserverTotal.v',
  '| failure=>Out failure previous (prefix++[Activate target failure]) end',
  '| failure=>Out (Returned (Symbol name)) previous (prefix++[Activate target failure]) end'),
 ('SignedZeroHidden','StockDivisionGeneral.v','else round v | r=>r end','else round v | r=>Returned Nil end'),
 ('CallWrongCallee','CallRefinement.v',
  '(eval_with (S (S (S n))) p op rho (Let name a (Call f (Var name::args)))).',
  '(eval_with (S (S (S n))) p op rho (Let name a (Call "wrong" (Var name::args)))).'),
 ('FreshBogusCount','FreshSupply.v',
  '| Symbol name=>Returned (Boolean (Z.eqb 0 (Z.of_nat (O.occurrences name used))))',
  '| Symbol name=>Returned (Boolean true)'),
]
for name,file,old,new in variants:
 source=Path('rocq',file).read_text(); assert old in source,(name,old)
 mutated=source.replace(old,new,1)
 if name=='FreshBogusCount':
  mutated=mutated.replace('Definition count_result candidate used :=',
                          'Definition count_result candidate (used:value) :=')
 if name=='ReverseDroppedArgument':
  mutated=mutated.replace('Lemma finish_exhausted', '''Module ReverseMutationCheck.
From Coq Require Import ZArith.
Open Scope string_scope.
Example argument_value_is_retained :
 finish 1 (fun _=>None) [Arguments (fun _=>None) "cons" [Lit (Integer 2)] []]
 (Returned (Integer 1))=Returned (Pair (Integer 1) (Integer 2)).
Proof. vm_compute;reflexivity. Qed.
End ReverseMutationCheck.
Lemma finish_exhausted''')
 if name=='SignedZeroHidden':
  mutated=mutated.replace('Lemma divide_stage', '''Example division_error_is_not_success :
 expected (fun _ _=>Raised (Symbol "division") (Text "failed")) (fun _=>false)
 (fun _=>Unsupported) Nil Nil=Raised (Symbol "division") (Text "failed").
Proof. vm_compute;reflexivity. Qed.
Lemma divide_stage''')
 Path('_build/mutations',name+'.v').write_text(mutated)
source=Path('rocq/EqualityAdmission.v').read_text()
assert source.count('if Z.leb 0 z then')==1
source=source.replace('if Z.leb 0 z then','if true then')
source=source.replace('Lemma elements_canonical', '''Example negative_index_must_not_be_admitted :
 read_term 3 (L [Symbol "var";Integer (-1)])=None.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_canonical''')
Path('_build/mutations/AdmissionNegativeAccepted.v').write_text(source)

g=read.__globals__; g['bits'],g['index']=Path('ports/equality-seal.bits').read_text(),0
raw=read(); assert encode(raw)==g['bits'] and g['index']==len(g['bits'])
profile,tagged=unpack(raw); original=untag(tagged)
for name,definition,old,new in [
 ('SealWrongHelper','kl:buri.eq2-seal-program','equal?','eq?'),
 ('SealAuthorityEscape','kl:buri.eq2-seal-request','pair?','eval'),
 ('SealWrongEntry','kl:buri.eq2-seal-program','kl:buri.eq2-derive','kl:buri.eq2-trans'),
 ('SealExecutorBypass','kl:buri.make-sealed-eq2','eval','evil'),
]:
 mutant=copy.deepcopy(original)
 d=next(d for d in mutant if d[1][0]==('sym',definition))
 before=copy.deepcopy(d[2]);d[2]=replace(d[2],('sym',old),('sym',new));assert d[2]!=before
 bits,module=(Path('_build/mutations',name+suffix) for suffix in ['.bits','.v'])
 bits.write_text(encode(pack([profile,tag(mutant)])))
 subprocess.run(['python3','scripts/package-provenance.py','equality_seal',str(bits),str(module)],check=True)
 with module.open('a') as out:out.write('\n'+Path('rocq/EqualitySealCorrect.v').read_text().replace(' EqualitySealInput',''))
