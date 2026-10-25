"""Tampering fixtures; all semantic acceptance remains in Rocq."""
from pathlib import Path
import copy
import runpy
import subprocess
h = runpy.run_path('tests/mutate-constructor.py')
read, unpack, pack, encode, untag, tag, replace = (h[k] for k in
 ['read', 'unpack', 'pack', 'encode', 'untag', 'tag', 'replace'])
for kind, capture, variants, proof_file, removed_import in [
 ('bootstrap', 'bootstrap', [
  ('BootstrapBooleanTag', 'kl:buri.native-node', ('sym', 'bool'), ('sym', 'sym')),
  ('BootstrapWrongChild', 'kl:buri.native-node', ('sym', 'cdr'), ('sym', 'car'))],
  'BootstrapCorrect.v', ' BootstrapInput.'),
 ('compiler_pass', 'compiler-pass', [
  ('CompilerPassWrongKeyword', 'kl:_scm.merge-nested-lets', ('sym', 'let*'), ('sym', 'wrong'))],
  'CompilerPassCorrect.v', ' CompilerPassInput.'),
 ('observer', 'observer', [
  ('ObserverWrongActivation', 'kl:buri.install-observed', ('sym', 'eval'), ('sym', 'evil')),
  ('ObserverWrongPublication', 'kl:buri.install-observed', ('sym', 'kl:set'), ('sym', 'evil'))],
  None, None),
]:
 g=read.__globals__
 g['bits'],g['index']=Path('ports',capture+'.bits').read_text(),0
 raw=read(); assert encode(raw)==g['bits'] and g['index']==len(g['bits'])
 profile,tagged=unpack(raw); original=untag(tagged)
 for name,definition,old,new in variants:
  mutant=copy.deepcopy(original)
  d=next(d for d in mutant if d[1][0]==('sym',definition))
  before=copy.deepcopy(d[2]); d[2]=replace(d[2],old,new); assert d[2]!=before
  bits,module=(Path('_build/mutations',name+suffix) for suffix in ['.bits','.v'])
  bits.write_text(encode(pack([profile,tag(mutant)])))
  subprocess.run(['python3','scripts/package-provenance.py',kind,str(bits),str(module)],check=True)
  if proof_file:
   proof=Path('rocq',proof_file).read_text().replace(removed_import,'.')
  else:
   proof='''
From Coq Require Import ZArith.
From Buri Require Import ObserverEffects.
Import ObserverEffects.ObserverEffects.
Example actual_installer_must_activate_and_publish :
 (match lookup observer_program "kl:buri.install-observed" with
 | Some d => eval 30 (lookup observer_program) (fun _ => Returned (Symbol "target"))
   (fun _ => Returned Nil) (arguments (params d) [form (Symbol "f") [] Nil]) (body d) Nil
 | None => Out Unsupported Nil [] end) =
 Out (Returned (Symbol "f")) (Pair (L [form (Symbol "f") [] Nil;Symbol "target"]) Nil)
 [Arity (Symbol "f") (Integer 0);Compile (form (Symbol "f") [] Nil) (Returned (Symbol "target"));
 Activate (Symbol "target") (Returned Nil);ReadRecords;
 WriteRecords (Pair (L [form (Symbol "f") [] Nil;Symbol "target"]) Nil)].
Proof. vm_compute; reflexivity. Qed.
'''
  with module.open('a') as out: out.write('\n'+proof)
