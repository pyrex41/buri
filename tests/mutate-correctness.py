"""Adversarial implementation artifacts; theorem acceptance stays in Rocq."""
from pathlib import Path
import copy
import runpy
import subprocess
h = runpy.run_path('tests/mutate-constructor.py')
read, unpack, pack, encode, untag, tag, replace = (h[k] for k in
 ['read', 'unpack', 'pack', 'encode', 'untag', 'tag', 'replace'])
for kind,capture,name,definition,old,new,proof in [
 ('io_read','io-read','ReadWrongPath','kl:read-file-as-string','string-append','evil','IOReadCorrect.v'),
 ('order_call','order-call','FreshGuardBypass','kl:_scm.fresh-call-variable','eqv?','evil','OrderCallCorrect.v'),
 ('order_call','order-call','OrderWrongDirection','kl:_scm.order-call-inputs','kl:reverse','evil','OrderCallCorrect.v'),
 ('observer_forms','observer','PipelineWrongFrontend','kl:buri.observe-forms','kl:shen.shen->kl-h','evil','ObserverPipeline.v'),
]:
 g=read.__globals__; g['bits'],g['index']=Path('ports',capture+'.bits').read_text(),0
 raw=read(); assert encode(raw)==g['bits'] and g['index']==len(g['bits'])
 profile,tagged=unpack(raw); original=untag(tagged); mutant=copy.deepcopy(original)
 d=next(d for d in mutant if d[1][0]==('sym',definition))
 before=copy.deepcopy(d[2]); d[2]=replace(d[2],('sym',old),('sym',new)); assert d[2]!=before
 bits,module=(Path('_build/mutations',name+suffix) for suffix in ['.bits','.v'])
 bits.write_text(encode(pack([profile,tag(mutant)])))
 subprocess.run(['python3','scripts/package-provenance.py',kind,str(bits),str(module)],check=True)
 removed = {'order_call':' OrderCallInput','observer_forms':' ObserverFormsInput','io_read':' IOReadInput'}[kind]
 with module.open('a') as out: out.write('\n'+Path('rocq',proof).read_text().replace(removed,''))
source=Path('rocq/StockDivisionInput.v').read_text()
assert source.count('(inexact result)')==1
proof=Path('rocq/StockDivision.v').read_text().replace(' StockDivisionInput','')
Path('_build/mutations/StockWrongBranch.v').write_text(source.replace('(inexact result)','result')+'\n'+proof)
