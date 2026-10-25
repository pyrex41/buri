from pathlib import Path
import copy,runpy,subprocess
h=runpy.run_path('tests/mutate-constructor.py')
read,unpack,pack,encode,untag,tag=(h[k] for k in ['read','unpack','pack','encode','untag','tag'])
g=read.__globals__;g['bits']=Path('ports/observer.bits').read_text();g['index']=0
raw=read();profile,tagged=unpack(raw);original=untag(tagged)
proof=Path('rocq/CheckedFileIO.v').read_text().replace(' CheckedIOInput.','.')
for name in ['UncheckedSuccess','UncheckedRead']:
 v=copy.deepcopy(original);d=v[3]
 assert d[1][0]==('sym','kl:buri.checked-write')
 if name=='UncheckedSuccess':
  assert d[2][2][0]==('sym','if');d[2][2][1]=('bool','1')
 else:
  d[2]=h['replace'](d[2],('sym','kl:read-file-as-string'),('sym','evil'))
 bits,module=(Path('_build/mutations',name+suffix) for suffix in ['.bits','.v'])
 bits.write_text(encode(pack([profile,tag(v)])))
 subprocess.run(['python3','scripts/package-provenance.py','checked_io',str(bits),str(module)],check=True)
 with module.open('a') as out:out.write('\n'+proof)
