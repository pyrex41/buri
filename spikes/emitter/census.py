#!/usr/bin/env python3
"""Summarises /tmp/move-census.txt: operand classes and emitted lengths of every move."""
import collections,sys
c=collections.Counter(); ex={}; n=0
for l in open(sys.argv[1] if len(sys.argv)>1 else '/tmp/move-census.txt'):
    p=l.split()
    if len(p)<6: continue
    d,s,h,ca,k,ln=int(p[0]),int(p[1]),int(p[2]),int(p[3]),int(p[4]),int(p[5]); b=p[6] if len(p)>6 else ''
    n+=1
    const=bool(s&0x80000000)
    srcc='cached' if ca==s or (ca==-1 and s==0xffffffff) else ('const' if const else ('home' if 2<=s<h+2 else 'slot'))
    dstc='home' if 2<=d<h+2 else 'slot'
    off='small' if s*8<=0xf8 else ('mid' if s*8<=2047 else 'big')
    if const: off='-'
    doff='small' if d*8<=0xf8 else ('mid' if d*8<=2047 else 'big')
    key=(dstc,srcc,off,doff if dstc=='slot' else '-',k,ln)
    c[key]+=1; ex.setdefault(key,(d,s,h,ca,b))
print('total',n)
for k,v in c.most_common(): print(v,k,ex[k])
