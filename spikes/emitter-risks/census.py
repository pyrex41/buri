#!/usr/bin/env python3
"""Census of stage 0 bytecode: how much of it each opcode domain covers. Usage: census.py STAGE0_DIR"""
import glob, re, sys, collections
def toks(s):
    i=0;n=len(s)
    while i<n:
        c=s[i]
        if c.isspace(): i+=1
        elif c in '()': yield c; i+=1
        elif c=='"':
            j=i+1
            while s[j]!='"':
                j+= 2 if s[j]=='\\' else 1
            yield s[i:j+1]; i=j+1
        else:
            j=i
            while j<n and not s[j].isspace() and s[j] not in '()': j+=1
            yield s[i:j]; i=j
def parse(t):
    st=[[]]
    for x in t:
        if x=='(': st.append([])
        elif x==')':
            a=st.pop(); st[-1].append(a)
        else: st[-1].append(x)
    return st[0]
funcs=[]
for f in sorted(glob.glob(sys.argv[1]+'/*.sbc')):
    for form in parse(toks(open(f,errors='replace').read())):
        if isinstance(form,list) and form and form[0]=='defun':
            funcs.append((form[1],form[2],f))
def body(code): return code[5]
LEAF={'cons?','hd','tl','cons'}
ops=collections.Counter(); prims=collections.Counter()
for n,c,f in funcs:
    for i in body(c):
        ops[i[0]]+=1
        if i[0]=='prim': prims[i[2]]+=1
print(len(funcs),'functions',sum(ops.values()),'instructions')
print(ops.most_common()); print(prims.most_common(30))
DOM={'move','const','label','jump','jump-if-false','return'}
def indom(c,pr):
    return all(i[0] in DOM or (i[0]=='prim' and i[2] in pr) for i in body(c))
for name,pr in [('list prims',{'cons?','hd','tl','cons'}),('plus =',{'cons?','hd','tl','cons','='})]:
    d=[x for x in funcs if indom(x[1],pr)]
    print(name,len(d),'functions',sum(len(body(x[1])) for x in d),'instructions')
cand=[x for x in funcs if indom(x[1],{'cons?','hd','tl','cons'}) and any(i[0]=='jump-if-false' for i in body(x[1])) and any(i[0]=='prim' and i[2]=='cons' for i in body(x[1]))]
for n,c,f in sorted(cand,key=lambda x:len(body(x[1])))[:6]:
    print(n,c[2],c[3],c[4],body(c))
print('smallest with branch:')
cand=[x for x in funcs if indom(x[1],{'cons?','hd','tl','cons','='}) and any(i[0]=='jump-if-false' for i in body(x[1]))]
for n,c,f in sorted(cand,key=lambda x:len(body(x[1])))[:8]:
    print(n,c[2],c[3],c[4],body(c))
