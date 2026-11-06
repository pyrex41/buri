#!/usr/bin/env python3
"""Static call closure and instruction counts, from nm and objdump of the check build.
Over-approximates what an emit path can reach: a whole function counts even if only one of its
cases is used. Indirect calls are reported, not followed. Usage: closure.py RUNTIME ROOT[,ROOT]..."""
import bisect,re,subprocess,sys
R=sys.argv[1]
syms=[]
for l in subprocess.run(['riscv64-linux-gnu-nm','-S',R],capture_output=True,text=True).stdout.splitlines():
    p=l.split()
    if len(p)==4 and p[2] in 'tTwW' and int(p[1],16)>0: syms.append((int(p[0],16),int(p[1],16),p[3]))
syms.sort(); addrs=[s[0] for s in syms]
def fn(a):
    i=bisect.bisect_right(addrs,a)-1
    return syms[i][2] if i>=0 and a<syms[i][0]+syms[i][1] else None
n={};calls={};ind={}
for l in subprocess.run(['riscv64-linux-gnu-objdump','-d',R],capture_output=True,text=True).stdout.splitlines():
    m=re.match(r'^\s+([0-9a-f]+):\s+[0-9a-f]+\s+(\S+)\s*(.*)',l)
    if not m: continue
    a=int(m[1],16); f=fn(a)
    if not f: continue
    n[f]=n.get(f,0)+1; calls.setdefault(f,set())
    t=re.search(r'([0-9a-f]+) <',m[3]) if m[2] in('jal','j','jalr','jr','beq','bne','blt','bge','bltu','bgeu','beqz','bnez','blez','bgez','bltz','bgtz') else None
    if t:
        g=fn(int(t[1],16))
        if g and g!=f: calls[f].add(g)
    if m[2] in('jalr','jr') and not re.search(r'ra\)|^ra$',m[3]) and 'ra' not in m[3].split(',')[0:1]: ind[f]=ind.get(f,0)+1
def closure(roots):
    seen=set(); st=list(roots)
    while st:
        x=st.pop()
        if x in seen or x not in n: continue
        seen.add(x); st+=calls[x]
    return seen
print('total text instructions',sum(n.values()))
for spec in sys.argv[2:]:
    c=closure(spec.split(','))
    print(spec,'functions',len(c),'instructions',sum(n[x] for x in c))
    print('  ',', '.join(f'{x}:{n[x]}' for x in sorted(c,key=lambda x:-n[x])[:24]))
