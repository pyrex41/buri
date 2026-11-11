#!/usr/bin/env python3
"""D00 census, NOT proof: each inlining marker (let stage0.lower.inlining (const F) N) in the stage 0
witnesses (<file>.norm from tests/shen-jit/capture_passes.sh), compared with F's own witness body.
Python only classifies syntax; Rocq decides nothing here, and the inline relation that will be
checked is rocq/JitFrontD.v's inl_site.

    d00_inline_census.py WITNESS_DIR                       site and definition totals (alpha / differs)
    MODE=3 d00_inline_census.py WITNESS_DIR                classes: alpha, int-subst, thaw-with, depth-cut
    MODE=4 d00_inline_census.py WITNESS_DIR OUT.tsv        one row per definition: the classes of its sites
    MODE=5 d00_inline_census.py WITNESS_DIR                integer sites with and without folding; cut sites
    d00_inline_census.py WITNESS_DIR CALLER CALLEE         print one site and the callee's body
"""
import sys, glob, os, collections
sys.setrecursionlimit(1000000)
import threading
threading.stack_size(1<<29)
def tokens(t):
    i,n=0,len(t)
    while i<n:
        c=t[i]
        if c in ' \n\t\r': i+=1
        elif c in '()': yield c; i+=1
        elif c=='"':
            j=i+1
            while t[j]!='"':
                j+= 2 if t[j]=='\\' else 1
            yield ('s',t[i:j+1]); i=j+1
        else:
            j=i
            while j<n and t[j] not in ' \n\t\r()"': j+=1
            yield t[i:j]; i=j
def parse(toks):
    st=[[]]
    for x in toks:
        if x=='(': st.append([])
        elif x==')': y=st.pop(); st[-1].append(y)
        else: st[-1].append(x)
    return st[0]
MK='stage0.lower.inlining'
def alpha(a,b,env):
    # env: list of (x,y) pairs, innermost first
    if isinstance(a,list) and isinstance(b,list):
        if not a or not b: return a==b
        h=a[0]
        if h!=b[0]: return False
        if h=='const': return a==b
        if h=='var':
            for x,y in env:
                if x==a[1] or y==b[1]: return x==a[1] and y==b[1]
            return a[1]==b[1]
        if h=='let':
            return alpha(a[2],b[2],env) and alpha(a[3],b[3],[(a[1],b[1])]+env)
        if h=='lambda':
            return alpha(a[2],b[2],[(a[1],b[1])]+env)
        if h=='trap':
            return alpha(a[1],b[1],env) and alpha(a[3],b[3],[(a[2],b[2])]+env)
        if h in ('prim','call'):
            return a[1]==b[1] and len(a[2])==len(b[2]) and all(alpha(x,y,env) for x,y in zip(a[2],b[2]))
        return len(a)==len(b) and all(alpha(x,y,env) for x,y in zip(a[1:],b[1:]))
    return a==b
def strip(n):
    # drop markers (erase drops them)
    if isinstance(n,list) and n:
        if n[0]=='let' and n[1]==MK: return strip(n[3])
        if n[0] in ('prim','call'): return [n[0],n[1],[strip(x) for x in n[2]]]
        if n[0]=='const': return n
        return [strip(x) for x in n]
    return n
def main(d):
    own={}
    order=[]
    for f in sorted(glob.glob(d+'/*.norm')):
        for e in parse(tokens(open(f).read())):
            own[e[0]]=(e[1],e[2]); order.append((os.path.basename(f),e[0]))
    sites=[]
    def walk(n,owner,depth):
        if isinstance(n,list) and n:
            if n[0]=='let' and n[1]==MK:
                sites.append((owner,n[2][1],n[3],depth)); walk(n[3],owner,depth+1); return
            if n[0]=='const': return
            for x in n: walk(x,owner,depth)
    for name,(ps,body) in own.items(): walk(body,name,0)
    c=collections.Counter(); ex=collections.defaultdict(list)
    for owner,F,N,dep in sites:
        if F not in own: c['callee-not-stage0']+=1; continue
        ps,eF=own[F]
        if alpha(N,eF,[]): k='alpha-equal'
        elif alpha(strip(N),strip(eF),[]): k='alpha-equal-mod-markers'
        else: k='differs'
        c[k]+=1; c[k+'@depth%d'%dep]+=1; ex[k].append((owner,F))
    print('inline sites',len(sites)); 
    for k,v in sorted(c.items()): print(k,v)
    callers=collections.defaultdict(set)
    for owner,F,N,dep in sites: callers[owner].add(F)
    print('definitions with a marker',len(callers))
    print('distinct inlined callees',len({F for _,F,_,_ in sites}))
    bad={o for o,F in ex['differs']}
    print('definitions with a differing site',len(bad))
    for o,F in ex['differs'][:12]: print('  differs',o,F)
    if len(sys.argv)>2:
        o,F=sys.argv[2],sys.argv[3]
        for ow,FF,N,dep in sites:
            if ow==o and FF==F: print('SITE',N); print('OWN ',own[F]); break
if __name__=='__main__' and os.environ.get('MODE','1')=='1':
    th=threading.Thread(target=lambda: main(sys.argv[1])); th.start(); th.join()

def isint(s):
    try: int(s); return True
    except: return False
def collect(a,b,free,sig):
    if isinstance(a,list) and isinstance(b,list) and a and b:
        if a[0]=='var' and a[1] in free and b[0]=='const' and isint(b[1]):
            if sig.get(a[1],b[1])!=b[1]: sig[a[1]]=None
            else: sig[a[1]]=b[1]
            return
        if a[0]!=b[0] or a[0]=='const': return
        if a[0] in ('prim','call'):
            for x,y in zip(a[2],b[2]): collect(x,y,free,sig)
        else:
            for x,y in zip(a[1:],b[1:]): collect(x,y,free,sig)
def subst_fold(n,sig,bound=()):
    if not (isinstance(n,list) and n): return n
    h=n[0]
    if h=='var': return ['const',sig[n[1]]] if n[1] in sig and n[1] not in bound else n
    if h=='const': return n
    if h=='let': return ['let',n[1],subst_fold(n[2],sig,bound),subst_fold(n[3],sig,bound+(n[1],))]
    if h=='lambda': return ['lambda',n[1],subst_fold(n[2],sig,bound+(n[1],))]
    if h=='trap': return ['trap',subst_fold(n[1],sig,bound),n[2],subst_fold(n[3],sig,bound+(n[2],))]
    if h in ('prim','call'):
        args=[subst_fold(x,sig,bound) for x in n[2]]
        if h=='prim' and n[1] in ('+','-') and len(args)==2 and all(a[0]=='const' and isint(a[1]) for a in args):
            x,y=int(args[0][1]),int(args[1][1])
            if abs(x)<10**9 and abs(y)<10**9: return ['const',str(x+y if n[1]=='+' else x-y)]
        return [h,n[1],args]
    return [h]+[subst_fold(x,sig,bound) for x in n[1:]]
def main2(d):
    own={}
    for f in sorted(glob.glob(d+'/*.norm')):
        for e in parse(tokens(open(f).read())): own[e[0]]=(e[1],e[2])
    sites=[]
    def walk(n,owner):
        if isinstance(n,list) and n:
            if n[0]=='let' and n[1]==MK: sites.append((owner,n[2][1],n[3])); walk(n[3],owner); return
            if n[0]=='const': return
            for x in n: walk(x,owner)
    for name,(ps,body) in own.items(): walk(body,name)
    c=collections.Counter(); rest=[]
    for o,F,N in sites:
        ps,eF=own[F]
        if alpha(N,eF,[]): continue
        sig={}; collect(eF,N,set(ps),sig); sig={k:v for k,v in sig.items() if v is not None}
        if sig and alpha(N,subst_fold(eF,sig),[]): c['int-subst+fold']+=1
        else: c['other']+=1; rest.append((o,F))
    print(dict(c)); 
    for r in rest[:20]: print(' other',r)
if __name__=='__main__' and os.environ.get('MODE')=='2':
    th=threading.Thread(target=lambda: main2(sys.argv[1])); th.start(); th.join()

def recon(n,cut,depth=0):
    # replace inline regions at marker depth >= cut by the call they came from, when reconstructible
    if not (isinstance(n,list) and n): return n
    if n[0]=='let' and isinstance(n[1],str) and n[1].startswith('stage0.lower.arg'):
        # collect fresh lets, then param lets, then marker
        fr=[]; m=n
        while isinstance(m,list) and m and m[0]=='let' and m[1].startswith('stage0.lower.arg'): fr.append((m[1],m[2])); m=m[3]
        pl=[]
        while isinstance(m,list) and m and m[0]=='let' and m[1]!=MK and m[2][0]=='var' and m[2][1] in [a for a,_ in fr]: pl.append((m[1],m[2][1])); m=m[3]
        if isinstance(m,list) and m and m[0]=='let' and m[1]==MK and len(pl)==len(fr) and [b for _,b in pl]==[a for a,_ in fr]:
            if depth>=cut:
                return ['call',m[2][1],[recon(v,cut,depth) for _,v in fr]]
            inner=recon(m[3],cut,depth+1)
            out=['let',MK,m[2],inner]
            for p,a in reversed(pl): out=['let',p,['var',a],out]
            for a,v in reversed(fr): out=['let',a,recon(v,cut,depth),out]
            return out
    if n[0]=='let' and n[1]==MK: return ['let',MK,n[2],recon(n[3],cut,depth+1)]
    if n[0]=='const': return n
    if n[0] in ('prim','call'): return [n[0],n[1],[recon(x,cut,depth) for x in n[2]]]
    return [recon(x,cut,depth) if isinstance(x,list) else x for x in n]
def thawsub(eF,N,ps):
    # find P with exactly one (apply (var P)) in eF; try replacing it by the subterm of N at the same path
    def paths(n,p=()):
        if isinstance(n,list) and n:
            if n[0]=='apply' and len(n)==2 and n[1][0]=='var' and n[1][1] in ps: yield p,n[1][1]
            if n[0]=='const': return
            for i,x in enumerate(n):
                if isinstance(x,list): yield from paths(x,p+(i,))
    def get(n,p):
        for i in p:
            if not (isinstance(n,list) and i<len(n)): return None
            n=n[i]
        return n
    def put(n,p,v):
        if not p: return v
        m=list(n); m[p[0]]=put(n[p[0]],p[1:],v); return m
    out=eF
    for p,P in list(paths(eF)):
        s=get(N,p)
        if s is not None: out=put(out,p,s)
    return out
def main3(d):
    own={}
    for f in sorted(glob.glob(d+'/*.norm')):
        for e in parse(tokens(open(f).read())): own[e[0]]=(e[1],e[2])
    sites=[]
    def walk(n,owner,dep):
        if isinstance(n,list) and n:
            if n[0]=='let' and n[1]==MK: sites.append((owner,n[2][1],n[3],dep)); walk(n[3],owner,dep+1); return
            if n[0]=='const': return
            for x in n: walk(x,owner,dep)
    for name,(ps,body) in own.items(): walk(body,name,0)
    c=collections.Counter(); rest=[]
    for o,F,N,dep in sites:
        ps,eF=own[F]
        if alpha(N,eF,[]): c['alpha']+=1; continue
        sig={}; collect(eF,N,set(ps),sig); sig={k:v for k,v in sig.items() if v is not None}
        if sig and alpha(N,subst_fold(eF,sig),[]): c['int-subst']+=1; continue
        ok=None
        for cut in (1,0):
            r=recon(eF,cut)
            if alpha(N,r,[]): ok='depth-cut'; break
            if sig and alpha(N,subst_fold(r,sig),[]): ok='depth-cut+int-subst'; break
        if not ok:
            t=thawsub(eF,N,set(ps))
            if t!=eF and alpha(N,t,[]): ok='thaw-with'
        if not ok:
            for cut in (1,0):
                t=thawsub(recon(eF,cut),N,set(ps))
                if alpha(N,t,[]): ok='thaw-with+depth-cut'; break
        if ok: c[ok]+=1
        else: c['other']+=1; rest.append((o,F,dep))
    print(dict(c), 'total', len(sites))
    for r in rest[:20]: print(' other',r)
if __name__=='__main__' and os.environ.get('MODE')=='3':
    th=threading.Thread(target=lambda: main3(sys.argv[1])); th.start(); th.join()

def main4(d,out):
    own={}
    for f in sorted(glob.glob(d+'/*.norm')):
        for e in parse(tokens(open(f).read())): own[e[0]]=(e[1],e[2])
    sites=[]
    def walk(n,owner,dep):
        if isinstance(n,list) and n:
            if n[0]=='let' and n[1]==MK: sites.append((owner,n[2][1],n[3],dep)); walk(n[3],owner,dep+1); return
            if n[0]=='const': return
            for x in n: walk(x,owner,dep)
    for name,(ps,body) in own.items(): walk(body,name,0)
    per=collections.defaultdict(set)
    for o,F,N,dep in sites:
        ps,eF=own[F]
        if alpha(N,eF,[]): k='alpha'
        else:
            sig={}; collect(eF,N,set(ps),sig); sig={k2:v for k2,v in sig.items() if v is not None}
            if sig and alpha(N,subst_fold(eF,sig),[]): k='int'
            elif any(alpha(N,recon(eF,c),[]) for c in (1,0)): k='cut'
            elif alpha(N,thawsub(eF,N,set(ps)),[]): k='thaw'
            else: k='other'
        per[o].add(k)
    with open(out,'w') as f:
        for o in own: f.write('%s\t%s\n'%(o,','.join(sorted(per[o])) or '-'))
if __name__=='__main__' and os.environ.get('MODE')=='4':
    th=threading.Thread(target=lambda: main4(sys.argv[1],sys.argv[2])); th.start(); th.join()

def subst_only(n,sig,bound=()):
    if not (isinstance(n,list) and n): return n
    h=n[0]
    if h=='var': return ['const',sig[n[1]]] if n[1] in sig and n[1] not in bound else n
    if h=='const': return n
    if h=='let': return ['let',n[1],subst_only(n[2],sig,bound),subst_only(n[3],sig,bound+(n[1],))]
    if h=='lambda': return ['lambda',n[1],subst_only(n[2],sig,bound+(n[1],))]
    if h=='trap': return ['trap',subst_only(n[1],sig,bound),n[2],subst_only(n[3],sig,bound+(n[2],))]
    if h in ('prim','call'): return [h,n[1],[subst_only(x,sig,bound) for x in n[2]]]
    return [h]+[subst_only(x,sig,bound) for x in n[1:]]
def main5(d):
    own={}
    for f in sorted(glob.glob(d+'/*.norm')):
        for e in parse(tokens(open(f).read())): own[e[0]]=(e[1],e[2])
    sites=[]
    def walk(n,owner):
        if isinstance(n,list) and n:
            if n[0]=='let' and n[1]==MK: sites.append((owner,n[2][1],n[3])); walk(n[3],owner); return
            if n[0]=='const': return
            for x in n: walk(x,owner)
    for name,(ps,body) in own.items(): walk(body,name)
    c=collections.Counter(); fold_defs=set(); cut=[]
    for o,F,N in sites:
        ps,eF=own[F]
        if alpha(N,eF,[]): continue
        sig={}; collect(eF,N,set(ps),sig); sig={k:v for k,v in sig.items() if v is not None}
        if sig and alpha(N,subst_only(eF,sig),[]): c['int-nofold']+=1
        elif sig and alpha(N,subst_fold(eF,sig),[]): c['int-fold']+=1; fold_defs.add((o,F))
        else:
            for k in (1,0):
                if alpha(N,recon(eF,k),[]): cut.append((o,F,k))
    print(dict(c)); print(sorted(fold_defs)); print('cut sites',cut)
if __name__=='__main__' and os.environ.get('MODE')=='5':
    th=threading.Thread(target=lambda: main5(sys.argv[1])); th.start(); th.join()
