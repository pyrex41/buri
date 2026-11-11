# Census only (not proof): independent Python walk of the image appended to the binary.
import struct, sys, re, collections
exe, d = sys.argv[1], sys.argv[2]
b = open(exe,'rb').read(); n = struct.unpack('<Q', b[-16:-8])[0]; img = b[-n:]
W = struct.unpack('<%dQ' % (n//8), img)
hw, ce, cc = W[6], W[7], W[8]
H = W[13:13+hw]; C = W[13+hw:13+hw+ce]; K = W[13+hw+ce:13+hw+ce+cc]
def ow(h):
    t, s = (h>>3)&31, h>>8
    return {1:max(2,1+(s+7)//8),2:max(2,1+(s+7)//8),3:4,4:2,5:max(2,1+s),6:3+s,7:5,8:10,9:3,10:3,11:5}[t]
objs = {}; i = 0; cnt = collections.Counter()
while i < hw:
    w = H[i]
    if w & 7 == 7: t = (w>>3)&31; objs[i] = t; cnt[t] += 1; i += ow(w)
    else: objs[i] = 0; cnt[0] += 1; i += 2
assert i == hw
def sbytes(o): s = H[o]>>8; return b''.join(struct.pack('<Q', H[o+1+j]) for j in range((s+7)//8))[:s]
syms = {}
for o, t in objs.items():
    if t == 3: nm = sbytes(H[o+1]>>3).decode('latin1'); syms[nm] = H[o+3]
names = []
FILES = ["toplevel","core","sys","dict","sequent","yacc","reader","prolog","track","load","writer","macros","declarations","types","t-star","init","shen-jit","lower","extension-features","extension-launcher","extension-programmable-pattern-matching","extension-namespaces","extension-expand-dynamic","extension-type-annotations"]
for f in FILES:
    for line in open('%s/%s.sbc' % (d, f)):
        m = re.match(r'\(defun (\S+) ', line)
        if m: names.append((f, m.group(1)))
print('types', sorted(cnt.items()))
print('defs', len(names), 'symbols', len(syms))
sealed = collections.Counter(); called = collections.Counter()
for f, nm in names:
    w = syms[nm]; sealed[f] += (w>>58)&1
print('sealed by file', [(f, sealed[f], sum(1 for g,_ in names if g==f)) for f in FILES])
allsealed = sum(1 for nm,w in syms.items() if (w>>58)&1)
print('symbols with sealed bit', allsealed)
# code objects reachable from function cells of the 955
def reach(v, acc):
    o = v >> 3; acc.add(o); cb, nk, nc = H[o+4], H[o+5], H[o+6]
    for j in range(nc): reach(K[cb+nk+j], acc)
acc = set()
for f, nm in names:
    cell = syms[nm] & ((1<<56)-1); fv = C[2*cell+1]; assert fv & 7 == 5
    reach(H[(fv>>3)+2], acc)
codes = [o for o,t in objs.items() if t == 8]
unr = [o for o in codes if o not in acc]
def val_name(v):
    if v & 7 == 6: return sbytes(H[(v>>3)+1]>>3).decode('latin1')
    return repr(v)
print('code objects', len(codes), 'reached', len(acc), 'unreached', len(unr))
print('unreached names', collections.Counter(val_name(H[o+7]) for o in unr).most_common(40))
# function cells of all symbols holding closures not among the 955
fn955 = set(nm for _, nm in names)
extra = [nm for nm, w in syms.items() if C[2*(w & ((1<<56)-1))+1] & 7 == 5 and nm not in fn955]
print('other symbols with a procedure in their function cell', len(extra), sorted(extra)[:60])
# who points to the unreached code objects
ptrs = collections.defaultdict(list)
for o, t in objs.items():
    if t == 0: fields = [o, o+1]
    elif t == 5: fields = range(o+1, o+1+(H[o]>>8))
    elif t == 6: fields = range(o+2, o+3+(H[o]>>8))
    elif t == 8: fields = range(o+7, o+10)
    elif t == 3: fields = [o+1]
    elif t == 9: fields = [o+1, o+2]
    else: fields = []
    for fld in fields:
        v = H[fld]
        if v & 7 in (1,3,5,6): ptrs[v>>3].append(('heap', o, t))
for j, v in enumerate(C):
    if v & 7 in (1,3,5,6): ptrs[v>>3].append(('cell', j//2, j%2))
for j, v in enumerate(K):
    if v & 7 in (1,3,5,6): ptrs[v>>3].append(('const', j, None))
cellname = {w & ((1<<56)-1): nm for nm, w in syms.items()}
def who(o, depth=0, seen=None):
    seen = seen or set()
    for p in ptrs[o][:4]:
        kind, x, y = p
        if kind == 'cell': print('  '*depth, 'cell', cellname.get(x), 'value' if y == 0 else 'function')
        elif kind == 'const': print('  '*depth, 'const slot', x)
        else:
            print('  '*depth, 'heap obj type', y, 'at', x)
            if depth < 6 and x not in seen: seen.add(x); who(x, depth+1, seen)
for o in unr:
    print('code', val_name(H[o+7]), 'arity', H[o+2], 'nconst', H[o+5], 'ncode', H[o+6], 'bytes', H[H[o+8]>>3]>>8)
    who(o, 1)
print('--- roots')
def root(o, seen):
    while True:
        ps = ptrs[o]
        if not ps: return ('none', o)
        kind, x, y = ps[0]
        if kind != 'heap': return (kind, cellname.get(x) if kind == 'cell' else x, y)
        if x in seen: return ('cycle', x)
        seen.add(x); o = x
for o in unr: print(val_name(H[o+7]), root(o, set()))
# describe const slot 7698 and the code index owning it
for o in codes:
    cb, nk, nc = H[o+4], H[o+5], H[o+6]
    if cb <= 7698 < cb+nk+nc: print('slot 7698 inside window of', val_name(H[o+7]))
print('consts total', cc, 'max window end', max(H[o+4]+H[o+5]+H[o+6] for o in codes))
