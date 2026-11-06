#!/usr/bin/env python3
"""Risk 1 measure: the stores an emitter memory-safety (frame) proof has to bound.
For the static call closure of compile_code, counts store instructions by base register:
sp (its own stack frame), gp/static (globals), and computed pointers (heap and malloc'd buffers),
and lists calls that leave the closure (libc, indirect). Usage: stores.py RUNTIME"""
import bisect, re, subprocess, sys, collections
R = sys.argv[1]
syms = []
for l in subprocess.run(['riscv64-linux-gnu-nm', '-S', R], capture_output=True, text=True).stdout.splitlines():
    p = l.split()
    if len(p) == 4 and p[2] in 'tTwW' and int(p[1], 16) > 0: syms.append((int(p[0], 16), int(p[1], 16), p[3]))
syms.sort(); addrs = [s[0] for s in syms]
def fn(a):
    i = bisect.bisect_right(addrs, a) - 1
    return syms[i][2] if i >= 0 and a < syms[i][0] + syms[i][1] else None
n = collections.Counter(); calls = collections.defaultdict(set); st = collections.defaultdict(collections.Counter)
ind = collections.Counter()
for l in subprocess.run(['riscv64-linux-gnu-objdump', '-d', '--no-show-raw-insn', R], capture_output=True, text=True).stdout.splitlines():
    m = re.match(r'^\s+([0-9a-f]+):\s+(\S+)\s*(.*)', l)
    if not m: continue
    a = int(m[1], 16); f = fn(a)
    if not f: continue
    op, args = m[2], m[3]
    n[f] += 1
    t = re.search(r'([0-9a-f]+) <', args)
    if op in ('jal', 'j', 'call', 'tail', 'jalr', 'jr') and t:
        g = fn(int(t[1], 16))
        if g and g != f: calls[f].add(g)
    elif op in ('jalr', 'jr') and args.strip() not in ('ra', '0(ra)'):
        ind[f] += 1
    if op in ('sd', 'sw', 'sh', 'sb', 'c.sd', 'c.sw', 'fsd', 'fsw', 'c.sdsp', 'c.swsp', 'c.fsd') or op.startswith('amo') or op.startswith('sc.'):
        base = re.search(r'\((\w+)\)', args)
        b = base[1] if base else '?'
        kind = 'sp' if b == 'sp' else ('gp' if b == 'gp' else 'computed')
        st[f][kind] += 1
def closure(roots, stop):
    seen = set(); stk = list(roots)
    while stk:
        x = stk.pop()
        if x in seen or x not in n or any(x.startswith(s) for s in stop): continue
        seen.add(x); stk += calls[x]
    return seen
LIBC = ('malloc', 'calloc', 'realloc', 'free', 'memcpy', 'memset', 'memmove', '__', 'fprintf', 'abort', 'spike_')
c = closure(['compile_code'], ['spike_'])
mine = [f for f in c if not f.startswith(LIBC)]
lib = [f for f in c if f.startswith(LIBC)]
tot = collections.Counter()
for f in mine: tot.update(st[f])
print('emitter closure (without libc and spike code): functions', len(mine), 'instructions', sum(n[f] for f in mine))
print('  stores', dict(tot), 'indirect jumps/calls', sum(ind[f] for f in mine))
print('  libc reached', len(lib), 'functions', sum(n[f] for f in lib), 'instructions:', ', '.join(sorted(lib)[:20]))
print('  top store sites:', ', '.join(f'{f}:{st[f]["computed"]}' for f in sorted(mine, key=lambda f: -st[f]['computed'])[:12]))
