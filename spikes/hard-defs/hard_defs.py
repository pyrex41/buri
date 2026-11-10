#!/usr/bin/env python3
"""Hard stage 0 definitions after round 2 (spikes/hard-defs/REPORT.md, defs.tsv). CENSUS ONLY.

Nothing here is proof or validation. It re-reads the same inputs as tests/shen-jit/feature_census.py
(T02), reuses its walk and classification so the numbers reconcile with spikes/pass-split/FEATURES.md,
and adds: a blocker classification by what would have to change (planned round-2 task, decision item,
or a gap no task or decision option covers), round-2 coverage per item, the callee closure with and
without function-symbol-constant edges, the strongly connected component's blocker set, per-definition
size, and forecasts for the proposals in REPORT.md.

    hard_defs.py STAGE0_DIR CAPTURE_DIR JUDGE_DIR OUT_TSV > tables.md

Inputs are those of feature_census.py: STAGE0_DIR/<f>.{forms,sbc}, CAPTURE_DIR/witness/<f>.norm,
CAPTURE_DIR/count/<f>.ticks, JUDGE_DIR/{src,nf,tf}/<f>.codes.
"""
import collections, os, sys
sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'tests', 'shen-jit'))
import feature_census as fc
from feature_census import atom

# ------------------------------------------------------------------ item classes
# Items are T02's: emit features (fx.feats - BASE) and front families ('fam:' + FAMILY_OF[tick]).
# Round 2 (p2-round2.json) plans every T02 part-A item. Coverage per item is the owning task.
COVER = {
    'value/set': 'r1-emit-families (sim_Store)', 'eq-symbol-const': 'eq-guard-merge',
    'simple-error': 'r1-emit-families (sim_Prim)', 'error-to-string': 'r1-emit-families (sim_Prim)',
    'vector': 'r1-emit-families (sim_Prim)', 'io': 'r1-emit-families (sim_Prim)',
    'do': 'r1-emit-families (sim_DoFold)', 'folded-const': 'r1-emit-families (sim_DoFold)',
    'lambda': 'r1-emit-families (sim_Clo)', 'freeze': 'r1-emit-families (sim_Clo)',
    'let-freeze': 'r1-emit-families (sim_Clo)', 'thaw': 'r1-emit-families (sim_Clo)',
    'apply-dynamic': 'r1-emit-families (sim_App)', 'trap': 'r1-emit-families (sim_Trap)',
    'fam:inline': 'r1-f-inline', 'fam:cond': 'r1-f-sugar', 'fam:sugar': 'r1-f-sugar',
    'fam:thaw-sugar': 'r1-f-sugar', 'fam:trap-sugar': 'r1-f-sugar',
    'fam:fold-cons': 'r1-f-copy-fold-apply', 'fam:fold-arith': 'r1-f-copy-fold-apply',
    'fam:copy': 'r1-f-copy-fold-apply', 'fam:share': 'r1-share-ht', 'fam:bind': 'r1-f-prolog',
    'fam:cut-deref': 'r1-f-prolog',
}
def cover(item):
    if item.startswith('prim:'):
        return 'r1-emit-families (sim_Prim)'
    return COVER.get(item)

NAN = {'eq-two-computed', 'eq-two-computed-unguarded'}
EVALKL = {'fam:eval-kl'}
ID_CAND = {'port:shen-jit.same?', 'port:shen-jit.tagged?'}          # proposed rule; OWrong on pairs etc.
PVAR = {'port:shen-jit.deref', 'port:shen-jit.pvar', 'port:shen-jit.pvar?', 'port:shen-jit.pvar-offset'}
HASHED = {'port:shen-jit.hash', 'port:shen-jit.dict-find', 'port:shen-jit.dict-put', 'port:shen-jit.dict-remove'}
CAND_CORE = {'port:' + p for p in ['shen-jit.symbol?', 'shen-jit.integer?', 'shen-jit.append',
             'shen-jit.absvector3', 'shen-jit.filled-vector', 'shen-jit.vector?', 'shen-jit.symbol-kind',
             'char-stream?', 'read-unit-string', 'write-string', 'shen-jit.decimal', 'shen-jit.dict-entries']}
BYTES = {'port:shen-jit.write-bytes', 'port:shen-jit.string->bytes', 'port:shen-jit.bytes-length',
         'port:shen-jit.u8'}
NOCARRIER_ONE = {'port:shen-jit.' + p for p in ['read-file', 'exit', 'quiet?', 'mark-toplevel', 'trace-text',
                 'install', 'inline-body', 'sealed?', 'sealing']}

def klass(item):
    """(blocker class, decision item or '-') for an item no planned task covers."""
    if item in NAN: return ('nan-eq', 'nan-eq')
    if item in EVALKL: return ('eval-kl', 'eval-kl')
    if item in ID_CAND: return ('identity-cand', 'identity')
    if item == 'port:shen-jit.deref': return ('pvar', 'identity')
    if item in PVAR: return ('pvar', 'port-prims')
    if item in HASHED: return ('port-cand-hash', 'port-prims')
    if item in CAND_CORE: return ('port-cand', 'port-prims')
    if item in BYTES: return ('bytes', 'port-prims')
    if item in NOCARRIER_ONE: return (item[5:], 'port-prims')
    return ('UNCLASSIFIED', '-')

# Proposals (REPORT.md section 3): the items each one admits. Census forecast only.
PROPOSALS = collections.OrderedDict([
    ('P1-lim', ('limit outcome in call_preservation_src\' for a target stuck on RIdentity/RCyclic/RExcluded',
                NAN | {'port:shen-jit.mark-toplevel', 'port:shen-jit.trace-text'})),
    ('P2-wire', ('wire jit_port_prims_proposed, rule_param per rule, hash_go transcribed as the hash instance',
                 CAND_CORE | HASHED)),
    ('P2b-wire-id', ('same?/tagged? from the proposal, admitted with P1\'s RIdentity limit', ID_CAND)),
    ('P3-stop-evalkl', ('stop outcome at shen-jit.eval-kl calls and at install (limit points)', EVALKL |
                        {'port:shen-jit.install'})),
    ('P4-sealed', ('sealed? reads jit_rules\' sealed parameter', {'port:shen-jit.sealed?'})),
    ('P5-inline-body', ('inline-body as a parameter tied to D\'s inline forms', {'port:shen-jit.inline-body'})),
    ('P6-quiet', ('quiet? read from the source continuation\'s innermost trap frame', {'port:shen-jit.quiet?'})),
    ('P7-bytes', ('byte buffers: stop at string->bytes and u8 (P7a) or kernel-reference proofs (P7b)', BYTES)),
    ('P8-stop-misc', ('stop outcomes for exit, sealing, read-file', {'port:shen-jit.exit', 'port:shen-jit.sealing',
                                                                    'port:shen-jit.read-file'})),
    ('P9-pvar', ('a Prolog-variable carrier, and same? on pairs in unify=/occurs-in?/deref=', PVAR)),
])

# Planned ticks whose round-2 task spec may not cover them (REPORT section 2.2).
RISKY = ['inline-int-arg', 'share-chain', 'frozen-late-hoist', 'inline-frozen', 'let-lambda', 'let-frozen-copy',
         'bound-now', 'bound-now-frozen', 'unified-now', 'trap-other']
PLANNED_ITEMS = None  # filled in main: every item cover() maps

# ------------------------------------------------------------------ extra walk
def size(n):
    if n[0] == 'list':
        return 1 + sum(size(x) for x in n[1])
    return 1

def sym_consts(n, out):
    """Every symbol constant (const S) in a normal form, S an atom (a function-symbol candidate)."""
    l = n[1]
    if n[0] != 'list':
        return
    if l and atom(l[0]) == 'const':
        if l[1][0] == 'atom':
            out.add(atom(l[1]))
        return
    for x in l:
        sym_consts(x, out)

def prim_ops(n, out):
    l = n[1]
    if n[0] != 'list' or not l:
        return
    if atom(l[0]) == 'const':
        return
    if atom(l[0]) == 'prim':
        out[atom(l[1])] += 1
    for x in l:
        prim_ops(x, out)

def scc_of(names, E):
    index, low, onst, st, comps, idx = {}, {}, set(), [], [], [0]
    for root in names:
        if root in index:
            continue
        work = [(root, iter(sorted(E[root])))]
        index[root] = low[root] = idx[0]; idx[0] += 1; st.append(root); onst.add(root)
        while work:
            v, it = work[-1]
            w = next(it, None)
            if w is not None:
                if w not in index:
                    index[w] = low[w] = idx[0]; idx[0] += 1; st.append(w); onst.add(w)
                    work.append((w, iter(sorted(E[w]))))
                elif w in onst:
                    low[v] = min(low[v], index[w])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == index[v]:
                    c = set()
                    while True:
                        w = st.pop(); onst.discard(w); c.add(w)
                        if w == v:
                            break
                    comps.append(c)
    return comps

def closure(n, E):
    seen, todo = {n}, [n]
    while todo:
        x = todo.pop()
        for y in E[x]:
            if y not in seen:
                seen.add(y); todo.append(y)
    return seen

# ------------------------------------------------------------------ main
def main(s0, cap, judge, out_tsv):
    files = sorted(f[:-6] for f in os.listdir(s0) if f.endswith('.forms'))
    wit, cnt = os.path.join(cap, 'witness'), os.path.join(cap, 'count')
    D = collections.OrderedDict()
    for f in files:
        norms = fc.read(os.path.join(wit, f + '.norm'))
        ticks = fc.read(os.path.join(cnt, f + '.ticks'))
        forms = fc.read(os.path.join(s0, f + '.forms'))
        sbcs = fc.read(os.path.join(s0, f + '.sbc'))
        vs, vn, vt = (fc.verdicts(judge, v, f) for v in ('src', 'nf', 'tf'))
        assert len(norms) == len(ticks) == len(forms) == len(sbcs) == len(vs), f
        for i, nm in enumerate(norms):
            name = atom(nm[1][0])
            assert atom(ticks[i][1][0]) == name and atom(forms[i][1][1]) == name, (f, name)
            fx = fc.Facts(); fc.walk(nm[1][2], fx)
            keys = collections.Counter()
            for kv in ticks[i][1][1][1]:
                keys[atom(kv[1][0])] += int(atom(kv[1][1]))
            sc = set(); sym_consts(nm[1][2], sc)
            ops = collections.Counter(); prim_ops(nm[1][2], ops)
            code = sbcs[i][1][2][1]   # (code Name Arity Frame Consts Instrs Nested ...)
            D[name] = dict(file=f, index=i + 1, fx=fx, keys=keys, src=vs[i], nf=vn[i], tf=vt[i],
                           opaque={k for k in keys if k not in fc.SRC_TRANSPARENT_KEYS},
                           syms=sc, ops=ops, nsize=size(nm[1][2]), fsize=size(forms[i]),
                           sbcsize=size(sbcs[i]), ticks=sum(keys.values()))
    names = list(D); N = len(names); defined = set(names)

    def need(r):
        fams = {'fam:' + fc.FAMILY_OF[k] for k in r['keys'] if k in fc.FAMILY_OF} if r['opaque'] else set()
        return (r['fx'].feats - fc.BASE) | fams
    def emit_need(r):
        return r['fx'].feats - fc.BASE
    for n in names:
        D[n]['need'] = need(D[n])
    allitems = set().union(*(D[n]['need'] for n in names))
    planned = {x for x in allitems if cover(x)}
    unplanned = allitems - planned
    unclassified = [x for x in unplanned if klass(x)[0] == 'UNCLASSIFIED']
    assert not unclassified, unclassified

    E_call = {n: {c for c in D[n]['fx'].calls if c in defined and c != n} for n in names}
    E_inl = {n: {c for c in D[n]['fx'].inlined if c in defined and c != n} for n in names}
    E_all = {n: E_call[n] | E_inl[n] for n in names}
    E_sym = {n: E_all[n] | {s for s in D[n]['syms'] if s in defined and s != n} for n in names}
    CL = {n: closure(n, E_all) for n in names}
    CLs = {n: closure(n, E_sym) for n in names}
    comps = scc_of(names, E_all); big = max(comps, key=len)
    comps_s = scc_of(names, E_sym); big_s = max(comps_s, key=len)
    reach_big = {n for n in names if CL[n] & big}
    reach_big_s = {n for n in names if CLs[n] & big_s}

    # dynamic calls anywhere in the closure: the static closure is then only a lower bound
    dyn_self = {n for n in names if D[n]['fx'].feats & {'apply-dynamic', 'thaw'}}
    dyn_cl = {n for n in names if CL[n] & dyn_self}

    def count(A, edges_drop=frozenset(), CLmap=None):
        """direct, D-src, D-low under admitted set A. edges_drop: callees whose bodies the claim
        never enters (a stop outcome at their call)."""
        CLm = CLmap or CL
        ok = {n for n in names if D[n]['need'] <= A}
        eok = {n for n in names if emit_need(D[n]) <= A}
        def cl(n):
            if not edges_drop:
                return CLm[n]
            E = {m: E_sym[m] if CLmap else E_all[m] for m in names}
            E = {m: E[m] - edges_drop for m in names}
            return closure(n, E)
        cache = {n: cl(n) for n in names} if edges_drop else CLm
        dsrc = {n for n in ok if cache[n] <= ok}
        dlow = {n for n in ok if (cache[n] - {n}) <= eok}
        return ok, dsrc, dlow

    P = print
    P('<!-- generated by spikes/hard-defs/hard_defs.py; census, not proof -->\n')
    # ---- reconciliation with T02
    ok0, s0_, l0 = count(set())
    okA, sA, lA = count(planned)
    allA = allitems
    okZ, sZ, lZ = count(allA)
    P('## Reconciliation with T02 (FEATURES.md)\n')
    P('| set | direct | D-src | D-low | T02 |')
    P('|---|---:|---:|---:|---|')
    P('| current Comp | %d | %d | %d | 111 / 46 / 46 |' % (len(ok0), len(s0_), len(l0)))
    P('| every planned (part A) item | %d | %d | %d | 564 / 235 / 235 |' % (len(okA), len(sA), len(lA)))
    P('| every item | %d | %d | %d | 955 / 955 / 955 |' % (len(okZ), len(sZ), len(lZ)))
    P('\nRocq verdicts read: src %d, nf %d, tf %d accepted.\n' % (
        sum(D[n]['src'] == 1 for n in names), sum(D[n]['nf'] == 1 for n in names),
        sum(D[n]['tf'] == 1 for n in names)))

    # ---- blockers beyond the plan
    P('## Blocker classes no round-2 task covers (self and closure)\n')
    P('A definition counts under "self" if its own normal form needs an item of the class; under')
    P('"closure" if any definition in its call-plus-marker closure (itself included) does. Planned')
    P('items are assumed delivered as T02 forecasts them.\n')
    cls_self = collections.defaultdict(set)
    for n in names:
        for x in D[n]['need'] - planned:
            cls_self[klass(x)[0]].add(n)
    cls_cl = {c: {n for n in names if CL[n] & s} for c, s in cls_self.items()}
    cls_cls = {c: {n for n in names if CLs[n] & s} for c, s in cls_self.items()}
    P('| class | decision item | self | closure | closure with symbol edges | in the SCC (self) |')
    P('|---|---|---:|---:|---:|---:|')
    dec_of = {}
    for x in unplanned:
        dec_of.setdefault(klass(x)[0], set()).add(klass(x)[1])
    for c in sorted(cls_self, key=lambda c: (-len(cls_self[c]), c)):
        P('| %s | %s | %d | %d | %d | %d |' % (c, ','.join(sorted(dec_of[c])), len(cls_self[c]),
                                              len(cls_cl[c]), len(cls_cls[c]), len(cls_self[c] & big)))
    anyself = set().union(*cls_self.values())
    P('\nany class: self %d, closure %d; validated-closure ceiling with the plan alone: D-src %d, D-low %d.\n'
      % (len(anyself), len({n for n in names if CL[n] & anyself}), len(sA), len(lA)))

    # ---- per-item table, unplanned
    P('### Unplanned items\n')
    P('| item | class | decision | self | closure | self in SCC |')
    P('|---|---|---|---:|---:|---:|')
    for x in sorted(unplanned, key=lambda x: (-sum(x in D[n]['need'] for n in names), x)):
        s = {n for n in names if x in D[n]['need']}
        c = {n for n in names if CL[n] & s}
        P('| `%s` | %s | %s | %d | %d | %d |' % (x, klass(x)[0], klass(x)[1], len(s), len(c), len(s & big)))

    # ---- SCC
    P('\n## The strongly connected component\n')
    P('call + marker edges: largest SCC %d, %d definitions reach it. With function-symbol constants as edges'
      ' too: largest SCC %d, %d reach it.\n' % (len(big), len(reach_big), len(big_s), len(reach_big_s)))
    scc_cl = set().union(*(CL[n] for n in big))
    P('The SCC\'s own closure has %d definitions (the SCC and what it calls).\n' % len(scc_cl))
    need_in = collections.defaultdict(set)
    for n in scc_cl:
        for x in D[n]['need'] - planned:
            need_in[x].add(n)
    P('Every unplanned item needed anywhere in the SCC\'s closure; all must be admitted before any of the'
      ' %d definitions reaching the SCC validates under the closure limit:\n' % len(reach_big))
    P('| item | class | definitions in SCC closure needing it | of them in the SCC | names |')
    P('|---|---|---:|---:|---|')
    for x in sorted(need_in, key=lambda x: (-len(need_in[x]), x)):
        nm = sorted(need_in[x])
        P('| `%s` | %s | %d | %d | %s |' % (x, klass(x)[0], len(nm), len(need_in[x] & big),
                                          ', '.join('`%s`' % y for y in nm[:6]) + (' ...' if len(nm) > 6 else '')))

    # ---- dynamic-call caveat
    P('\n## Closure is a lower bound\n')
    P('Definitions with a dynamic application or thaw of their own: %d. Definitions whose static closure'
      ' contains one: %d of %d. Definitions with a function-symbol constant naming a stage 0 definition'
      ' outside their static closure: %d.\n' % (len(dyn_self), len(dyn_cl), N,
      sum(1 for n in names if ({s for s in D[n]['syms'] if s in defined} - CL[n]))))

    # ---- forecasts
    P('## Forecasts (census): planned tasks plus proposals\n')
    P('Each row adds its proposal to everything above it. D-src: the definition and its call-plus-marker')
    P('closure all direct. "+sym": closure with function-symbol constants as edges too. A stop outcome')
    P('drops the call edge to the stopped callee (the claim never enters its body).\n')
    P('| row | admits | direct | D-src | D-low | D-src +sym |')
    P('|---|---|---:|---:|---:|---:|')
    A = set(planned); drop = set()
    _, ds_sym, _ = count(A, CLmap=CLs)
    P('| plan | round 2 as planned (T02 part A) | %d | %d | %d | %d |' % (len(okA), len(sA), len(lA), len(ds_sym)))
    rows = []
    for key, (desc, items) in PROPOSALS.items():
        A |= items
        if key == 'P3-stop-evalkl':
            drop |= {'shen-jit.eval-kl'}
        ok, ds, dl = count(A, frozenset(drop))
        _, dss, _ = count(A, frozenset(drop), CLmap=CLs)
        rows.append((key, len(ok), len(ds), len(dl), len(dss)))
        P('| %s | %s | %d | %d | %d | %d |' % (key, desc, len(ok), len(ds), len(dl), len(dss)))
    # bundles: what flips the cliff
    P('\n### Bundles\n')
    P('| bundle (on top of the plan) | direct | D-src | D-low | self-blocked | callee-link |')
    P('|---|---:|---:|---:|---:|---:|')
    for label, keys in [('P3 alone', ['P3-stop-evalkl']),
                        ('P1 + P3', ['P1-lim', 'P3-stop-evalkl']),
                        ('P1 + P2 + P2b + P3', ['P1-lim', 'P2-wire', 'P2b-wire-id', 'P3-stop-evalkl']),
                        ('P1 + P2 + P2b + P3 + P6', ['P1-lim', 'P2-wire', 'P2b-wire-id', 'P3-stop-evalkl', 'P6-quiet']),
                        ('cliff bundle: P1 + P2 + P2b + P3 + P6 + P7',
                         ['P1-lim', 'P2-wire', 'P2b-wire-id', 'P3-stop-evalkl', 'P6-quiet', 'P7-bytes']),
                        ('cliff bundle without P3', ['P1-lim', 'P2-wire', 'P2b-wire-id', 'P6-quiet', 'P7-bytes']),
                        ('cliff bundle + P4 + P5 (lowerer)',
                         ['P1-lim', 'P2-wire', 'P2b-wire-id', 'P3-stop-evalkl', 'P6-quiet', 'P7-bytes', 'P4-sealed',
                          'P5-inline-body']),
                        ('all but P9 (Prolog variables residual)', [k for k in PROPOSALS if k != 'P9-pvar']),
                        ('all', list(PROPOSALS))]:
        Ab = set(planned).union(*(PROPOSALS[k][1] for k in keys))
        dr = frozenset({'shen-jit.eval-kl'}) if 'P3-stop-evalkl' in keys else frozenset()
        ok, ds, dl = count(Ab, dr)
        sb = sum(1 for n in names if not D[n]['need'] <= Ab)
        P('| %s | %d | %d | %d | %d | %d |' % (label, len(ok), len(ds), len(dl), sb, N - len(ds) - sb))
    # marginal, one at a time against the plan, and leave-one-out against all proposals
    P('\n### Each proposal alone on top of the plan, and each left out of all of them\n')
    P('| proposal | alone: direct | alone: D-src | left out: direct | left out: D-src | left out: D-src +sym |')
    P('|---|---:|---:|---:|---:|---:|')
    full = set(planned).union(*(it for _, it in PROPOSALS.values()))
    okF, dsF, _ = count(full, frozenset({'shen-jit.eval-kl'}))
    _, dsFs, _ = count(full, frozenset({'shen-jit.eval-kl'}), CLmap=CLs)
    for key, (desc, items) in PROPOSALS.items():
        dr = frozenset({'shen-jit.eval-kl'}) if key == 'P3-stop-evalkl' else frozenset()
        ok1, ds1, _ = count(set(planned) | items, dr)
        drl = frozenset() if key == 'P3-stop-evalkl' else frozenset({'shen-jit.eval-kl'})
        rest = set(planned).union(*(it for k2, (_, it) in PROPOSALS.items() if k2 != key))
        ok2, ds2, _ = count(rest, drl)
        _, ds2s, _ = count(rest, drl, CLmap=CLs)
        P('| %s | +%d | +%d | -%d | -%d | -%d |' % (key, len(ok1) - len(okA), len(ds1) - len(sA),
                                                   len(okF) - len(ok2), len(dsF) - len(ds2), len(dsFs) - len(ds2s)))
    P('\nall proposals: direct %d, D-src %d, D-src +sym %d.\n' % (len(okF), len(dsF), len(dsFs)))

    # ---- decision items: self and closure counts
    P('## Decision items: definitions at stake (census)\n')
    P('"self": the definition\'s own normal form needs the item. "closure": some definition in its closure')
    P('does. "loo": left out of the plan plus every proposal, the D-src count lost.\n')
    groups = collections.OrderedDict([
        ('port primitives: proposed candidates (wiring)', CAND_CORE | HASHED | ID_CAND),
        ('port primitives: no candidate (byte buffers, pvar, read-file, exit, quiet?, ...)',
         BYTES | PVAR | NOCARRIER_ONE),
        ('eval-kl', EVALKL),
        ('identity: same?, tagged?', ID_CAND),
        ('identity: deref', {'port:shen-jit.deref'}),
        ('NaN = (two computed operands)', NAN),
        ('NaN = unguarded only (static non-real guard taken)', {'eq-two-computed-unguarded'}),
    ])
    P('| item | self | closure | closure +sym | loo D-src | loo direct |')
    P('|---|---:|---:|---:|---:|---:|')
    for g, items in groups.items():
        s = {n for n in names if D[n]['need'] & items}
        c = {n for n in names if CL[n] & s}
        cs = {n for n in names if CLs[n] & s}
        rest = full - items
        if items == {'eq-two-computed-unguarded'}:
            rest = full - {'eq-two-computed-unguarded'}
            s = {n for n in names if 'eq-two-computed-unguarded' in D[n]['need']}
        ok2, ds2, _ = count(rest, frozenset({'shen-jit.eval-kl'}) if not (items & EVALKL) else frozenset())
        P('| %s | %d | %d | %d | -%d | -%d |' % (g, len(s), len(c), len(cs), len(dsF) - len(ds2), len(okF) - len(ok2)))

    # ---- 20-cap classification under the plan alone
    P('\n## Residuals under the plan alone, by kind (the DoD\'s 20 cap)\n')
    self_dec = [n for n in names if not D[n]['need'] <= planned]
    callee_only = [n for n in names if D[n]['need'] <= planned and n not in sA]
    P('Plan alone: %d definitions validate under D-src. Of the other %d:\n' % (len(sA), N - len(sA)))
    P('- %d are self-blocked, every one by decision-gated items only (no non-decision item is unplanned);' % len(self_dec))
    P('- %d are self-clear but have a decision-gated definition in their closure: callee-link failures.\n'
      % len(callee_only))

    # ---- size
    P('## Largest definitions\n')
    P('| definition | file | norm nodes | source nodes | sbc nodes | ticks | inlined callees | closure |')
    P('|---|---|---:|---:|---:|---:|---:|---:|')
    for n in sorted(names, key=lambda n: (-D[n]['nsize'], n))[:20]:
        r = D[n]
        P('| `%s` | %s | %d | %d | %d | %d | %d | %d |' % (n, r['file'], r['nsize'], r['fsize'], r['sbcsize'],
                                                      r['ticks'], len(r['fx'].inlined), len(CL[n]) - 1))
    P('\nnorm nodes: total %d; median %d; >= 1000: %d; >= 3000: %d.\n' % (
        sum(D[n]['nsize'] for n in names), sorted(D[n]['nsize'] for n in names)[N // 2],
        sum(D[n]['nsize'] >= 1000 for n in names), sum(D[n]['nsize'] >= 3000 for n in names)))

    # ---- at-risk planned ticks
    P('## Planned items whose task spec may not cover every firing (definitions)\n')
    for k in ['inline-int-arg', 'share-chain', 'frozen-late-hoist', 'inline-frozen', 'let-lambda',
              'let-frozen-copy', 'bound-now', 'bound-now-frozen', 'unified-now', 'trap-other', 'protect', 'type',
              'lambda-app']:
        s = sorted(n for n in names if D[n]['keys'].get(k))
        P('- `%s`: %d: %s' % (k, len(s), ', '.join('`%s`' % x for x in s[:12]) + (' ...' if len(s) > 12 else '')))
    Ab = full - PROPOSALS['P9-pvar'][1]
    _, dsb, _ = count(Ab, frozenset({'shen-jit.eval-kl'}))
    P('\nIf one of these firings were not validated (each definition with it a residual), what it would cost'
      ' the "all but P9" forecast (%d D-src):\n' % len(dsb))
    P('| tick | definitions | of them in the forecast | forecast definitions whose closure has one |')
    P('|---|---:|---:|---:|')
    for k in ['inline-int-arg', 'share-chain', 'frozen-late-hoist', 'inline-frozen', 'let-lambda',
              'let-frozen-copy', 'trap-other']:
        s = {n for n in names if D[n]['keys'].get(k)}
        P('| `%s` | %d | %d | %d |' % (k, len(s), len(s & dsb), len({n for n in dsb if CL[n] & s})))
    rew = {'shen-jit.unify=', 'shen-jit.unify=!', 'shen.bindv', 'shen.unwind', 'shen-jit.undo', 'shen-jit.deref=',
           'shen.bind!'}
    P('\nCalls to the bind/is rewrite targets (D00\'s D_compiled\' failures): ' + ', '.join(
        '`%s` %d' % (c, sum(c in D[n]['fx'].calls for n in names)) for c in sorted(rew)))
    P('')

    # ---- TSV
    with open(out_tsv, 'w') as o:
        o.write('# hard_defs.py: census, not proof. One row per stage 0 definition, .forms order.\n')
        o.write('# at_risk: planned ticks whose task spec may not cover them (inline-int-arg has no owning task spec).\n')
        o.write('# blockers: unplanned items the definition itself needs (class:item). closure-blocked-by: '
                'definitions in its closure (not itself) that are self-blocked, up to 8, then a count.\n')
        o.write('\t'.join(['file', 'index', 'name', 'rocq_src', 'norm_nodes', 'ticks', 'in_scc', 'closure',
                           'planned_items', 'planned_coverage', 'blockers', 'decision_items',
                           'closure_blocked_by', 'status_plan', 'proposal', 'at_risk']) + '\n')
        selfblocked = {n for n in names if not D[n]['need'] <= planned}
        for n in names:
            r = D[n]
            un = sorted(r['need'] - planned)
            pl = sorted(r['need'] & planned)
            cov = sorted({cover(x).split(' ')[0] for x in pl})
            cb = sorted((CL[n] - {n}) & selfblocked)
            props = sorted({k for k, (_, it) in PROPOSALS.items() if set(un) & it})
            cbprops = sorted({k for m in cb for k, (_, it) in PROPOSALS.items() if (D[m]['need'] - planned) & it}
                             - set(props))
            if n in sA:
                st = 'validates-forecast'
            elif not un:
                st = 'callee-link'
            else:
                st = 'self-blocked'
            o.write('\t'.join([r['file'], str(r['index']), n, str(r['src']), str(r['nsize']), str(r['ticks']),
                               'yes' if n in big else 'no', str(len(CL[n]) - 1),
                               ','.join(pl) or '-', ','.join(cov) or '-',
                               ','.join('%s:%s' % (klass(x)[0], x) for x in un) or '-',
                               ','.join(sorted({klass(x)[1] for x in un})) or '-',
                               (','.join(cb[:8]) + ('...(%d)' % len(cb) if len(cb) > 8 else '')) or '-',
                               st,
                               (','.join(props) or '-') + ((' | closure:' + ','.join(cbprops)) if cbprops else ''),
                               ','.join(k for k in RISKY if r['keys'].get(k)) or '-'])
                    + '\n')

if __name__ == '__main__':
    main(*sys.argv[1:5])
