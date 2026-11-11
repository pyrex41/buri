#!/usr/bin/env python3
"""Feature census for Phase 2 (spikes/pass-split/FEATURES.md, features.tsv). CENSUS ONLY.

Python decides nothing here. It counts, per stage 0 definition, the emit features its erased normal
form needs, the front (norm/share) rewrite families that fired, the definitions it reaches through
sealed calls and inlining markers, and whether it uses identity primitives. From those it forecasts
which definitions a given feature set would admit. The forecast is a prediction about future
Rocq checkers, not evidence. The only Rocq facts it reads are the existing judge's per-definition
verdicts (judge_split.sh), and its one check is that the prediction for the current feature set
agrees with them definition by definition (src and tf).

    feature_census.py STAGE0_DIR CAPTURE_DIR JUDGE_DIR OUT_TSV [--accepted ACCEPTED_TXT]
                      [--forecast OUT_FORECAST_TSV] > FEATURES-tables.md
    feature_census.py --check-tsv FEATURES_TSV ACCEPTED_TXT

--accepted also checks the per-file Rocq src verdict counts, and the per-file current-set prediction,
against the pinned tests/shen-jit/stage0-accepted.txt. --forecast writes the per-family forecast
(spikes/pass-split/FORECAST.tsv): for each norm and emit family, the definitions predicted accepted under
the merged feature set (MERGED_FRONT, BASE) plus that family. --check-tsv repeats the current-set check
from a features.tsv alone (no capture or judge needed): its rocq_src column against the prediction
(features and required_families both empty) and the per-file sums against ACCEPTED_TXT.

Inputs: STAGE0_DIR/<f>.forms (names), CAPTURE_DIR/witness/<f>.{norm,share,ncensus} and
CAPTURE_DIR/count/<f>.ticks from capture_passes.sh, JUDGE_DIR/{src,tf}/<f>.codes from judge_split.sh.
Exit status 1 if any definition's current-set prediction disagrees with a Rocq verdict.
"""
import collections, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from stage0_to_rocq import tokens, parse

# ---------------------------------------------------------------- classification tables
# JitLowerRel.pmap (= is guarded separately, see eq_kind).
ADMITTED = {'+', '-', '*', '>', '<', '>=', '<=', 'cons', 'hd', 'tl', 'cons?', 'number?', 'string?'}
# KLSyntax.all_prims, by prim_name.
KL_PRIMS = {'intern', 'pos', 'tlstr', 'cn', 'str', 'string?', 'n->string', 'string->n', 'set', 'value',
            'simple-error', 'error-to-string', 'cons', 'hd', 'tl', 'cons?', '=', 'eval-kl', 'absvector',
            'address->', '<-address', 'absvector?', 'write-byte', 'read-byte', 'open', 'close',
            'get-time', '+', '-', '*', '/', '>', '<', '>=', '<=', 'number?'}
GLOBALS = {'value', 'set'}
IO = {'open', 'close', 'read-byte', 'write-byte', 'get-time'}
VECTOR = {'absvector', '<-address', 'address->', 'absvector?'}
ERRORS = {'simple-error': 'simple-error', 'error-to-string': 'error-to-string'}
IDENTITY = {'shen-jit.same?', 'shen-jit.tagged?', 'shen-jit.deref', 'shen-jit.deref='}
# Primitives whose result is never a real (for the "static non-real guard" option for =).
NONREAL = {'cons', 'cn', 'str', 'intern', 'tlstr', 'n->string', 'absvector', 'cons?', 'number?',
           'string?', 'absvector?', '=', '>', '<', '>=', '<=', 'shen-jit.same?', 'shen-jit.tagged?',
           'shen-jit.symbol?', 'shen-jit.integer?', 'shen-jit.vector?', 'shen-jit.pvar?',
           'char-stream?', 'shen-jit.absvector3', 'shen-jit.deref='}

# Tick keys (instrument_lower.py SITES) -> front families. dynamic-apply counts norm-apply entries,
# not a rewrite.
FAMILY_OF = {
    'share-chain': 'share',
    'sealed-inline': 'inline', 'inline-int-arg': 'inline', 'open-inline': 'inline',
    'cond': 'cond', 'type': 'sugar', 'protect': 'sugar', 'lambda-app': 'sugar',
    # JitFrontSugar rejects these and defers curried apply and multi-argument lambda application to
    # the uncurrying family; fn sugar has no rule and no owning task (none fires in the v0.6 capture)
    'lambda-app-more': 'uncurry', 'curried-apply': 'uncurry', 'fn-sealed': 'fn', 'fn-open': 'fn',
    'trap-lambda': 'trap-sugar', 'trap-other': 'trap-sugar',
    'fold-cons': 'fold-cons', 'fold-plus': 'fold-arith', 'fold-minus': 'fold-arith',
    'let-frozen-copy': 'copy', 'let-frozen-keep': 'copy', 'frozen-late-hoist': 'copy',
    'inline-frozen': 'copy', 'let-lambda': 'copy',
    'thaw': 'thaw-sugar',
    'unified-now': 'bind', 'bound-now': 'bind', 'bound-now-frozen': 'bind',
    'cut-fail': 'cut-deref', 'deref-eq': 'cut-deref',
    'eval-kl': 'eval-kl',
}
# Rewrites the existing Comp sees through when judging the source form: cond has C_cond_* rules
# with the shapes of the desugared if chain, and type has C_type. Every other family changes the
# term Comp is asked about. Calibrated, and checked definition by definition below.
SRC_TRANSPARENT_KEYS = {'cond', 'type', 'dynamic-apply'}

MARKER = 'stage0.lower.inlining'
ARG = 'stage0.lower.arg'

def atom(x):
    return x[1] if x[0] == 'atom' else None

def is_number(a):
    return a[0].isdigit() or (len(a) > 1 and a[0] in '+-.' and (a[1].isdigit() or a[1] == '.'))

def const_kind(v):
    """Kind of a (const V) datum: safe (eq_safe_val), symbol, list (folded), nan."""
    if v[0] == 'str':
        return 'safe'
    if v[0] == 'list':
        return 'safe' if not v[1] else 'list'
    a = v[1]
    if a in ('true', 'false'):
        return 'safe'
    if is_number(a):
        return 'nan' if 'nan' in a.lower() else 'safe'
    return 'symbol'

def result_kind(n):
    """Static kind of the value of normal-form node n: 'safe'/'symbol'/'list'/'nan' for a constant,
    'nonreal' when it is never a real, otherwise 'unknown'."""
    l = n[1]
    tag = atom(l[0])
    if tag == 'const':
        return const_kind(l[1])
    if tag == 'let':
        return result_kind(l[3])
    if tag == 'prim':
        return 'nonreal' if atom(l[1]) in NONREAL else 'unknown'
    if tag in ('and', 'or', 'lambda', 'freeze'):
        return 'nonreal'
    if tag == 'if':
        a, b = result_kind(l[2]), result_kind(l[3])
        return 'nonreal' if a != 'unknown' and b != 'unknown' and 'nan' not in (a, b) else 'unknown'
    return 'unknown'

def eq_kind(args):
    """Which = feature a (prim = (A B)) needs, mirroring JitLowerRel.pguard on its operands."""
    ks = [const_kind(a[1][1]) if atom(a[1][0]) == 'const' else None for a in args]
    if 'safe' in ks:
        return 'eq-safe-const', None
    if 'symbol' in ks:
        return 'eq-symbol-const', None
    rk = [result_kind(a) for a in args]
    guard = any(k in ('nonreal', 'symbol', 'list') for k in rk)
    return 'eq-two-computed', ('guarded' if guard else 'unguarded')

class Facts:
    def __init__(self):
        self.feats = set()          # emit features needed
        self.calls = set()          # names of (call F ...) targets
        self.inlined = set()        # inlining marker constants
        self.identity = set()       # identity primitives used
        self.eq = collections.Counter()
        self.marker_depth = 0       # most inlining markers stacked directly at one node
        self.fold_under_marker = 0  # a folded constant directly under a marker stack
        self.evalkl = False         # calls shen-jit.eval-kl (norm's eval-kl sugar)

def walk(n, fx, stack=0):
    l = n[1]
    tag = atom(l[0])
    def each(xs):
        for x in xs:
            walk(x, fx)
    if tag == 'const':
        if const_kind(l[1]) == 'list':
            fx.feats.add('folded-const')
            if stack:
                fx.fold_under_marker = max(fx.fold_under_marker, stack + 1)
        elif const_kind(l[1]) == 'nan':
            fx.feats.add('nan-const')
    elif tag == 'var':
        pass
    elif tag in ('if', 'and', 'or'):
        each(l[1:])
    elif tag == 'let':
        x, v, b = atom(l[1]), l[2], l[3]
        if x == MARKER:
            fx.inlined.add(atom(v[1][1]))
            fx.marker_depth = max(fx.marker_depth, stack + 1)
            walk(b, fx, stack + 1)
        elif v[0] == 'list' and atom(v[1][0]) == 'freeze':
            fx.feats.add('let-freeze')
            each([v[1][1], b])
        elif x.startswith(ARG) or (atom(v[1][0]) == 'var' and atom(v[1][1]).startswith(ARG)):
            # an inlined call's argument preamble: the call's own node continues in the body, so
            # a marker below it is stacked on the markers above
            walk(v, fx)
            walk(b, fx, stack)
        else:
            each([v, b])
    elif tag == 'do':
        fx.feats.add('do'); each(l[1:])
    elif tag in ('lambda', 'freeze'):
        fx.feats.add(tag); each([l[-1]])
    elif tag == 'trap':
        fx.feats.add('trap'); each([l[1], l[3]])
    elif tag == 'prim':
        op, args = atom(l[1]), l[2][1]
        if op == '=':
            k, g = eq_kind(args)
            fx.feats.add(k)
            if g == 'unguarded':
                fx.feats.add('eq-two-computed-unguarded')
            fx.eq[k if g is None else k + '-' + g] += 1
        elif op in ADMITTED:
            pass
        elif op in GLOBALS:
            fx.feats.add('value/set')
        elif op in IO:
            fx.feats.add('io')
        elif op in VECTOR:
            fx.feats.add('vector')
        elif op in ERRORS:
            fx.feats.add(ERRORS[op])
        elif op in KL_PRIMS:
            fx.feats.add('prim:' + op)
        else:
            fx.feats.add('port:' + op)
        if op in IDENTITY:
            fx.identity.add(op)
        each(args)
    elif tag == 'call':
        f = atom(l[1])
        fx.calls.add(f)
        if f == 'shen-jit.eval-kl':
            fx.evalkl = True   # emit sees a plain sealed call; the front family is eval-kl
        each(l[2][1])
    elif tag == 'apply':
        fx.feats.add('thaw' if len(l) == 2 else 'apply-dynamic'); each(l[1:])
    else:
        raise ValueError('not a normal form: %r' % (n,))

# what Comp admits today beyond the plain constructs: JitLowerRel.eq_safe_val takes symbols too
# since = against a symbol constant was admitted (OB-JIT-SYM-INJECTIVE)
BASE = {'eq-safe-const', 'eq-symbol-const'}

# ---------------------------------------------------------------- per-family forecast (FORECAST.tsv)
# The merged feature set the per-family forecast starts from. It is NOT the current-set model above
# (no judge runs these checkers, so row 0 and the 148 check keep BASE with cond/type transparent).
# Emit: BASE only; every Rule_X/RuleT_X/RuleO_X hook in rocq/JitEmitRule<X>.v is still empty.
# Front: the four families whose checkers are composed by JitFrontSugar.chk_front and proved sound with
# no premise but D_wf (chk_front_sound, r1-f-sugar). JitFrontProlog.bind_rule (r1-f-prolog) is proved
# sound but is not composed into a checker and covers only the bound-now shape with a literal freeze, so
# census family bind (also unified-now, bound-now-frozen) is not merged.
MERGED_FRONT = {'fam:cond', 'fam:sugar', 'fam:thaw-sugar', 'fam:trap-sugar'}
PRIM_FEATS = {'prim:' + p for p in KL_PRIMS - ADMITTED - GLOBALS - IO - VECTOR - set(ERRORS) - {'=', 'eval-kl'}}
# (row name, kind, status, items). kind: norm (front family), emit (JitEmitRule<X> family), decision
# (Reuben's call, defaults to a named residual). Each census item belongs to exactly one row besides
# the merged one. Choices: `vector` (absvector, <-address, address->, absvector?) goes to Store, whose
# header names the first three; `io` (open close read-byte write-byte get-time) goes to Prim, as there
# is no IO rule file (the remaining KL primitives); `=` on two computed operands is split into the
# guarded part (Eq) and the unguarded part plus NaN constants (decision OB-JIT-NAN-IDENTITY).
FAMILIES = [
    ('F-share', 'norm', 'open', {'fam:share'}),
    ('F-inline', 'norm', 'open', {'fam:inline'}),
    ('F-sugar', 'norm', 'merged', set(MERGED_FRONT)),
    ('F-fold', 'norm', 'open', {'fam:fold-cons', 'fam:fold-arith'}),
    ('F-copy', 'norm', 'open', {'fam:copy'}),
    ('F-bind', 'norm', 'open', {'fam:bind'}),
    ('F-cut-deref', 'norm', 'open', {'fam:cut-deref'}),
    ('F-uncurry', 'norm', 'open', {'fam:uncurry'}),
    ('F-fn', 'norm', 'unowned', {'fam:fn'}),
    ('E-Eq', 'emit', 'open', {'eq-two-computed'}),
    ('E-Store', 'emit', 'open', {'value/set', 'vector'}),
    ('E-Prim', 'emit', 'open', PRIM_FEATS | {'simple-error', 'error-to-string', 'io'}),
    ('E-DoFold', 'emit', 'open', {'do', 'folded-const'}),
    ('E-Clo', 'emit', 'open', {'lambda', 'freeze', 'let-freeze'}),
    ('E-App', 'emit', 'open', {'apply-dynamic', 'thaw'}),
    ('E-Trap', 'emit', 'open', {'trap'}),
    ('D-eq-nan', 'decision', 'decision', {'eq-two-computed', 'eq-two-computed-unguarded', 'nan-const'}),
    ('D-eval-kl', 'decision', 'decision', {'fam:eval-kl'}),
    ('D-port-identity', 'decision', 'decision', {'port:' + x for x in IDENTITY}),
    ('D-port-other', 'decision', 'decision', None),   # every other port: item, filled in from the census
]

def names_hash(ns):
    """sha256 of the names sorted by their UTF-8 bytes, each followed by LF."""
    import hashlib
    return hashlib.sha256(''.join(n + '\n' for n in sorted(ns, key=lambda x: x.encode())).encode()).hexdigest()

def read_accepted(path):
    rows = {}
    for line in open(path):
        if line.strip():
            f, a, r, u = line.split()
            rows[f] = (int(a), int(r), int(u))
    return rows

def check_accepted(pinned, got, pred, out):
    """Compare per-file (accepted, rejected, unreadable) from Rocq and the per-file predicted accepted
    count with the pinned file. Returns the number of disagreeing lines."""
    bad = 0
    for f in sorted(set(pinned) | set(got)):
        if pinned.get(f) != got.get(f):
            out('    ACCEPTED_MISMATCH rocq %s pinned %r got %r' % (f, pinned.get(f), got.get(f))); bad += 1
        if pinned.get(f, (None,))[0] != pred.get(f, 0):
            out('    ACCEPTED_MISMATCH predicted %s pinned %r predicted %d' % (f, pinned.get(f), pred.get(f, 0))); bad += 1
    return bad

def check_tsv(tsv, accepted):
    """Current-set check from features.tsv alone (census; Rocq verdicts as recorded in the tsv)."""
    got, pred, bad = collections.defaultdict(lambda: [0, 0, 0]), collections.Counter(), 0
    n = 0
    for line in open(tsv):
        if line.startswith('#') or line.startswith('definition\t'):
            continue
        c = line.rstrip('\n').split('\t')
        n += 1
        f, v = c[1], int(c[2])
        got[f][{1: 0, 2: 1, 0: 2}[v]] += 1
        p = c[5] == '-' and c[6] == '-'
        pred[f] += p
        if p != (v == 1):
            print('    MISMATCH %s rocq_src %d predicted %s' % (c[0], v, p)); bad += 1
    got = {f: tuple(x) for f, x in got.items()}
    bad += check_accepted(read_accepted(accepted), got, pred, print)
    print('check-tsv: %d definitions; rocq_src accepted %d, predicted %d; pinned %d; mismatches %d'
          % (n, sum(x[0] for x in got.values()), sum(pred.values()),
             sum(x[0] for x in read_accepted(accepted).values()), bad))
    return 1 if bad else 0

def read(path):
    return parse(tokens(open(path).read()))

def verdicts(judge, variant, f):
    lines = open(os.path.join(judge, variant, f + '.codes')).read().split('\n')
    return [int(v) for v in lines[1].split()]

# ---------------------------------------------------------------- main
def main(s0, cap, judge, out_tsv, accepted=None, forecast=None):
    files = sorted(f[:-6] for f in os.listdir(s0) if f.endswith('.forms'))
    wit, cnt = os.path.join(cap, 'witness'), os.path.join(cap, 'count')
    D = collections.OrderedDict()   # name -> record
    for f in files:
        norms = read(os.path.join(wit, f + '.norm'))
        ticks = read(os.path.join(cnt, f + '.ticks'))
        vs, vn, vt = verdicts(judge, 'src', f), verdicts(judge, 'nf', f), verdicts(judge, 'tf', f)
        assert len(norms) == len(ticks) == len(vs) == len(vn) == len(vt), f
        for i, nm in enumerate(norms):
            name = atom(nm[1][0])
            assert atom(ticks[i][1][0]) == name, (f, name)
            fx = Facts()
            walk(nm[1][2], fx)
            keys = collections.Counter()
            for kv in ticks[i][1][1][1]:
                keys[atom(kv[1][0])] += int(atom(kv[1][1]))
            fams = {FAMILY_OF[k] for k in keys if k in FAMILY_OF}
            assert set(keys) <= set(FAMILY_OF) | {'dynamic-apply'}, keys
            assert name not in D, name
            D[name] = dict(file=f, fx=fx, keys=keys, fams=fams, src=vs[i], nf=vn[i], tf=vt[i],
                           opaque={k for k in keys if k not in SRC_TRANSPARENT_KEYS})
    names = list(D)
    N = len(names)

    # ---- consistency with Rocq (current feature set)
    def emit_ok(r, S):
        return (r['fx'].feats - BASE) <= S
    mism = []
    for n in names:
        r = D[n]
        ptf = emit_ok(r, set())
        psrc = ptf and not r['opaque']
        if ptf != (r['tf'] == 1):
            mism.append(('tf', n, ptf, sorted(r['fx'].feats - BASE)))
        if psrc != (r['src'] == 1):
            mism.append(('src', n, psrc, sorted(r['fx'].feats - BASE), sorted(r['opaque'])))
        # nf (marker kept as a let): not calibrated on; the marker is a let Comp gives a slot
        # while the code gives none, so any marker rejects
        pnf = ptf and not r['fx'].inlined
        if pnf != (r['nf'] == 1):
            mism.append(('nf', n, pnf, sorted(r['fx'].feats - BASE), sorted(r['fx'].inlined)))
    acc_src = sum(D[n]['src'] == 1 for n in names)
    acc_tf = sum(D[n]['tf'] == 1 for n in names)
    acc_nf = sum(D[n]['nf'] == 1 for n in names)
    unread = sum(0 in (D[n]['src'], D[n]['nf'], D[n]['tf']) for n in names)

    P = print
    P('<!-- generated by tests/shen-jit/feature_census.py; census, not proof -->\n')
    P('## Consistency with the Rocq judge (current feature set)\n')
    P('| variant | Rocq accepted | predicted | mismatches |')
    P('|---|---:|---:|---:|')
    P('| src | %d | %d | %d |' % (acc_src, sum(emit_ok(D[n], set()) and not D[n]['opaque'] for n in names),
                                   sum(m[0] == 'src' for m in mism)))
    P('| tf | %d | %d | %d |' % (acc_tf, sum(emit_ok(D[n], set()) for n in names), sum(m[0] == 'tf' for m in mism)))
    P('| nf (held out) | %d | %d | %d |' % (acc_nf, sum(emit_ok(D[n], set()) and not D[n]['fx'].inlined for n in names),
                                            sum(m[0] == 'nf' for m in mism)))
    P('\ndefinitions: %d; unreadable (verdict 0) in src, nf or tf: %d; unexplained mismatches: %d\n'
      % (N, unread, len(mism)))
    for m in mism:
        P('    MISMATCH %r' % (m,))
    acc_bad = 0
    if accepted:
        got, pred = collections.defaultdict(lambda: [0, 0, 0]), collections.Counter()
        for n in names:
            r = D[n]
            got[r['file']][{1: 0, 2: 1, 0: 2}[r['src']]] += 1
            pred[r['file']] += emit_ok(r, set()) and not r['opaque']
        lines = []
        acc_bad = check_accepted(read_accepted(accepted), {f: tuple(x) for f, x in got.items()}, pred,
                                 lines.append)
        P('Pinned per-file src counts (`tests/shen-jit/stage0-accepted.txt`): Rocq verdicts and the current-set')
        P('prediction each agree on %d of %d files; disagreeing lines: %d\n'
          % (len(files) - len({l.split()[2] for l in lines}), len(files), acc_bad))
        for l in lines:
            P(l)

    # ---- feature usage
    allfeats = collections.Counter()
    for n in names:
        for x in D[n]['fx'].feats - BASE:
            allfeats[x] += 1
    famuse = collections.Counter(x for n in names for x in D[n]['fams'])

    # ---- sealed-callee graph
    defined = set(names)
    edges_call = {n: {c for c in D[n]['fx'].calls if c in defined and c != n} for n in names}
    edges_inl = {n: {c for c in D[n]['fx'].inlined if c in defined and c != n} for n in names}
    open_callees = collections.Counter(c for n in names for c in D[n]['fx'].calls if c not in defined)
    def closure(n, edges):
        seen, todo = {n}, [n]
        while todo:
            x = todo.pop()
            for y in edges[x]:
                if y not in seen:
                    seen.add(y); todo.append(y)
        return seen
    E_all = {n: edges_call[n] | edges_inl[n] for n in names}
    CL = {n: closure(n, E_all) for n in names}
    CL_inl = {n: closure(n, edges_inl) for n in names}
    # strongly connected components (Tarjan, iterative) of call + marker edges
    index, low, onst, st, comps, idx = {}, {}, set(), [], [], [0]
    for root in names:
        if root in index:
            continue
        work = [(root, iter(sorted(E_all[root])))]
        index[root] = low[root] = idx[0]; idx[0] += 1; st.append(root); onst.add(root)
        while work:
            v, it = work[-1]
            w = next(it, None)
            if w is not None:
                if w not in index:
                    index[w] = low[w] = idx[0]; idx[0] += 1; st.append(w); onst.add(w)
                    work.append((w, iter(sorted(E_all[w]))))
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
    big = max(comps, key=len)

    # ---- forecast: greedy cumulative order over features and families (end-to-end src -> bytecode)
    def need(r):
        # A definition whose only rewrites are cond and type is validated today directly on its
        # source form (Comp has C_cond_* and C_type), and needs no front checker. Once any other
        # rewrite fires, it goes source -> norm -> bytecode, and the front end must then justify
        # every rewrite that fired, cond and type included.
        fams = {'fam:' + FAMILY_OF[k] for k in r['keys'] if k in FAMILY_OF} if r['opaque'] else set()
        return (r['fx'].feats - BASE) | fams
    NEED = {n: need(D[n]) for n in names}
    def direct(S):
        return {n for n in names if NEED[n] <= S}
    def emit_direct(S):
        return {n for n in names if (D[n]['fx'].feats - BASE) <= S}
    def d_src(S):
        a = direct(S)
        return {n for n in a if CL[n] <= a}
    def d_low(S):
        a, e = direct(S), emit_direct(S)
        return {n for n in a if CL[n] <= e}
    def d_inl(S):
        a = direct(S)
        return {n for n in a if CL_inl[n] <= a}
    cand = sorted(set().union(*NEED.values()))
    # Decision items (FEATURES.md, "Decisions for Reuben"): each defaults to a named residual.
    DECISION = {'fam:eval-kl', 'eq-two-computed', 'eq-two-computed-unguarded', 'nan-const'} \
        | {x for x in cand if x.startswith('port:')}
    nondec = set(cand) - DECISION
    base_direct = direct(set())
    def greedy(S, pool):
        order = []
        while True:
            cur = len(direct(S))
            best = None
            for x in sorted(pool - S):
                g = len(direct(S | {x}))
                if best is None or g > best[1]:
                    best = (x, g)
            if best is None:
                break
            if best[1] == cur:
                # nothing admits more alone: take the item blocking the most still-rejected definitions
                rej = [n for n in names if not NEED[n] <= S]
                c = collections.Counter(x for n in rej for x in (NEED[n] - S) & pool)
                if not c:
                    break
                best = (max(sorted(c), key=lambda k: c[k]), cur)
            S = S | {best[0]}
            order.append((best[0], len(direct(S)), len(d_src(S)), len(d_low(S)), len(d_inl(S)),
                          len(emit_direct(S))))
        return S, order
    S1, order1 = greedy(set(), nondec)
    S2, order2 = greedy(S1, DECISION & set(cand))

    P('## Forecast: cumulative feature sets in census rank order\n')
    P('Each row adds one emit feature or front family (`fam:`) to everything above it, picked')
    P('greedily: the one that admits the most further definitions on its own (ties by name; when')
    P('none admits any alone, the one blocking the most remaining definitions). Part A ranks the')
    P('features and families that family tasks own; part B then ranks the decision items, each of')
    P('which defaults to a named residual. Columns count definitions of %d predicted to validate' % N)
    P('source -> norm -> bytecode with that set: **direct** (the definition alone), **D-src** (direct,')
    P('and every definition in its transitive sealed-callee closure direct too: a store of source')
    P('bodies with direct acceptance), **D-low** (direct, and every definition in its closure')
    P('emit-accepted on its lowered body: a lowered store), **D-inl** (as D-src, closure over the')
    P('inlining-marker edges only), and **emit** (norm -> bytecode alone, front families ignored).')
    P('Census forecast, not proof.\n')
    P('| # | added | direct | D-src | D-low | D-inl | emit |')
    P('|---:|---|---:|---:|---:|---:|---:|')
    P('| 0 | (current Comp; row 0 direct = Rocq src, emit = Rocq tf) | %d | %d | %d | %d | %d |'
      % (len(base_direct), len(d_src(set())), len(d_low(set())), len(d_inl(set())), len(emit_direct(set()))))
    for i, (x, a, b, c, d, e) in enumerate(order1, 1):
        P('| A%d | `%s` | %d | %d | %d | %d | %d |' % (i, x, a, b, c, d, e))
    for i, (x, a, b, c, d, e) in enumerate(order2, 1):
        P('| B%d | `%s` (decision) | %d | %d | %d | %d | %d |' % (i, x, a, b, c, d, e))
    P()

    P('## Feature and family usage (definitions needing each)\n')
    P('| feature or family | definitions | sole blocker |')
    P('|---|---:|---:|')
    sole = collections.Counter()
    for n in names:
        if len(NEED[n]) == 1:
            sole[next(iter(NEED[n]))] += 1
    rows = [(x, allfeats[x]) for x in allfeats] + [('fam:' + x, famuse[x]) for x in famuse]
    for x, c in sorted(rows, key=lambda kv: (-kv[1], kv[0])):
        P('| `%s` | %d | %d |' % (x, c, sole[x]))
    P()

    # ---- chain depth
    P('## Chain depth (rewrites stacked at one node; witness-structural lower bound)\n')
    P('Per definition, the most rewrites the witness shows stacked at one node: directly nested inlining')
    P('markers, plus one when a folded constant list sits directly under them. Rewrites that leave')
    P('no mark in the normal form (cond, sugar, freeze copying, bind!) are counted per definition by')
    P('the ticks (next table) but cannot be placed at a node from the capture, so this is a lower bound.\n')
    h = collections.Counter(max(D[n]['fx'].marker_depth, D[n]['fx'].fold_under_marker) for n in names)
    P('| chain depth | definitions |')
    P('|---:|---:|')
    for k in sorted(h):
        P('| %d | %d |' % (k, h[k]))
    hf = collections.Counter(len(D[n]['fams']) for n in names)
    P('\n| front families fired (per definition) | definitions |')
    P('|---:|---:|')
    for k in sorted(hf):
        P('| %d | %d |' % (k, hf[k]))
    ht = collections.Counter(sum(v for k, v in D[n]['keys'].items() if k != 'dynamic-apply') for n in names)
    buckets = [(0, 0), (1, 1), (2, 4), (5, 9), (10, 19), (20, 49), (50, 99), (100, 10**9)]
    P('\n| rewrite firings (ticks, per definition) | definitions |')
    P('|---|---:|')
    for lo, hi in buckets:
        c = sum(v for k, v in ht.items() if lo <= k <= hi)
        P('| %s | %d |' % (str(lo) if lo == hi else ('%d+' % lo if hi > 10**8 else '%d-%d' % (lo, hi)), c))
    P()

    # ---- callee closure sizes
    P('## Sealed-callee closure (call edges and inlining-marker edges to the %d stage 0 definitions)\n' % N)
    sz = collections.Counter()
    for n in names:
        s = len(CL[n]) - 1
        sz['0' if s == 0 else '1-9' if s < 10 else '10-99' if s < 100 else '100-299' if s < 300 else '300+'] += 1
    P('| closure size (excluding itself) | definitions |')
    P('|---|---:|')
    for k in ['0', '1-9', '10-99', '100-299', '300+']:
        P('| %s | %d |' % (k, sz[k]))
    szi = collections.Counter()
    for n in names:
        s_ = len(CL_inl[n]) - 1
        szi['0' if s_ == 0 else '1-9' if s_ < 10 else '10-99' if s_ < 100 else '100+'] += 1
    P('\nmarker edges only: ' + ', '.join('%s: %d' % (k, szi[k]) for k in ['0', '1-9', '10-99', '100+']))
    reach_big = sum(1 for n in names if big <= CL[n])
    P('\nlargest strongly connected component (call + marker edges): %d definitions; %d definitions'
      % (len(big), reach_big))
    P('(itself included) have it inside their closure. Other components of size > 1: %s.'
      % (', '.join(str(len(c)) for c in sorted(comps, key=len, reverse=True)[1:8] if len(c) > 1) or 'none'))
    P('Dynamic application and function-symbol constants are not edges, so every closure is a lower bound.')
    P('\ncall edges %d, inlining edges %d; calls to names outside stage 0: %d sites over %d names: %s\n'
      % (sum(map(len, edges_call.values())), sum(map(len, edges_inl.values())),
         sum(open_callees.values()), len(open_callees), ', '.join(sorted(open_callees)[:20])))

    # ---- identity
    ident = {}
    for n in names:
        fx = D[n]['fx']
        ident[n] = 'yes' if fx.identity else ('maybe' if fx.eq['eq-two-computed-unguarded'] else 'no')
    ic = collections.Counter(ident.values())
    P('## Identity dependence\n')
    P('yes: uses %s; maybe: no such primitive, but an = on two computed operands of unknown static' % ', '.join(sorted(IDENTITY)))
    P('kind (identity of heap objects or NaN may decide it); no: neither.\n')
    P('| identity | definitions |')
    P('|---|---:|')
    for k in ('yes', 'maybe', 'no'):
        P('| %s | %d |' % (k, ic[k]))
    P()

    # ---- decisions: what each option unlocks, given every non-decision feature and family
    full_minus = direct(nondec)
    P('## Decisions (counts each option unlocks)\n')
    P('Baseline: every feature and family except the decision items (%d direct; D-src %d; D-low %d).'
      % (len(full_minus), len(d_src(nondec)), len(d_low(nondec))))
    P('Each row adds only that option to the baseline. Census forecast.\n')
    P('| option | adds | direct | D-src | D-low |')
    P('|---|---|---:|---:|---:|')
    ports = {x for x in cand if x.startswith('port:')}
    idp = {'port:' + x for x in IDENTITY} & ports
    def row(label, add):
        S3 = nondec | add
        P('| %s | %s | +%d | +%d | +%d |' % (label, ', '.join('`%s`' % a for a in sorted(add)) if len(add) < 4
              else '%d features' % len(add), len(direct(S3)) - len(full_minus),
              len(d_src(S3)) - len(d_src(nondec)), len(d_low(S3)) - len(d_low(nondec))))
    row('identity port primitives', idp)
    row('port primitives other than identity', ports - idp)
    row('all port primitives', ports)
    row('eval-kl (shipped checker)', {'fam:eval-kl'} & set(cand))
    row('NaN `=`: residual (default)', set())
    row('NaN `=`: static non-real guard', {'eq-two-computed'})
    row('NaN `=`: model NaN identity', {'eq-two-computed', 'eq-two-computed-unguarded'})
    row('all decision items', DECISION & set(cand))
    P()
    alld = nondec | (DECISION & set(cand))
    P('Leave one out: every decision item admitted except the named group (what that group costs).\n')
    P('| all decision items except | direct | D-src | D-low |')
    P('|---|---:|---:|---:|')
    def loo(label, drop):
        S3 = alld - drop
        P('| %s | -%d | -%d | -%d |' % (label, len(direct(alld)) - len(direct(S3)),
              len(d_src(alld)) - len(d_src(S3)), len(d_low(alld)) - len(d_low(S3))))
    loo('identity port primitives', idp)
    loo('port primitives other than identity', ports - idp)
    loo('eval-kl', {'fam:eval-kl'})
    loo('NaN `=` (residual: both two-computed items)', {'eq-two-computed', 'eq-two-computed-unguarded'})
    loo('NaN `=` unguarded only (static non-real guard chosen)', {'eq-two-computed-unguarded'})
    P()
    big_res = collections.Counter()
    for n in big:
        for x in NEED[n] & DECISION:
            big_res[x] += 1
    P('Decision items needed inside the largest component (%d definitions): %s.\n'
      % (len(big), ', '.join('`%s` %d' % kv for kv in sorted(big_res.items(), key=lambda kv: (-kv[1], kv[0])))))

    # ---- residuals by reason under the all-non-decision set
    P('## Residuals by reason (all non-decision features and families admitted)\n')
    P('Each definition still rejected is listed under the first decision item it needs, in this order:')
    P('eval-kl, port primitives (identity first), = on two computed operands.\n')
    reasons = collections.OrderedDict()
    def reason(n):
        nd = NEED[n] - nondec
        if 'fam:eval-kl' in nd:
            return 'eval-kl'
        if nd & idp:
            return 'identity port primitive'
        if nd & ports:
            return 'port primitive ' + ', '.join(sorted(x[5:] for x in nd & ports)[:3])
        if 'eq-two-computed' in nd:
            return '= on two computed operands' + (' (unguarded)' if 'eq-two-computed-unguarded' in nd
                                                    else ' (static non-real guard applies)')
        return 'other: ' + ', '.join(sorted(nd))
    res = collections.defaultdict(list)
    for n in names:
        if n not in full_minus:
            res[reason(n)].append(n)
    P('| reason | definitions | examples |')
    P('|---|---:|---|')
    for k, v in sorted(res.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        P('| %s | %d | %s |' % (k, len(v), ', '.join('`%s`' % x for x in v[:4])))
    P('\nresidual total: %d\n' % sum(map(len, res.values())))

    # ---- per-family forecast (merged features plus one family)
    if forecast:
        fams = [list(x) for x in FAMILIES]
        ports = {x for x in cand if x.startswith('port:')}
        for x in fams:
            if x[3] is None:
                x[3] = ports - {'port:' + i for i in IDENTITY}
        covered = set().union(*(x[3] for x in fams)) | BASE
        assert set(cand) <= covered, 'items in no family row: %r' % sorted(set(cand) - covered)
        own = collections.Counter(i for x in fams if x[0] != 'D-eq-nan' for i in x[3])
        assert all(v == 1 for v in own.values()), own
        M = set(MERGED_FRONT)
        def sets(S):
            return {'src': {n for n in emit_direct(S) if not D[n]['opaque']}, 'direct': direct(S), 'nf': {n for n in emit_direct(S) if not D[n]['fx'].inlined},
                    'tf': emit_direct(S)}
        base = sets(M)
        assert base['direct'] == direct(set()) | {n for n in names if NEED[n] <= M}
        with open(forecast, 'w') as o:
            w = o.write
            w('# FORECAST.tsv: census, not proof. Generated by tests/shen-jit/feature_census.py --forecast; do not edit.\n')
            w('# Per family: the stage 0 definitions (of %d) predicted accepted under the merged feature set plus\n' % N)
            w('# that family alone, for the family tasks\' count floor. A prediction from a syntactic walk of the\n')
            w('# untrusted norm witness and the count-run ticks; Rocq decides acceptance. Nothing here is validated.\n')
            w('# merged set: emit BASE (Comp today: %s; every JitEmitRule<X> hook empty);\n' % ', '.join(sorted(BASE)))
            w('#   front %s (JitFrontSugar.chk_front, chk_front_sound).\n' % ', '.join(sorted(M)))
            w('# variants: src = what the existing source judge (JitLowerStage0.judge on <f>.forms, judge_split.sh src)\n')
            w('#   would accept with the set\'s emit features in Comp (cond, type, dynamic-apply transparent; any other\n')
            w('#   rewrite rejects); row "merged" src is the current-set prediction, %d (Rocq src: %d).\n'
              % (len(base['src']), acc_src))
            w('#   direct = source -> norm -> bytecode (emit features and required front families within the set;\n')
            w('#   row "merged" direct is %d: the src set plus %d needing only merged front families);\n'
              % (len(base['direct']), len(base['direct'] - base['src'])))
            w('#   nf = emit only, on the erased normal form with markers (judge_split.sh nf); tf = emit only,\n')
            w('#   markers dropped (judge_split.sh tf). new = definitions in the set and not in row "merged".\n')
            w('# sha256: of the definition names sorted by UTF-8 bytes, each followed by LF (definitions column).\n')
            w('# status: merged (in the merged set), open (owning task not landed), decision (Reuben\'s call; defaults\n')
            w('#   to a named residual), unowned (no rule and no task). Single-family rows: a definition needing two\n')
            w('#   non-merged families is in neither row.\n')
            w('family\tkind\tstatus\titems\tvariant\tcount\tnew\tsha256\tnew_definitions\tdefinitions\n')
            rows = [('merged', 'baseline', 'merged', set())] + [tuple(x) for x in fams]
            for name, kind, status, items in rows:
                ss = sets(M | items)
                for v in ('src', 'direct', 'nf', 'tf'):
                    st, nw = ss[v], ss[v] - base[v]
                    k = lambda x: x.encode()
                    w('%s\t%s\t%s\t%s\t%s\t%d\t%d\t%s\t%s\t%s\n' % (
                        name, kind, status, ','.join(sorted(items)) or '-', v, len(st), len(nw), names_hash(st),
                        ','.join(sorted(nw, key=k)) or '-', ','.join(sorted(st, key=k)) or '-'))

    # ---- TSV
    with open(out_tsv, 'w') as o:
        o.write('# feature_census.py: census, not proof. One row per stage 0 definition.\n')
        o.write('# Columns: see spikes/pass-split/FEATURES.md, "features.tsv". Verdicts: 1 accepted, 2 rejected.\n')
        o.write('definition\tfile\trocq_src\trocq_nf\trocq_tf\tfeatures\trequired_families\tfired_families'
                '\tidentity\tbig_scc\tclosure_all\tclosure_marker\tinlined\n')
        for n in names:
            r = D[n]
            fams_req = sorted(x[4:] for x in NEED[n] if x.startswith('fam:'))
            o.write('%s\t%s\t%d\t%d\t%d\t%s\t%s\t%s\t%s\t%s\t%d\t%d\t%s\n' % (
                n, r['file'], r['src'], r['nf'], r['tf'], ','.join(sorted(r['fx'].feats - BASE)) or '-',
                ','.join(fams_req) or '-', ','.join(sorted(r['fams'])) or '-', ident[n],
                'yes' if n in big else 'no', len(CL[n]) - 1, len(CL_inl[n]) - 1,
                ','.join(sorted(r['fx'].inlined)) or '-'))
    return 1 if mism or acc_bad else 0

if __name__ == '__main__':
    a = sys.argv[1:]
    if a and a[0] == '--check-tsv':
        sys.exit(check_tsv(a[1], a[2]))
    opts = {}
    while len(a) > 4 and a[-2] in ('--accepted', '--forecast'):
        opts[a[-2][2:]] = a[-1]; a = a[:-2]
    sys.exit(main(*a[:4], **opts))
