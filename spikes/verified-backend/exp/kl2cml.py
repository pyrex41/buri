#!/usr/bin/env python3
"""Spike 10 prototype: translate a KLambda fragment into CakeML source over one tagged value type.

UNVERIFIED. This is the shape of the code generator a CakeML route would prove (cf. CakeML's
compiler/scheme/scheme_to_cakeScript.sml, which is verified). It covers the Phase 2 fragment only:
integer/string/symbol/boolean/nil literals, variables, let, if, cond, and, or, the primitives
+ - * > < >= <= = cons hd tl cons? simple-error, and named calls and tail calls to functions
defined in the same file. Calls are direct: each defun becomes one CakeML function, so this assumes
the store's function cell for f is f's own code (Phase 2's FunRel premise); redefinition at run time
would need an indirect call through a cell, not done here.

KLambda evaluates arguments left to right; CakeML right to left. So every call or primitive whose
arguments are not all atoms binds them in order with `let val`.

    kl2cml.py DEFS.kl ... > out.cml
"""
import re, sys

def tokens(t):
    i = 0
    while i < len(t):
        c = t[i]
        if c.isspace(): i += 1
        elif c in '()': yield c; i += 1
        elif c == '"':
            j = i + 1
            while t[j] != '"': j += 1
            yield ('str', t[i + 1:j]); i = j + 1
        else:
            j = i
            while j < len(t) and not t[j].isspace() and t[j] not in '()"': j += 1
            yield t[i:j]; i = j

def parse(t):
    st = [[]]
    for k in tokens(t):
        if k == '(': st.append([])
        elif k == ')': x = st.pop(); st[-1].append(x)
        else: st[-1].append(k)
    return st[0]

PRIM2 = {'+': 'kl_add', '-': 'kl_sub', '*': 'kl_mul', '>': 'kl_gt', '<': 'kl_lt', '>=': 'kl_ge',
         '<=': 'kl_le', '=': 'kl_eqv', 'cons': 'KCons'}
PRIM1 = {'hd': 'kl_hd', 'tl': 'kl_tl', 'cons?': 'kl_consp', 'simple-error': 'kl_error'}

def ident(s, pre):
    return pre + re.sub(r'[^A-Za-z0-9]', lambda m: '_%02x' % ord(m.group()), s)

def cml_str(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n') + '"'

class Gen:
    def __init__(self, funs): self.funs, self.n = funs, 0
    def fresh(self): self.n += 1; return 't%d' % self.n
    def atom(self, e, env):
        if isinstance(e, tuple): return '(KStr ' + cml_str(e[1]) + ')'
        if isinstance(e, list):
            return 'KNil' if e == [] else None
        if re.fullmatch(r'-?[0-9]+', e): return '(KInt (%s))' % (e if e[0] != '-' else '~' + e[1:])
        if e in env: return env[e]
        if e in ('true', 'false'): return '(KBool ' + ('True' if e == 'true' else 'False') + ')'
        return '(KSym ' + cml_str(e) + ')'
    def args(self, es, env, k):
        """Evaluate es left to right, then k(list of atoms)."""
        binds, atoms = [], []
        for e in es:
            a = self.atom(e, env)
            if a is None:
                t = self.fresh(); binds.append('val %s = %s' % (t, self.exp(e, env))); a = t
            atoms.append(a)
        body = k(atoms)
        return body if not binds else '(let %s in %s end)' % (' '.join(binds), body)
    def test(self, e, env): return '(kl_test %s)' % self.exp(e, env)
    def exp(self, e, env):
        a = self.atom(e, env)
        if a is not None: return a
        h, *r = e
        if h == 'let':
            x = ident(r[0], 'v_'); x2 = x + '_' + str(self.n); self.n += 1
            return '(let val %s = %s in %s end)' % (x2, self.exp(r[1], env), self.exp(r[2], {**env, r[0]: x2}))
        if h == 'if':
            return '(if %s then %s else %s)' % (self.test(r[0], env), self.exp(r[1], env), self.exp(r[2], env))
        if h == 'cond':
            out = '(raise (KlErr "cond failure"))'
            for c, b in reversed(r):
                out = '(if %s then %s else %s)' % (self.test(c, env), self.exp(b, env), out)
            return out
        if h == 'and': return '(KBool (%s andalso %s))' % (self.test(r[0], env), self.test(r[1], env))
        if h == 'or': return '(KBool (%s orelse %s))' % (self.test(r[0], env), self.test(r[1], env))
        if h in PRIM2 and len(r) == 2:
            f = PRIM2[h]
            return self.args(r, env, lambda xs: '(%s %s %s)' % (f, xs[0], xs[1]))
        if h in PRIM1 and len(r) == 1:
            return self.args(r, env, lambda xs: '(%s %s)' % (PRIM1[h], xs[0]))
        if h in self.funs:
            if len(r) != self.funs[h]: return '(raise (KlErr "arity"))'
            fn = ('(!%s)' % ident(h, 'c_')) if CELLS else ident(h, 'f_')
            return self.args(r, env, lambda xs: '(%s %s)' % (fn, ' '.join(xs) if xs else '()'))
        raise SystemExit('not in fragment: %r' % (e,))

PRELUDE = r'''
datatype kv = KInt int | KSym string | KStr string | KBool bool | KNil | KCons kv kv;
exception KlErr string;
fun kl_test v = case v of KBool b => b | _ => raise KlErr "not a boolean";
fun kl_num2 f a b = case (a, b) of (KInt x, KInt y) => f x y | _ => raise KlErr "not a number";
fun kl_add a b = kl_num2 (fn x => fn y => KInt (x + y)) a b;
fun kl_sub a b = kl_num2 (fn x => fn y => KInt (x - y)) a b;
fun kl_mul a b = kl_num2 (fn x => fn y => KInt (x * y)) a b;
fun kl_gt a b = kl_num2 (fn x => fn y => KBool (x > y)) a b;
fun kl_lt a b = kl_num2 (fn x => fn y => KBool (x < y)) a b;
fun kl_ge a b = kl_num2 (fn x => fn y => KBool (x >= y)) a b;
fun kl_le a b = kl_num2 (fn x => fn y => KBool (x <= y)) a b;
fun kl_eq a b = case (a, b) of
    (KInt x, KInt y) => x = y | (KSym x, KSym y) => x = y | (KStr x, KStr y) => x = y
  | (KBool x, KBool y) => x = y | (KNil, KNil) => True
  | (KCons a1 d1, KCons a2 d2) => kl_eq a1 a2 andalso kl_eq d1 d2
  | _ => False;
fun kl_eqv a b = KBool (kl_eq a b);
fun kl_hd v = case v of KCons a _ => a | _ => raise KlErr "hd: not a pair";
fun kl_tl v = case v of KCons _ d => d | _ => raise KlErr "tl: not a pair";
fun kl_consp v = case v of KCons _ _ => KBool True | _ => KBool False;
fun kl_error v = case v of KStr s => raise KlErr s | _ => raise KlErr "simple-error: not a string";
'''

# Variant (KL2CML_FO=1): first-order arithmetic, no closures passed through kl_num2.
FO = r'''
fun kl_add a b = case a of KInt x => (case b of KInt y => KInt (x + y) | _ => raise KlErr "not a number") | _ => raise KlErr "not a number";
fun kl_sub a b = case a of KInt x => (case b of KInt y => KInt (x - y) | _ => raise KlErr "not a number") | _ => raise KlErr "not a number";
fun kl_mul a b = case a of KInt x => (case b of KInt y => KInt (x * y) | _ => raise KlErr "not a number") | _ => raise KlErr "not a number";
fun kl_gt a b = case a of KInt x => (case b of KInt y => KBool (x > y) | _ => raise KlErr "not a number") | _ => raise KlErr "not a number";
fun kl_lt a b = case a of KInt x => (case b of KInt y => KBool (x < y) | _ => raise KlErr "not a number") | _ => raise KlErr "not a number";
fun kl_ge a b = case a of KInt x => (case b of KInt y => KBool (x >= y) | _ => raise KlErr "not a number") | _ => raise KlErr "not a number";
fun kl_le a b = case a of KInt x => (case b of KInt y => KBool (x <= y) | _ => raise KlErr "not a number") | _ => raise KlErr "not a number";
'''

# Variant (KL2CML_CELLS=1): every named call goes through a mutable function cell, as KLambda's
# redefinable global function namespace requires.
CELLS = bool(__import__('os').environ.get('KL2CML_CELLS'))

def main():
    import os
    global PRELUDE
    if os.environ.get('KL2CML_FO'):
        PRELUDE = '\n'.join(l for l in PRELUDE.split('\n')
                            if not l.startswith(('fun kl_add', 'fun kl_sub', 'fun kl_mul', 'fun kl_gt', 'fun kl_lt', 'fun kl_ge', 'fun kl_le'))) + FO
    forms = []
    for p in sys.argv[1:]: forms += parse(open(p).read())
    funs = {f[1]: len(f[2]) for f in forms if f[0] == 'defun'}
    g = Gen(funs)
    out = []
    for f in forms:
        _, name, ps, body = f
        env = {p: ident(p, 'v_') for p in ps}
        out.append('%s %s = %s' % (ident(name, 'f_'), ' '.join(env[p] for p in ps) or '()', g.exp(body, env)))
    cells = ''
    if CELLS:
        for f in forms:
            n = len(f[2]); ty = ' -> '.join(['kv'] * (n + 1)) if n else 'unit -> kv'
            lam = ''.join('fn (x%d : kv) => ' % i for i in range(n)) if n else 'fn () => '
            cells += 'val %s = Ref (%s(raise KlErr "undefined") : %s);\n' % (ident(f[1], 'c_'), lam, 'kv')
    sets = ''.join('val _ = %s := %s;\n' % (ident(f[1], 'c_'), ident(f[1], 'f_')) for f in forms) if CELLS else ''
    print(PRELUDE + cells + 'fun ' + '\nand '.join(out) + ';\n' + sets)

if __name__ == '__main__': main()
