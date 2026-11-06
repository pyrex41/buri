#!/usr/bin/env python3
"""Turn tests/shen-jit/capture.shen output into a Rocq file of cases. This only packages
bytes: Rocq runs the cases and computes every verdict.

    gen_diff.py CAPTURE STAGE0-DIR OUT.v [--sealed-only]
"""
import re, struct, sys, glob, os
sys.setrecursionlimit(1000000)

def real_bits(text):
    if 'nan' in text: return 0x7FF8000000000000
    if 'inf' in text:
        return 0xFFF0000000000000 if text.startswith('-') else 0x7FF0000000000000
    return struct.unpack('<Q', struct.pack('<d', float(text)))[0]

# --- canonical text, as capture.shen prints it, to a term tree
def parse_canon(s, i=0):
    c = s[i]
    if c == '(':
        a, i = parse_canon(s, i + 1)
        assert s[i] == ' '
        d, i = parse_canon(s, i + 1)
        assert s[i] == ')'
        return ('pair', a, d), i + 1
    if c == '"':
        j = s.index('"', i + 1)
        return ('str', s[i + 1:j]), j + 1
    if c in 'TFN':
        return ({'T': ('bool', True), 'F': ('bool', False), 'N': ('nil',)}[c]), i + 1
    j = i
    while j < len(s) and s[j] not in ' )]':
        j += 1
    tok = s[i:j]
    if c == 'n':
        body = tok[1:]
        if re.fullmatch(r'-?\d+', body): return ('fix', int(body)), j
        return ('real', real_bits(body)), j
    if c == 's': return ('sym', tok[1:]), j
    if c == 'V': return ('pvar', int(tok[1:])), j
    if c == '[': raise ValueError('vector')
    raise ValueError('unsupported ' + tok)

def term(t):
    # iterative along list tails, so long lists stay on one line and shallow
    out, tail = [], t
    while tail[0] == 'pair':
        out.append(term(tail[1])); tail = tail[2]
    if out:
        return '(' + ' ;; '.join(out + [term(tail)]) + ')'
    k = t[0]
    if k == 'nil': return 'VNil'
    if k == 'bool': return '(VBool %s)' % ('true' if t[1] else 'false')
    if k == 'fix': return '(VFix (%d)%%Z)' % t[1]
    if k == 'real': return '(VReal %d%%N)' % t[1]
    if k == 'sym': return '(yx "%s")' % t[1]
    if k == 'str': return '(sx "%s")' % t[1]
    if k == 'pvar': return '(VPvar %d%%Z)' % t[1]
    raise ValueError(k)

# --- stage 0 text: (defun Name (code ...))
TOK = re.compile(r'\s*(\(|\)|"(?:[^"\\]|\\.)*"|[^\s()"]+)')
def parse_sbc_line(line):
    pos, stack, cur = 0, [], None
    while True:
        m = TOK.match(line, pos)
        if not m: break
        tok, pos = m.group(1), m.end()
        if tok == '(':
            stack.append([])
        elif tok == ')':
            done = stack.pop()
            if stack: stack[-1].append(done)
            else: return done
        else:
            stack[-1].append(atom(tok))
def unescape(s):
    return re.sub(rb'\\x([0-9a-fA-F]{2})|\\(.)', lambda m: bytes([int(m.group(1), 16)]) if m.group(1) else m.group(2), s.encode('latin1'))
def hexs(b): return b.hex()
def atom(tok):
    if tok.startswith('"'): return ('str', hexs(unescape(tok[1:-1])))
    if re.fullmatch(r'-?\d+', tok): return ('fix', int(tok))
    if re.fullmatch(r'-?\d*\.\d+(e-?\d+)?|-?\d+e-?\d+|[-+]inf\.0|\+nan\.0', tok): return ('real', real_bits(tok))
    if tok == 'true': return ('bool', True)
    if tok == 'false': return ('bool', False)
    return ('sym', hexs(tok.encode('latin1')))
def to_tree(x):
    if isinstance(x, list):
        t = ('nil',)
        for e in reversed(x): t = ('pair', to_tree(e), t)
        return t
    return x

CALLS = {'call': 3, 'call-sealed': 3, 'tail-call': 2, 'tail-call-sealed': 2, 'inline': None}
def sym_name(h): return bytes.fromhex(h).decode('latin1')
def tree_list(t):
    out = []
    while t[0] == 'pair':
        out.append(t[1]); t = t[2]
    return out
def callees(code_tree, acc):
    """Names called by a code object and its nested codes. ('code', name, arity, frame, consts, ins, codes, inl)"""
    parts = tree_list(code_tree)
    if len(parts) < 7: return
    for ins in tree_list(parts[5]):
        i = tree_list(ins)
        if i and i[0][0] == 'sym':
            op = sym_name(i[0][1])
            k = CALLS.get(op)
            if k is not None and i[k][0] == 'sym': acc.add(sym_name(i[k][1]))
    for c in tree_list(parts[6]): callees(c, acc)
    inl = parts[7:] 
def main():
    capture, stage0, out = sys.argv[1:4]
    defs = {}
    for f in sorted(glob.glob(os.path.join(stage0, '*.sbc'))):
        for line in open(f, encoding='latin1'):
            if line.startswith('(defun'):
                form = parse_sbc_line(line)
                defs[sym_name(form[1][1])] = to_tree(form)
    cases, unsupported, lowerr, atoms = [], 0, 0, 0
    lines = open(capture, encoding='latin1').read().split('\n')
    i, idx = 0, 0
    pending, skipped = None, []
    glob_lines = []
    for ln in lines:
        tag, _, rest = ln.partition(' ')
        if tag == '@lowerr': lowerr += 1; idx += 1
        elif tag == '@atom': atoms += 1; idx += 1
        elif tag == '@code': pending = rest
        elif tag == '@global': glob_lines.append(rest)
        elif tag in ('@ok', '@err'):
            idx += 1
            try:
                form, _ = parse_canon(pending)
                cases.append((idx, form, tag == '@ok', rest))
            except ValueError as e:
                unsupported += 1; skipped.append((idx, str(e)))
            pending = None
    # stage 0 closure
    need, seen = set(), set()
    locally = set()
    for _, form, _, _ in cases:
        parts = tree_list(form)
        if parts and parts[0][0] == 'sym' and sym_name(parts[0][1]) == 'defun':
            locally.add(sym_name(parts[1][1]))
            callees(parts[2], need)
        else:
            callees(form, need)
    order, todo = [], sorted(need)
    while todo:
        n = todo.pop()
        if n in seen or n not in defs: continue
        seen.add(n); order.append(n)
        s = set(); callees(tree_list(defs[n])[2], s); todo.extend(sorted(s - seen))
    with open(out, 'w') as f:
        f.write('(* Generated by tests/shen-jit/gen_diff.py from a capture. Not a hand-maintained file. *)\n')
        f.write('From Coq Require Import List ZArith NArith String.\nFrom Buri Require Import JitBytecode.\nFrom JitDiff Require Import JitDiffLib.\n')
        f.write('Import ListNotations JitBytecode.JitBytecode JitDiffLib.JitDiffLib.\nLocal Open Scope string_scope.\n')
        for k, n in enumerate(order):
            f.write('Definition d%d : val := %s.\n' % (k, term(defs[n])))
        f.write('Definition defs : list val := [%s].\n' % '; '.join('d%d' % k for k in range(len(order))))
        f.write('Definition sealed_names : list string := [%s].\n' % '; '.join('"%s"' % n.encode('latin1').hex() for n in sorted(defs)))
        gs = []
        for g in glob_lines:
            name, _, v = g.partition(' ')
            try:
                gs.append('("%s", %s)' % (sym_name(name).replace('"', '""'), term(parse_canon(v)[0])))
            except (ValueError, IndexError, AssertionError):
                pass
        f.write('Definition globals : list (string * val) := [%s].\n' % ';\n '.join(gs))
        for idx_, form, ok, exp in cases:
            f.write('Definition c%d : val := %s.\n' % (idx_, term(form)))
        f.write('Definition cases : list (val * bool * string) :=\n [%s].\n' % ';\n  '.join(
            '(c%d, %s, "%s")' % (ix, 'true' if ok else 'false', exp.replace('"', '""')) for ix, _, ok, exp in cases))
        f.write('Definition ids : list nat := [%s]%%nat.\n' % '; '.join(str(c[0]) for c in cases))
    print('cases', len(cases), 'lowering-errors', lowerr, 'atoms', atoms, 'unsupported', unsupported, 'stage0-closure', len(order),
          'unresolved', sorted(need - set(defs) - locally)[:20], 'skipped', skipped[:10])
main()
