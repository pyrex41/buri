#!/usr/bin/env python3
"""Expand constructor-pattern shorthands in an F* template.

    %%KD_let 24=kc 17=me%%  ->  KD_let _ _ ... kc ...   (arity from the constructor's declaration)

Arities are read from the F* sources given after the template (Buri.JitLowerKont.fst and others),
so a pattern cannot have the wrong number of arguments. Usage: expand_patterns.py TEMPLATE OUT SRC...
"""
import re, sys
def arities(files):
    ar = {}
    for f in files:
        s = open(f).read()
        for m in re.finditer(r'\|\s+([A-Z][A-Za-z_0-9]*)\s*:(.*?)(?=\n\s*\||\nand |\nnoeq|\n\n|\Z)', s, re.S):
            body = m.group(2); depth = 0; n = 0; i = 0
            while i < len(body) - 1:
                ch = body[i]
                if ch in '([{': depth += 1
                elif ch in ')]}': depth -= 1
                elif body[i:i+2] == '->' and depth == 0: n += 1; i += 1
                i += 1
            ar[m.group(1)] = n
    return ar
tpl, out, *srcs = sys.argv[1:]
ar = arities(srcs)
def rep(m):
    parts = m.group(1).split()
    name = parts[0]; n = ar[name]; args = ['_'] * n
    for p in parts[1:]:
        k, v = p.split('=')
        args[int(k) - 1] = v
    return name + (' ' + ' '.join(args) if n else '')
text = re.sub(r'%%(.*?)%%', rep, open(tpl).read())
open(out, 'w').write(text)
