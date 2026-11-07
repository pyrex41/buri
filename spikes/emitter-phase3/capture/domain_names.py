#!/usr/bin/env python3
"""Lists stage 0 functions whose bytecode is in the function checker's domain, with arity. usage: domain_names.py STAGE0"""
import glob, sys, re
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0] + '/..')
exec(open(sys.argv[0].rsplit('/', 1)[0] + '/../census.py').read().split('ops=collections.Counter()')[0])
DOM = {'move', 'const', 'label', 'jump', 'jump-if-false', 'return'}
PR = {'cons?', 'hd', 'tl', 'cons', '='}
for n, c, f in funcs:
    if all(i[0] in DOM or (i[0] == 'prim' and i[2] in PR) for i in body(c)):
        print(n, c[2], len(body(c)))
