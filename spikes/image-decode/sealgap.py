# Census only (not proof): the measuring scripts of docs/SHEN-JIT-IMAGE.md.
import re,collections,sys
d=sys.argv[1]
FILES = ["toplevel","core","sys","dict","sequent","yacc","reader","prolog","track","load","writer","macros","declarations","types","t-star","init","shen-jit","lower","extension-features","extension-launcher","extension-programmable-pattern-matching","extension-namespaces","extension-expand-dynamic","extension-type-annotations"]
defs={}
for f in FILES:
    for line in open('%s/%s.sbc'%(d,f)):
        m=re.match(r'\(defun (\S+) ',line); defs[m.group(1)]=(f,line)
ext={n for n,(f,_) in defs.items() if f.startswith('extension')}
print('ext defs',len(ext))
sites=collections.Counter(); callers=set(); inl=collections.Counter()
for n,(f,line) in defs.items():
    for m in re.finditer(r'\((?:tail-)?call-sealed \d+ (?:\d+ )?(\S+) \d+\)',line):
        if m.group(1) in ext: sites[f]+=1; callers.add(n)
    for m in re.finditer(r'\(inline (\S+) \d+\)',line):
        if m.group(1) in ext: inl[f]+=1
print('sealed call sites to extension defs by caller file',dict(sites),'callers',len(callers))
print('inline markers of extension defs',dict(inl))
print('non-extension callers',sorted(c for c in callers if not defs[c][0].startswith('extension')))
