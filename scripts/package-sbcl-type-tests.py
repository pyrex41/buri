#!/usr/bin/env python3
"""E2E-21 SBCL host-operation capture packaging (packaging only).

Reads the pinned SBCL 2.6.8 sources and the image capture of the arm64 code
the pinned aarch64 SBCL emits for the host operations of
CLContracts.cl_host_ops, refuses any input whose sha256 differs from its
pin, and writes rocq/SbclTypeTests.v containing only definitions of
integers and integer lists:

  code_<case>        the raw 32-bit instruction words, from the simple-fun
                     entry to the end of the code text, as read from the code
                     object by sbcl-type-tests.lisp (not the disassembler text);
  tv_<name>          type-code lists named by define-type-vop forms of
                     generic/type-vops.lisp and type-vop-macros.lisp, as lists of
                     SbclLayout source constants (src_ prefix);
  srcflag_<name>     1 iff a quoted generator or genesis line occurs verbatim
                     exactly once in the pinned source, else 0.

This script decides nothing about theorems. Decoding the instruction words,
running them, and every agreement between the capture and the sources are
Rocq definitions and lemmas (SbclA64.v, SbclTests.v).

usage: package-sbcl-type-tests.py OUTDIR   (writes OUTDIR/SbclTypeTests.v)
"""
import hashlib
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

PINS = {
    # SBCL 2.6.8 source tarball sha256 ad5126df...; files copied unchanged:
    # src/compiler/arm64/type-vops.lisp, src/compiler/arm64/pred.lisp,
    # src/compiler/generic/type-vops.lisp, src/compiler/type-vop-macros.lisp,
    # src/compiler/generic/genesis.lisp.
    'ports/repr/sbcl/arm64-type-vops.lisp': 'b1b0a0ad8cb6fd45efca3d716a247ba04cfcf899dc737aae46b491f9b587fea5',
    'ports/repr/sbcl/arm64-pred.lisp': 'b664bbbae7e041a4aeef7defb5a461e2f6c0a27cc4eff6eee42bc62e6a76c4f0',
    'ports/repr/sbcl/generic-type-vops.lisp': '3ced2a91f8f30fe24f7aa12155a577ddc657555225a4ea6b3f94c2a19b270f59',
    'ports/repr/sbcl/type-vop-macros.lisp': '6a61679ca53b9c30f6fc5904d022927cb78f7d07e50541f19d0804a4da1ae934',
    'ports/repr/sbcl/genesis.lisp': '4fc64cafe89fc8bc7304f08a49b8d911b75a0364cf83a9f5fd626fa36830ba73',
    'ports/repr/sbcl/early-objdef.lisp': 'c160facbaf0447828846b111d33b984c50265c06b39a203174ff534c1cb97aa3',
    # Image capture under qemu-aarch64 of the pinned aarch64 SBCL; see README.
    'ports/repr/sbcl/sbcl-type-tests.lisp': None,
    'ports/repr/sbcl/sbcl-2.6.8-arm64-type-tests.capture': None,
}
PINS_FILE = 'ports/repr/SHA256SUMS'

CASES = ['eq', 'typep-fixnum', 'integerp', 'numberp', 'consp', 'stringp', 'arrayp',
         'symbolp', 'not', 'null', 'string=', 'equal', 'eql', 'num-eq']

# Generator and genesis lines whose presence the Rocq lemmas cite.
FLAGS = [
    ('consp_vop', 'ports/repr/sbcl/arm64-type-vops.lisp',
     '(define-vop (consp type-predicate)\n  (:translate consp)\n  (:conditional :ne)\n  (:info)\n'
     '  (:generator 8\n    (inst and temp value lowtag-mask)\n    (inst cmp temp list-pointer-lowtag)\n'
     '    (inst ccmp value null-tn :eq 4)))'),
    ('symbolp_vop_nil_first', 'ports/repr/sbcl/arm64-type-vops.lisp',
     '(define-vop (symbolp type-predicate)\n  (:translate symbolp)\n  (:generator 12\n'
     '    (unless (other-pointer-tn-ref-p args t)\n      (inst cmp value null-tn)\n'
     '      (inst b :eq (if not-p drop-thru target)))\n    (test-type value temp target not-p (symbol-widetag)\n'
     '               :value-tn-ref args)\n    drop-thru))'),
    ('fixnump_vop', 'ports/repr/sbcl/arm64-type-vops.lisp',
     '(define-vop (fixnump)\n  (:translate fixnump)\n  (:arg-refs arg-ref)\n'
     '  (:args (value :scs (any-reg descriptor-reg)))\n  (:conditional :eq)\n  (:policy :fast-safe)\n'
     '  (:generator 4\n    (inst tst value n-fixnum-tag-bits)))'),
    ('test_fixnum_tbz', 'ports/repr/sbcl/arm64-type-vops.lisp',
     '    (if not-p\n        (inst tbnz* value 0 target)\n        (inst tbz* value 0 target))))'),
    ('if_eq_translate_eq', 'ports/repr/sbcl/arm64-pred.lisp',
     '  (:conditional :eq)\n  (:policy :fast-safe)\n  (:translate eq)'),
    ('if_eq_cmp', 'ports/repr/sbcl/arm64-pred.lisp',
     '            ((or (not (integerp value))\n                 (add-sub-immediate-p value))\n'
     '             (inst cmp x value))'),
    ('nil_symbol_header_widetag', 'ports/repr/sbcl/genesis.lisp',
     '        (write-wordindexed/raw des 1 sb-vm:symbol-widetag)'),
    ('nil_car_is_nil', 'ports/repr/sbcl/genesis.lisp',
     '        (write-wordindexed nil-val 0 nil-val)'),
    ('nil_cdr_is_nil', 'ports/repr/sbcl/genesis.lisp',
     '        (write-wordindexed nil-val 1 nil-val)'),
    ('nil_val_offset', 'ports/repr/sbcl/genesis.lisp',
     '         (nil-val (make-descriptor (+ (descriptor-bits des)\n'
     '                                      (* 2 sb-vm:n-word-bytes)\n'
     '                                      (- sb-vm:list-pointer-lowtag'),
    ('fixnum_lowtags_even', 'ports/repr/sbcl/early-objdef.lisp',
     "(defconstant-eqx fixnum-lowtags\n    '#.(loop for i from 0 to lowtag-mask\n"
     "             when (zerop (logand i fixnum-tag-mask)) collect i)"),
    ('other_pointer_vops_symbolp', 'ports/repr/sbcl/generic-type-vops.lisp',
     '  `(symbolp (,symbol-widetag)))'),
]

# define-type-vop forms whose type codes are lifted (generic/type-vops.lisp).
TYPE_VOPS = ['integerp', 'numberp', 'stringp', 'arrayp', 'fixnump', 'non-null-symbol-p']

# Features of the pinned image (ports/repr/sbcl/sbcl-2.6.8-arm64-image.capture).
FEATURES = {'sb-unicode': True, 'long-float': False, '64-bit': True}


def fail(msg):
    sys.stderr.write('package-sbcl-type-tests: ' + msg + '\n')
    sys.exit(1)


def load_pins():
    pins = {}
    with open(os.path.join(ROOT, PINS_FILE), encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            h, p = line.split(None, 1)
            pins['ports/repr/' + p.lstrip('./')] = h
    for p, h in PINS.items():
        if p not in pins:
            fail('no SHA256SUMS entry for ' + p)
        if h is not None and pins[p] != h:
            fail('SHA256SUMS entry for %s differs from the upstream pin' % p)
    return pins


def read(path, pins):
    with open(os.path.join(ROOT, path), 'rb') as f:
        data = f.read()
    h = hashlib.sha256(data).hexdigest()
    if h != pins[path]:
        fail('%s has sha256 %s, pinned %s' % (path, h, pins[path]))
    return data.decode('utf-8')


def ident(s):
    s = s.replace('string=', 'string_eq')
    return re.sub(r'[^A-Za-z0-9_]', '_', s)


def resolve_codes(text):
    """Tokens of a type-code list, #+/#- resolved against FEATURES, as Rocq terms."""
    text = '\n'.join(l.split(';')[0] for l in text.split('\n'))
    toks = re.findall(r'#[+-][^\s()]+|\.|#\.[^\s()]+|,?[^\s()]+', text)
    out = []
    i = 0
    while i < len(toks):
        t = toks[i]
        if t.startswith('#+') or t.startswith('#-'):
            f = t[2:]
            if f not in FEATURES:
                fail('unknown feature ' + f)
            keep = FEATURES[f] if t.startswith('#+') else not FEATURES[f]
            if keep:
                out.extend(resolve_codes(toks[i + 1]))
            i += 2
            continue
        if t == '.':
            i += 1
            continue
        if t == '#.fixnum-lowtags':
            out.append('@FIXNUM')
        elif re.match(r'^,?[a-z0-9-]+-(widetag|lowtag)$', t):
            out.append('src_' + ident(t.lstrip(',')))
        elif t.startswith('#.+') or t.startswith(',@'):
            out.append('@' + t.lstrip('#.,@'))
        else:
            fail('unexpected type-code token ' + t)
        i += 1
    return out


def main():
    if len(sys.argv) != 2:
        fail('usage: package-sbcl-type-tests.py OUTDIR')
    pins = load_pins()
    srcs = {p: read(p, pins) for p in PINS if p.endswith('.lisp')}
    cap = read('ports/repr/sbcl/sbcl-2.6.8-arm64-type-tests.capture', pins)
    out = ['(* GENERATED by scripts/package-sbcl-type-tests.py from the pinned inputs in',
           '   ports/repr/sbcl/ (sha256 in ports/repr/SHA256SUMS). Do not edit. The',
           '   instruction words are copied from the image capture; type-code lists and',
           '   flags from the pinned SBCL 2.6.8 sources. Nothing here is proved; the',
           '   Rocq modules SbclA64, SbclTests and SbclHostOps decode and check them. *)',
           'From Coq Require Import ZArith List.',
           'From Buri Require Import SbclLayout.',
           'Import ListNotations.',
           'Open Scope Z_scope.',
           'Module SbclTypeTests.',
           'Import SbclLayout.SbclLayout.']
    head = {}
    cases = {}
    cur = None
    for line in cap.split('\n'):
        if line.startswith('; ') or line == '':
            continue
        k, _, v = line.partition(' ')
        if k == 'case':
            if v in cases or cur is not None:
                fail('bad case structure at ' + v)
            cur = v
            cases[cur] = {}
        elif k == 'end':
            if cur is None:
                fail('end without case')
            cur = None
        elif cur is None:
            if k in head:
                fail('capture key twice: ' + k)
            head[k] = v
        else:
            if k in cases[cur]:
                fail('case key twice: %s %s' % (cur, k))
            cases[cur][k] = v
    if head.get('lisp-implementation-version') != '2.6.8' or head.get('machine-type') != 'ARM64':
        fail('capture is not SBCL 2.6.8 on ARM64')
    if list(cases) != CASES:
        fail('capture cases differ from ' + ' '.join(CASES))
    out.append('(* image capture header *)')
    out.append('Definition cap_nil_value : Z := %d.' % int(head['nil-value']))
    out.append('Definition cap_t_address : Z := %d.' % int(head['t-address']))
    out.append('(* instruction words from the simple-fun entry, per case *)')
    for c in CASES:
        d = cases[c]
        words = [int(x) for x in d['words'].split()]
        if any(w < 0 or w >= 2 ** 32 for w in words):
            fail('word out of range in ' + c)
        out.append('Definition entry_%s : Z := %d.' % (ident(c), int(d['entry-offset'])))
        out.append('Definition code_%s : list Z := [%s].' % (ident(c), '; '.join(str(w) for w in words)))
    out.append('(* define-type-vop type codes (generic/type-vops.lisp, type-vop-macros.lisp) *)')
    gtv = srcs['ports/repr/sbcl/generic-type-vops.lisp']
    tvm = srcs['ports/repr/sbcl/type-vop-macros.lisp']
    consts = {}
    for m in re.finditer(r'^\(defconstant-eqx (\+[a-z0-9-]+\+)\n  `\(((?:[^()]|\([^()]*\))*)\)\n  #\'equal\)', tvm, re.M):
        consts[m.group(1)] = m.group(2)
    for name in TYPE_VOPS:
        ms = re.findall(r'^\(define-type-vop %s\s*\n?\s*((?:\((?:[^()]|\([^()]*\))*\))|#\.\+[a-z0-9-]+\+|#\.fixnum-lowtags)\)$'
                        % re.escape(name), gtv, re.M)
        if len(ms) != 1:
            fail('define-type-vop %s: expected one form, found %d' % (name, len(ms)))
        body = ms[0]
        if body == '#.fixnum-lowtags':
            body = '(#.fixnum-lowtags)'
        elif body.startswith('#.'):
            cname = body[2:]
            if cname not in consts:
                out.append('(* %s: %s is computed from the saetp table; not lifted *)' % (name, cname))
                continue
            body = '(' + consts[cname] + ')'
        toks = resolve_codes(body[1:-1])
        if any(t.startswith('@') and t != '@FIXNUM' for t in toks):
            out.append('(* %s: type codes use %s; not lifted *)' % (name, ' '.join(toks)))
            continue
        codes = [t for t in toks if t != '@FIXNUM']
        out.append('Definition tv_%s_codes : list Z := [%s].' % (ident(name), '; '.join(codes)))
        out.append('Definition tv_%s_fixnum : Z := %d.' % (ident(name), 1 if '@FIXNUM' in toks else 0))
    out.append('(* generator and genesis lines (1 iff present verbatim exactly once) *)')
    for name, path, text in FLAGS:
        out.append('Definition srcflag_%s : Z := %d.' % (name, 1 if srcs[path].count(text) == 1 else 0))
    out.append('End SbclTypeTests.')
    with open(os.path.join(sys.argv[1], 'SbclTypeTests.v'), 'w', encoding='utf-8') as f:
        f.write('\n'.join(out) + '\n')


main()
