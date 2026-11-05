#!/usr/bin/env python3
"""E2E-21 inert layout extraction (packaging only).

Reads the pinned Chez Scheme 10.3.0 tarm64le and SBCL 2.6.8 arm64 inputs in
ports/repr/, refuses any input whose sha256 differs from the pin below, and
writes Rocq files that contain only `Definition name : Z := value.` lines:

  rocq/ChezLayout.v   constants from the generated tarm64le equates.h, literal
                      constants from cmacros.ss / arm64.def, the arm64.ss
                      register assignment, and the emulated sample values.
  rocq/SbclLayout.v   SBCL lowtags/widetags evaluated from early-objdef.lisp
                      defenum forms, registers from arm64/vm.lisp, and the
                      constants captured from the pinned aarch64 image.

This script decides nothing about theorems: it does not compare sources with
each other. Every cross-source agreement (cmacros.ss vs equates.h, source vs
image capture, sample vs encoding) is a lemma that Rocq checks.

usage: package-repr-layout.py OUTDIR   (writes OUTDIR/ChezLayout.v, OUTDIR/SbclLayout.v)
"""
import hashlib
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

PINS = {
    # Chez Scheme 10.3.0, tag v10.3.0 commit adfaf9e6 (identical bytes in csv10.3.0.tar.gz d237d987).
    'ports/repr/chez/cmacros.ss': 'c4065be7509e8034b6add8adb72585ec568359324f8429dc5b0b2d996fab2253',
    'ports/repr/chez/arm64.ss': '9afef064e0a7eba9e8826163b447e318c76e9283082d969954aff75b5d91146a',
    'ports/repr/chez/arm64.def': 'd85f403368ae7511b5c727cfc8419c1cf83a4e98be4becc042c45301a9afab77',
    'ports/repr/chez/types.h': '88da87a0686e81089478cf073ae317ad59bab5968f8ed47acdcaf32636390c3f',
    # Build-time outputs of nix/arm/build-chez-10.3.0-aarch64.sh (tarm64le, threaded).
    'ports/repr/chez/tarm64le-equates.h': '980e7c82a80f2c617878825f9f552eec7791e82a8c0181618319d2050f783a60',
    'ports/repr/chez/tarm64le-machine.def': '0187f57c73fabe3d80245c3ca4f48faeeb1a32a12461fb9a35808c9864e07d00',
    # Emulated sample (qemu-aarch64) of the built tarm64le scheme; see README.
    'ports/repr/chez/chez-layout-sample.ss': None,
    'ports/repr/chez/chez-10.3.0-tarm64le-sample.capture': None,
    # SBCL 2.6.8 source tarball sha256 ad5126df...; files copied unchanged.
    'ports/repr/sbcl/early-objdef.lisp': 'c160facbaf0447828846b111d33b984c50265c06b39a203174ff534c1cb97aa3',
    'ports/repr/sbcl/early-vm.lisp': '23f1fed0d27afa8444c9c2b4ae5f19f4f76167728149ff88330c0ce1dccbd258',
    'ports/repr/sbcl/arm64-parms.lisp': 'ddce6416e12938bfb4538e136945a666057590f7f525b55143804336c7006421',
    'ports/repr/sbcl/arm64-vm.lisp': 'e258a8a0da17dd5572f32b59e96f84b17a2baf2f6312f6648372cac37a43a933',
    # Image capture of the pinned aarch64 SBCL (qemu-aarch64); see README.
    'ports/repr/sbcl/sbcl-layout.lisp': None,
    'ports/repr/sbcl/sbcl-2.6.8-arm64-image.capture': None,
}
PINS_FILE = 'ports/repr/SHA256SUMS'


def fail(msg):
    sys.stderr.write('package-repr-layout: ' + msg + '\n')
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


def zlit(v):
    return '(%d)' % v if v < 0 else '%d' % v


def ident(s):
    return re.sub(r'[^A-Za-z0-9_]', '_', s)


# ---------------------------------------------------------------- Chez

EQUATES = '''ptr_bits ptr_bytes log2_ptr_bytes typemod primary_type_bits byte_alignment
fixnum_bits fixnum_offset fixnum_factor mask_fixnum type_fixnum
most_positive_fixnum most_negative_fixnum
type_pair type_flonum type_symbol type_closure type_immediate type_typed_object
mask_pair mask_flonum mask_symbol mask_closure mask_immediate mask_typed_object
type_boolean mask_boolean sfalse strue snil svoid sunbound seof sbwp black_hole forward_marker
type_char mask_char char_data_offset char_factor
pair_car_disp pair_cdr_disp size_pair
string_type_disp string_data_disp string_length_offset string_immutable_flag
string_char_bytes string_char_bits type_string mask_string type_mutable_string type_immutable_string
vector_type_disp vector_data_disp vector_length_offset vector_immutable_flag type_vector mask_vector
type_mutable_vector type_immutable_vector
bignum_type_disp bignum_data_disp bignum_length_offset bignum_sign_offset bigit_bits bigit_bytes
type_bignum mask_bignum mask_bignum_sign type_positive_bignum type_negative_bignum
flonum_data_disp size_flonum flonum_bytes
symbol_value_disp symbol_pvalue_disp symbol_plist_disp symbol_name_disp symbol_splist_disp
symbol_hash_disp size_symbol
closure_code_disp closure_data_disp code_type_disp code_data_disp type_code mask_code
type_record mask_record record_type_disp type_port mask_port port_type_disp
tc_arg_regs_disp tc_ac0_disp tc_sfp_disp tc_ap_disp tc_eap_disp tc_trap_disp tc_cp_disp tc_ret_disp
return_address_mv_return_address_disp return_address_livemask_disp return_address_toplink_disp
return_address_frame_size_disp
machine_type machine_type_tarm64le'''.split()

# Literal (define-constant ...) forms in cmacros.ss, re-read independently.
CMACROS = '''typemod type-fixnum type-pair type-flonum type-symbol type-closure type-immediate
type-typed-object type-boolean sfalse strue type-char sunbound snil seof svoid sbwp
type-string type-bignum type-positive-bignum type-negative-bignum type-code
type-port type-record string-char-bits string-char-bytes string-length-offset
bignum-sign-offset bignum-length-offset bigit-bits char-data-offset'''.split()

SAMPLE = '''machine-type-tarm64le fixnum-width most-positive-fixnum most-negative-fixnum
pair-car-word pair-cdr-word vector-header vector-elt0-true vector-elt1-false vector-elt2-nil
vector-elt3-void vector-elt4-fixnum5 string-header string-char0 string-char1 bignum-header
bignum-bigit0 bignum-bigit1 bignum-bigit2 flonum-bits symbol-name-is-string
closure-code-is-code closure-entry-mod16 closure-free0 pair-ptr-mod16 flonum-ptr-mod16
symbol-ptr-mod16 closure-ptr-mod16 string-ptr-mod16 vector-ptr-mod16 bignum-ptr-mod16
closure-entry-minus-code'''.split()


def parse_int(tok):
    neg = tok.startswith('-')
    t = tok[1:] if neg else tok
    if t.startswith('#b'):
        v = int(t[2:], 2)
    elif t.startswith('0x') or t.startswith('0X'):
        v = int(t[2:], 16)
    else:
        v = int(t, 10)
    return -v if neg else v


def unique(matches, what):
    if len(matches) != 1:
        fail('%s: expected exactly one definition, found %d' % (what, len(matches)))
    return matches[0]


def chez(pins):
    eq = read('ports/repr/chez/tarm64le-equates.h', pins)
    cm = read('ports/repr/chez/cmacros.ss', pins)
    asm = read('ports/repr/chez/arm64.ss', pins)
    adef = read('ports/repr/chez/arm64.def', pins)
    mdef = read('ports/repr/chez/tarm64le-machine.def', pins)
    sample = read('ports/repr/chez/chez-10.3.0-tarm64le-sample.capture', pins)
    read('ports/repr/chez/chez-layout-sample.ss', pins)
    if not eq.startswith('/* equates.h for Chez Scheme Version 10.3.0 */\n'):
        fail('equates.h is not the Chez Scheme 10.3.0 header')
    out = []
    out.append('(* constants of the generated tarm64le equates.h *)')
    for n in EQUATES:
        ms = re.findall(r'^#define %s (?:\((?:iptr|uptr|ptr)\))?(-?0x[0-9A-Fa-f]+|-?[0-9]+)$' % re.escape(n), eq, re.M)
        out.append('Definition %s : Z := %s.' % (n, zlit(parse_int(unique(ms, 'equates.h ' + n)))))
    out.append('(* literal define-constant forms of cmacros.ss (cm_ prefix) *)')
    for n in CMACROS:
        ms = re.findall(r'^\(define-constant (?:ptr )?%s +(#b[01]+|-?[0-9]+)\)' % re.escape(n), cm, re.M)
        out.append('Definition cm_%s : Z := %s.' % (ident(n), zlit(parse_int(unique(ms, 'cmacros.ss ' + n)))))
    th = read('ports/repr/chez/types.h', pins)
    out.append('(* c/types.h TYPE(x,type): 1 iff it is exactly x - typemod + type *)')
    tm = re.findall(r'^#define TYPE\(x,type\) \(\(ptr\)\(\(iptr\)\(x\) - typemod \+ \(type\)\)\)$', th, re.M)
    out.append('Definition c_TYPE_is_minus_typemod : Z := %d.' % (1 if len(tm) == 1 else 0))
    out.append('(* arm64.def *)')
    for n in ['ptr-bits', 'asm-arg-reg-max', 'asm-arg-reg-cnt']:
        ms = re.findall(r'^\(define-constant %s ([0-9]+)\)$' % re.escape(n), adef, re.M)
        out.append('Definition def_%s : Z := %s.' % (ident(n), zlit(parse_int(unique(ms, 'arm64.def ' + n)))))
    little = re.findall(r"^\(define-constant native-endianness 'little\)$", adef, re.M)
    out.append('Definition def_little_endian : Z := %d.' % (1 if len(little) == 1 else 0))
    mt = re.findall(r'^\(define-constant machine-type \(constant machine-type-tarm64le\)\)$', mdef, re.M)
    out.append('Definition def_machine_tarm64le : Z := %d.' % (1 if len(mt) == 1 else 0))
    thr = re.findall(r'^\(features [a-z ]*\bpthreads\b[a-z ]*\)$', mdef, re.M)
    out.append('Definition def_pthreads : Z := %d.' % (1 if len(thr) == 1 else 0))
    # Register assignment: the define-registers form of arm64.ss.
    start = asm.find('(define-registers')
    stop = asm.find('(machine-dependent', start)
    if start < 0 or stop < 0:
        fail('arm64.ss define-registers form not found')
    block = asm[start:stop]
    sect = {}
    cur = None
    for line in block.split('\n'):
        s = line.split(';')[0].strip()
        m = re.match(r'^\((reserved|allocable)$', s)
        if m:
            cur = m.group(1)
            sect[cur] = []
            continue
        m = re.match(r'^\[\s*((?:%[A-Za-z0-9]+\s+)+)(#t|#f)\s+([0-9]+)\s+(uptr|fp)\]\)?$', s)
        if m and cur:
            names = m.group(1).split()
            sect[cur].append((names, int(m.group(3)), m.group(4)))
    md = asm[stop:asm.find('\n  )', stop)]
    mdregs = []
    for line in md.split('\n'):
        s = line.split(';')[0].strip()
        m = re.match(r'^\[\s*((?:%[A-Za-z0-9-]+\s+)+)(#t|#f)\s+([0-9]+)\s+(uptr|fp)\]\)?$', s)
        if m:
            mdregs.append((m.group(1).split(), int(m.group(3)), m.group(4)))
    if 'reserved' not in sect or 'allocable' not in sect:
        fail('arm64.ss register sections not found')
    out.append('(* arm64.ss define-registers: hardware register numbers *)')
    seen = set()

    def reg(name, num):
        if name in seen:
            fail('register %s defined twice' % name)
        seen.add(name)
        out.append('Definition reg_%s : Z := %d.' % (ident(name.lstrip('%')), num))
    for names, num, ty in sect['reserved']:
        reg(names[0], num)
    alloc = sect['allocable']
    if [a[0][0] for a in alloc[:4]] != ['%ac0', '%xp', '%ts', '%td']:
        fail('allocable registers do not start with %ac0 %xp %ts %td')
    extra = []
    for names, num, ty in alloc:
        if names[0] in ('%ac0', '%xp', '%ts', '%td', '%ac1', '%yp', '%cp', '%ret'):
            reg(names[0], num)
        elif ty == 'uptr':
            extra.append((names[0], num))
    for names, num, ty in mdregs:
        if names[0] in ('%jmptmp', '%sp'):
            reg(names[0], num)
    # np-register.ss define-allocable-registers: the first asm-arg-reg-cnt
    # non-fp "extra" registers, in order, are the argument registers.
    cnt = parse_int(unique(re.findall(r'^\(define-constant asm-arg-reg-cnt ([0-9]+)\)$', adef, re.M), 'cnt'))
    out.append('Definition reg_extra_count : Z := %d.' % len(extra))
    for i, (n, num) in enumerate(extra[:cnt]):
        out.append('Definition reg_arg%d : Z := %d.' % (i + 1, num))
    lr = [num for n, num in extra if n == '%lr']
    out.append('Definition reg_lr : Z := %d.' % unique(lr, 'lr'))
    out.append('(* emulated sample of the built tarm64le process (sample_ prefix) *)')
    vals = {}
    for line in sample.strip().split('\n'):
        k, v = line.split()
        if k in vals:
            fail('sample key twice: ' + k)
        vals[k] = int(v)
    for k in SAMPLE:
        if k not in vals:
            fail('sample key missing: ' + k)
        out.append('Definition sample_%s : Z := %s.' % (ident(k), zlit(vals[k])))
    return out


# ---------------------------------------------------------------- SBCL

def feature_true(expr, feats):
    expr = expr.strip()
    if not expr.startswith('('):
        return expr.lower() in feats
    toks = re.findall(r'\(|\)|[^\s()]+', expr)
    pos = [0]

    def parse():
        t = toks[pos[0]]
        pos[0] += 1
        if t != '(':
            return t.lower() in feats
        op = toks[pos[0]].lower()
        pos[0] += 1
        args = []
        while toks[pos[0]] != ')':
            args.append(parse())
        pos[0] += 1
        if op == 'and':
            return all(args)
        if op == 'or':
            return any(args)
        if op == 'not':
            return not args[0]
        fail('unknown feature operator ' + op)
    v = parse()
    if pos[0] != len(toks):
        fail('trailing feature tokens in ' + expr)
    return v


def feature_items(body, feats):
    """Identifiers of a defenum body with #+/#- conditionals resolved."""
    body = '\n'.join(l.split(';')[0] for l in body.split('\n'))
    toks = re.findall(r'#[+-](?:\([^()]*(?:\([^()]*\)[^()]*)*\)|[^\s()]+)|[^\s()]+', body)
    items = []
    i = 0
    while i < len(toks):
        t = toks[i]
        if t.startswith('#+') or t.startswith('#-'):
            keep = feature_true(t[2:], feats)
            if t.startswith('#-'):
                keep = not keep
            if i + 1 >= len(toks):
                fail('dangling feature conditional')
            if keep:
                items.append(toks[i + 1])
            i += 2
        else:
            items.append(t)
            i += 1
    return items


def sbcl(pins):
    obj = read('ports/repr/sbcl/early-objdef.lisp', pins)
    evm = read('ports/repr/sbcl/early-vm.lisp', pins)
    parms = read('ports/repr/sbcl/arm64-parms.lisp', pins)
    vm = read('ports/repr/sbcl/arm64-vm.lisp', pins)
    cap = read('ports/repr/sbcl/sbcl-2.6.8-arm64-image.capture', pins)
    read('ports/repr/sbcl/sbcl-layout.lisp', pins)
    img = {}
    feats = set()
    for line in cap.strip().split('\n'):
        k, _, v = line.partition(' ')
        if k in ('features', 'internal-features'):
            feats.update(v.split())
            continue
        if k in img:
            fail('capture key twice: ' + k)
        img[k] = v
    if img.get('lisp-implementation-version') != '2.6.8' or img.get('machine-type') != 'ARM64':
        fail('capture is not SBCL 2.6.8 on ARM64')
    out = []
    out.append('(* SBCL build features used to resolve #+/#- (from the image capture) *)')
    for f in ['64-bit', 'arm64', 'sb-unicode', 'sb-thread', 'sb-simd-pack', 'sb-simd-pack-256',
              'sb-simd-pack-512', 'ppc64', 'x86-64', 'darwin', 'win32', 'compact-instance-header']:
        out.append('Definition feature_%s : Z := %d.' % (ident(f), 1 if f in feats else 0))
    ms = re.findall(r'^\(defconstant n-word-bits ([0-9]+)\)$', parms, re.M)
    out.append('Definition src_n_word_bits : Z := %d.' % parse_int(unique(ms, 'n-word-bits')))
    ms = re.findall(r'^\(defconstant n-widetag-bits ([0-9]+)\)$', evm, re.M)
    out.append('Definition src_n_widetag_bits : Z := %d.' % parse_int(unique(ms, 'n-widetag-bits')))
    # early-vm.lisp: n-lowtag-bits = integer-length (1- (/ (* 2 n-word-bits) n-byte-bits)).
    if '(defconstant n-lowtag-bits\n  (integer-length (1- (/ (* 2 n-word-bits) n-byte-bits))))' not in evm:
        fail('n-lowtag-bits definition changed')
    nw = parse_int(unique(re.findall(r'^\(defconstant n-word-bits ([0-9]+)\)$', parms, re.M), 'nw'))
    nlow = (2 * nw // 8 - 1).bit_length()
    out.append('Definition src_n_lowtag_bits : Z := %d.' % nlow)
    # Lowtag defenum: the one selected by the build features.
    out.append('(* early-objdef.lisp lowtag defenum (start 0, step 1) *)')
    forms = re.findall(r'  #\+(\([^\n]*\)|[^\s(]+)\n  \(defenum \(\)\n((?:    [^\n]*\n)+?)    ([a-z0-9-]+)\)', obj)
    chosen = [f for f in forms if feature_true(f[0], feats)]
    if len(chosen) != 1:
        fail('expected one lowtag defenum for these features, found %d' % len(chosen))
    lows = feature_items(chosen[0][1] + chosen[0][2], feats)
    for i, n in enumerate(lows):
        out.append('Definition src_%s : Z := %d.' % (ident(n), i))
    # Widetag defenum: :start (+ (ash 1 n-lowtag-bits) other-immediate-0-lowtag) :step 4.
    m = re.search(r'\(defenum \(;;[^\n]*\n(?:\s*;;[^\n]*\n)*\s*:start #\.\(\+ \(ash 1 n-lowtag-bits\) other-immediate-0-lowtag\)\n\s*:step 4\)\n(.*?)\n\)\)\n', obj, re.S)
    if not m:
        fail('widetag defenum not found')
    start = (1 << nlow) + lows.index('other-immediate-0-lowtag')
    wides = feature_items(m.group(1), feats)
    out.append('(* early-objdef.lisp widetag defenum (start %d, step 4) *)' % start)
    seen = set()
    for i, n in enumerate(wides):
        if not n.endswith('-widetag'):
            continue
        if n in seen:
            fail('widetag twice: ' + n)
        seen.add(n)
        out.append('Definition src_%s : Z := %d.' % (ident(n), start + 4 * i))
    ms = re.findall(r'^#\+64-bit \(defconstant unbound-marker-widetag ([0-9]+)\)$', obj, re.M)
    out.append('Definition src_unbound_marker_widetag : Z := %d.' % parse_int(unique(ms, 'unbound-marker')))
    out.append('(* arm64/vm.lisp defreg: register numbers *)')
    seen = set()
    for line in vm.split('\n'):
        m = re.match(r'^  \(defreg (.*?) ([0-9]+)\)\s*(?:;.*)?$', line)
        if not m:
            continue
        items = feature_items(m.group(1), feats)
        if len(items) != 1:
            fail('defreg line not resolved: ' + line)
        n = items[0]
        if n in seen:
            continue  # nsp and zr share 31; keep both names once each
        seen.add(n)
        out.append('Definition src_reg_%s : Z := %d.' % (ident(n), int(m.group(2))))
    m = re.search(r'\(defregset \*register-arg-offsets\*\s+([a-z0-9 ]+)\)', vm)
    if not m:
        fail('register-arg-offsets not found')
    for i, n in enumerate(m.group(1).split()):
        out.append('Definition src_arg_reg%d_is_%s : Z := 1.' % (i, ident(n)))
    out.append('(* constants captured from the pinned aarch64 image (img_ prefix) *)')
    for k in sorted(img):
        v = img[k]
        if re.fullmatch(r'-?[0-9]+', v):
            out.append('Definition img_%s : Z := %s.' % (ident(k), zlit(int(v))))
    return out


HEAD = '''(* GENERATED by scripts/package-repr-layout.py from the pinned inputs in
   ports/repr/ (sha256 in ports/repr/SHA256SUMS). Do not edit. Every value is
   copied from a pinned file; nothing here is proved. Agreement between the
   different sources is checked by lemmas in %s. *)
From Coq Require Import ZArith.
Open Scope Z_scope.
Module %s.
'''


def main():
    if len(sys.argv) != 2:
        fail('usage: package-repr-layout.py OUTDIR')
    pins = load_pins()
    for path in PINS:
        read(path, pins)
    for mod, lines, user in [('ChezLayout', chez(pins), 'ChezRepr.v'),
                             ('SbclLayout', sbcl(pins), 'SbclRepr.v')]:
        text = HEAD % (user, mod) + '\n'.join(lines) + '\nEnd %s.\n' % mod
        with open(os.path.join(sys.argv[1], mod + '.v'), 'w', encoding='utf-8') as f:
            f.write(text)


if __name__ == '__main__':
    main()
