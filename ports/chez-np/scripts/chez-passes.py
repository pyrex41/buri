"""Write spec/chez-passes.json: the Chez 10.3.0 compile pipeline for eval/compile
(reading aid; not a proof input).

Line ranges are located in a Chez 10.3.0 source tree (tag v10.3.0, commit
adfaf9e6) with a paren-matching scan; which passes ran, and in what order, is
read from the captured trace ports/chez-np/tarm64le-buri-arm-add.np.  Rocq
re-derives the trace order itself (ChezNpValidate.trace_pass_order).

usage: chez-passes.py CHEZ-SRC-DIR TRACE.np OUT.json
"""
import hashlib
import json
import re
import sys
from pathlib import Path

src, trace, out = sys.argv[1:]
S = Path(src) / 's'


def span(fname, pat):
    s = (S / fname).read_text()
    m = re.search(pat, s, re.M)
    if not m:
        raise SystemExit('not found: %s %s' % (fname, pat))
    st = m.start()
    depth, j, in_str = 0, st, False
    while True:
        c = s[j]
        if in_str:
            if c == '\\':
                j += 2
                continue
            if c == '"':
                in_str = False
            j += 1
            continue
        if c == ';':
            j = s.index('\n', j)
            continue
        if s.startswith('#\\', j):
            j += 3
            continue
        if c == '"':
            in_str = True
        elif c in '([':
            depth += 1
        elif c in ')]':
            depth -= 1
            if depth == 0:
                break
        j += 1
    first, last = s.count('\n', 0, st) + 1, s.count('\n', 0, j) + 1
    # Cap at the next form starting at the same or a smaller indentation
    # (guards against a paren scan confused by reader syntax it lacks).
    lines = s.split('\n')
    indent = len(lines[first - 1]) - len(lines[first - 1].lstrip())
    for k in range(first, last):
        ln = lines[k]
        if ln.strip().startswith('(') and len(ln) - len(ln.lstrip()) <= indent:
            last = k
            while last > first and not lines[last - 1].strip():
                last -= 1
            break
    return [first, last]


def dp(name):
    return r'\(define-pass ' + re.escape(name) + r' '


def dw(name):
    return r'\((?:define-who|define) ' + re.escape(name) + r'\s'


text = Path(trace).read_text()
tr = text[text.index('@@@ np-trace\n'):]
traced = re.findall(r'^output of (.*):$', tr, re.M)
bodies = re.split(r'^output of .*:\n', tr, flags=re.M)[1:]
changed = {}
for i, n in enumerate(traced):
    if n not in changed:
        changed[n] = (i == 0) or bodies[i] != bodies[i - 1]

S_CLASS = 'syntactic'      # shape change only; checkable from the two terms
W_CLASS = 'witness'        # needs a certificate the pass can emit (maps, liveness, frames)
H_CLASS = 'semantic'       # needs a semantics of primitives, machine words, or effects
T_CLASS = 'trusted-printer'

front = [
    ('expand', 'syntax.ss', r'\(set! sc-expand', None, 'Lexpand/Lsrc', 'non-nanopass expander; Rocq-side model of syntax-case is out of scope; prints as $uncprep', H_CLASS),
    ('cpvalid', 'cpvalid.ss', r'\(set! \$cpvalid', None, 'Lsrc', 'letrec restriction checks (inserts valid-checks)', S_CLASS),
    ('cp0#1', 'cp0.ss', dp('cp0'), 'run-cp0 default (cp0 (cp0 x))', 'Lsrc', 'inliner/constant folder; heavy (effort counters, primitive folding)', H_CLASS),
    ('cptypes#1', 'cptypes.ss', r'\(define-pass cptypes ', 'enable-type-recovery #t', 'Lsrc', 'type recovery; removes checks it proves redundant', H_CLASS),
    ('cpletrec#1', 'cpletrec.ss', dp('cpletrec'), None, 'Lsrc', 'letrec optimisation', W_CLASS),
    ('cp0#2', 'cp0.ss', dp('cp0'), 'run-cp0 default (cp0 (cp0 x))', 'Lsrc', 'second cp0 round', H_CLASS),
    ('cptypes#2', 'cptypes.ss', r'\(define-pass cptypes ', 'enable-type-recovery #t', 'Lsrc', 'second round', H_CLASS),
    ('cpletrec#2', 'cpletrec.ss', dp('cpletrec'), None, 'Lsrc', 'second round', W_CLASS),
    ('cpcheck', 'cpcheck.ss', dp('cpcheck'), None, 'Lsrc', 'argument-count checks for known calls', S_CLASS),
    ('cpcommonize', 'cpcommonize.ss', r'\(define-who commonization-level', 'commonization-level 0 => identity', 'Lsrc', 'returns its input at level 0 (cpcommonize.ss 580-585)', S_CLASS),
]

conditional = {
    'np-lift-well-known-closures': '($lift-closures) = #t (default)',
    'np-expand/optimize-closures': '($optimize-closures) = #t (default); otherwise np-expand-closures',
    'np-expand-closures': 'only when ($optimize-closures) = #f: NOT RUN',
    'np-profile-unroll-loops': 'only when ($loop-unroll-limit) /= 0 (default 0): NOT RUN',
    'np-add-block-source!': "only when compile-profile = block (or profile-block-data) and $sfd: NOT RUN",
    'np-insert-profiling': "only when compile-profile = source, or block with $sfd: NOT RUN",
    'identify-poison!': 'only when more than 1000 spillables: NOT RUN',
}

np = [
    # name, file, pattern, in, out, class, note
    ('cpnanopass', 'cpnanopass.ss', dp('cpnanopass'), 'Lsrc', 'L1', S_CLASS, 'prelex -> uvar, preinfo -> info'),
    ('np-recognize-let', 'cpnanopass.ss', dp('np-recognize-let'), 'L1', 'L2', S_CLASS, ''),
    ('np-discover-names', 'cpnanopass.ss', dp('np-discover-names'), 'L2', 'L3', S_CLASS, 'names into info only'),
    ('np-convert-assignments', 'cpnanopass.ss', dp('np-convert-assignments'), 'L3', 'L4', H_CLASS, 'boxes assigned variables'),
    ('np-sanitize-bindings', 'cpnanopass.ss', dp('np-sanitize-bindings'), 'L4', 'L4', S_CLASS, ''),
    ('np-suppress-procedure-checks', 'cpnanopass.ss', dp('np-suppress-procedure-checks'), 'L4', 'L4', S_CLASS, 'changes call info flags (not printed)'),
    ('np-recognize-mrvs', 'cpnanopass.ss', dp('np-recognize-mrvs'), 'L4', 'L4.5', S_CLASS, 'VALIDATED (ChezNpValidate)'),
    ('np-expand-foreign', 'cpnanopass.ss', dp('np-expand-foreign'), 'L4.5', 'L4.75', H_CLASS, 'FFI'),
    ('np-recognize-loops', 'cpnanopass.ss', dp('np-recognize-loops'), 'L4.75', 'L4.875', S_CLASS, ''),
    ('np-recognize-attachment', 'cpnanopass.ss', dp('np-recognize-attachment'), 'L4.875', 'L4.9375', H_CLASS, 'continuation attachments'),
    ('np-name-anonymous-lambda', 'cpnanopass.ss', dp('np-name-anonymous-lambda'), 'L4.9375', 'L5', S_CLASS, 'needs freshness + closure-value relation'),
    ('np-convert-closures', 'cpnanopass.ss', dp('np-convert-closures'), 'L5', 'L6', W_CLASS, 'free-variable lists are checkable witnesses'),
    ('np-optimize-direct-call', 'cpnanopass.ss', dp('np-optimize-direct-call'), 'L6', 'L6', S_CLASS, ''),
    ('np-identify-scc', 'cpnanopass.ss', dp('np-identify-scc'), 'L6', 'L6', S_CLASS, ''),
    ('np-lift-well-known-closures', 'cpnanopass.ss', dp('np-lift'), 'L6', 'L6', W_CLASS, ''),
    ('np-expand/optimize-closures', 'cpnanopass.ss', dp('np-expand/optimize-closures'), 'L6', 'L7', W_CLASS, 'closure layout'),
    ('np-expand-closures', 'cpnanopass.ss', dp('np-expand-closures'), 'L6', 'L7', W_CLASS, ''),
    ('np-profile-unroll-loops', 'cpnanopass.ss', dp('np-profile-unroll-loops'), 'L7', 'L7', S_CLASS, ''),
    ('np-simplify-if', 'cpnanopass.ss', dp('np-simplify-if'), 'L7', 'L7', S_CLASS, ''),
    ('np-unbox-fp-vars!', 'cpnanopass.ss', dp('np-unbox-fp-vars!'), 'L7', 'L7', H_CLASS, 'flonum representation'),
    ('$np-expand-primitives', 'cpprim.ss', dp('np-expand-primitives'), 'L7', 'L9', H_CLASS, 'cpprim: inline primitive expansion (fixnum fast path for +)'),
    ('np-place-overflow-and-trap', 'cpnanopass.ss', dp('np-place-overflow-and-trap'), 'L9', 'L9.5', H_CLASS, 'interrupt trap placement'),
    ('np-rebind-on-ruined-path', 'cpnanopass.ss', dp('np-rebind-on-ruined-path'), 'L9.5', 'L9.5', S_CLASS, ''),
    ('np-finalize-loops', 'cpnanopass.ss', dp('np-finalize-loops'), 'L9.5', 'L9.75', S_CLASS, ''),
    ('np-optimize-pred-in-value', 'cpnanopass.ss', dp('np-optimize-pred-in-value'), 'L9.75', 'L9.75', S_CLASS, ''),
    ('np-remove-complex-opera*', 'cpnanopass.ss', dp('np-remove-complex-opera*'), 'L9.75', 'L10', S_CLASS, 'fixes argument evaluation order: needs the unspecified-order semantics'),
    ('np-push-mrvs', 'cpnanopass.ss', dp('np-push-mrvs'), 'L10', 'L10.5', S_CLASS, ''),
    ('np-normalize-context', 'cpnanopass.ss', dp('np-normalize-context'), 'L10.5', 'L11', S_CLASS, ''),
    ('np-flatten-case-lambda', 'cpnanopass.ss', dp('np-flatten-case-lambda'), 'L11', 'L12', S_CLASS, 'arity dispatch, doargerr'),
    ('np-insert-trap-check', 'cpnanopass.ss', dp('np-insert-trap-check'), 'L12', 'L12.5', H_CLASS, 'event counter'),
    ('np-impose-calling-conventions', 'cpnanopass.ss', dp('np-impose-calling-conventions'), 'L12.5', 'L13', W_CLASS, 'registers/frame/return points; needs a calling-convention spec (E2E-21)'),
    ('np-expand-hand-coded', 'cpnanopass.ss', dp('np-expand-hand-coded'), 'L13', 'L13.5', H_CLASS, ''),
    ('np-expose-allocation-pointer', 'cpnanopass.ss', dp('np-expose-allocation-pointer'), 'L13.5', 'L14', H_CLASS, 'allocation'),
    ('np-expose-basic-blocks', 'cpnanopass.ss', dp('np-expose-basic-blocks'), 'L14', 'L15a', W_CLASS, 'block graph'),
    ('np-remove-repeater-blocks!', 'cpnanopass.ss', dp('np-remove-repeater-blocks!'), 'L15a', 'L15a', S_CLASS, ''),
    ('np-add-block-source!', 'cpnanopass.ss', dp('np-add-block-source!'), 'L15a', 'L15a', S_CLASS, ''),
    ('np-propagate-pariahty!', 'cpnanopass.ss', dp('np-propagate-pariahty!'), 'L15a', 'L15a', S_CLASS, 'layout hints only'),
    ('np-insert-profiling', 'cpnanopass.ss', dp('np-insert-profiling'), 'L15a', 'L15a', H_CLASS, ''),
    ('np-add-in-links!', 'cpnanopass.ss', dp('np-add-in-links!'), 'L15a', 'L15a', S_CLASS, ''),
    ('np-compute-loop-depth!', 'cpnanopass.ss', dp('np-compute-loop-depth!'), 'L15a', 'L15a', S_CLASS, ''),
    ('np-weight-references!', 'cpnanopass.ss', dp('np-weight-references!'), 'L15a', 'L15a', S_CLASS, ''),
    ('np-allocate-registers', 'cpnanopass.ss', dp('np-allocate-registers'), 'L15a', 'L16', W_CLASS, 'aggregate pass (no pass macro); sub-passes below, run per lambda'),
    ('np-remove-repeater-blocks-again!', 'cpnanopass.ss', dp('np-remove-repeater-blocks-again!'), 'L16', 'L16', S_CLASS, ''),
    ('np-optimize-block-order!', 'cpnanopass.ss', dp('np-optimize-block-order!'), 'L16', 'L16', S_CLASS, 'block list permutation'),
    ('np-generate-code', 'cpnanopass.ss', dp('np-generate-code'), 'L16', '$c-func code-list', H_CLASS, 'instruction encoding via arm64.ss; output VALIDATED against bytes (ChezNpReloc)'),
]

ra = [
    ('do-live-analysis!', r'\(define do-live-analysis!', 'L15a', 'L15a'),
    ('record-call-live!', dw('record-call-live!'), 'L15a', 'L15a'),
    ('identify-poison!', dw('identify-poison!'), 'L15a', 'L15a'),
    ('do-spillable-conflict!', dw('do-spillable-conflict!'), 'L15a', 'L15a'),
    ('assign-frame!', r'\(define assign-frame!', 'L15a/L15b', 'same'),
    ('record-inspector-information!', r'\(define record-inspector-information!', 'L15a', 'L15a'),
    ('assign-new-frame!', dp('assign-new-frame!'), 'L15a', 'L15b'),
    ('record-fp-offsets!', dw('record-fp-offsets!'), 'L15b', 'L15b'),
    ('finalize-frame-locations!', dp('finalize-frame-locations!'), 'L15b', 'L15c'),
    ('select-instructions!', dp('select-instructions!'), 'L15c', 'L15d'),
    ('do-unspillable-conflict!', dw('do-unspillable-conflict!'), 'L15d', 'L15d'),
    ('assign-registers!', dw('assign-registers!'), 'L15d', 'L15d'),
    ('finalize-register-locations!', dp('finalize-register-locations!'), 'L15d', 'L15e'),
    ('expose-overflow-check-blocks!', dp('expose-overflow-check-blocks!'), 'L15e', 'L16'),
]

doc = {
    'source': {'release': 'csv10.3.0.tar.gz',
               'release_sha256': 'd237d9874c6e8b0ccf7758daa8286a6e825528b13ce3b2bca56eb1f73cddbc2c',
               'git_tag': 'v10.3.0', 'git_commit': 'adfaf9e6d47a4238a9e5e4bf6a00f9d58792a3db',
               'files': {f: hashlib.sha256((S / f).read_bytes()).hexdigest()
                         for f in ['compile.ss', 'cpnanopass.ss', 'cpprim.ss', 'np-languages.ss',
                                   'arm64.ss', 'cp0.ss', 'cptypes.ss', 'cpletrec.ss', 'cpvalid.ss',
                                   'cpcheck.ss', 'cpcommonize.ss', 'syntax.ss']}},
    'configuration': {
        'machine': 'tarm64le (threaded)', 'entry': 'eval with current-eval = compile (compile.ss set-who! compile, 1784-1823)',
        'parameters': 'see the parameters section of ports/chez-np/tarm64le-buri-arm-add.np: optimize-level 0, debug-level 1, '
                      'generate-inspector-information #t, enable-type-recovery #t, generate-interrupt-trap #t, '
                      'compile-interpret-simple #t (not taken: the form is not simple), commonization-level 0, compile-profile #f, '
                      '$lift-closures #t, $optimize-closures #t, $loop-unroll-limit 0, $enable-check-prelex-flags #f',
        'pipeline_source': 'cpnanopass.ss $np-compile 10795-10838 and np-after-calling-conventions 10771-10793; '
                           'compile.ss compile 1797-1823; c-compile wraps the form as main (compile.ss 68-74)',
        'after_codegen': 'compile.ss c-mkcode (102-190) lays out the code-list; c/fasl.c arm64_set_abs (1714-1735) relocates',
    },
    'difficulty_classes': {
        S_CLASS: 'output relates to input by a shape change checkable from the two printed terms',
        W_CLASS: 'checkable only with a witness the pass can export (free-variable lists, register/frame maps, liveness)',
        H_CLASS: 'needs a semantics of primitives, machine integers, effects, interrupts or the ISA',
    },
    'front_end': [],
    'nanopass': [],
    'register_allocator_subpasses': [],
}
for name, f, pat, cond, lang, note, cls in front:
    doc['front_end'].append({'name': name, 'kind': 'non-nanopass' if name in ('expand', 'cpvalid', 'cpcommonize') else 'nanopass (Lsrc -> Lsrc)',
                             'file': 's/' + f, 'lines': span(f, pat), 'language': lang,
                             'condition': cond, 'ran': True, 'class': cls, 'note': note})
order = 0
for name, f, pat, li, lo, cls, note in np:
    ran = name in changed
    if ran:
        order += 1
    doc['nanopass'].append({'order': order if ran else None, 'name': name, 'file': 's/' + f, 'lines': span(f, pat),
                            'in': li, 'out': lo, 'condition': conditional.get(name), 'ran': ran or name == 'np-allocate-registers',
                            'printed_output_changed': changed.get(name), 'class': cls, 'note': note})
for name, pat, li, lo in ra:
    doc['register_allocator_subpasses'].append({'name': name, 'file': 's/cpnanopass.ss', 'lines': span('cpnanopass.ss', pat),
                                                'in': li, 'out': lo, 'condition': conditional.get(name),
                                                'ran': name in changed, 'times_traced': traced.count(name),
                                                'class': W_CLASS})
doc['trace_order'] = traced
Path(out).write_text(json.dumps(doc, indent=1) + '\n')
