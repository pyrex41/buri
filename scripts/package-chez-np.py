"""E2E-22: package Chez nanopass sources and captured IR dumps (bytes only).

This script never decides validity.  It
  * copies exact source/dump bytes into Rocq string literals, which Rocq then
    reads, resolves and checks itself (rocq/ChezNpReader.v, ChezNpGrammar.v);
  * writes a reading aid (spec/chez-np-languages.json) and generated Rocq
    inductive syntax (rocq/ChezNpSyntax.v).  The generated grammar data in
    ChezNpSyntax.v is compared by Rocq against Rocq's own extends-resolution
    of the packaged np-languages.ss text (ChezNpGrammarCheck.v), so a bug here
    makes the proof gate fail rather than change a claim.

usage:
  package-chez-np.py languages NP-LANGUAGES.ss OUT-Input.v OUT.json OUT-Syntax.v
  package-chez-np.py capture TRACE.np CODE.hex CODE.relocs OUT-Input.v
"""
from pathlib import Path
import hashlib
import json
import re
import sys

UPSTREAM = {
    'release': 'csv10.3.0.tar.gz',
    'release_sha256': 'd237d9874c6e8b0ccf7758daa8286a6e825528b13ce3b2bca56eb1f73cddbc2c',
    'git_tag': 'v10.3.0',
    'git_commit': 'adfaf9e6d47a4238a9e5e4bf6a00f9d58792a3db',
    'file': 's/np-languages.ss',
    'sha256': 'db2c01ecfff979bf6b6c2ea2c493c0e2fbe9049f414a5c938f7114b2d48c9f2e',
}


def coq_string(text):
    assert all(ord(c) < 128 for c in text), 'non-ASCII input'
    return '"' + text.replace('"', '""') + '"'


# ---------------------------------------------------------------- reader
def read_all(text):
    """Minimal reader for the define-language subset (reading aid only)."""
    toks = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c == ';':
            i = text.index('\n', i)
        elif c in '()[]':
            toks.append(c)
            i += 1
        elif c == '"':
            j = text.index('"', i + 1)
            toks.append(('str', text[i + 1:j]))
            i = j + 1
        elif text.startswith('#{', i):
            j = text.index('}', i)
            toks.append(text[i:j + 1])
            i = j + 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in '()[]";':
                j += 1
            toks.append(text[i:j])
            i = j
    pos = 0

    def datum():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t in ('(', '['):
            out = []
            while toks[pos] not in (')', ']'):
                out.append(datum())
            pos += 1
            return out
        return t
    out = []
    while pos < len(toks):
        out.append(datum())
    return out


def language_spans(text):
    starts = [m.start() for m in re.finditer(r'\(define-language ', text)]
    spans = []
    for st in starts:
        depth, j = 0, st
        while True:
            c = text[j]
            if c == ';':
                j = text.index('\n', j)
                continue
            if c == '"':
                j = text.index('"', j + 1) + 1
                continue
            if c in '([':
                depth += 1
            elif c in ')]':
                depth -= 1
                if depth == 0:
                    spans.append((st, j + 1))
                    break
            j += 1
    return spans


# ------------------------------------------------- nanopass extends (aid)
def raw_meta(sym):
    """nanopass helpers.ss meta-var->raw-meta-var."""
    i = len(sym) - 1
    while i >= 0 and sym[i] in '*^?':
        i -= 1
    if i == -1:
        return sym
    while i >= 0 and sym[i].isdigit():
        i -= 1
    if i == -1:
        return sym
    return sym[:i + 1]


def parse_alts(items):
    """[(syntax, pretty-or-None)] following nanopass parse-alts."""
    out, k = [], 0
    while k < len(items):
        a = items[k]
        if k + 1 < len(items) and items[k + 1] == '=>':
            out.append((a, items[k + 2]))
            k += 3
        elif isinstance(a, list) and a and a[0] == '=>':
            out.append((a[1], a[2]))
            k += 1
        else:
            out.append((a, None))
            k += 1
    return out


def parse_terms(items):
    out, k = [], 0
    while k < len(items):
        t = items[k]
        if k + 1 < len(items) and items[k + 1] == '=>':
            out.append((t[0], tuple(t[1]), items[k + 2]))
            k += 3
        else:
            out.append((t[0], tuple(t[1]), None))
            k += 1
    return out


def resolve(forms):
    langs = {}
    order = []
    for f in forms:
        assert f[0] == 'define-language'
        name, clauses = f[1], f[2:]
        base = None
        entry = None
        terms = []
        nts = []
        for c in clauses:
            if c[0] == 'nongenerative-id':
                continue
            if c[0] == 'extends':
                base = c[1]
            elif c[0] == 'entry':
                entry = c[1]
            elif c[0] == 'terminals':
                terms.extend(c[1:])
            else:
                nts.append((c[0], list(c[1]), c[2:]))
        if base is None:
            tspecs = parse_terms(terms)
            ntspecs = [(nm, metas, parse_alts(alts)) for nm, metas, alts in nts]
            entry = entry or ntspecs[0][0]
        else:
            b = langs[base]
            entry = entry or b['entry']
            tplus, tminus = [], []
            for grp in terms:
                (tplus if grp[0] == '+' else tminus).extend(parse_terms(grp[1:]))
                assert grp[0] in '+-'
            # freshen-tspecs: drop removed (match type and metas), keep order
            tspecs = []
            pending = list(tminus)
            for t in b['terminals']:
                hit = [m for m in pending if m[0] == t[0] and m[1] == t[1]]
                if hit:
                    pending.remove(hit[0])
                else:
                    tspecs.append(t)
            assert not pending, pending
            for t in tplus:  # add-tspecs prepends one at a time
                tspecs.insert(0, t)
            # partition-ntspecs (result lists are reversed)
            plus, minus = [], []
            for nm, metas, alts in nts:
                ap, am = [], []
                for grp in alts:
                    assert grp[0] in '+-'
                    (ap if grp[0] == '+' else am).extend(parse_alts(grp[1:]))
                if ap:
                    plus.insert(0, (nm, metas, ap))
                if am:
                    minus.insert(0, (nm, metas, am))
            # freshen-ntspecs
            nts2 = []
            for nm, metas, alts in b['nonterminals']:
                m = [x for x in minus if x[0] == nm]
                if not m:
                    nts2.append((nm, metas, list(alts)))
                    continue
                minus.remove(m[0])
                rem = list(m[0][2])
                kept = []
                for a in alts:
                    h = [r for r in rem if r[0] == a[0]]
                    if h:
                        rem.remove(h[0])
                    else:
                        kept.append(a)
                assert not rem, rem
                if kept:
                    nts2.append((nm, m[0][1], kept))
            assert not minus, minus
            # add-ntspecs
            nts3 = []
            remaining = list(plus)
            for nm, metas, alts in nts2:
                m = [x for x in remaining if x[0] == nm]
                if not m:
                    nts3.append((nm, metas, alts))
                    continue
                remaining.remove(m[0])
                alts2 = list(alts)
                for a in m[0][2]:
                    assert all(a[0] != x[0] for x in alts2)
                    alts2.insert(0, a)
                nts3.append((nm, m[0][1], alts2))
            nts3.extend(remaining)
            ntspecs = nts3
        langs[name] = {'entry': entry, 'terminals': tspecs, 'nonterminals': ntspecs}
        order.append(name)
    return order, langs


# ------------------------------------------------------- Rocq rendering
def sx(d):
    """Render a datum as a Rocq ChezNpReader.sexp term."""
    if isinstance(d, list):
        return '(Lst [' + '; '.join(sx(x) for x in d) + '])'
    if isinstance(d, tuple):
        assert d[0] == 'str'
        return '(Str ' + coq_string(d[1]) + ')'
    return '(Atom ' + coq_string(d) + ')'


def grammar_term(lang):
    ts = '[' + '; '.join('(' + coq_string(t) + ', [' + '; '.join(coq_string(m) for m in ms) + '], '
                         + ('None' if h is None else 'Some ' + sx(h)) + ')'
                         for t, ms, h in lang['terminals']) + ']'
    nts = []
    for nm, metas, alts in lang['nonterminals']:
        al = '[' + '; '.join('(' + sx(a) + ', ' + ('None' if p is None else 'Some ' + sx(p)) + ')'
                             for a, p in alts) + ']'
        nts.append('(' + coq_string(nm) + ', [' + '; '.join(coq_string(m) for m in metas) + '], ' + al + ')')
    return '(mkGrammar ' + coq_string(lang['entry']) + ' ' + ts + ' [' + '; '.join(nts) + '])'


def ident(s):
    out = []
    for ch in s:
        if ch.isalnum():
            out.append(ch)
        else:
            out.append({'.': '_', '-': '_', '!': '_bang', '?': '_p', '*': '_star',
                        '/': '_', '$': 'D_', '%': 'P_', '+': 'plus', '>': 'gt',
                        '<': 'lt', '=': 'eq'}.get(ch, '_'))
    return ''.join(out)


def field_types(pattern, lang, prefix, nt_names, meta_to_nt, terminal_metas):
    """Rocq field types for a production pattern (after its keyword)."""
    def ty(p):
        if isinstance(p, list):
            if len(p) == 2 and p[0] == 'maybe':
                return 'option ' + paren(ty(p[1]))
            return tuple_ty(p)
        rm = raw_meta(p)
        if rm in terminal_metas:
            return 'sexp'
        if rm in meta_to_nt:
            return prefix + ident(meta_to_nt[rm])
        raise SystemExit('unknown meta-variable %r' % p)

    def items(ps):
        out, k = [], 0
        while k < len(ps):
            if k + 1 < len(ps) and ps[k + 1] == '...':
                out.append('list ' + paren(ty(ps[k])))
                k += 2
            else:
                out.append(ty(ps[k]))
                k += 1
        return out

    def tuple_ty(ps):
        its = items(ps)
        if not its:
            return 'unit'
        return ' * '.join(paren(t) for t in its) if len(its) > 1 else its[0]
    return items(pattern)


def paren(t):
    return '(' + t + ')' if ' ' in t else t


def inductive(name, lang):
    prefix = ident(name) + '_'
    terminal_metas = {m for _, ms, _ in lang['terminals'] for m in ms}
    meta_to_nt = {}
    for nm, metas, _ in lang['nonterminals']:
        for m in metas:
            meta_to_nt[m] = nm
    lines = []
    first = True
    for nm, metas, alts in lang['nonterminals']:
        tname = prefix + ident(nm)
        lines.append(('Inductive ' if first else 'with ') + tname + ' : Type :=')
        first = False
        for k, (a, _) in enumerate(alts):
            if isinstance(a, list):
                head = a[0] if isinstance(a[0], str) and raw_meta(a[0]) not in terminal_metas | set(meta_to_nt) else None
                pats = a[1:] if head else a
                fts = field_types(pats, lang, prefix, None, meta_to_nt, terminal_metas)
                cname = tname + '_' + str(k) + '_' + ident(head or 'app')
            else:
                fts = field_types([a], lang, prefix, None, meta_to_nt, terminal_metas)
                cname = tname + '_' + str(k) + '_' + ident(a)
            lines.append('| ' + cname + ' : ' + ''.join(paren(t) + ' -> ' for t in fts) + tname)
    return '\n'.join(lines) + '.\n'


def languages(src, out_input, out_json, out_syntax):
    raw = Path(src).read_bytes()
    text = raw.decode('ascii')
    spans = language_spans(text)
    assert len(spans) == 28, len(spans)
    digest = hashlib.sha256(raw).hexdigest()
    if digest != UPSTREAM['sha256']:
        raise SystemExit('np-languages.ss is not the pinned Chez 10.3.0 file')
    Path(out_input).write_text(
        '(* Generated by scripts/package-chez-np.py: exact bytes of Chez Scheme 10.3.0\n'
        '   ' + UPSTREAM['file'] + ' (sha256 ' + digest + ', tag ' + UPSTREAM['git_tag'] + ', commit\n'
        '   ' + UPSTREAM['git_commit'] + ') and the byte spans of its define-language forms.\n'
        '   Packaging only: Rocq reads, counts and resolves these forms itself. *)\n'
        'From Coq Require Import String List.\nImport ListNotations.\nOpen Scope string_scope.\n'
        'Set Warnings "-abstract-large-number".\n'
        'Definition np_languages_sha256 : string := "' + digest + '".\n'
        'Definition np_languages_source : string := ' + coq_string(text) + '.\n'
        'Definition np_language_spans : list (nat * nat) := [' +
        '; '.join('(%d, %d)' % (a, b - a) for a, b in spans) + '].\n')
    forms = [read_all(text[a:b])[0] for a, b in spans]
    order, langs = resolve(forms)
    doc = {'source': dict(UPSTREAM), 'note':
           'Reading aid generated by scripts/package-chez-np.py; Rocq re-resolves the packaged '
           'source and checks rocq/ChezNpSyntax.v against it (ChezNpGrammarCheck.v).',
           'languages': []}
    for nm in order:
        L = langs[nm]
        base = [c[1] for c in forms[order.index(nm)][2:] if c[0] == 'extends']
        doc['languages'].append({
            'name': nm, 'extends': base[0] if base else None, 'entry': L['entry'],
            'span': list(spans[order.index(nm)]),
            'terminals': [{'type': t, 'metas': list(ms), 'printer': h} for t, ms, h in L['terminals']],
            'nonterminals': [{'name': n, 'metas': ms,
                              'productions': [{'syntax': a, 'unparse': p} for a, p in alts]}
                             for n, ms, alts in L['nonterminals']]})
    Path(out_json).write_text(json.dumps(doc, indent=1, default=lambda t: t[1]) + '\n')
    syn = ['(* Generated by scripts/package-chez-np.py from Chez Scheme 10.3.0 s/np-languages.ss\n'
           '   (sha256 ' + digest + ').  Inert syntax: one mutual inductive per nanopass\n'
           '   language with every extends delta resolved; terminals are uninterpreted sexp data.\n'
           '   The grammar_* data below is checked against Rocq\'s own resolution of the packaged\n'
           '   source in ChezNpGrammarCheck.v. *)',
           'From Coq Require Import String List.',
           'From Buri Require Import ChezNpReader ChezNpGrammar.',
           'Import ListNotations.', 'Open Scope string_scope.', '']
    for nm in order:
        syn.append('(* ' + nm + ' *)')
        syn.append(inductive(nm, langs[nm]))
        syn.append('Definition grammar_' + ident(nm) + ' : grammar := ' + grammar_term(langs[nm]) + '.\n')
    syn.append('Definition generated_grammars : list (string * grammar) := [' +
               '; '.join('(' + coq_string(nm) + ', grammar_' + ident(nm) + ')' for nm in order) + '].')
    Path(out_syntax).write_text('\n'.join(syn) + '\n')


def capture(trace, hexfile, relocs, out):
    t = Path(trace).read_bytes().decode('ascii')
    start = t.index('@@@ np-trace\n') + len('@@@ np-trace\n')
    end = t.index('@@@ end\n', start)
    params = t[t.index('@@@ parameters\n') + len('@@@ parameters\n'):t.index('@@@ end\n')]
    h = Path(hexfile).read_bytes().decode('ascii')
    r = Path(relocs).read_bytes().decode('ascii')
    sections = split_trace(t[start:end])
    Path(out).write_text(
        '(* Generated by scripts/package-chez-np.py: exact captured text, packaging only.\n'
        '   np_sections: the np-trace section of ports/chez-np/tarm64le-buri-arm-add.np (sha256\n'
        '   ' + hashlib.sha256(Path(trace).read_bytes()).hexdigest() + ') cut at each\n'
        '   tracer header line "output of NAME:"; scripts/check-chez-np-package.py checks that\n'
        '   the headers and bodies reassemble the trace byte for byte.\n'
        '   arm_code_hex / arm_code_relocs: ports/arm/chez/chez1030-buri-arm-add.{hex,relocs}\n'
        '   (sha256 ' + hashlib.sha256(Path(hexfile).read_bytes()).hexdigest() + ' / '
        + hashlib.sha256(Path(relocs).read_bytes()).hexdigest() + '). *)\n'
        'From Coq Require Import String List.\nImport ListNotations.\nOpen Scope string_scope.\n'
        'Definition np_parameters : string := ' + coq_string(params) + '.\n'
        'Definition np_sections : list (string * string) := [\n' +
        ';\n'.join(' (' + coq_string(n) + ', ' + coq_string(b) + ')' for n, b in sections) + '].\n'
        'Definition arm_code_hex : string := ' + coq_string(h) + '.\n'
        'Definition arm_code_relocs : string := ' + coq_string(r) + '.\n')


HEADER = re.compile(r'^output of (.*):$')


def split_trace(text):
    """Cut the tracer output at its header lines; bodies keep their newlines."""
    out = []
    for line in text.splitlines(keepends=True):
        m = HEADER.match(line.rstrip('\n'))
        if m and line.endswith('\n'):
            out.append([m.group(1), ''])
        else:
            assert out, 'text before the first header'
            out[-1][1] += line
    return [tuple(x) for x in out]


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'languages':
        languages(*sys.argv[2:])
    elif mode == 'capture':
        capture(*sys.argv[2:])
    else:
        raise SystemExit('unknown mode')
