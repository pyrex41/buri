#!/usr/bin/env python3
"""Make a counting copy of the Shen/JIT lowerer, for the rewrite census only (never for witnesses).

Reads upstream src/lowerer/lower.shen and writes a copy in which each rewrite named below wraps its
result as (do (pc.tick Key) Result), then renames it exactly as the build makes build/tools/lower.shen
(Makefile: shen-jit.lower. -> stage0.lower., and the calls to shen-jit.sealed? and
shen-jit.inline-body). pc.tick (tests/shen-jit/capture_passes.shen) only counts, so the copy lowers
to the same code; capture_passes.sh checks that it still reproduces every stage 0 line byte for byte
before its counts are reported.

Each site is (key, anchor): the anchor occurs exactly once, and the wrapped expression is the one
that starts where the anchor ends (or at the anchor itself when it starts with '(' or '[' and ends
with no '-> ').

    instrument_lower.py LOWER.shen OUT.shen
"""
import sys

# A rule's body is the single expression after its "-> "; an anchor ending in "-> " names the rule.
SITES = [
    # share
    ('share-chain', '(let G (shen-jit.lower.fresh shen-jit.lower.else)'),
    # sugar and fixed forms in norm
    ('fn-sealed', '[call F (shen-jit.lower.norm-list Scope Args)]'),
    ('fn-open', '(shen-jit.lower.norm Scope (shen-jit.lower.fn-call F Args))'),
    ('lambda-app-more', '(shen-jit.lower.norm Scope [[let X A Body] | More])'),
    ('lambda-app', '[let X (shen-jit.lower.norm Scope A) (shen-jit.lower.norm [X | Scope] Body)]'),
    ('dynamic-apply', '(shen-jit.lower.norm-apply (shen-jit.lower.norm Scope F)'),
    ('curried-apply', '(shen-jit.lower.norm-apply [apply F X] Xs)'),
    ('unified-now', '(shen-jit.lower.unified-now (if (= Is is)'),
    ('bound-now', '(shen-jit.lower.bound-now (shen-jit.lower.norm Scope X)'),
    ('cond', 'Scope [cond | Clauses] -> '),
    ('thaw', '[apply (shen-jit.lower.norm Scope X)]'),
    ('type', 'Scope [type X _] -> '),
    ('protect', 'Scope [protect X] -> '),
    ('trap-lambda', 'Scope [trap-error X [lambda E H]] -> '),
    ('trap-other', 'Scope [trap-error X H] -> '),
    ('eval-kl', 'Scope [eval-kl X] -> '),
    # constant folding
    ('fold-cons', '  cons [[const A] [const B]] -> '),
    ('fold-plus', '  + [[const A] [const B]] -> '),
    ('fold-minus', '  - [[const A] [const B]] -> '),
    # inlining
    ('sealed-inline', '(shen-jit.lower.inline F (hd Inline) (hd (tl Inline)) Args)'),
    ('open-inline', '  F Inline Args -> '),
    ('inline-int-arg', '  -> (shen-jit.lower.inline-numbers F Ps (shen-jit.lower.subst P N Body) As Qs Bs)'),
    ('inline-frozen', '  -> (shen-jit.lower.inline-frozen F Ps As (shen-jit.lower.thaw-with P E Normal) Qs Bs)'),
    # freeze copying
    ('let-frozen-copy', '(shen-jit.lower.frozen-in X E Body)'),
    ('let-frozen-keep', '(shen-jit.lower.frozen-late X E Body))))'),
    ('frozen-late-hoist', '[if [or C1 C2] [let X [freeze E] [if C1 Y1 Y2]] [const false]]'),
    ('bound-now-frozen', '(shen-jit.lower.bound-now A B C E)'),
    # Prolog rewrites added at 0.6
    ('cut-fail', '(shen-jit.lower.norm Scope [if [shen.unlocked? L] [shen.lock K L] false])'),
    ('deref-eq', '(shen-jit.lower.norm Scope [shen-jit.deref= X Y B])'),
    # lambda copying
    ('let-lambda', '(shen-jit.lower.apply-in X Params (shen-jit.lower.lambda-body V) Body)'),
]

def expr_end(s, i):
    """End (exclusive) of the expression starting at s[i], which is ( or [."""
    assert s[i] in '([', s[i:i + 40]
    depth, j = 0, i
    while True:
        c = s[j]
        if c == '"':
            j = s.index('"', j + 1)
        elif c in '([':
            depth += 1
        elif c in ')]':
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1

def instrument(text):
    for key, anchor in SITES:
        assert text.count(anchor) == 1, (key, text.count(anchor))
        a = text.index(anchor)
        if anchor.rstrip().endswith('->'):
            start = a + len(anchor)
        else:
            start = a + len(anchor) - len(anchor.lstrip())
            if anchor.lstrip().startswith('-> '):
                start += 3
        end = expr_end(text, start)
        text = text[:start] + '(do (pc.tick %s) %s)' % (key, text[start:end]) + text[end:]
    return text

def rename(text):
    # As the Makefile's rule for build/tools/%.shen.
    return (text.replace('shen-jit.lower.', 'stage0.lower.')
                .replace('(shen-jit.sealed? ', '(stage0.sealed? ')
                .replace('(shen-jit.inline-body ', '(stage0.inline-body '))

if __name__ == '__main__':
    src, out = sys.argv[1:3]
    open(out, 'w').write(rename(instrument(open(src).read())))
