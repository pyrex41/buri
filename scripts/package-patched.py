"""Byte packaging of the proposed upstream port patches (port-fix lane).

Packaging only, never acceptance: it checks the pinned identity of each
vendored upstream file and of each patch file, applies the unified diff with
the system `patch` program into an output directory, checks the pinned blob
of the patched result, and (for the patched multiply) copies exact definition
bytes into a Coq string literal. Reading, decoding, admission and every
theorem are Rocq computations (rocq/SchemePatched.v, rocq/CLLoweringPatch.v,
rocq/CLMultiplyPatched.v).

  apply OUT               write OUT/shen-scheme/{compiler.shen,primitives.scm}, OUT/shen-cl/{compiler.shen,primitives.lsp}
  check-branches OUT      ports/compiler-branches-patched.shen is the patched extraction
  multiply OUT DEST.v     exact bytes of the patched |shen-cl.multiply|
"""
from pathlib import Path
import hashlib
import shutil
import subprocess
import sys

# (output path, vendored upstream file, upstream blob, patch, patch sha256, patched blob)
PATCHES = [
    ('shen-scheme/compiler.shen', 'ports/upstream/compiler.shen', '42ac753b8f305c578998b74693fc85b28112a814',
     'ports/patches/shen-scheme-compiler.diff', '097f3a3edeaaa3d0e064d573d220b7a9318e8d93c035610ca12709fba2aa7136',
     '8a0aa129faae22e6df57094a559c0366e85d91f6'),
    ('shen-cl/compiler.shen', 'ports/upstream/shen-cl/compiler.shen', '2d624377c02030f9513769f7bad11e84330b8c5a',
     'ports/patches/shen-cl-compiler.diff', 'e822c30069808ebbae2b5d812915165819f664adceadb9cda09566ff55c7fdec',
     '60522d0924b44a218161bced9771783192ae301d'),
    ('shen-cl/primitives.lsp', 'ports/upstream/shen-cl/primitives.lsp', 'f9b11c8a0b57c8492e66094d5e236a8711983e7a',
     'ports/patches/shen-cl-primitives.diff', '577724bc2d477217c430d8967ad7fd1784f67512f4b2e9aaec6c76d8c323b895',
     '3872f83e8a50f5b4e9c445380dd52c839dddccc2'),
    # Wave-D primitives lane: kl:intern no longer maps digit-led names through
    # string->number (rocq/SchemeIntern.v; bytes packaged by package-prims2.py).
    ('shen-scheme/primitives.scm', 'ports/upstream/primitives.scm', '92b8875a276848b473c59879f075f429ba44a7a0',
     'ports/patches/shen-scheme-primitives.diff', '6c21e6799c5bf23ef17ff040d71b0312aa06679a39dd06829543242cb4e991d3',
     '526a89b2d7693e11f50b4726efbd2ed8f111d1fe'),
]
# Upstream test change that accompanies the multiply patch (applied only in the
# native reproduction; the test file is not vendored).
TEST_PATCH = ('ports/patches/shen-cl-primitives-tests.diff',
              '290b8d822a81d77e3fcf22a6b200c81c14953d3b9f15ed819f30621cfe4c57ec')


def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def apply(out):
    out = Path(out)
    data = Path(TEST_PATCH[0]).read_bytes()
    if hashlib.sha256(data).hexdigest() != TEST_PATCH[1]:
        raise SystemExit('Pinned patch hash mismatch: ' + TEST_PATCH[0])
    for target, source, sblob, patch, psha, pblob in PATCHES:
        raw = Path(source).read_bytes()
        if blob(raw) != sblob:
            raise SystemExit('Pinned upstream blob mismatch: ' + source)
        if hashlib.sha256(Path(patch).read_bytes()).hexdigest() != psha:
            raise SystemExit('Pinned patch hash mismatch: ' + patch)
        dest = out / target
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, dest)
        subprocess.run(['patch', '--quiet', '--forward', '--no-backup-if-mismatch', '-r', '-',
                        str(dest), patch], check=True)
        if blob(dest.read_bytes()) != pblob:
            raise SystemExit('Patched blob mismatch: ' + target)


def extract(source, name):
    start = source.index('(define ' + name + '\n')
    depth = 0
    for i in range(start, len(source)):
        depth += (source[i] == '(') - (source[i] == ')')
        if depth == 0:
            return source[start:i + 1]
    raise SystemExit('Unterminated upstream definition')


def check_branches(out):
    text = (Path(out) / 'shen-scheme/compiler.shen').read_text()
    header_start = text.index('(package _scm')
    header = text[header_start:text.index('\n\n', header_start)]
    names = ['yields-boolean?', 'force-boolean', 'emit-symbol', 'emit-let', 'emit-if',
             'emit-cond', 'emit-cond-clauses', 'emit-equality-check']
    for name in names:
        if text.count('(define ' + name + '\n') != 1:
            raise SystemExit('Patched compiler branch is not uniquely defined: ' + name)
    expected = '(tc -)\n' + header + '\n\n' + '\n\n'.join(extract(text, n) for n in names) + '\n\n)\n'
    captured = Path('ports/compiler-branches-patched.shen').read_text()
    comment, _, body = captured.partition('(tc -)\n')
    if not comment or any(not line.startswith('\\\\ ') for line in comment.splitlines()):
        raise SystemExit('Patched compiler branches capture has a non-comment prefix')
    if '(tc -)\n' + body != expected:
        raise SystemExit('Patched compiler branches differ from the patched upstream file')


def multiply(out, dest):
    sys.path.insert(0, 'scripts')
    import importlib.util
    spec = importlib.util.spec_from_file_location('pp', 'scripts/package-primitives.py')
    pp = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(pp)
    path = Path(out) / 'shen-cl/primitives.lsp'
    text = path.read_bytes()
    if any(b >= 128 for b in text):
        raise SystemExit('Non-ASCII patched source')
    text = text.decode()
    opening = '(defun |shen-cl.multiply| (x y)\n'
    if text.count(opening) != 1:
        raise SystemExit('Patched multiply not unique')
    start = text.index(opening)
    end = pp.form_end(text, start)
    body = text[start:end].replace('"', '""')
    Path(dest).write_text(
        '(* Generated by scripts/package-patched.py: exact bytes of the patched\n'
        '   |shen-cl.multiply| (upstream primitives.lsp blob f9b11c8a with\n'
        '   ports/patches/shen-cl-primitives.diff applied; patched blob 3872f83e).\n'
        '   Nothing here is decoded. *)\n'
        'From Coq Require Import String.\n'
        'Open Scope string_scope.\n'
        'Definition patched_multiply_span : nat * nat := (%d, %d).\n'
        'Definition patched_multiply_source : string := "%s\n".\n' % (start, end, body))


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'apply':
        apply(sys.argv[2])
    elif cmd == 'check-branches':
        check_branches(sys.argv[2])
    elif cmd == 'multiply':
        multiply(sys.argv[2], sys.argv[3])
    else:
        raise SystemExit('Unknown command')
