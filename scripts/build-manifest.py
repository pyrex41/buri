"""Build identity manifests (E2E-03). Packaging/orchestration only.

A manifest records the bytes that went into and came out of one gate build:
source files, pinned tool payloads, the dynamic runtime that launched them,
the exact gate commands and flags, relevant environment variables and the
produced proof objects. Comparing two manifests is IDENTITY evidence only:
equal bytes from independent builds show the build is reproducible, never
that any compiler, checker or runtime is correct. This script decides no
theorem validity; Coq/coqchk under `make prove` does that.

usage: build-manifest.py write OUT.json
       build-manifest.py compare A.json B.json

compare exit status: 0 identical (route differences explained), 1 identity
difference, 2 unusable manifest, 3 identical bytes but different recorded
environment variables.
"""
import hashlib
import json
import os
import pathlib
import platform
import re
import resource
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parent.parent
SCHEMA = 'buri-build-manifest-1'
EXCLUDED_DIRS = {'.git', '.tools', '_build', '__pycache__', '.claude'}
# Local-only CA file the Earthfile may copy into a container (never a source).
EXCLUDED_FILES = {'ci-extra-ca.crt'}
EXCLUDED_SUFFIXES = ('.vo', '.vos', '.vok', '.glob', '.aux', '.lia.cache')
ENVIRONMENT = ['SHEN_SCHEME_HOME', 'SHEN_SCHEME_RUNTIME', 'SHEN_SCHEME_BOOT',
               'OCAMLFIND_CONF', 'OCAMLPATH', 'OCAMLRUNPARAM', 'OCAMLLIB',
               'CAMLLIB', 'COQPATH', 'COQLIB', 'COQCORELIB', 'COQ_COLORS',
               'COQEXTRAFLAGS', 'LC_ALL', 'LANG', 'TZ', 'SOURCE_DATE_EPOCH',
               'PYTHONHASHSEED', 'PYTHONDONTWRITEBYTECODE']
INFORMATIONAL_ENVIRONMENT = ['PATH', 'TMPDIR', 'HOME', 'SHELL']


def digest(path):
    h = hashlib.sha256()
    with open(path, 'rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def entry(path):
    """Content identity of one tree entry: symlink target or file bytes."""
    if path.is_symlink():
        return 'symlink:' + os.readlink(path)
    return digest(path)


def tree(base):
    """Map relative path -> identity for every file/symlink below base."""
    base = pathlib.Path(base)
    out = {}
    for directory, dirs, files in os.walk(base):
        dirs.sort()
        here = pathlib.Path(directory)
        for name in sorted(files) + sorted(d for d in dirs if (here / d).is_symlink()):
            path = here / name
            out[str(path.relative_to(base))] = entry(path)
    return dict(sorted(out.items()))


def tree_digest(files):
    h = hashlib.sha256()
    for name, value in sorted(files.items()):
        h.update(name.encode() + b'\0' + value.encode() + b'\n')
    return h.hexdigest()


def sources():
    out = {}
    for directory, dirs, files in os.walk(root):
        here = pathlib.Path(directory)
        dirs[:] = sorted(d for d in dirs if d not in EXCLUDED_DIRS
                         and not (here == root and d.startswith('result')))
        for name in sorted(files):
            path = here / name
            relative = path.relative_to(root)
            if name.endswith(EXCLUDED_SUFFIXES) or (here == root and name.startswith('result')):
                continue
            if name == '.tools' or (here == root and (name in EXCLUDED_DIRS or name in EXCLUDED_FILES)):
                continue
            out[str(relative)] = entry(path)
    return dict(sorted(out.items()))


def run(command, **kwargs):
    # A nested `make manifest` must not leak MAKEFLAGS/MAKELEVEL into probes.
    env = {k: v for k, v in os.environ.items() if k not in ('MAKEFLAGS', 'MAKELEVEL', 'MFLAGS')}
    try:
        result = subprocess.run(command, cwd=root, capture_output=True, text=True, env=env, **kwargs)
    except OSError as error:
        return {'command': command, 'error': str(error)}
    return {'command': command, 'returncode': result.returncode,
            'stdout': result.stdout, 'stderr': result.stderr}


def launcher():
    path = root / '.tools/launcher.json'
    if path.is_file():
        return json.loads(path.read_text())
    host = (root / (root / '.tools/host-path').read_text().strip())
    return {'schema': 'buri-launcher-1', 'route': 'host-bootstrap',
            'loader': None, 'library_path': [],
            'shen_payload': str(host.resolve().parents[1]),
            'shen_executable': str(host.resolve()),
            'rocq_payload': str((root / '.tools/rocq').resolve())}


def elf_interpreter(path):
    data = pathlib.Path(path).read_bytes()
    if data[:4] != b'\x7fELF':
        return None
    marker = data.find(b'/lib64/ld-linux')
    if marker < 0:
        return None
    return data[marker:data.index(b'\0', marker)].decode()


def runtime_libraries(launch, executable):
    """Resolve the shared objects the dynamic loader would map."""
    loader = launch.get('loader') or elf_interpreter(executable)
    if loader is None:
        return {'loader': None, 'libraries': {}}
    command = [loader]
    if launch.get('library_path'):
        command += ['--library-path', ':'.join(launch['library_path'])]
    command += ['--list', str(executable)]
    listing = run(command)
    libraries = {}
    for line in listing.get('stdout', '').splitlines():
        parts = line.split()
        if '=>' in parts and len(parts) >= 3 and parts[2].startswith('/'):
            target = os.path.realpath(parts[2])
            libraries[parts[0]] = {'path': target, 'sha256': digest(target)}
    real = os.path.realpath(loader)
    return {'loader': {'path': real, 'sha256': digest(real)}, 'libraries': libraries}


def tool_identity(launch):
    shen_payload = pathlib.Path(launch['shen_payload'])
    rocq_payload = pathlib.Path(launch['rocq_payload'])
    shen_files = tree(shen_payload)
    rocq_files = tree(rocq_payload)
    lock = (root / 'rocq-packages.lock').read_text().split()
    host_path = (root / '.tools/host-path').read_text().strip()
    host_launcher = pathlib.Path(host_path if host_path.startswith('/') else root / host_path)
    coq_executables = {name: value for name, value in rocq_files.items()
                       if name.startswith('usr/bin/')}
    return {
        'shen_scheme': {
            'kind': 'prebuilt-binary-pinned-by-archive-hash',
            'archive_sha256_declared': json.loads(
                (root / 'toolchain.lock.json').read_text())['host_archive_sha256'],
            'payload_tree_sha256': tree_digest(shen_files),
            'payload_files': shen_files,
        },
        'kernel_overlay': {'path': '.tools/t-star-pr117.shen',
                           'sha256': digest(root / '.tools/t-star-pr117.shen')},
        'coq': {
            'kind': 'ubuntu-snapshot-debs-extracted-unmodified',
            'debs_declared': dict(zip(lock[1::2], lock[0::2])),
            'payload_tree_sha256': tree_digest(rocq_files),
            'payload_file_count': len(rocq_files),
            'payload_files': rocq_files,
            'executables': coq_executables,
        },
        'self_report': {
            'coqc_version': run([str(root / 'scripts/rocq'), 'coqc', '--version']).get('stdout'),
        },
        '_launch': {
            'route': launch['route'],
            'shen_launcher': {'path': str(host_launcher), 'sha256': entry(host_launcher),
                              'is_elf': elf_interpreter(host_launcher) is not None},
            'coqc_launcher_is_elf': elf_interpreter(root / '.tools/rocq/usr/bin/coqc') is not None,
            'shen_runtime': runtime_libraries(launch, launch['shen_executable']),
            'coqc_runtime': runtime_libraries(launch, rocq_payload / 'usr/bin/coqc'),
            'payload_roots': {'shen': str(shen_payload), 'coq': str(rocq_payload)},
            'nixpkgs_revision': launch.get('nixpkgs_revision'),
        },
    }


def orchestration():
    shell = os.path.realpath('/bin/sh')
    make = run(['make', '--version']).get('stdout', '').splitlines()[:1]
    return {
        'bin_sh': {'path': shell, 'sha256': digest(shell)},
        'python': {'version': platform.python_version(),
                   'executable': os.path.realpath(sys.executable),
                   'sha256': digest(os.path.realpath(sys.executable))},
        'make': make,
        'machine': platform.machine(),
        'kernel_release': platform.release(),
    }


def commands():
    prove = (root / 'scripts/prove').read_text().splitlines()
    rocq = (root / 'scripts/rocq').read_text().splitlines()
    return {
        'make_dry_run': run(['make', '--no-print-directory', '-n', 'test', 'prove']).get('stdout', '').splitlines(),
        'coq_invocations': [line.strip() for line in prove if 'scripts/rocq' in line],
        'coq_launcher': [line.strip() for line in rocq if line.strip().startswith(('ulimit', 'export', 'exec'))],
        'shen_launcher': [line.strip() for line in (root / 'scripts/shen').read_text().splitlines()
                          if line.strip().startswith(('unset', 'exec', '-e', '-l'))],
    }


# Wall-clock lines Shen-Scheme prints after each top-level form in test/export logs.
VOLATILE_LOG_LINE = re.compile(rb'^run time: [0-9.e-]+ secs$', re.M)


def outputs():
    build = root / '_build'
    groups = {'proof_objects': {}, 'glob': {}, 'proof_sources': {}, 'generated': {},
              'logs_normalized': {}, '_volatile': {'logs_raw': {}, 'coq_aux': {}}}
    for path in sorted(build.rglob('*')):
        if not path.is_file() or path.name == 'manifest.json' or 'earthly' in path.parts:
            continue
        name = str(path.relative_to(build))
        if path.suffix in ('.vo', '.vos', '.vok'):
            groups['proof_objects'][name] = digest(path)
        elif path.suffix == '.glob':
            groups['glob'][name] = digest(path)
        elif path.suffix == '.v':
            groups['proof_sources'][name] = digest(path)
        elif path.suffix == '.log':
            data = path.read_bytes()
            groups['_volatile']['logs_raw'][name] = hashlib.sha256(data).hexdigest()
            groups['logs_normalized'][name] = hashlib.sha256(
                VOLATILE_LOG_LINE.sub(b'run time: <masked> secs', data)).hexdigest()
        elif path.suffix == '.aux':
            # coqc .aux files hold the absolute source path and proof timings;
            # coqchk and the gates never read them.
            groups['_volatile']['coq_aux'][name] = digest(path)
        else:
            groups['generated'][name] = digest(path)
    return groups


def environment():
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    return {
        'variables': {name: os.environ.get(name) for name in ENVIRONMENT},
        '_informational': {name: os.environ.get(name) for name in INFORMATIONAL_ENVIRONMENT},
        '_stack_limit_of_manifest_process': [soft, hard],
    }


def git_identity():
    head = run(['git', 'rev-parse', 'HEAD'])
    status = run(['git', 'status', '--porcelain'])
    return {'head': head.get('stdout', '').strip() or None,
            'dirty': bool(status.get('stdout', '').strip()) if status.get('returncode') == 0 else None}


def write(out):
    launch = launcher()
    data = {
        'schema': SCHEMA,
        'kind': 'identity-evidence-not-proof',
        'sources': sources(),
        'tools': tool_identity(launch),
        'commands': commands(),
        'environment': environment(),
        'outputs': outputs(),
        '_orchestration': orchestration(),
        '_git': git_identity(),
    }
    data['summary'] = {
        'source_tree_sha256': tree_digest(data['sources']),
        'proof_objects_sha256': tree_digest(data['outputs']['proof_objects']),
        'proof_object_count': len(data['outputs']['proof_objects']),
        'generated_sha256': tree_digest(data['outputs']['generated']),
    }
    pathlib.Path(out).write_text(json.dumps(data, indent=1, sort_keys=True) + '\n')
    print('BURI_MANIFEST_WRITTEN %s route=%s sources=%d proof_objects=%d' % (
        out, launch['route'], len(data['sources']), len(data['outputs']['proof_objects'])))


# Keys beginning with '_' are expected to differ between routes; each gets an
# explanation. Everything else is identity-relevant.
EXPLANATIONS = {
    '_launch': 'launcher/runtime differs by route: host route execs payload ELF files with the '
               'host /lib64 loader, host glibc and host libgmp; nix route uses pinned nixpkgs '
               'glibc/gmp through an explicit loader. Payload bytes are compared separately.',
    '_orchestration': 'orchestration tools (/bin/sh, python, make) are not pinned on the host route',
    '_git': 'nix builds see no .git directory; git identity is informational',
    '_informational': 'PATH/TMPDIR/HOME/SHELL contain build-local paths',
    '_volatile': 'raw logs contain Shen wall-clock "run time" lines (compared after masking in '
                 'outputs/logs_normalized); coqc .aux files contain the absolute source path and '
                 'proof timings and are read by no gate',
    '_stack_limit_of_manifest_process': 'stack limit of the manifest process, not of coqc '
               '(scripts/rocq always sets ulimit -s 65536)',
}


def flatten(value, prefix=()):
    if isinstance(value, dict) and value:
        for key, item in value.items():
            yield from flatten(item, prefix + (key,))
    else:
        yield prefix, value


def compare(a_path, b_path):
    a = json.loads(pathlib.Path(a_path).read_text())
    b = json.loads(pathlib.Path(b_path).read_text())
    if a.get('schema') != SCHEMA or b.get('schema') != SCHEMA:
        print('BURI_MANIFEST_SCHEMA_MISMATCH')
        return 2
    fa, fb = dict(flatten(a)), dict(flatten(b))
    identity, explained, environment = [], [], []
    for key in sorted(set(fa) | set(fb), key=lambda k: tuple(map(str, k))):
        left, right = fa.get(key, '<absent>'), fb.get(key, '<absent>')
        if left == right:
            continue
        reason = next((EXPLANATIONS[k] for k in key if k in EXPLANATIONS), None)
        if reason:
            explained.append((key, left, right, reason))
        elif key[:2] == ('environment', 'variables'):
            environment.append((key, left, right, None))
        else:
            identity.append((key, left, right, None))

    def show(value):
        text = json.dumps(value)
        return text if len(text) <= 160 else text[:157] + '...'
    for key, left, right, _ in environment:
        print('ENVIRONMENT-DIFF %s\n  A: %s\n  B: %s' % ('/'.join(key), show(left), show(right)))
    for key, left, right, _ in identity:
        print('IDENTITY-DIFF %s\n  A: %s\n  B: %s' % ('/'.join(key), show(left), show(right)))
    reasons = {}
    for key, left, right, reason in explained:
        reasons.setdefault(reason, []).append(key)
        print('EXPLAINED-DIFF %s\n  A: %s\n  B: %s' % ('/'.join(key), show(left), show(right)))
    for reason, keys in reasons.items():
        print('EXPLANATION (%d keys): %s' % (len(keys), reason))
    count = sum(1 for k in fa if not any(part.startswith('_') for part in k))
    if identity:
        print('BURI_MANIFEST_DIFFERENT %d identity differences, %d environment, %d explained' % (
            len(identity), len(environment), len(explained)))
        return 1
    if environment:
        # Distinct outcome: every compared byte agrees, but the recorded
        # environments were not the same, so the builds are not the same build.
        print('BURI_MANIFEST_SAME_BYTES_DIFFERENT_ENVIRONMENT %d identity entries equal; '
              '%d environment differences; %d explained route differences' % (
                  count, len(environment), len(explained)))
        return 3
    print('BURI_MANIFEST_IDENTICAL %d identity entries equal; %d explained route differences' % (count, len(explained)))
    return 0


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == 'write':
        write(sys.argv[2])
    elif len(sys.argv) == 4 and sys.argv[1] == 'compare':
        sys.exit(compare(sys.argv[2], sys.argv[3]))
    else:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
