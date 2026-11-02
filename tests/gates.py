"""Regression checks for orchestration failures, not theorem validity."""
from pathlib import Path
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent.parent
count = 0

def executable(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)
    path.chmod(0o755)

with tempfile.TemporaryDirectory(prefix='buri-gates-') as directory:
    tree = Path(directory)
    (tree / 'scripts').mkdir()
    (tree / '_build').mkdir()
    shutil.copy(root / 'scripts/check-shen', tree / 'scripts/check-shen')
    executable(tree / 'scripts/shen', '#!/bin/sh\necho "Exception: deliberately failed"\nexit 0\n')
    (tree / '_build/kernel.log').write_text('BURI_TESTS_OK 999\n')
    result = subprocess.run([str(tree / 'scripts/check-shen'), 'tests/kernel.shen'], capture_output=True, text=True)
    assert result.returncode != 0 and 'Exception:' in result.stdout
    assert 'BURI_TESTS_OK' not in result.stdout
    count += 1

    shutil.copy(root / 'scripts/prove', tree / 'scripts/prove')
    executable(tree / 'scripts/rocq', '#!/bin/sh\necho "The Coq Proof Assistant, version 8.18.0"\n')
    (tree / '_build/EquationBridge.v').write_text('stale previously accepted source')
    (tree / '_build/observed-encoder.bits').write_text('stale capture')
    (tree / '_build/ObservedCapture.v').write_text('stale proof')
    (tree / '_build/sealed.bits').write_text('stale sealed capture')
    (tree / '_build/SealedInput.v').write_text('stale sealed proof')
    (tree / '_build/constructor.bits').write_text('stale constructor capture')
    (tree / '_build/ConstructorInput.v').write_text('stale constructor proof')
    (tree / '_build/adapter.bits').write_text('stale adapter capture')
    (tree / '_build/AdapterInput.v').write_text('stale adapter proof')
    (tree / '_build/CheckedIOInput.v').write_text('stale checked IO proof')
    for name in ['bootstrap', 'observer', 'compiler-pass']:
        (tree / '_build' / (name + '.bits')).write_text('stale provenance capture')
    (tree / '_build/encoder-kl.bits').write_text('stale capture')
    (tree / '_build/EncoderKLambda.v').write_text('stale proof input')
    result = subprocess.run([str(tree / 'scripts/prove')], capture_output=True, text=True)
    assert result.returncode != 0
    assert not (tree / '_build/EquationBridge.v').exists()
    assert not (tree / '_build/encoder-kl.bits').exists()
    assert not (tree / '_build/EncoderKLambda.v').exists()
    assert not (tree / '_build/observed-encoder.bits').exists()
    assert not (tree / '_build/ObservedCapture.v').exists()
    assert not (tree / '_build/sealed.bits').exists()
    assert not (tree / '_build/SealedInput.v').exists()
    assert not (tree / '_build/constructor.bits').exists()
    assert not (tree / '_build/ConstructorInput.v').exists()
    assert not (tree / '_build/adapter.bits').exists()
    assert not (tree / '_build/AdapterInput.v').exists()
    assert not (tree / '_build/CheckedIOInput.v').exists()
    for name in ['bootstrap', 'observer', 'compiler-pass']:
        assert not (tree / '_build' / (name + '.bits')).exists()
    assert 'BURI_ROCQ_OK' not in result.stdout
    count += 1

    for folder in ['rocq', 'ports']:
        shutil.copytree(root / folder, tree / folder)
    (tree / 'tests').mkdir()
    for name in ['mutate-wire.py', 'mutate-frontend.py', 'mutate-observed.py', 'mutate-sealed.py', 'mutate-constructor.py', 'mutate-adapter.py', 'mutate-provenance.py', 'mutate-checkedio.py', 'mutate-correctness.py', 'mutate-stages.py', 'mutate-cl-lowering.py', 'mutate-order.py', 'mutate-compose.py', 'mutate-eq1.py', 'mutate-termination.py']:
        shutil.copy(root / 'tests' / name, tree / 'tests' / name)
    for name in ['proof-mutations', 'package-wire.py', 'package-frontend.py', 'package-observed.py', 'package-sealed.py', 'package-constructor.py', 'package-adapter.py', 'package-provenance.py']:
        shutil.copy(root / 'scripts' / name, tree / 'scripts' / name)
    executable(tree / 'scripts/rocq', '#!/bin/sh\necho "Error: Cannot find a physical path bound to logical path Buri"\nexit 1\n')
    result = subprocess.run([str(tree / 'scripts/proof-mutations')], capture_output=True, text=True)
    assert result.returncode != 0 and 'Cannot find' in result.stdout
    assert 'Rejected proof mutation:' not in result.stdout
    count += 1

    raw = tree / 'data.bits'
    module = tree / 'Packaged.v'
    raw.write_text('00')
    module.write_text('Definition native_capture_text : string := "01".')
    result = subprocess.run(['python3', str(root / 'scripts/check-wire-package.py'), str(raw), str(module)],
                            capture_output=True, text=True)
    assert result.returncode != 0 and 'exact captured bytes' in result.stderr
    count += 1

with tempfile.TemporaryDirectory(prefix='buri-encoder-gate-') as directory:
    tree = Path(directory)
    source = tree / 'wire.shen'
    module = tree / 'EncoderSource.v'
    source.write_text('(tc -)\n')
    subprocess.run(['python3', str(root / 'scripts/package-encoder.py'), str(source), str(module)], check=True)
    subprocess.run(['python3', str(root / 'scripts/check-encoder-package.py'), str(source), str(module)], check=True)
    source.write_text('(tc +)\n')
    result = subprocess.run(['python3', str(root / 'scripts/check-encoder-package.py'), str(source), str(module)],
                            capture_output=True, text=True)
    assert result.returncode != 0 and 'exact loaded encoder source bytes' in result.stderr
    count += 1

with tempfile.TemporaryDirectory(prefix='buri-frontend-gate-') as directory:
    tree = Path(directory)
    capture = tree / 'capture.bits'
    module = tree / 'Capture.v'
    capture.write_bytes(b'00')
    subprocess.run(['python3', str(root / 'scripts/package-frontend.py'), str(capture), str(module)], check=True)
    subprocess.run(['python3', str(root / 'scripts/check-frontend-package.py'), str(capture), str(module)], check=True)
    capture.write_bytes(b'01')
    result = subprocess.run(['python3', str(root / 'scripts/check-frontend-package.py'), str(capture), str(module)],
                            capture_output=True, text=True)
    assert result.returncode != 0 and 'exact KLambda capture bytes' in result.stderr
    count += 1

with tempfile.TemporaryDirectory(prefix='buri-observed-gate-') as directory:
    tree = Path(directory)
    capture, module = tree / 'capture.bits', tree / 'Capture.v'
    capture.write_bytes(b'00')
    subprocess.run(['python3', str(root / 'scripts/package-observed.py'), str(capture), str(module)], check=True)
    subprocess.run(['python3', str(root / 'scripts/check-observed-package.py'), str(capture), str(module)], check=True)
    capture.write_bytes(b'01')
    result = subprocess.run(['python3', str(root / 'scripts/check-observed-package.py'), str(capture), str(module)], capture_output=True, text=True)
    assert result.returncode != 0 and 'exact observed compilation bytes' in result.stderr
    count += 1

with tempfile.TemporaryDirectory(prefix='buri-sealed-gate-') as directory:
    tree = Path(directory)
    capture, module = tree / 'capture.bits', tree / 'Capture.v'
    capture.write_bytes(b'00')
    subprocess.run(['python3', str(root / 'scripts/package-sealed.py'), str(capture), str(module)], check=True)
    subprocess.run(['python3', str(root / 'scripts/check-sealed-package.py'), str(capture), str(module)], check=True)
    capture.write_bytes(b'01')
    result = subprocess.run(['python3', str(root / 'scripts/check-sealed-package.py'), str(capture), str(module)], capture_output=True, text=True)
    assert result.returncode != 0 and 'does not match source bytes' in result.stderr
    count += 1

with tempfile.TemporaryDirectory(prefix='buri-constructor-gate-') as directory:
    tree = Path(directory)
    capture, module = tree / 'capture.bits', tree / 'Capture.v'
    capture.write_bytes(b'00')
    subprocess.run(['python3', str(root / 'scripts/package-constructor.py'), str(capture), str(module)], check=True)
    subprocess.run(['python3', str(root / 'scripts/check-constructor-package.py'), str(capture), str(module)], check=True)
    capture.write_bytes(b'01')
    result = subprocess.run(['python3', str(root / 'scripts/check-constructor-package.py'), str(capture), str(module)], capture_output=True, text=True)
    assert result.returncode != 0 and 'does not match source bytes' in result.stderr
    count += 1

with tempfile.TemporaryDirectory(prefix='buri-adapter-gate-') as directory:
    tree = Path(directory)
    capture, module = tree / 'capture.bits', tree / 'Capture.v'
    capture.write_bytes(b'00')
    subprocess.run(['python3', str(root / 'scripts/package-adapter.py'), str(capture), str(module)], check=True)
    subprocess.run(['python3', str(root / 'scripts/check-adapter-package.py'), str(capture), str(module)], check=True)
    capture.write_bytes(b'01')
    result = subprocess.run(['python3', str(root / 'scripts/check-adapter-package.py'), str(capture), str(module)], capture_output=True, text=True)
    assert result.returncode != 0 and 'does not match source bytes' in result.stderr
    count += 1

for profile in ['bootstrap','observer','compiler_pass','checked_io','order_call','observer_forms','io_read','equality_core','equality_seal','eq1_base','eq1_equations','eq1_theory','eq1_kernel']:
    with tempfile.TemporaryDirectory(prefix='buri-provenance-gate-') as directory:
        capture, module = Path(directory)/'capture.bits', Path(directory)/'Capture.v'
        capture.write_bytes(b'00')
        subprocess.run(['python3', str(root/'scripts/package-provenance.py'), profile, str(capture), str(module)], check=True)
        subprocess.run(['python3', str(root/'scripts/check-provenance-package.py'), profile, str(capture), str(module)], check=True)
        capture.write_bytes(b'01')
        result = subprocess.run(['python3', str(root/'scripts/check-provenance-package.py'), profile, str(capture), str(module)], capture_output=True, text=True)
        assert result.returncode != 0 and 'does not match source bytes' in result.stderr
        count += 1

with tempfile.TemporaryDirectory(prefix='buri-source-literal-') as directory:
    source, module = Path(directory)/'source.scm', Path(directory)/'Source.v'
    source.write_text('(define (f x) "quoted text")\n')
    subprocess.run(['python3', str(root/'scripts/package-implementation.py'), 'stock_division', str(source), str(module)], check=True)
    subprocess.run(['python3', str(root/'scripts/check-implementation-package.py'), 'stock_division', str(source), str(module)], check=True)
    module.write_text(module.read_text().replace('quoted text','changed text'))
    result = subprocess.run(['python3', str(root/'scripts/check-implementation-package.py'), 'stock_division', str(source), str(module)], capture_output=True, text=True)
    assert result.returncode != 0 and 'does not match source bytes' in result.stderr
    count += 1

with tempfile.TemporaryDirectory(prefix='buri-report-log-') as directory:
    import os
    tree = Path(directory)
    (tree / 'scripts').mkdir()
    (tree / '_build').mkdir()
    shutil.copy(root / 'scripts/report.py', tree / 'scripts/report.py')
    env = dict(os.environ, PATH=str(tree / 'bin') + os.pathsep + os.environ['PATH'])
    for code in [0, 7]:
        executable(tree / 'bin/make',
                   '#!/bin/sh\necho BEFORE\necho stale > _build/check.log\necho AFTER\nexit ' + str(code) + '\n')
        result = subprocess.run(['python3', str(tree / 'scripts/report.py'), 'check'],
                                env=env, capture_output=True, text=True)
        assert result.returncode == code
        assert (tree / '_build/check.log').read_text() == 'BEFORE\nAFTER\n'
        assert result.stdout == ('BEFORE\nAFTER\n' if code else '')
        count += 1

print(f'BURI_GATE_TESTS_OK {count}')
