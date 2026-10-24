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
    (tree / '_build/encoder-kl.bits').write_text('stale capture')
    (tree / '_build/EncoderKLambda.v').write_text('stale proof input')
    result = subprocess.run([str(tree / 'scripts/prove')], capture_output=True, text=True)
    assert result.returncode != 0
    assert not (tree / '_build/EquationBridge.v').exists()
    assert not (tree / '_build/encoder-kl.bits').exists()
    assert not (tree / '_build/EncoderKLambda.v').exists()
    assert 'BURI_ROCQ_OK' not in result.stdout
    count += 1

    for folder in ['rocq', 'ports']:
        shutil.copytree(root / folder, tree / folder)
    (tree / 'tests').mkdir()
    for name in ['mutate-wire.py', 'mutate-frontend.py']:
        shutil.copy(root / 'tests' / name, tree / 'tests' / name)
    for name in ['proof-mutations', 'package-wire.py', 'package-frontend.py']:
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

print(f'BURI_GATE_TESTS_OK {count}')
