"""Process orchestration/provenance only. No theorem-validity decisions here."""
import hashlib
import json
import pathlib
import re
import subprocess
import sys
from datetime import datetime, timezone

root = pathlib.Path(__file__).resolve().parent.parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def manifest():
    names = subprocess.check_output(
        ['git', 'ls-files', '--cached', '--others', '--exclude-standard'], cwd=root,
        text=True).splitlines()
    return {name: digest(root / name) for name in sorted(set(names)) if (root / name).is_file()}

if sys.argv[1] == 'before':
    (root / '_build/source-before.json').write_text(json.dumps(manifest(), indent=2))
    (root / '_build/report.json').unlink(missing_ok=True)
    sys.exit(0)

before = json.loads((root / '_build/source-before.json').read_text())
assert before == manifest(), 'Source changed during checking; no report issued.'
checks = (root / '_build/check.log').read_text()
counts = [int(n) for n in re.findall(r'^BURI_TESTS_OK (\d+)$', checks, re.M)]
assert len(counts) == 3, 'Incomplete test gate output'
assert 'BURI_ROCQ_OK 28 audited theorems; 18 equation bridges; 12 native compiler schemas; coqchk replay passed' in checks
assert checks.count('Rejected proof mutation:') == 4
host_path = (root / '.tools/host-path').read_text().strip()
host_root = (root / host_path).resolve().parents[1]
host_files = {str(p.relative_to(root)): digest(p) for p in sorted(host_root.rglob('*'))
              if p.is_file() and (p.name.endswith(('.so', '.boot')) or p.name == 'shen-scheme')}
report = {
    'schema': 'buri-evidence-1',
    'created_at': datetime.now(timezone.utc).isoformat(),
    'source_sha256': before,
    'host_sha256': host_files,
    'toolchain': json.loads((root / 'toolchain.lock.json').read_text()),
    'formal_model_proofs': {
        'checker': 'Coq 8.18.0 / coqchk',
        'audit_log_sha256': digest(root / '_build/rocq/Audit.log'),
        'audit_log': '_build/rocq/Audit.log',
        'audited_theorems': 28,
        'custom_axioms': [],
        'scope': ['arithmetic reference compiler', 'equational certificate calculus',
                  'lexical lambda evaluator fuel stability and determinism', 'let-to-lambda lowering', '12 actual compiler-output schema equivalences'],
    },
    'equation_bridge': {'checked_equations': 18, 'checked_theorem_statements': 2,
                       'exporter_correctness': 'assumed; not mechanically proved'},
    'native_translation_validation': {'schemas': 12, 'domain': 'all exact integer inputs',
        'source_decoder_correctness': 'assumed; not mechanically proved',
        'output_transcript_sha256': digest(root / '_build/compiler-output.sexp')},
    'shen_tests': {'kernel': counts[0], 'evaluator': counts[1]},
    'port_conformance': {'port': 'shen-scheme', 'cases': counts[2], 'evidence': 'sampled-agreement'},
    'rejected_proof_mutations': 4,
    'open': ['Shen checker correspondence to Rocq', 'Shen evaluator correspondence to Rocq',
             'Shen-to-KLambda compiler preservation', 'Shen-Scheme backend preservation',
             'primitive representation correctness', 'System S and PR117 preservation',
             'Chez/native machine-code correctness', 'artifact execution refinement'],
    'trusted': ['Rocq kernel and its execution environment', 'formal theorem statements',
                'source/export byte correspondence', 'Shen-Scheme/Chez for Shen-side results',
                'OS and hardware'],
    'port_verified': False,
}
(root / '_build/report.json').write_text(json.dumps(report, indent=2) + '\n')
print('Wrote _build/report.json (formal-model proofs and port tests kept separate)')
