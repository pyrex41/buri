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
rows = re.findall(r'^BURI_SUITE_OK (\w+) (\d+)$', checks, re.M)
suite_counts = {name: int(n) for name, n in rows}
assert len(rows) == 4 and set(suite_counts) == {'kernel', 'evaluator', 'wire', 'conformance'}, 'Incomplete suite gates'
assert 'BURI_ROCQ_OK 61 audited theorems; 18 equation bridges; 12 native compiler schemas; raw capture validated; coqchk replay passed' in checks
assert checks.count('Rejected proof mutation:') == 12
assert re.findall(r'^BURI_GATE_TESTS_OK (\d+)$', checks, re.M) == ['5']
host_path = (root / '.tools/host-path').read_text().strip()
host_root = (root / host_path).resolve().parents[1]
host_files = {str(p.relative_to(root)): digest(p) for p in sorted(host_root.rglob('*'))
              if p.is_file() and (p.name.endswith(('.so', '.boot')) or p.name == 'shen-scheme')}
report = {
    'schema': 'buri-evidence-2',
    'created_at': datetime.now(timezone.utc).isoformat(),
    'source_sha256': before,
    'host_sha256': host_files,
    'toolchain': json.loads((root / 'toolchain.lock.json').read_text()),
    'formal_model_proofs': {
        'checker': 'Coq 8.18.0 / coqchk',
        'audit_log_sha256': digest(root / '_build/rocq/Audit.log'),
        'audit_log': '_build/rocq/Audit.log',
        'audited_theorems': 61,
        'custom_axioms': [],
        'scope': ['arithmetic reference compiler', 'equational certificate calculus',
                  'lexical lambda evaluator fuel stability and determinism', 'let-to-lambda lowering', '12 actual compiler-output schema equivalences',
                  'exact wire decoding, lexical resolution and symbolic normalization',
                  'raw captured-data validation and complete record coverage',
                  'source-linked encoder termination, unique output and decoding roundtrip'],
    },
    'equation_bridge': {'checked_equations': 18, 'checked_theorem_statements': 2,
                       'exporter_correctness': 'assumed; not mechanically proved'},
    'native_translation_validation': {'schemas': 12, 'domain': 'all exact integer inputs',
        'source_decoder': 'formal admitted grammar inside Rocq',
        'name_resolution_preservation': 'machine-checked',
        'symbolic_normalization_preservation': 'machine-checked',
        'capture_wire_identity': 'machine-checked for supplied Rocq input',
        'record_coverage': 'machine-checked for the complete supplied capture',
        'capture_encoder_correspondence': 'source-linked fragment proved; native execution and representation assumed',
        'capture_sha256': digest(root / '_build/native-capture.bits'),
        'captured_proof_input_sha256': digest(root / '_build/NativeCapture.v'),
        'output_transcript_sha256': digest(root / '_build/compiler-output.sexp')},
    'encoder_program_verification': {
        'source': 'shen/wire.shen',
        'source_sha256': digest(root / 'shen/wire.shen'),
        'proof_input_sha256': digest(root / '_build/EncoderSource.v'),
        'source_to_program': 'exact rendered-source equality checked inside Rocq',
        'domain': 'all finite abstract datums and byte strings',
        'evidence': 'source-linked-fragment-proof',
        'proved': ['termination in the admitted semantics', 'unique canonical output',
                   'decoding recovers original datum'],
        'assumed_for_native_execution': ['reader/define compilation preservation',
            'native input representation and primitive contracts',
            'Shen-Scheme/Chez/runtime preservation', 'specified source is loaded without rebinding'],
        'native_execution_verified': False,
    },
    'shen_tests': {'kernel': suite_counts['kernel'], 'evaluator': suite_counts['evaluator'],
                   'wire': suite_counts['wire']},
    'port_conformance': {'port': 'shen-scheme', 'cases': suite_counts['conformance'], 'evidence': 'sampled-agreement'},
    'rejected_proof_mutations': 12,
    'rocq_regression_examples': 35,
    'orchestration_regressions': 5,
    'open': ['Encoder native execution and primitive representation refinement', 'Shen checker correspondence to Rocq', 'Shen evaluator correspondence to Rocq',
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
