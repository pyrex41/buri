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
assert len(rows) == 7 and set(suite_counts) == {'kernel', 'evaluator', 'wire', 'frontend', 'trust', 'observed', 'conformance'}, 'Incomplete suite gates'
assert 'BURI_ROCQ_OK 100 audited theorems; 18 equation bridges; 12 native compiler schemas; raw capture validated; coqchk replay passed' in checks
assert checks.count('Rejected proof mutation:') == 26
assert re.findall(r'^BURI_GATE_TESTS_OK (\d+)$', checks, re.M) == ['7']
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
        'audited_theorems': 100,
        'custom_axioms': [],
        'scope': ['arithmetic reference compiler', 'equational certificate calculus',
                  'lexical lambda evaluator fuel stability and determinism', 'let-to-lambda lowering', '12 actual compiler-output schema equivalences',
                  'exact wire decoding, lexical resolution and symbolic normalization',
                  'raw captured-data validation and complete record coverage',
                  'source-linked encoder termination, unique output and decoding roundtrip',
                  'named recursive program resolution and registered KLambda validation',
                  'observed paired compilation validation and target administrative-let preservation'],
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
        'registered_kl': 'all three captured definitions translation-validated',
        'assumed_for_native_execution': ['registered KLambda metadata identifies the installed code',
            'native input representation and primitive contracts',
            'Shen-Scheme/Chez/runtime preservation', 'specified source is loaded without rebinding'],
        'native_execution_verified': False,
    },
    'encoder_frontend_validation': {
        'definitions': 3,
        'capture': 'ports/encoder-kl.bits',
        'capture_sha256': digest(root / '_build/encoder-kl.bits'),
        'proof_input_sha256': digest(root / '_build/EncoderKLambda.v'),
        'registered_definitions_sha256': digest(root / '_build/encoder-kl.sexp'),
        'scope': 'registered KLambda for the three source-bound encoder functions',
        'evidence': 'instance-translation-validation',
        'named_resolution_and_recursive_calls': 'machine-checked for every abstract fuel and environment satisfying scope correspondence',
        'definition_coverage': 'all three expected definitions in order; no extra or missing definitions',
        'semantic_decoder': 'strict admitted grammar inside Rocq; includes explicit composite primitive contracts',
        'capture_provenance': 'assumed; ps metadata is independently mutable',
        'tagged_protocol': 'generic roundtrip, injectivity and exact-root validation proved in CaptureTag',
        'native_tagging_implementation': 'assumed; protocol theorem does not verify Shen adapter execution',
        'generic_frontend_verified': False,
        'backend_or_binary_verified': False,
    },
    'observed_compilation_validation': {
        'source': 'shen/wire.shen',
        'observer': 'shen/observe-encoder.shen',
        'observer_sha256': digest(root / 'shen/observe-encoder.shen'),
        'capture_sha256': digest(root / '_build/observed-encoder.bits'),
        'transcript_sha256': digest(root / '_build/observed-encoder.sexp'),
        'proof_input_sha256': digest(root / '_build/ObservedCapture.v'),
        'evidence': 'instance-translation-validation',
        'path': 'controlled loader: actual frontend -> actual backend -> eval of the captured Scheme value',
        'stock_loader_intercepted': False,
        'reads_ps_metadata': False,
        'backend_mode': 'compatible; empty native-local map',
        'paired_definitions': 3,
        'coverage': 'all three source and target bodies, parameters and recursive callees',
        'administrative_let_preservation': 'generic kernel-checked theorem',
        'execution_scope': 'successful finite execution in the admitted target semantics; encoder termination and unique output',
        'assumptions': ['observer faithfully reports the actual load path',
                        'reader and exact source byte correspondence', 'native tagging and encoding',
                        'composite primitive contracts and representations',
                        'immutable transitive helper/global bindings', 'Chez eval and runtime behavior'],
        'exception_payloads_or_divergence_verified': False,
        'native_execution_verified': False,
        'backend_binary_verified': False,
    },
    'trust_audit': {
        'ledger': 'docs/TRUST-AUDIT.md',
        'byte_recursion_domain': 'machine-checked: character inputs and recursive halvings stay below 256, counts at most 8',
        'native_byte_contracts': {'evidence': 'finite-domain execution tests', 'inputs': 256, 'counts_per_input': 9},
        'counterexamples': ['unrestricted natural halving is false on the pinned host',
                            'ps metadata can differ from the installed executable'],
        'unrestricted_native_byte_helper_verified': False,
        'metadata_identifies_executable': False,
        'tagging_adapter_implementation_verified': False,
        'binary_source_correspondence_verified': False,
    },
    'shen_tests': {'kernel': suite_counts['kernel'], 'evaluator': suite_counts['evaluator'],
                   'wire': suite_counts['wire'], 'frontend': suite_counts['frontend'],
                   'trust': suite_counts['trust'], 'observed': suite_counts['observed']},
    'port_conformance': {'port': 'shen-scheme', 'cases': suite_counts['conformance'], 'evidence': 'sampled-agreement'},
    'rejected_proof_mutations': 26,
    'rocq_regression_examples': 59,
    'orchestration_regressions': 7,
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
