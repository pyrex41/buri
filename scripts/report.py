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

if sys.argv[1] == 'check':
    # Own the completed log: children never inherit its writable descriptor.
    result = subprocess.run(['make', 'check'], cwd=root,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (root / '_build/check.log').write_bytes(result.stdout)
    if result.returncode:
        sys.stdout.buffer.write(result.stdout)
    sys.exit(result.returncode)

before = json.loads((root / '_build/source-before.json').read_text())
assert before == manifest(), 'Source changed during checking; no report issued.'
checks = (root / '_build/check.log').read_text()
rows = re.findall(r'^BURI_SUITE_OK ([\w-]+) (\d+)$', checks, re.M)
suite_counts = {name: int(n) for name, n in rows}
assert len(rows) == 27 and set(suite_counts) == {'contracts', 'primitives', 'representation', 'scheme-port-order', 'observation', 'ledger', 'kernel', 'evaluator', 'wire', 'frontend', 'trust', 'observed', 'bindings', 'sealed', 'constructor', 'adapter', 'bootstrap', 'compilerpass', 'checkedio', 'correctness', 'stages', 'equalityseal', 'conformance', 'scheme-port-merge', 'cl-port-guard', 'cl-lowering-capture', 'scheme-compose'}, 'Incomplete suite gates'
audit_counts = {f.stem: int(f.read_text().strip()) for f in sorted((root / 'rocq/audit.d').glob('*.count'))}
audited_total = sum(audit_counts.values())
assert f'BURI_ROCQ_OK {audited_total} audited theorems; 18 equation bridges; 12 native compiler schemas; raw capture validated; coqchk replay passed' in checks
assert checks.count('Rejected proof mutation:') == 190
assert re.findall(r'^BURI_GATE_TESTS_OK (\d+)$', checks, re.M) == ['27']
ledger = json.loads((root / 'spec/six-stages.json').read_text())
assert [stage['id'] for stage in ledger['stages']] == list(range(1,7))
assert not ledger['full_plan_complete'] and all(stage['status'] == 'partial' for stage in ledger['stages'])
audit_source = (root / 'rocq/Audit.v').read_text()
for stage in ledger['stages']:
    for claim in stage['established']:
        for name in claim['evidence']:
            assert 'Check ' + name + '.' in audit_source, 'Missing audited evidence: ' + name
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
        'audit_logs_sha256': {name: digest(root / f'_build/rocq/{name}.log') for name in audit_counts},
        'audited_theorems': audited_total,
        'custom_axioms': [],
        'scope': ['arithmetic reference compiler', 'equational certificate calculus',
                  'lexical lambda evaluator fuel stability and determinism', 'let-to-lambda lowering', '12 actual compiler-output schema equivalences',
                  'exact wire decoding, lexical resolution and symbolic normalization',
                  'raw captured-data validation and complete record coverage',
                  'source-linked encoder termination, unique output and decoding roundtrip',
                  'named recursive program resolution and registered KLambda validation',
                  'observed paired compilation validation and target administrative-let preservation',
                  'captured native constructor assembly and authority plan', 'exact helper contracts and instruction-level rebinding isolation'],
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
        'source_to_program': 'exact rendered-source equality and independent rejecting source parse checked inside Rocq',
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
        'native_tagging_implementation': 'captured kl-node/kl-bytes target bodies proved in fixed helper model; native execution/provenance remains assumed',
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
                        'native reader and capture truthfulness', 'host execution of proved tagging and sealed encoding models',
                        'composite primitive contracts and representations',
                        'immutable transitive helper/global bindings', 'Chez eval and runtime behavior'],
        'exception_payloads_or_divergence_verified': False,
        'native_execution_verified': False,
        'backend_binary_verified': False,
    },
    'binding_guard': {
        'source': 'shen/binding-guard.shen',
        'evidence': 'native procedure-identity checks and separate abstract version-vector theorems',
        'inventory_sha256': digest(root / 'shen/binding-guard.shen'),
        'source_snapshot_sha256': digest(root / '_build/observed-encoder.bits.source'),
        'helper_source_sha256': digest(root / 'shen/base.shen'),
        'single_read': 'the saved string is passed directly to read-from-string',
        'complete_transitive_runtime_closure': False,
        'concurrent_rebinding_protection': False,
        'native_guard_refinement_proved': False,
    },
    'sealed_execution': {
        'source': 'shen/sealed-encoder.shen',
        'source_sha256': digest(root / 'shen/sealed-encoder.shen'),
        'capture_sha256': digest(root / '_build/sealed.bits'),
        'proof_input_sha256': digest(root / '_build/SealedInput.v'),
        'evidence': 'exact native syntax validation, constructor execution, helper contracts, lexical-machine interleaving proofs; native regressions',
        'application_dependency_closure': 'all capsule bodies checked, including seven private helpers, up to 27 named Chez primitives',
        'runtime_dependency_closure_below_primitive_boundary': False,
        'mutable_shen_global_dependencies_in_capsule': [],
        'guard_strategy': 'private lexical procedures evaluated in an only-import Chez library environment',
        'legacy_identity_guard_used': False,
        'concurrent_global_rebinding': 'isolated after construction, conditional on Chez lexical/library semantics; synchronized native regression',
        'formal_noninterference_scope': 'instruction-level pure lexical machine on the decoded capsule; arbitrary ambient rebindings; no Chez simulation claim',
        'captured_constructor_pure_scheme_execution': 'universally quantified target preservation, assembly, import plan and executor/entry shape',
        'helper_body_contracts': 'proved for the exact seven shim bodies in explicit primitive semantics; includes all-natural exact halving',
        'constructor_capture_sha256': digest(root / '_build/constructor.bits'),
        'constructor_proof_sha256': digest(root / '_build/ConstructorInput.v'),
        'constructor_source_snapshot_sha256': digest(root / '_build/constructor.bits.source'),
        'buri_evaluator_to_machine_refinement': 'all non-exhausted results, arbitrary programs and inputs; exact errors and unsupported outcomes',
        'buri_evaluator_to_machine_simulation_proved': True,
        'buri_simulation_direction': 'functional evaluator to instruction machine; converse and divergence not proved',
        'buri_simulation_proof_sha256': digest(root / 'rocq/NativeSimulation.v'),
        'chez_to_lexical_machine_simulation_proved': False,
        'universal_native_capsule_codec_refinement_proved': True,
        'codec_refinement_scope': 'exact captured sealed target in Native/NativeRuntime; all finite pairs, exact integers and byte-spelled symbols',
        'codec_proof_sha256': digest(root / 'rocq/NativeCodec.v'),
        'exact_observed_to_sealed_record_identity': True,
        'independent_source_parse_checked': True,
        'general_shen_compiler_verified': False,
        'assumptions': ['trusted construction and capture provenance', 'restricted environment and Chez lexical semantics',
                        '27 Chez primitive contracts and their runtime internals', 'representation relation to actual Chez values',
                        'caller retains the opaque procedure and does not mutate input data concurrently'],
    },
    'capture_adapter': {
        'source': 'shen/export-encoder-kl.shen',
        'source_snapshot_sha256': digest(root / '_build/adapter.bits.source'),
        'capture_sha256': digest(root / '_build/adapter.bits'),
        'proof_input_sha256': digest(root / '_build/AdapterInput.v'),
        'implementation_proof_sha256': digest(root / 'rocq/AdapterCorrect.v'),
        'captured_target_execution_proved': True,
        'scope': 'two pure tagging functions, fixed table of captured bodies and seven pinned helpers',
        'execution_domain': 'all finite EncoderFrontend nodes with natural numerals and byte strings',
        'decoder_roundtrip_domain': 'admitted nodes: numerals <= 256, matching the existing KLambda protocol',
        'effectful_exporter_verified': False,
        'native_boolean_aware_bootstrap_adapter_verified': False,
        'bootstrap_captured_pure_targets_proved': True,
        'capture_provenance_verified': False,
    },
    'observer_and_bootstrap': {
        'bootstrap_capture_sha256': digest(root / '_build/bootstrap.bits'),
        'bootstrap_source_snapshot_sha256': digest(root / '_build/bootstrap.bits.source'),
        'bootstrap_proof_sha256': digest(root / 'rocq/BootstrapCorrect.v'),
        'bootstrap_captured_execution': 'all finite typed nodes with natural numerals and native booleans; fixed helper model',
        'bootstrap_roundtrip_domain': 'typed syntax with numerals at most 256',
        'observer_capture_sha256': digest(root / '_build/observer.bits'),
        'observer_source_snapshot_sha256': digest(root / '_build/observer.bits.source'),
        'installer_proof_sha256': digest(root / 'rocq/ObserverEffects.v'),
        'installer_captured_effect_sequence_proved': True,
        'installer_scope': 'exact one-definition target in explicit state/effect semantics; compile and activation responses remain external contracts',
        'publication_after_success': True,
        'failed_compile_or_activation_preserves_records': True,
        'arity_side_effects_rolled_back': False,
        'observer_io_plan_proved': 'single source binding, read/parse/snapshot linkage, all three writes checked; structural entry proof plus captured checked-write execution',
        'native_read_write_truthfulness_verified': False,
        'native_effect_machine_correspondence_verified': False,
        'full_effectful_observer_verified': False,
    },
    'checked_file_io': {
        'source': 'shen/observe-encoder.shen',
        'proof_sha256': digest(root / 'rocq/CheckedFileIO.v'),
        'proof_input_sha256': digest(root / '_build/CheckedIOInput.v'),
        'captured_wrapper_execution_proved': True,
        'postcondition': 'every successful modeled return equals the requested text and lookup of the requested file in the final world returns that text',
        'writer_may_lie_or_corrupt': True,
        'trusted_boundary': 'read-back reflects the current file world; fixed equality/helper semantics and native execution correspondence',
        'native_counterexample': 'write-to-file with *hush* true returns text while leaving the file empty',
        'observer_write_strategy': 'write, read back, compare; reject mismatch',
        'atomic_write_or_durability_proved': False,
        'read_primitive_truthfulness_proved': False,
    },
    'upstream_compiler_pass': {
        'source': 'ports/upstream/compiler.shen',
        'upstream_blob': '42ac753b8f305c578998b74693fc85b28112a814',
        'extracted_source': 'ports/compiler-merge.shen',
        'capture_sha256': digest(root / '_build/compiler-pass.bits'),
        'proof_sha256': digest(root / 'rocq/CompilerPassCorrect.v'),
        'pass': '_scm.merge-nested-lets',
        'captured_assembly': 'arbitrary bindings/bodies for both supported merge cases',
        'semantic_preservation': 'both cases, arbitrary binding lists with stable operand decoding; every evaluator result and arbitrary modeled effect handler',
        'general_compiler_correctness': False,
    },
    'implementation_correctness': {
        'stock_division_source_blob': '92b8875a276848b473c59879f075f429ba44a7a0',
        'numeric_proof_sha256': digest(root / 'rocq/StockDivision.v'),
        'numeric_scope': 'actual independently parsed wrapper: exact integral quotients, external rounding for fractions; positive denominator model only',
        'replacement_floor_division': 'all integer numerators and positive integer denominators, fixed exact-helper model',
        'compiler_order_capture_sha256': digest(root / '_build/order-call.bits'),
        'compiler_order_proof_sha256': digest(root / 'rocq/OrderCallCorrect.v'),
        'freshness_scope': 'actual captured guard/loop under a constant symbol generator and specified occurrences; collision exhaustion and preservation of existing symbol bindings',
        'ordering_scope': 'generic two nullary computations preserve arbitrary modeled effects/errors; exact captured transformation of one syntax instance',
        'arbitrary_call_ordering_proved': False,
        'observer_pipeline_proof_sha256': digest(root / 'rocq/ObserverPipeline.v'),
        'observer_pipeline_scope': 'actual captured three-form loader: arbitrary valid translated definitions; exact success trace; first/second frontend failure and third backend failure',
        'read_override_capture_sha256': digest(root / '_build/io-read.bits'),
        'read_override_proof_sha256': digest(root / 'rocq/IOReadCorrect.v'),
        'read_override_scope': 'actual captured Shen wrapper constructs home-directory prefix and exactly forwards the host read outcome/state/trace; Chez read contract remains trusted',
        'full_observer_entry_verified': False,
        'native_io_correspondence_verified': False,
        'whole_compiler_verified': False,
    },
    'six_stage_plan': {
        'complete': False,
        'ledger': ledger,
        'ledger_sha256': digest(root / 'spec/six-stages.json'),
        'scope_evidence_freshly_audited': True,
        'evidence_does_not_imply_entire_stage_complete': True,
    },
    'general_refinement': {
        'effects_proof_sha256': digest(root / 'rocq/EffectContract.v'),
        'call_lifting_proof_sha256': digest(root / 'rocq/CallRefinement.v'),
        'reverse_machine_proof_sha256': digest(root / 'rocq/NativeReverse.v'),
        'pure_effect_bridge_sha256': digest(root / 'rocq/PureEffectBridge.v'),
        'both_directions_all_non_exhausted_results': True,
        'pure_model_divergence_equivalence': True,
        'stateful_noncompletion_includes_external_exhaustion': True,
        'generic_fresh_operand_lifting': 'arbitrary admitted operand and argument tail; all modeled effects, failures and traces; existential fuel',
        'native_chez_correspondence_verified': False,
    },
    'general_wrappers_and_loader': {
        'division_proof_sha256': digest(root / 'rocq/StockDivisionGeneral.v'),
        'division_profile': 'all input values under named division, classification and rounding contracts; signed exact denominator extension',
        'zero_error_payload_verified': False,
        'fresh_generator_proof_sha256': digest(root / 'rocq/FreshSupply.v'),
        'fresh_generator_profile': 'arbitrary stateful/erroring generators; every successful candidate is absent; first available finite-supply candidate terminates',
        'observer_proof_sha256': digest(root / 'rocq/ObserverTotal.v'),
        'observer_profile': 'all nine failure positions and success of the actual captured three-form loader, under admitted frontend outputs',
        'full_observer_entry_verified': False,
    },
    'axiom_free_shen_checker': {
        'source': 'shen/equality-core.shen',
        'capture_sha256': digest(root / '_build/equality-core.bits'),
        'proof_sha256': digest(root / 'rocq/EqualityCoreCorrect.v'),
        'admission_proof_sha256': digest(root / 'rocq/EqualityAdmission.v'),
        'profile': 'finite typed Refl/Sym/Trans/Cong certificates over uninterpreted first-order terms; no artifact rules',
        'all_typed_certificates_refine_equality_check_empty': True,
        'raw_acceptance_sound': True,
        'original_eq1_induction_checker_verified': False,
        'shen_typechecker_verified': False,
        'native_binary_verified': False,
    },
    'private_checker_capsule': {
        'source': 'shen/sealed-equality.shen',
        'capture_sha256': digest(root / '_build/equality-seal.bits'),
        'proof_sha256': digest(root / 'rocq/EqualitySealCorrect.v'),
        'construction_and_table_correspondence': True,
        'exact_activation_request_wiring': True,
        'raw_identifier_closure_checked': True,
        'native_imports': ['lambda','let','let*','letrec','if','cond','and','or','quote','eq?','equal?','null?','pair?','car','cdr','cons','list'],
        'ambient_rebinding_model_soundness': True,
        'native_rebinding_evidence': 'sampled sequential and synchronized hostile rebinding',
        'code_authority': 'controlled compiler records; certificate data is never evaluated as native code',
        'remaining_contracts': ['stable construction context','actual capture provenance','Chez eval/environment, primitive and representation semantics','immutable input data'],
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
        'tagging_adapter_captured_pure_targets_proved': True,
        'binary_source_correspondence_verified': False,
    },
    'shen_tests': {'scheme-port-merge': suite_counts['scheme-port-merge'], 'cl-port-guard': suite_counts['cl-port-guard'], 'kernel': suite_counts['kernel'], 'evaluator': suite_counts['evaluator'],
                   'wire': suite_counts['wire'], 'frontend': suite_counts['frontend'],
                   'trust': suite_counts['trust'], 'observed': suite_counts['observed'], 'bindings': suite_counts['bindings'], 'sealed': suite_counts['sealed'], 'constructor': suite_counts['constructor'], 'adapter': suite_counts['adapter'], 'bootstrap': suite_counts['bootstrap'], 'compilerpass': suite_counts['compilerpass'], 'checkedio': suite_counts['checkedio'], 'correctness': suite_counts['correctness'], 'stages': suite_counts['stages'], 'equalityseal': suite_counts['equalityseal']},
    'parallel_port_scope': {
        'scheme': 'captured merge-nested-lets preserves arbitrary admitted binding tails',
        'cl': 'exact admitted guard AST implements strict booleans in a restricted CL model',
        'cl_native_source_regenerated_by_this_report': False,
        'cl_native_gate': 'optional make check-cl-port; separate pinned source checkout',
        'cl_shen_adapter_correspondence_proved': False,
        'coalton': 'optional tooling experiment; no proof contribution',
    },
    'port_conformance': {'port': 'shen-scheme', 'cases': suite_counts['conformance'], 'evidence': 'sampled-agreement'},
    'rejected_proof_mutations': 188,
    'rocq_regression_examples': 96,
    'orchestration_regressions': 22,
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
