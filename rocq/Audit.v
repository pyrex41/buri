From Buri Require Import Arithmetic Equality Lambda EquationBridge NativeArithmetic NativeOutput Wire Resolve Normalize NativeValidation NativeCapture Encoder EncoderSource EncoderNames EncoderFrontend EncoderKLambda CaptureTag ByteDomain EncoderScheme ObservedEncoder ObservedCapture BindingVersions Sealed Native NativeRuntime NativeHelpers SealedInput ConstructorInput.
Check nadd_standard.
Print Assumptions nadd_standard.
Check nmul_standard.
Print Assumptions nmul_standard.
Check compiler_continuation.
Print Assumptions compiler_continuation.
Check compiler_result.
Print Assumptions compiler_result.
Check compiler_no_stack_fault.
Print Assumptions compiler_no_stack_fault.
Check evaluation_sound.
Print Assumptions evaluation_sound.
Check evaluation_complete.
Print Assumptions evaluation_complete.
Check Arithmetic.evaluation_deterministic.
Print Assumptions Arithmetic.evaluation_deterministic.
Check compiler_relational.
Print Assumptions compiler_relational.
Check check_sound_under_rules.
Print Assumptions check_sound_under_rules.
Check Lexical.fuel_monotone.
Print Assumptions Lexical.fuel_monotone.
Check Lexical.evaluation_deterministic.
Print Assumptions Lexical.evaluation_deterministic.
Check exported_compiler_continuation.
Print Assumptions exported_compiler_continuation.
Check exported_compiler_result.
Print Assumptions exported_compiler_result.
Check Lexical.let_lowering.
Print Assumptions Lexical.let_lowering.
Check lower_preserves.
Print Assumptions lower_preserves.
Check native_schema_0.
Print Assumptions native_schema_0.
Check native_schema_1.
Print Assumptions native_schema_1.
Check native_schema_2.
Print Assumptions native_schema_2.
Check native_schema_3.
Print Assumptions native_schema_3.
Check native_schema_4.
Print Assumptions native_schema_4.
Check native_schema_5.
Print Assumptions native_schema_5.
Check native_schema_6.
Print Assumptions native_schema_6.
Check native_schema_7.
Print Assumptions native_schema_7.
Check native_schema_8.
Print Assumptions native_schema_8.
Check native_schema_9.
Print Assumptions native_schema_9.
Check native_schema_10.
Print Assumptions native_schema_10.
Check native_schema_11.
Print Assumptions native_schema_11.
Check Wire.decode_encode.
Print Assumptions Wire.decode_encode.
Check Wire.decode_exact.
Print Assumptions Wire.decode_exact.
Check Wire.encode_injective.
Print Assumptions Wire.encode_injective.
Check Wire.capture_roundtrip.
Print Assumptions Wire.capture_roundtrip.
Check Wire.capture_exact.
Print Assumptions Wire.capture_exact.
Check Resolve.resolve_preserves.
Print Assumptions Resolve.resolve_preserves.
Check Resolve.resolved_equal_sound.
Print Assumptions Resolve.resolved_equal_sound.
Check Normalize.symbolic_preserves.
Print Assumptions Normalize.symbolic_preserves.
Check Normalize.normalize_preserves.
Print Assumptions Normalize.normalize_preserves.
Check Normalize.normal_equal_sound.
Print Assumptions Normalize.normal_equal_sound.
Check NativeValidation.agrees_sound.
Print Assumptions NativeValidation.agrees_sound.
Check NativeValidation.check_record_sound.
Print Assumptions NativeValidation.check_record_sound.
Check NativeValidation.check_records_sound.
Print Assumptions NativeValidation.check_records_sound.
Check NativeValidation.check_records_exact.
Print Assumptions NativeValidation.check_records_exact.
Check NativeValidation.check_capture_sound.
Print Assumptions NativeValidation.check_capture_sound.
Check NativeValidation.check_capture_complete_record_coverage.
Print Assumptions NativeValidation.check_capture_complete_record_coverage.
Check NativeValidation.checked_count_sound.
Print Assumptions NativeValidation.checked_count_sound.
Check NativeValidation.checked_count_coverage.
Print Assumptions NativeValidation.checked_count_coverage.
Check NativeValidation.unique_names_sound.
Print Assumptions NativeValidation.unique_names_sound.
Check native_capture_checked.
Print Assumptions native_capture_checked.
Check native_capture_sound.
Print Assumptions native_capture_sound.
Check native_capture_record_coverage.
Print Assumptions native_capture_record_coverage.
Check Encoder.eval_monotone.
Print Assumptions Encoder.eval_monotone.
Check Encoder.evaluation_deterministic.
Print Assumptions Encoder.evaluation_deterministic.
Check Encoder.byte_correct.
Print Assumptions Encoder.byte_correct.
Check Encoder.byte_ascii.
Print Assumptions Encoder.byte_ascii.
Check Encoder.string_correct.
Print Assumptions Encoder.string_correct.
Check Encoder.datum_correct.
Print Assumptions Encoder.datum_correct.
Check Encoder.encoder_output_unique.
Print Assumptions Encoder.encoder_output_unique.
Check Encoder.encoder_decodes.
Print Assumptions Encoder.encoder_decodes.
Check encoder_source_exact.
Print Assumptions encoder_source_exact.
Check source_linked_encoder.
Print Assumptions source_linked_encoder.
Check source_linked_roundtrip.
Print Assumptions source_linked_roundtrip.
Check EncoderNames.resolve_preserves.
Print Assumptions EncoderNames.resolve_preserves.
Check EncoderNames.program_preserves.
Print Assumptions EncoderNames.program_preserves.
Check EncoderNames.program_encoder_total.
Print Assumptions EncoderNames.program_encoder_total.
Check EncoderNames.program_encoder_unique.
Print Assumptions EncoderNames.program_encoder_unique.
Check EncoderFrontend.definition_ok_sound.
Print Assumptions EncoderFrontend.definition_ok_sound.
Check EncoderFrontend.check_program_sound.
Print Assumptions EncoderFrontend.check_program_sound.
Check EncoderFrontend.check_program_coverage.
Print Assumptions EncoderFrontend.check_program_coverage.
Check EncoderFrontend.capture_program_coverage.
Print Assumptions EncoderFrontend.capture_program_coverage.
Check EncoderFrontend.check_capture_coverage.
Print Assumptions EncoderFrontend.check_capture_coverage.
Check EncoderFrontend.check_capture_sound.
Print Assumptions EncoderFrontend.check_capture_sound.
Check EncoderFrontend.accepted_sound.
Print Assumptions EncoderFrontend.accepted_sound.
Check EncoderFrontend.accepted_execution.
Print Assumptions EncoderFrontend.accepted_execution.
Check encoder_kl_checked.
Print Assumptions encoder_kl_checked.
Check encoder_kl_sound.
Print Assumptions encoder_kl_sound.
Check encoder_kl_execution.
Print Assumptions encoder_kl_execution.
Check CaptureTag.bytes_roundtrip.
Print Assumptions CaptureTag.bytes_roundtrip.
Check CaptureTag.tag_roundtrip.
Print Assumptions CaptureTag.tag_roundtrip.
Check CaptureTag.tag_injective.
Print Assumptions CaptureTag.tag_injective.
Check CaptureTag.wire_tag_roundtrip.
Print Assumptions CaptureTag.wire_tag_roundtrip.
Check CaptureTag.capture_root_exact.
Print Assumptions CaptureTag.capture_root_exact.
Check ByteDomain.calls_bounded.
Print Assumptions ByteDomain.calls_bounded.
Check ByteDomain.string_byte_domain.
Print Assumptions ByteDomain.string_byte_domain.
Check EncoderScheme.rename_exec.
Print Assumptions EncoderScheme.rename_exec.
Check EncoderScheme.anf_preserves.
Print Assumptions EncoderScheme.anf_preserves.
Check EncoderScheme.exec_deterministic.
Print Assumptions EncoderScheme.exec_deterministic.
Check EncoderScheme.evaluator_exec.
Print Assumptions EncoderScheme.evaluator_exec.
Check EncoderScheme.encoder_target_total.
Print Assumptions EncoderScheme.encoder_target_total.
Check EncoderScheme.encoder_target_unique.
Print Assumptions EncoderScheme.encoder_target_unique.
Check ObservedEncoder.target_ok_sound.
Print Assumptions ObservedEncoder.target_ok_sound.
Check ObservedEncoder.check_pair_sound.
Print Assumptions ObservedEncoder.check_pair_sound.
Check ObservedEncoder.check_program_coverage.
Print Assumptions ObservedEncoder.check_program_coverage.
Check ObservedEncoder.coverage_resolves.
Print Assumptions ObservedEncoder.coverage_resolves.
Check ObservedEncoder.capture_coverage.
Print Assumptions ObservedEncoder.capture_coverage.
Check ObservedEncoder.accepted_sound.
Print Assumptions ObservedEncoder.accepted_sound.
Check ObservedEncoder.exec_table.
Print Assumptions ObservedEncoder.exec_table.
Check ObservedEncoder.checked_execution.
Print Assumptions ObservedEncoder.checked_execution.
Check observed_encoder_checked.
Print Assumptions observed_encoder_checked.
Check observed_encoder_execution.
Print Assumptions observed_encoder_execution.
Check ObservedEncoder.paired_execution.
Print Assumptions ObservedEncoder.paired_execution.
Check BindingVersions.current_exact.
Print Assumptions BindingVersions.current_exact.
Check BindingVersions.current_covers.
Print Assumptions BindingVersions.current_covers.
Check BindingVersions.changed_rejected.
Print Assumptions BindingVersions.changed_rejected.
Check Sealed.guard_sound.
Print Assumptions Sealed.guard_sound.
Check Sealed.guard_complete.
Print Assumptions Sealed.guard_complete.
Check Sealed.resolution_noninterference.
Print Assumptions Sealed.resolution_noninterference.
Check Sealed.no_dynamic_authority.
Print Assumptions Sealed.no_dynamic_authority.
Check SealedCapture.node_eqb_sound.
Print Assumptions SealedCapture.node_eqb_sound.
Check SealedCapture.linked_exact.
Print Assumptions SealedCapture.linked_exact.
Check SealedCapture.check_sound.
Print Assumptions SealedCapture.check_sound.
Check sealed_checked.
Print Assumptions sealed_checked.
Check NativeRuntime.execute_trace.
Print Assumptions NativeRuntime.execute_trace.
Check NativeRuntime.step_deterministic.
Print Assumptions NativeRuntime.step_deterministic.
Check NativeRuntime.terminal_unique.
Print Assumptions NativeRuntime.terminal_unique.
Check NativeRuntime.erase_rebindings.
Print Assumptions NativeRuntime.erase_rebindings.
Check NativeRuntime.concurrent_output_unique.
Print Assumptions NativeRuntime.concurrent_output_unique.
Check NativeRuntime.every_world_schedule_preserves_trace.
Print Assumptions NativeRuntime.every_world_schedule_preserves_trace.
Check NativeHelpers.helpers_exact.
Print Assumptions NativeHelpers.helpers_exact.
Check NativeHelpers.boolean_identity.
Print Assumptions NativeHelpers.boolean_identity.
Check NativeHelpers.boolean_type_error.
Print Assumptions NativeHelpers.boolean_type_error.
Check NativeHelpers.exact_integer_classification.
Print Assumptions NativeHelpers.exact_integer_classification.
Check NativeHelpers.inexact_classification.
Print Assumptions NativeHelpers.inexact_classification.
Check NativeHelpers.fraction_classification.
Print Assumptions NativeHelpers.fraction_classification.
Check NativeHelpers.symbol_classification.
Print Assumptions NativeHelpers.symbol_classification.
Check NativeHelpers.integer_spelling.
Print Assumptions NativeHelpers.integer_spelling.
Check NativeHelpers.symbol_spelling.
Print Assumptions NativeHelpers.symbol_spelling.
Check NativeHelpers.exact_division.
Print Assumptions NativeHelpers.exact_division.
Check NativeHelpers.exact_floor.
Print Assumptions NativeHelpers.exact_floor.
Check NativeHelpers.fractional_floor.
Print Assumptions NativeHelpers.fractional_floor.
Check NativeHelpers.exact_halving.
Print Assumptions NativeHelpers.exact_halving.
Check NativeHelpers.natural_halving.
Print Assumptions NativeHelpers.natural_halving.
Check NativeHelpers.integer_equality.
Print Assumptions NativeHelpers.integer_equality.
Check NativeHelpers.machine_boolean_identity.
Print Assumptions NativeHelpers.machine_boolean_identity.
Check NativeHelpers.machine_boolean_error.
Print Assumptions NativeHelpers.machine_boolean_error.
Check NativeHelpers.machine_integer_classification.
Print Assumptions NativeHelpers.machine_integer_classification.
Check NativeHelpers.machine_inexact_classification.
Print Assumptions NativeHelpers.machine_inexact_classification.
Check NativeHelpers.machine_symbol_classification.
Print Assumptions NativeHelpers.machine_symbol_classification.
Check NativeHelpers.machine_integer_spelling.
Print Assumptions NativeHelpers.machine_integer_spelling.
Check NativeHelpers.machine_symbol_spelling.
Print Assumptions NativeHelpers.machine_symbol_spelling.
Check NativeHelpers.machine_integer_equality.
Print Assumptions NativeHelpers.machine_integer_equality.
Check NativeHelpers.machine_floor.
Print Assumptions NativeHelpers.machine_floor.
Check NativeHelpers.machine_fractional_floor.
Print Assumptions NativeHelpers.machine_fractional_floor.
Check NativeHelpers.machine_division.
Print Assumptions NativeHelpers.machine_division.
Check NativeHelpers.helper_execution_ignores_rebinding.
Print Assumptions NativeHelpers.helper_execution_ignores_rebinding.
Check constructor_exact.
Print Assumptions constructor_exact.
Check constructor_definitions_complete.
Print Assumptions constructor_definitions_complete.
Check constructor_definition.
Print Assumptions constructor_definition.
Check constructor_targets.
Print Assumptions constructor_targets.
Check constructor_helpers.
Print Assumptions constructor_helpers.
Check constructor_imports.
Print Assumptions constructor_imports.
Check constructor_program_correct.
Print Assumptions constructor_program_correct.
Check constructor_rejects_missing.
Print Assumptions constructor_rejects_missing.
Check constructor_rejects_bad_definition.
Print Assumptions constructor_rejects_bad_definition.
Check constructor_request.
Print Assumptions constructor_request.
Check constructor_executor_shape.
Print Assumptions constructor_executor_shape.
Check constructor_entry_shape.
Print Assumptions constructor_entry_shape.
Check sealed_native_exact.
Print Assumptions sealed_native_exact.
Check sealed_native_complete.
Print Assumptions sealed_native_complete.
Check sealed_native_helpers.
Print Assumptions sealed_native_helpers.
Check sealed_native_nil.
Print Assumptions sealed_native_nil.
Check sealed_native_integer.
Print Assumptions sealed_native_integer.
Check sealed_native_symbol.
Print Assumptions sealed_native_symbol.
Check sealed_native_pair.
Print Assumptions sealed_native_pair.
Check sealed_native_string_error.
Print Assumptions sealed_native_string_error.
Check sealed_native_boolean_error.
Print Assumptions sealed_native_boolean_error.
Check sealed_native_concurrent.
Print Assumptions sealed_native_concurrent.
