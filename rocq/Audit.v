From Buri Require Import Arithmetic Equality Lambda EquationBridge NativeArithmetic NativeOutput Wire Resolve Normalize NativeValidation NativeCapture Encoder EncoderSource EncoderNames EncoderFrontend EncoderKLambda CaptureTag ByteDomain EncoderScheme ObservedEncoder ObservedCapture.
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
