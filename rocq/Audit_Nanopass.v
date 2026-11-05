(* E2E-22 nanopass lane assumption audit.
   Universal theorems: sexp_eqb_true, same_denotation, check_recognize_mrvs_sound,
   check_printed_identity_sound, check_code_object_sound.
   Every other statement is a ground derivation about one packaged artifact. *)
From Buri Require Import ChezNpReader ChezNpGrammar ChezNpLanguagesInput ChezNpSyntax
  ChezNpGrammarCheck ChezNpCore ChezNpReloc ChezNpCaptureInput ChezNpValidate.
Print Assumptions sexp_eqb_true.
Print Assumptions same_denotation.
Print Assumptions check_recognize_mrvs_sound.
Print Assumptions check_printed_identity_sound.
Print Assumptions check_code_object_sound.
Print Assumptions np_languages_form_count.
Print Assumptions np_languages_spans_complete.
Print Assumptions np_languages_resolved.
Print Assumptions np_language_names.
Print Assumptions trace_pass_order.
Print Assumptions mrvs_input_read.
Print Assumptions mrvs_output_read.
Print Assumptions mrvs_buri_arm_add_checked.
Print Assumptions mrvs_buri_arm_add_preserves.
Print Assumptions mrvs_rejects_wrong_pairs.
Print Assumptions identity_passes_checked.
Print Assumptions code_shape.
Print Assumptions codegen_buri_arm_add_checked.
Print Assumptions codegen_buri_arm_add_instance.
Print Assumptions codegen_rejects_tampering.
