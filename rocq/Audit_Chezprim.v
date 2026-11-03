(* E2E-22 chezprim lane assumption audit.
   Universal theorems: check_raw_sound, plus_expansion_shape, plus_expansion_fast,
   plus_expansion_slow, check_expand_plus_sound, sort_refs_perm,
   check_block_order_sound.
   Every other statement is a ground derivation about one packaged artifact
   (ports/chez-np/tarm64le-buri-arm-add.raw.np). *)
From Buri Require Import ChezPrimRawInput ChezPrimRaw ChezPrimExpand ChezPrimBlocks ChezPrimValidate.
Print Assumptions check_raw_sound.
Print Assumptions plus_expansion_shape.
Print Assumptions plus_expansion_fast.
Print Assumptions plus_expansion_slow.
Print Assumptions check_expand_plus_sound.
Print Assumptions sort_refs_perm.
Print Assumptions check_block_order_sound.
Print Assumptions raw_trace_pass_order.
Print Assumptions raw_coverage.
Print Assumptions raw_codegen_same.
Print Assumptions raw_sections_read.
Print Assumptions raw_opaque_census.
Print Assumptions raw_identity_passes.
Print Assumptions suppress_raw_changed.
Print Assumptions suppress_raw_checked.
Print Assumptions suppress_raw_preserves.
Print Assumptions suppress_raw_matches_printed.
Print Assumptions mrvs_raw_checked.
Print Assumptions raw_rejects_wrong_pairs.
Print Assumptions expand_frame_kept.
Print Assumptions expand_in_is_plus.
Print Assumptions expand_out_shape.
Print Assumptions expand_plus_buri_arm_add_checked.
Print Assumptions expand_plus_buri_arm_add_preserves.
Print Assumptions plus_out_ok.
Print Assumptions expanded_fast_path_shen.
Print Assumptions expanded_slow_path.
Print Assumptions expand_rejects_wrong.
Print Assumptions block_order_changed.
Print Assumptions block_order_checked.
Print Assumptions block_order_rejects.
