(* Assumption audit of the Shen/JIT Phase 1 semantics. Theorems about the model only. *)
From Buri Require Import JitMeta JitProfile.
Print Assumptions JitMeta.JitMeta.step_deterministic_tau.
Print Assumptions JitMeta.JitMeta.step_deterministic_io.
Print Assumptions JitMeta.JitMeta.step_tau_excludes_io.
Print Assumptions JitMeta.JitMeta.move_classification.
Print Assumptions JitMeta.JitMeta.final_not_stuck.
Print Assumptions JitMeta.JitMeta.step_not_stuck.
Print Assumptions JitMeta.JitMeta.final_unique.
Print Assumptions JitMeta.JitMeta.excluded_prims_stuck.
Print Assumptions JitMeta.JitMeta.next_empty_rest.
Print Assumptions JitMeta.JitMeta.tget_tset_same.
Print Assumptions JitMeta.JitMeta.tget_tset_other.
Print Assumptions JitMeta.JitMeta.move_writes.
Print Assumptions JitMeta.JitMeta.jump_if_false_requires_boolean.
Print Assumptions JitMeta.JitMeta.return_at_top.
Print Assumptions JitMeta.JitMeta.raise_no_handler_final.
Print Assumptions JitMeta.JitMeta.install_sealed_refused.
Print Assumptions JitProfile.JitProfile.jit_division_by_zero_real.
Print Assumptions JitProfile.JitProfile.jit_absvector_fill.
