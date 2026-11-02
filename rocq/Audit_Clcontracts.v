(* Audit of the CL-contracts lane (E2E-16/E2E-17): the narrowed
   CLLowering.primitive_contracts and its discharge from captured bodies. *)
From Buri Require CLLowering CLLoweringCapture CLWrappers CLContracts.
Print Assumptions CLLowering.sem_pred1.
Print Assumptions CLLowering.sem_pred2.
Print Assumptions CLLowering.pred_refines_narrows.
Print Assumptions CLContracts.CLContracts.eq_exact.
Print Assumptions CLContracts.CLContracts.abs_symbolic_right.
Print Assumptions CLContracts.CLContracts.abs_symbolic_left.
Print Assumptions CLContracts.CLContracts.abs_string_right.
Print Assumptions CLContracts.CLContracts.abs_string_left.
Print Assumptions CLContracts.CLContracts.abs_numeric_right.
Print Assumptions CLContracts.CLContracts.abs_numeric_left.
Print Assumptions CLContracts.CLContracts.numeric_equal_value.
Print Assumptions CLContracts.CLContracts.helper_value.
Print Assumptions CLContracts.CLContracts.captured_contracts.
Print Assumptions CLContracts.CLContracts.all_arity_unjustified.
Print Assumptions CLContracts.CLContracts.captured_all_arity_false.
Print Assumptions CLContracts.CLContracts.discharged_optimise_sound.
Print Assumptions CLContracts.CLContracts.discharged_emit_if_refines.
Print Assumptions CLContracts.CLContracts.model_host_ops.
Print Assumptions CLContracts.CLContracts.model_kernel_ops.
Print Assumptions CLContracts.CLContracts.model_world_contracts.
Print Assumptions CLContracts.CLContracts.increment_int.
Print Assumptions CLContracts.CLContracts.decrement_int.
Print Assumptions CLContracts.CLContracts.step_refines_rules.
Print Assumptions CLContracts.CLContracts.model_step_ops.
