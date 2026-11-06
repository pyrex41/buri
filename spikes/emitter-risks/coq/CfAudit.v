(** Assumption audit of spike 8's statements. *)
From LinuxProcessSemantics.Examples.emitter_risks_ns Require Import CfDefs CfTop CfCaptured CfInstance.
Lemma cap_length : length cap_prog = 7%nat. Proof. vm_compute. reflexivity. Qed.
Print Assumptions run_sim.
Print Assumptions step_sim.
Print Assumptions cap_run.
Print Assumptions cap_step.
Print Assumptions cap_accepted.
Print Assumptions cap_parse.
Print Assumptions cap_length.
