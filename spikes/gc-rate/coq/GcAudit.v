(** Assumption audit of the rungs' top statements. *)
From LinuxProcessSemantics.Examples.gc_rate_ns Require Import Rung1ObjWords Rung2Paths Rung2Spine Rung3Scan Rung4Graph Rung4Witness.
Print Assumptions obj_words_contract.
Print Assumptions copy_value_nonptr.
Print Assumptions copy_value_contract.
Print Assumptions scan_contract.
Print Assumptions scan_iso.
Print Assumptions witness_iso.
Print Assumptions witness_dinv.
Print Assumptions witness_machine.
