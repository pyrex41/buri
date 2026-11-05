(** * jit-write-run TARGET: ordinary immutable code, no output, exit 42. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim.
From LinuxProcessSemantics.Examples.jit_write_run_ns Require Import jit_write_run_ns_code jit_write_run_ns_defs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

Section TargetProof.

Variable av ev : list (list byte).
Variable asp : word.
Variable arnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned asp)%Z.
Hypothesis Hsp_hi : (bv_unsigned asp <= sp_window_hi)%Z.
Variable uid : word.
Variable hw : word.

Lemma target_wexit :
  to_wexit target_segs
    (init_machine_state target_segs 0x11000 target_phdrs asp arnd av ev uid hw)
    [] (Z_to_bv 64 42).
Proof.
  rewrite init_mkst. norm_pc.
  (* 0x11000 li a0, 42 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 42);
      [ exact TF_11000 | reflexivity | exact TD_11000 | reflexivity
      | getr_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x11004 li a7, 93 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 93);
      [ exact TF_11004 | reflexivity | exact TD_11004 | reflexivity
      | getr_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x11008 ecall: exit(42) *)
  eapply tw_step;
    [ reflexivity
    | apply (step_ecall _ _ _ _ _ _ TF_11008 eq_refl)
    | ].
  apply tw_exit_coden.
  - getr_resolve; regupd_resolve; u_norm; lia.
  - regupd_resolve; bveq.
  - u_norm; lia.
Qed.

End TargetProof.
