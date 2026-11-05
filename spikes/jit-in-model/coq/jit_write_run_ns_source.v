(** * jit-write-run SOURCE: code written at runtime, then fetched and run.

    Unlike Theorem's rwx_flag_ns, this proof fetches through the overlay on bytes the
    program itself stored.  The frame invariant [mem_clear] still covers the fixed
    .text; the two generated words are fetched from the stores, by computation. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Examples.jit_write_run_ns Require Import jit_write_run_ns_code jit_write_run_ns_defs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

Section StepLemmas.
Context {fx : FPState}.

Lemma step_sw_val_wx : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hwx Hecall Hdecode Hok.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
  reflexivity.
Qed.

Lemma step_sw_at_wx : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 v)) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sw_val_wx segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(** fence.i has no effect in the model: the next fetch already sees the stores. *)
Lemma step_fencei_wx : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (FenceI rd rs1 imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_jalr_ra_wx : forall segs regs pc mem rom w rs1 (imm : bv 12) tgt,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Jalr 1 rs1 imm, 4%Z) ->
  jalr_tgt (getr regs rs1) (bv_signed imm) = tgt ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs 1 (v_addi pc 4)) tgt mem rom).
Proof.
  intros segs regs pc mem rom w rs1 imm tgt Hwx He Hd Ht.
  rewrite (step_jalr_gen_wx segs regs pc mem rom w 1 rs1 imm Hwx He Hd).
  rewrite Ht. reflexivity.
Qed.

End StepLemmas.

(** The memory after the two stores, over ANY earlier memory: the stores alone
    determine these fetches. *)
Definition written (m0 : word -> option byte) : word -> option byte :=
  wbytes (wbytes m0 (Z_to_bv 64 0x100b0) (word_to_le_bytes 4 (Z_to_bv 64 0x2a00513)))
         (Z_to_bv 64 0x100b4) (word_to_le_bytes 4 (Z_to_bv 64 0x8067)).

(** The word at the arena is 0x02a00513 in the memory the program wrote.  The
    source image holds zeros there, so this can only come from the stores. *)
Lemma image_arena_is_zero : fetch_word_wx source_segs 0x100b0 = Some (Z_to_bv 32 0).
Proof. vm_refl_bv. Qed.

Lemma image_arena_word_illegal : decode_any (Z_to_bv 32 0) = None.
Proof. vm_refl_bv. Qed.

Lemma gen_fetch_addi : forall m0,
  wx_fetch source_segs (written m0) (Z_to_bv 64 0x100b0) (Z_to_bv 32 0x02a00513).
Proof.
  intro m0. split.
  - apply fetch_word_none_no_ro_exec, source_no_ro_exec.
  - vm_refl_bv.
Qed.

Lemma gen_fetch_ret : forall m0,
  wx_fetch source_segs (written m0) (Z_to_bv 64 0x100b4) (Z_to_bv 32 0x00008067).
Proof.
  intro m0. split.
  - apply fetch_word_none_no_ro_exec, source_no_ro_exec.
  - vm_refl_bv.
Qed.

Lemma gen_decode_addi : decode_any (Z_to_bv 32 0x02a00513) = Some (OpImm ALU_ADD 10 0 42, 4%Z).
Proof. vm_refl_bv. Qed.

Lemma gen_decode_ret : decode_any (Z_to_bv 32 0x00008067) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.

Section SourceProof.

Variable av ev : list (list byte).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Variable rsp : word.
Variable rrnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned rsp)%Z.
Hypothesis Hsp_hi : (bv_unsigned rsp <= sp_window_hi)%Z.
Variable uid : word.
Variable hw : word.

Lemma rsp_lo_num : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma rsp_hi_num : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Ltac src_clear :=
  first
    [ apply mem_clear_wrap; unfold stack_max_size; lia
    | apply mem_clear_wbytes;
        [ src_clear
        | rewrite ?length_word_to_le_bytes; cbn [length];
          imm_norm; u_norm; left; lia
        | rewrite ?length_word_to_le_bytes; cbn [length];
          imm_norm; u_norm; lia ] ].

Ltac wxf SF :=
  eapply wx_fetch_intro with (lo := 0x10078%Z) (hi := 0x100a8%Z);
    [ exact source_no_ro_exec
    | src_clear
    | imm_norm; lia
    | imm_norm; lia
    | lia
    | exact SF ].

Lemma source_wexit :
  to_wexit source_segs
    (init_machine_state source_segs 0x10078 source_phdrs rsp rrnd av ev uid hw)
    [] (Z_to_bv 64 42).
Proof.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  rewrite init_mkst. norm_pc.
  (* 0x10078 auipc a5, 0 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_auipc_wx; [wxf SF_10078 | reflexivity | exact SD_10078]
    | step_simpl ].
  (* 0x1007c addi a5, a5, 56: a5 = arena *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at_wx with (v := Z_to_bv 64 0x100b0);
      [ wxf SF_1007c | reflexivity | exact SD_1007c | reflexivity
      | getr_resolve; regupd_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x10080 lui a4, 0x2a00 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_lui_wx; [wxf SF_10080 | reflexivity | exact SD_10080]
    | step_simpl ].
  (* 0x10084 addi a4, a4, 0x513: a4 = the instruction word *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at_wx with (v := Z_to_bv 64 0x2a00513);
      [ wxf SF_10084 | reflexivity | exact SD_10084 | reflexivity
      | getr_resolve; regupd_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x10088 sw a4, 0(a5): generate the first instruction *)
  eapply tw_step;
    [ reflexivity
    | eapply step_sw_at_wx with (a := Z_to_bv 64 0x100b0) (v := Z_to_bv 64 0x2a00513);
      [ wxf SF_10088 | reflexivity | exact SD_10088
      | getr_resolve; regupd_resolve; imm_norm; bveq
      | getr_resolve; regupd_resolve; reflexivity
      | apply source_store_ok; u_norm; cbn [Z.of_nat]; lia ]
    | step_simpl ].
  (* 0x1008c lui a4, 0x8 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_lui_wx; [wxf SF_1008c | reflexivity | exact SD_1008c]
    | step_simpl ].
  (* 0x10090 addi a4, a4, 0x67 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at_wx with (v := Z_to_bv 64 0x8067);
      [ wxf SF_10090 | reflexivity | exact SD_10090 | reflexivity
      | getr_resolve; regupd_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x10094 sw a4, 4(a5): generate the second instruction *)
  eapply tw_step;
    [ reflexivity
    | eapply step_sw_at_wx with (a := Z_to_bv 64 0x100b4) (v := Z_to_bv 64 0x8067);
      [ wxf SF_10094 | reflexivity | exact SD_10094
      | getr_resolve; regupd_resolve; imm_norm; bveq
      | getr_resolve; regupd_resolve; reflexivity
      | apply source_store_ok; u_norm; cbn [Z.of_nat]; lia ]
    | step_simpl ].
  (* 0x10098 fence.i *)
  eapply tw_step;
    [ reflexivity
    | eapply step_fencei_wx; [wxf SF_10098 | reflexivity | exact SD_10098]
    | step_simpl ].
  (* 0x1009c jalr ra, 0(a5): call the generated code *)
  eapply tw_step;
    [ reflexivity
    | eapply step_jalr_ra_wx with (tgt := Z_to_bv 64 0x100b0);
      [ wxf SF_1009c | reflexivity | exact SD_1009c
      | getr_resolve; regupd_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x100b0 GENERATED addi a0, zero, 42: fetched from the store *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at_wx with (v := Z_to_bv 64 42);
      [ match goal with |- wx_fetch _ (wbytes (wbytes ?m _ _) _ _) _ _ => exact (gen_fetch_addi m) end | reflexivity | exact gen_decode_addi | reflexivity
      | getr_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x100b4 GENERATED ret *)
  eapply tw_step;
    [ reflexivity
    | eapply step_jalr_x0_wx with (tgt := Z_to_bv 64 0x100a0);
      [ match goal with |- wx_fetch _ (wbytes (wbytes ?m _ _) _ _) _ _ => exact (gen_fetch_ret m) end | reflexivity | exact gen_decode_ret
      | getr_resolve; regupd_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x100a0 li a7, 93 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at_wx with (v := Z_to_bv 64 93);
      [ wxf SF_100a0 | reflexivity | exact SD_100a0 | reflexivity
      | getr_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x100a4 ecall: exit(42) *)
  eapply tw_step;
    [ reflexivity
    | eapply step_ecall_wx; [wxf SF_100a4 | reflexivity]
    | ].
  apply tw_exit_coden.
  - getr_resolve; regupd_resolve; u_norm; lia.
  - regupd_resolve; bveq.
  - u_norm; lia.
Qed.

End SourceProof.
