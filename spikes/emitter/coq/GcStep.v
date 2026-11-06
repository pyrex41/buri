(** * Step lemmas for a writable-and-executable image, at any instruction size.

    Theorem's step lemmas assume 4-byte instructions, and its w+x mirrors cover a few
    forms.  The Shen/JIT build uses RVC, so these take the size from the decode fact.
    Proof-side only: nothing here is trusted. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

Section S.
Context {fx : FPState}.

Lemma b_npc : forall (p : word) (sz : Z), p + Z_to_bv 64 sz = v_addi p sz.
Proof.
  intros. apply bv_eq. unfold v_addi.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  apply bv_wrap_add_idemp_r.
Qed.

Lemma z_opimm : forall sz segs regs pc mem rom w op rd rs (imm : bv 12),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, sz) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                  (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w op rd rs imm Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc; reflexivity.
Qed.

Lemma z_shift : forall sz segs regs pc mem rom w op rd rs (sh : bv 6),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, sz) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
                  (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w op rd rs sh Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc; reflexivity.
Qed.

Lemma z_op : forall sz segs regs pc mem rom w op rd rs1 rs2,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, sz) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                  (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w op rd rs1 rs2 Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc; reflexivity.
Qed.

Lemma z_auipc : forall sz segs regs pc mem rom w rd (imm : bv 20),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, sz) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
                  (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w rd imm Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc, ?b_auipc; reflexivity.
Qed.

Lemma z_jal : forall sz segs regs pc mem rom w rd (imm : bv 21),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc sz))
                  (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros sz segs regs pc mem rom w rd imm Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc, ?b_addsext; reflexivity.
Qed.

Lemma z_jalr : forall sz segs regs pc mem rom w rd rs1 (imm : bv 12),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, sz) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc sz))
                  (jalr_tgt (getr regs rs1) (bv_signed imm)) mem rom).
Proof.
  intros sz segs regs pc mem rom w rd rs1 imm Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_jalr, ?b_npc; reflexivity.
Qed.

Lemma z_branch_tk : forall sz segs regs pc mem rom w c rs1 rs2 (imm : bv 13),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, sz) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros sz segs regs pc mem rom w c rs1 rs2 imm Hwx Hecall Hdecode Hc.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

Lemma z_branch_ft : forall sz segs regs pc mem rom w c rs1 rs2 (imm : bv 13),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, sz) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w c rs1 rs2 imm Hwx Hecall Hdecode Hc.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite ?b_npc; reflexivity.
Qed.

Lemma z_ld : forall sz segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, sz) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
                  (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w rd rs imm bs v Hwx Hecall Hdecode Hread Hv.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_unsigned. }
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma z_lw : forall sz segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, sz) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
                  (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w rd rs imm bs v Hwx Hecall Hdecode Hread Hv.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma z_sd : forall sz segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, sz) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc sz) (wbytes mem a (word_to_le_bytes 8 v)) rom).
Proof.
  intros sz segs regs pc mem rom w rs1 rs2 imm a v Hwx Hecall Hdecode Ha Hv Hok.
  subst a v.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc.
  reflexivity.
Qed.

(* Value-named forms: the caller (or a tactic) names each result, so register chains
   don't pile up in the state. *)
Lemma z_opimm_at : forall sz segs regs pc mem rom w op rd rs (imm : bv 12) v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, sz) ->
  bv_eqb rd 0 = false ->
  alu64 op (getr regs rs) (sext 64 imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc sz) mem rom).
Proof.
  intros. subst v. erewrite z_opimm by eassumption. rewrite H2. reflexivity.
Qed.

Lemma z_shift_at : forall sz segs regs pc mem rom w op rd rs (sh : bv 6) v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, sz) ->
  bv_eqb rd 0 = false ->
  alu64 op (getr regs rs) (zext 64 sh) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc sz) mem rom).
Proof.
  intros. subst v. erewrite z_shift by eassumption. rewrite H2. reflexivity.
Qed.

Lemma z_op_at : forall sz segs regs pc mem rom w op rd rs1 rs2 v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, sz) ->
  bv_eqb rd 0 = false ->
  alu64 op (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc sz) mem rom).
Proof.
  intros. subst v. erewrite z_op by eassumption. rewrite H2. reflexivity.
Qed.

Lemma z_auipc_at : forall sz segs regs pc mem rom w rd (imm : bv 20) v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, sz) ->
  bv_eqb rd 0 = false ->
  v_auipc pc (Z.shiftl (bv_signed imm) 12) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc sz) mem rom).
Proof.
  intros. subst v. erewrite z_auipc by eassumption. rewrite H2. reflexivity.
Qed.

Lemma z_ld_at : forall sz segs regs pc mem rom w rd rs (imm : bv 12) bs a v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, sz) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc sz) mem rom).
Proof.
  intros. subst a. erewrite z_ld by eassumption. rewrite H2. reflexivity.
Qed.

Lemma z_lw_at : forall sz segs regs pc mem rom w rd rs (imm : bv 12) bs a v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, sz) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (v_lw v)) (v_addi pc sz) mem rom).
Proof.
  intros. subst a. erewrite z_lw by eassumption. rewrite H2. reflexivity.
Qed.

Lemma z_jr : forall sz segs regs pc mem rom w rs (imm : bv 12) tgt,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Jalr 0 rs imm, sz) ->
  jalr_tgt (getr regs rs) (bv_signed imm) = tgt ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs tgt mem rom).
Proof.
  intros sz segs regs pc mem rom w rs imm tgt Hf He Hd Ht.
  erewrite z_jalr by eassumption. rewrite Ht. reflexivity.
Qed.

Lemma z_call : forall sz segs regs pc mem rom w rd rs (imm : bv 12) tgt link,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs imm, sz) ->
  bv_eqb rd 0 = false ->
  jalr_tgt (getr regs rs) (bv_signed imm) = tgt ->
  v_addi pc sz = link ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd link) tgt mem rom).
Proof.
  intros sz segs regs pc mem rom w rd rs imm tgt link Hf He Hd Hr Ht Hl.
  erewrite z_jalr by eassumption. rewrite Hr, Ht, Hl. reflexivity.
Qed.

Lemma z_j : forall sz segs regs pc mem rom w (imm : bv 21) tgt,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Jal 0 imm, sz) ->
  btgt pc (bv_signed imm) = tgt ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs tgt mem rom).
Proof.
  intros sz segs regs pc mem rom w imm tgt Hf He Hd Ht.
  erewrite z_jal by eassumption. rewrite Ht. reflexivity.
Qed.

End S.

(** Memory facts: a word stored little-endian at [a]. *)
Definition word_at (segs : list Segment) (m : word -> option byte) (a v : word) : Prop :=
  rdn segs m a 8%nat = Some (word_le8 v).

Lemma mem_clear_read : forall segs m lo hi (a : word) (n : nat),
  mem_clear m lo hi ->
  (lo <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= hi)%Z -> (hi <= 2^64)%Z ->
  rdn segs m a n = rdn segs (fun _ => None) a n.
Proof.
  intros segs m lo hi a n Hc. revert a. induction n as [|n IH]; intros a Hlo Hhi Hh; [reflexivity|].
  cbn [rdn]. rewrite (Hc a) by lia.
  rewrite Nat2Z.inj_succ in Hhi.
  assert (Hna : (bv_unsigned (a + 1) = bv_unsigned a + 1)%Z \/ n = 0%nat).
  { destruct (Nat.eq_dec n 0) as [->|Hne]; [right; reflexivity|left].
    rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1%Z.
    apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z.
    pose proof (bv_unsigned_in_range _ a). lia. }
  destruct Hna as [Hna | ->]; [|reflexivity].
  rewrite IH by lia. reflexivity.
Qed.
