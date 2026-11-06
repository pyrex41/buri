(** * Steps for any instruction length, at any code address (from spike 4's [SliceStep]). Proof-side. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Examples.emitter_risks_ns Require Import CfDefs.
Import ListNotations.
Open Scope bv_scope.

Record CodeOK (c : cfg) (segs : list Segment) (m : word -> option byte) : Prop := {
  c_even : (cbase c mod 2 = 0)%Z;
  c_pos : (0 <= cbase c)%Z;
  c_small : (cbase c + code_len c < 2^48)%Z;
  c_ro : no_ro_exec segs = true;
  c_seg : exists seg, (forall a, (cbase c <= a)%Z -> (a + 4 <= cbase c + code_len c)%Z ->
            find_segment segs a 4 = Some seg) /\
          (seg_executable seg && seg_writable seg) = true;
  c_bytes : forall i, (0 <= i < code_len c)%Z -> m (at_ c i) = Some (code_byte c i)
}.

Lemma at_plus1 : forall c o, at_ c o + 1 = at_ c (o + 1).
Proof.
  intros c o. apply bv_eq. unfold at_.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned 1) with 1%Z.
  rewrite bv_wrap_add_idemp_l. f_equal. lia.
Qed.

Lemma u_at : forall c o, (0 <= cbase c)%Z -> (cbase c + code_len c < 2^48)%Z -> (0 <= o <= code_len c)%Z ->
  bv_unsigned (at_ c o) = (cbase c + o)%Z.
Proof.
  intros c o Hp Hs Ho. unfold at_. apply u_Z2bv; lia.
Qed.

Lemma wx_at : forall c segs m o,
  CodeOK c segs m -> (0 <= o)%Z -> (o + 4 <= code_len c)%Z -> (o mod 2 = 0)%Z ->
  wx_fetch segs m (at_ c o) (code_word c o).
Proof.
  intros c segs m o [Heven Hpos Hs Hro [seg [Hseg Hflags]] Hb] Hl Hh Hev. split.
  - apply fetch_word_none_no_ro_exec, Hro.
  - unfold fetch_word_ov.
    rewrite u_at by lia.
    assert (Hmod : ((cbase c + o) mod 2 = 0)%Z).
    { rewrite Z.add_mod by lia. rewrite Heven, Hev. reflexivity. }
    rewrite Hmod. cbn [Z.eqb negb].
    unfold code_read_ov.
    rewrite u_at by lia.
    change (Z.of_N 4) with 4%Z.
    rewrite Hseg by lia. rewrite Hflags.
    change (N.to_nat 4) with 4%nat.
    cbn [seg_ov_read_bytes].
    rewrite ?at_plus1.
    rewrite (Hb o) by lia.
    rewrite (Hb (o + 1)%Z) by lia.
    rewrite (Hb (o + 1 + 1)%Z) by lia.
    rewrite (Hb (o + 1 + 1 + 1)%Z) by lia.
    unfold code_word.
    replace (o + 1 + 1)%Z with (o + 2)%Z by lia.
    replace (o + 2 + 1)%Z with (o + 3)%Z by lia.
    reflexivity.
Qed.

Lemma wbytes_outside : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m a bs x = m x.
Proof.
  intros bs m a x Hnw [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

Lemma code_ok_wbytes : forall c segs m a bs,
  CodeOK c segs m ->
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned a + Z.of_nat (length bs) <= cbase c \/ cbase c + code_len c <= bv_unsigned a)%Z ->
  CodeOK c segs (wbytes m a bs).
Proof.
  intros c segs m a bs [He Hp Hs Hro Hg Hb] Hn Hd. constructor; try assumption.
  intros i Hi. rewrite <- (Hb i Hi).
  apply wbytes_outside; [exact Hn | ].
  rewrite u_at by lia. lia.
Qed.

Inductive steps (segs : list Segment) : machine_state -> machine_state -> Prop :=
| steps_refl : forall s, steps segs s s
| steps_step : forall s s1 t, RiscvSemantics.step segs s = MachineOk s1 -> steps segs s1 t -> steps segs s t.

Lemma steps_trans : forall segs a b d, steps segs a b -> steps segs b d -> steps segs a d.
Proof.
  intros segs a b d H. induction H; intros; [assumption | econstructor; eauto].
Qed.

Section Steps.
Context {fx : FPState}.
Variable c : cfg.

Lemma b_npc : forall (p : word) sz, p + Z_to_bv 64 sz = v_addi p sz.
Proof.
  intros. apply bv_eq. unfold v_addi.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  apply bv_wrap_add_idemp_r.
Qed.

Lemma at_next : forall o sz o', (o + sz = o')%Z -> v_addi (at_ c o) sz = at_ c o'.
Proof.
  intros o sz o' <-. apply bv_eq. unfold v_addi, at_.
  rewrite !Z_to_bv_unsigned. rewrite bv_wrap_add_idemp_l. f_equal. lia.
Qed.

Lemma j_opimm : forall segs regs o o' mem rom op rd rs (imm : bv 12) sz w,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, sz) ->
  (o + sz = o')%Z -> is_x0 rd = false ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst (regupd regs rd (alu64 op (getr regs rs) (sext 64 imm))) (at_ c o') mem rom).
Proof.
  intros segs regs o o' mem rom op rd rs imm sz w Hwx He Hd Ho Hrd.
  wx_step_pipeline Hwx He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  rewrite Hrd; cbv beta iota.
  rewrite b_npc, (at_next o sz o' Ho).
  destruct (is_x0 rs); reflexivity.
Qed.

Lemma j_op : forall segs regs o o' mem rom op rd rs1 rs2 sz w,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, sz) ->
  (o + sz = o')%Z -> is_x0 rd = false ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst (regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2))) (at_ c o') mem rom).
Proof.
  intros segs regs o o' mem rom op rd rs1 rs2 sz w Hwx He Hd Ho Hrd.
  wx_step_pipeline Hwx He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  rewrite Hrd; cbv beta iota.
  rewrite b_npc, (at_next o sz o' Ho).
  destruct (is_x0 rs1); destruct (is_x0 rs2); reflexivity.
Qed.

Lemma j_ld : forall segs regs o o' mem rom rd rs (imm : bv 12) sz w v,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, sz) ->
  (o + sz = o')%Z -> is_x0 rd = false ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some (word_to_le_bytes 8 v) ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst (regupd regs rd v) (at_ c o') mem rom).
Proof.
  intros segs regs o o' mem rom rd rs imm sz w v Hwx He Hd Ho Hrd Hread.
  assert (Hv : bytes_le_to_Z (word_to_le_bytes 8 v) = bv_unsigned v) by apply bytes_le_n_to_le_8.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
  wx_step_pipeline Hwx He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc, (at_next o sz o' Ho).
  rewrite Hrd. reflexivity.
Qed.

Lemma j_sd : forall segs regs o o' mem rom (rs1 rs2 : reg) (imm : bv 12) sz w a v,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, sz) ->
  (o + sz = o')%Z ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst regs (at_ c o') (wbytes mem a (word_to_le_bytes 8 v)) rom).
Proof.
  intros segs regs o o' mem rom rs1 rs2 imm sz w a v Hwx He Hd Ho Ha Hv Hok.
  subst a v.
  wx_step_pipeline Hwx He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc, (at_next o sz o' Ho).
  reflexivity.
Qed.

Lemma j_br_tk : forall segs regs o o' mem rom cc rs1 rs2 (imm : bv 13) sz w,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (Branch cc rs1 rs2 imm, sz) ->
  (o + bv_signed imm = o')%Z ->
  branch_taken cc (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst regs (at_ c o') mem rom).
Proof.
  intros segs regs o o' mem rom cc rs1 rs2 imm sz w Hwx He Hd Ho Hc.
  wx_step_pipeline Hwx He Hd.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext, (at_next o (bv_signed imm) o' Ho); reflexivity.
Qed.

Lemma j_br_ft : forall segs regs o o' mem rom cc rs1 rs2 (imm : bv 13) sz w,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (Branch cc rs1 rs2 imm, sz) ->
  (o + sz = o')%Z ->
  branch_taken cc (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst regs (at_ c o') mem rom).
Proof.
  intros segs regs o o' mem rom cc rs1 rs2 imm sz w Hwx He Hd Ho Hc.
  wx_step_pipeline Hwx He Hd.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc, (at_next o sz o' Ho); reflexivity.
Qed.


Lemma j_shift : forall segs regs o o' mem rom op rd rs (sh : bv 6) sz w,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, sz) ->
  (o + sz = o')%Z -> is_x0 rd = false ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst (regupd regs rd (alu64 op (getr regs rs) (zext 64 sh))) (at_ c o') mem rom).
Proof.
  intros segs regs o o' mem rom op rd rs sh sz w Hwx He Hd Ho Hrd.
  wx_step_pipeline Hwx He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  rewrite Hrd; cbv beta iota.
  rewrite b_npc, (at_next o sz o' Ho).
  destruct (is_x0 rs); reflexivity.
Qed.

Lemma j_lui : forall segs regs o o' mem rom rd (imm : bv 20) sz w,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, sz) ->
  (o + sz = o')%Z -> is_x0 rd = false ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst (regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12))) (at_ c o') mem rom).
Proof.
  intros segs regs o o' mem rom rd imm sz w Hwx He Hd Ho Hrd.
  wx_step_pipeline Hwx He Hd.
  rewrite ?bv_eqb0_is_x0.
  rewrite Hrd; cbv beta iota.
  rewrite b_lui, b_npc, (at_next o sz o' Ho). reflexivity.
Qed.

Lemma j_auipc : forall segs regs o o' mem rom rd (imm : bv 20) sz w,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, sz) ->
  (o + sz = o')%Z -> is_x0 rd = false ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst (regupd regs rd (v_auipc (at_ c o) (Z.shiftl (bv_signed imm) 12))) (at_ c o') mem rom).
Proof.
  intros segs regs o o' mem rom rd imm sz w Hwx He Hd Ho Hrd.
  wx_step_pipeline Hwx He Hd.
  rewrite ?bv_eqb0_is_x0.
  rewrite Hrd; cbv beta iota.
  rewrite b_auipc, b_npc, (at_next o sz o' Ho). reflexivity.
Qed.

Lemma j_jal0 : forall segs regs o mem rom rd (imm : bv 21) sz w,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) -> is_x0 rd = true ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst regs (at_ c (o + bv_signed imm)) mem rom).
Proof.
  intros segs regs o mem rom rd imm sz w Hwx He Hd Hrd.
  wx_step_pipeline Hwx He Hd.
  rewrite ?bv_eqb0_is_x0, Hrd; cbv beta iota.
  rewrite b_addsext, (at_next o (bv_signed imm) _ eq_refl). reflexivity.
Qed.

Lemma j_jal1 : forall segs regs o o' mem rom rd (imm : bv 21) sz w,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) -> is_x0 rd = false ->
  (o + sz = o')%Z ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst (regupd regs rd (at_ c o')) (at_ c (o + bv_signed imm)) mem rom).
Proof.
  intros segs regs o o' mem rom rd imm sz w Hwx He Hd Hrd Ho.
  wx_step_pipeline Hwx He Hd.
  rewrite ?bv_eqb0_is_x0, Hrd; cbv beta iota.
  rewrite b_addsext, b_npc, (at_next o sz o' Ho), (at_next o (bv_signed imm) _ eq_refl). reflexivity.
Qed.

Lemma j_jalr1 : forall segs regs o o' mem rom rd rs (imm : bv 12) sz w,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs imm, sz) -> is_x0 rd = false ->
  (o + sz = o')%Z ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst (regupd regs rd (at_ c o')) (jalr_tgt (getr regs rs) (bv_signed imm)) mem rom).
Proof.
  intros segs regs o o' mem rom rd rs imm sz w Hwx He Hd Hrd Ho.
  wx_step_pipeline Hwx He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0, Hrd; cbv beta iota.
  rewrite b_npc, (at_next o sz o' Ho).
  destruct (is_x0 rs); cbv beta iota; rewrite ?b_jalr; reflexivity.
Qed.

Lemma j_jalr0 : forall segs regs o mem rom rd rs (imm : bv 12) sz w,
  wx_fetch segs mem (at_ c o) w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs imm, sz) -> is_x0 rd = true ->
  RiscvSemantics.step segs (mkst regs (at_ c o) mem rom) =
  MachineOk (mkst regs (jalr_tgt (getr regs rs) (bv_signed imm)) mem rom).
Proof.
  intros segs regs o mem rom rd rs imm sz w Hwx He Hd Hrd.
  wx_step_pipeline Hwx He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0, Hrd; cbv beta iota.
  destruct (is_x0 rs); cbv beta iota; rewrite ?b_jalr; reflexivity.
Qed.

End Steps.
