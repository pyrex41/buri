(** * Per-instruction steps for any instruction length, and fetch from captured bytes.

    Theorem's [WxExec] lemmas assume 4-byte instructions; the emitted code is mostly
    compressed, so these take the length as a parameter.  Proof-side only. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec MemSplit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Examples.jit_slice Require Import SliceCode.
Import ListNotations.
Open Scope bv_scope.

Definition at_ (o : Z) : word := Z_to_bv 64 (code_base + o).

Definition code_byte (i : Z) : byte := Z_to_bv 8 (nth (Z.to_nat i) captured 0%Z).

Definition code_word (o : Z) : bv 32 :=
  le4 (code_byte (o + 3)) (code_byte (o + 2)) (code_byte (o + 1)) (code_byte o).

(** The captured code is in memory, in one writable and executable segment. *)
Record CodeOK (segs : list Segment) (m : word -> option byte) : Prop := {
  c_ro : no_ro_exec segs = true;
  c_seg : exists seg, (forall a, (code_base <= a)%Z -> (a + 4 <= code_base + code_len)%Z ->
            find_segment segs a 4 = Some seg) /\
          (seg_executable seg && seg_writable seg) = true;
  c_bytes : forall i, (0 <= i < code_len)%Z -> m (at_ i) = Some (code_byte i)
}.

Lemma at_plus1 : forall o, at_ o + 1 = at_ (o + 1).
Proof.
  intros o. apply bv_eq. unfold at_.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned 1) with 1%Z.
  rewrite bv_wrap_add_idemp_l. f_equal. lia.
Qed.

Lemma base_small : (code_base + code_len < 2^48)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma u_at : forall o, (0 <= o <= code_len)%Z -> bv_unsigned (at_ o) = (code_base + o)%Z.
Proof.
  intros o Ho. unfold at_. pose proof base_small as Hs.
  assert (Hp : (0 <= code_base)%Z) by (vm_compute; discriminate).
  apply u_Z2bv; lia.
Qed.

Lemma wx_at : forall segs m o,
  CodeOK segs m -> (0 <= o)%Z -> (o + 4 <= code_len)%Z -> (o mod 2 = 0)%Z ->
  wx_fetch segs m (at_ o) (code_word o).
Proof.
  intros segs m o [Hro [seg [Hseg Hflags]] Hb] Hl Hh Hev. split.
  - apply fetch_word_none_no_ro_exec, Hro.
  - unfold fetch_word_ov.
    rewrite u_at by lia.
    assert (Hbase : (code_base mod 2 = 0)%Z) by reflexivity.
    assert (Hmod : ((code_base + o) mod 2 = 0)%Z).
    { rewrite Z.add_mod by lia. rewrite Hbase, Hev. reflexivity. }
    rewrite Hmod. cbn [Z.eqb negb].
    unfold code_read_ov.
    rewrite u_at by lia.
    change (Z.of_N 4) with 4%Z.
    rewrite Hseg by lia. rewrite Hflags.
    cbn [seg_ov_read_bytes N.to_nat Pos.to_nat Pos.iter_op].
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

Lemma code_ok_wbytes : forall segs m a bs,
  CodeOK segs m ->
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned a + Z.of_nat (length bs) <= code_base \/ code_base + code_len <= bv_unsigned a)%Z ->
  CodeOK segs (wbytes m a bs).
Proof.
  intros segs m a bs [Hro Hs Hb] Hn Hd. constructor; [exact Hro | exact Hs | ].
  intros i Hi. rewrite <- (Hb i Hi).
  apply wbytes_outside; [exact Hn | ].
  rewrite u_at by lia. lia.
Qed.

Inductive steps (segs : list Segment) : machine_state -> machine_state -> Prop :=
| steps_refl : forall s, steps segs s s
| steps_step : forall s s1 t, RiscvSemantics.step segs s = MachineOk s1 -> steps segs s1 t -> steps segs s t.

Section Steps.
Context {fx : FPState}.

Lemma b_npc : forall (p : word) sz, p + Z_to_bv 64 sz = v_addi p sz.
Proof.
  intros. apply bv_eq. unfold v_addi.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  apply bv_wrap_add_idemp_r.
Qed.

Lemma at_next : forall o sz o', (o + sz = o')%Z -> v_addi (at_ o) sz = at_ o'.
Proof.
  intros o sz o' <-. apply bv_eq. unfold v_addi, at_.
  rewrite !Z_to_bv_unsigned. rewrite bv_wrap_add_idemp_l. f_equal. lia.
Qed.

Lemma j_opimm : forall segs regs o o' mem rom op rd rs (imm : bv 12) sz w,
  wx_fetch segs mem (at_ o) w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, sz) ->
  (o + sz = o')%Z -> is_x0 rd = false ->
  RiscvSemantics.step segs (mkst regs (at_ o) mem rom) =
  MachineOk (mkst (regupd regs rd (alu64 op (getr regs rs) (sext 64 imm))) (at_ o') mem rom).
Proof.
  intros segs regs o o' mem rom op rd rs imm sz w Hwx He Hd Ho Hrd.
  wx_step_pipeline Hwx He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  rewrite Hrd; cbv beta iota.
  rewrite b_npc, (at_next o sz o' Ho).
  destruct (is_x0 rs); reflexivity.
Qed.

Lemma j_op : forall segs regs o o' mem rom op rd rs1 rs2 sz w,
  wx_fetch segs mem (at_ o) w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, sz) ->
  (o + sz = o')%Z -> is_x0 rd = false ->
  RiscvSemantics.step segs (mkst regs (at_ o) mem rom) =
  MachineOk (mkst (regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2))) (at_ o') mem rom).
Proof.
  intros segs regs o o' mem rom op rd rs1 rs2 sz w Hwx He Hd Ho Hrd.
  wx_step_pipeline Hwx He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  rewrite Hrd; cbv beta iota.
  rewrite b_npc, (at_next o sz o' Ho).
  destruct (is_x0 rs1); destruct (is_x0 rs2); reflexivity.
Qed.

Lemma j_ld : forall segs regs o o' mem rom rd rs (imm : bv 12) sz w v,
  wx_fetch segs mem (at_ o) w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, sz) ->
  (o + sz = o')%Z -> is_x0 rd = false ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some (word_to_le_bytes 8 v) ->
  RiscvSemantics.step segs (mkst regs (at_ o) mem rom) =
  MachineOk (mkst (regupd regs rd v) (at_ o') mem rom).
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
  wx_fetch segs mem (at_ o) w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, sz) ->
  (o + sz = o')%Z ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (mkst regs (at_ o) mem rom) =
  MachineOk (mkst regs (at_ o') (wbytes mem a (word_to_le_bytes 8 v)) rom).
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

Lemma j_br_tk : forall segs regs o o' mem rom c rs1 rs2 (imm : bv 13) sz w,
  wx_fetch segs mem (at_ o) w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, sz) ->
  (o + bv_signed imm = o')%Z ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs (at_ o) mem rom) =
  MachineOk (mkst regs (at_ o') mem rom).
Proof.
  intros segs regs o o' mem rom c rs1 rs2 imm sz w Hwx He Hd Ho Hc.
  wx_step_pipeline Hwx He Hd.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext, (at_next o (bv_signed imm) o' Ho); reflexivity.
Qed.

Lemma j_br_ft : forall segs regs o o' mem rom c rs1 rs2 (imm : bv 13) sz w,
  wx_fetch segs mem (at_ o) w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, sz) ->
  (o + sz = o')%Z ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs (at_ o) mem rom) =
  MachineOk (mkst regs (at_ o') mem rom).
Proof.
  intros segs regs o o' mem rom c rs1 rs2 imm sz w Hwx He Hd Ho Hc.
  wx_step_pipeline Hwx He Hd.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc, (at_next o sz o' Ho); reflexivity.
Qed.

Lemma j_ret : forall segs regs o mem rom rs (imm : bv 12) sz w,
  wx_fetch segs mem (at_ o) w -> is_ecall w = false ->
  decode_any w = Some (Jalr 0 rs imm, sz) ->
  RiscvSemantics.step segs (mkst regs (at_ o) mem rom) =
  MachineOk (mkst regs (jalr_tgt (getr regs rs) (bv_signed imm)) mem rom).
Proof.
  intros segs regs o mem rom rs imm sz w Hwx He Hd.
  wx_step_pipeline Hwx He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota; rewrite ?b_jalr; reflexivity.
Qed.

Lemma j_jal_link : forall segs regs o o' mem rom (imm : bv 21) sz w tgt,
  wx_fetch segs mem (at_ o) w -> is_ecall w = false ->
  decode_any w = Some (Jal 1 imm, sz) ->
  (o + sz = o')%Z ->
  v_addi (at_ o) (bv_signed imm) = tgt ->
  RiscvSemantics.step segs (mkst regs (at_ o) mem rom) =
  MachineOk (mkst (regupd regs 1 (at_ o')) tgt mem rom).
Proof.
  intros segs regs o o' mem rom imm sz w tgt Hwx He Hd Ho Ht.
  wx_step_pipeline Hwx He Hd.
  rewrite b_addsext, b_npc, (at_next o sz o' Ho), Ht.
  reflexivity.
Qed.

End Steps.
