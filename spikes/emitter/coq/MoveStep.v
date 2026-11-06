(** * Step lemmas the checker's instructions need beyond spike 5's, and a continuation-style
    run predicate, so that a read value can be named after the run has started.
    Proof-side only: nothing here is trusted. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec.
From LinuxProcessSemantics.Examples.emitter_ns Require Import emitter_code GcStep.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

Section S.
Context {fx : FPState}.

Lemma z_lui : forall sz segs regs pc mem rom w rd (imm : bv 20),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, sz) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
                  (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w rd imm Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota; rewrite ?b_npc, ?b_lui; reflexivity.
Qed.

Lemma z_lui_at : forall sz segs regs pc mem rom w rd (imm : bv 20) v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, sz) ->
  bv_eqb rd 0 = false ->
  v_lui (Z.shiftl (bv_signed imm) 12) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc sz) mem rom).
Proof.
  intros. erewrite z_lui by eassumption. rewrite H2. subst v. reflexivity.
Qed.

Lemma z_addiw : forall sz segs regs pc mem rom w rd rs (imm : bv 12),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, sz) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addiw (getr regs rs) (bv_signed imm)))
                  (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w rd rs imm Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?w_addiw, ?b_npc; reflexivity.
Qed.

Lemma z_addiw_at : forall sz segs regs pc mem rom w rd rs (imm : bv 12) v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, sz) ->
  bv_eqb rd 0 = false ->
  v_addiw (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc sz) mem rom).
Proof.
  intros. erewrite z_addiw by eassumption. rewrite H2. subst v. reflexivity.
Qed.

Lemma z_lhu_at : forall sz segs regs pc mem rom w rd rs (imm : bv 12) bs a (z : Z),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, sz) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 2%nat = Some bs ->
  bytes_le_to_Z bs = z -> (0 <= z < 65536)%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (Z_to_bv 64 z)) (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w rd rs imm bs a z Hwx Hecall Hdecode Hrd Ha Hread Hz Hr.
  subst a.
  assert (Hv : zext 64 (bv_extract 0 16 (le_bytes_to_word bs)) = Z_to_bv 64 z).
  { apply bv_eq. unfold zext. rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    unfold le_bytes_to_word. rewrite Hz, Z_to_bv_unsigned.
    rewrite (bv_wrap_small 64 z) by (change (bv_modulus 64) with (2^64)%Z; lia).
    rewrite (bv_wrap_small 16 z) by (change (bv_modulus 16) with 65536%Z; lia).
    reflexivity. }
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite Hv, b_npc.
  rewrite bv_eqb0_is_x0 in Hrd. rewrite Hrd. reflexivity.
Qed.

(** Runs to the return address [r], ending in a state with property [P]. *)
Definition Run (segs : list Segment) (r : word) mem rom (P : bvmap 5 word -> Prop)
    (st : machine_state) : Prop :=
  exists regs', msteps segs st (mkst regs' r mem rom) /\ P regs'.

Lemma run_step : forall segs r mem rom P ms ms',
  ms_svc_pending ms = None -> RiscvSemantics.step segs ms = MachineOk ms' ->
  Run segs r mem rom P ms' -> Run segs r mem rom P ms.
Proof.
  intros segs r mem rom P ms ms' Hn Hs (regs' & Hm & Hp).
  exists regs'. split; [|exact Hp]. eapply mst_step; eauto.
Qed.

Lemma run_done : forall segs r mem rom (P : bvmap 5 word -> Prop) regs,
  P regs -> Run segs r mem rom P (mkst regs r mem rom).
Proof.
  intros. exists regs. split; [apply mst_refl | assumption].
Qed.

End S.

Open Scope Z_scope.

(** Decide branches from numbers, never from [decide] on bit vectors. *)
Lemma br_ltu_t : forall a b : word, bv_unsigned a < bv_unsigned b -> branch_taken BC_LTU a b = true.
Proof. intros a b H. cbn [branch_taken]. unfold bv_ltu. apply Z.ltb_lt. exact H. Qed.
Lemma br_ltu_f : forall a b : word, bv_unsigned b <= bv_unsigned a -> branch_taken BC_LTU a b = false.
Proof. intros a b H. cbn [branch_taken]. unfold bv_ltu. apply Z.ltb_ge. exact H. Qed.
Lemma br_geu_t : forall a b : word, bv_unsigned b <= bv_unsigned a -> branch_taken BC_GEU a b = true.
Proof. intros a b H. cbn [branch_taken]. unfold bv_ltu. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.
Lemma br_geu_f : forall a b : word, bv_unsigned a < bv_unsigned b -> branch_taken BC_GEU a b = false.
Proof. intros a b H. cbn [branch_taken]. unfold bv_ltu. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma eqb_num_t : forall a b : word, bv_unsigned a = bv_unsigned b -> bv_eqb a b = true.
Proof. intros a b H. unfold bv_eqb. apply Z.eqb_eq. exact H. Qed.
Lemma eqb_num_f : forall a b : word, bv_unsigned a <> bv_unsigned b -> bv_eqb a b = false.
Proof. intros a b H. unfold bv_eqb. apply Z.eqb_neq. exact H. Qed.
Lemma br_eq_t : forall a b : word, bv_unsigned a = bv_unsigned b -> branch_taken BC_EQ a b = true.
Proof. intros a b H. cbn [branch_taken]. apply eqb_num_t. exact H. Qed.
Lemma br_eq_f : forall a b : word, bv_unsigned a <> bv_unsigned b -> branch_taken BC_EQ a b = false.
Proof. intros a b H. cbn [branch_taken]. apply eqb_num_f. exact H. Qed.
Lemma br_ne_t : forall a b : word, bv_unsigned a <> bv_unsigned b -> branch_taken BC_NE a b = true.
Proof. intros a b H. cbn [branch_taken]. rewrite eqb_num_f by exact H. reflexivity. Qed.
Lemma br_ne_f : forall a b : word, bv_unsigned a = bv_unsigned b -> branch_taken BC_NE a b = false.
Proof. intros a b H. cbn [branch_taken]. rewrite eqb_num_t by exact H. reflexivity. Qed.

Lemma U : forall z : Z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply u_Z2bv; lia. Qed.
