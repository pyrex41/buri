(** * Rung 2: [copy_value], the paths with no copy: a non-pointer, and a pointer to an
    object already forwarded. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.gc_rate_ns Require Import gc_rate_code GcStep GcTac GcMem Rung2Frame.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

(** value.h: the low three bits of a value, and the pointer it holds. *)
Definition tag (v : word) : Z := (bv_unsigned v mod 8)%Z.
Definition ptr_of (v : word) : word := v_andi v (-8).
(** V_FORWARD = SPECIAL(4) = (4 << 3) | TAG_SPECIAL = 34. *)
Definition V_FORWARD : word := Z_to_bv 64 34.
Definition is_ptr_tag (t : Z) : Prop := (t = 1 \/ t = 3 \/ t = 5 \/ t = 6)%Z.
Definition non_ptr_tag (t : Z) : Prop := (t = 0 \/ t = 2 \/ t = 4 \/ t = 7)%Z.

Lemma tag_range : forall v, (0 <= tag v < 8)%Z.
Proof. intros. apply Z.mod_pos_bound. lia. Qed.

Lemma andi7 : forall v : word, v_andi v 7 = Z_to_bv 64 (tag v).
Proof.
  intros v. unfold v_andi, tag. change (bv_wrap 64 7) with (Z.ones 3).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma andi5 : forall v : word, v_andi v 5 = Z_to_bv 64 (Z.land (tag v) 5).
Proof.
  intros v. unfold v_andi, tag. change (bv_wrap 64 5) with 5%Z.
  change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia.
  rewrite <- Z.land_assoc. reflexivity.
Qed.

(** What every path promises its caller. *)
Definition returns {fx : FPState} (regs : bvmap 5 word) rom mem mem' (res : word) : Prop :=
  exists regs',
    msteps source_segs (mkst regs (0x11bc0 : word) mem rom)
      (mkst regs' (getr regs 1) mem' rom) /\
    getr regs' 10 = res /\
    getr regs' 1 = getr regs 1 /\ getr regs' 2 = getr regs 2 /\
    getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\
    getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\
    (forall x : reg, kept x -> getr regs' x = getr regs x).

Section S.
Context {fx : FPState}.

Lemma v_addi_zero : forall v : word, v_addi v 0 = v.
Proof. intros. exact (v_addi_0 v). Qed.

Lemma v_add_zero_l : forall y : word, v_add (Z_to_bv 64 0) y = y.
Proof.
  intros y. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_l. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_bv_unsigned.
Qed.

(** Exit: restore the frame and return a1. *)
Lemma cv_epilogue : forall R m rom (fp ra s0 s1 s2 s3 : word),
  mem_clear m TL TH ->
  getr R 2 = fp -> framed m fp ra s0 s1 s2 s3 ->
  (bv_unsigned ra mod 2 = 0)%Z ->
  (bv_unsigned fp + 48 <= 2^63)%Z ->
  exists R',
    msteps source_segs (mkst R (0x11dae : word) m rom) (mkst R' ra m rom) /\
    getr R' 10 = getr R 11 /\
    getr R' 1 = ra /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\ getr R' 18 = s2 /\ getr R' 19 = s3 /\
    getr R' 2 = at_off fp 48 /\
    (forall x : reg, kept x -> getr R' x = getr R x).
Proof.
  intros R m rom fp ra s0 s1 s2 s3 Hc Hsp [Hra [Hs0 [Hs1 [Hs2 Hs3]]]] Hev Hb.
  assert (Hadr : forall k, v_addi fp k = at_off fp k) by reflexivity.
  eexists. split.
  - wsv Hc SF_11dae SD_11dae (getr R 11) ltac:(apply v_add_zero_l).
    wld Hc SF_11db0 SD_11db0 (at_off fp 40) ra ltac:(rewrite Hsp; apply Hadr) Hra.
    wld Hc SF_11db2 SD_11db2 (at_off fp 32) s0 ltac:(rewrite Hsp; apply Hadr) Hs0.
    wld Hc SF_11db4 SD_11db4 (at_off fp 24) s1 ltac:(rewrite Hsp; apply Hadr) Hs1.
    wld Hc SF_11db6 SD_11db6 (at_off fp 16) s2 ltac:(rewrite Hsp; apply Hadr) Hs2.
    wld Hc SF_11db8 SD_11db8 (at_off fp 8) s3 ltac:(rewrite Hsp; apply Hadr) Hs3.
    wsv Hc SF_11dba SD_11dba (at_off fp 48) ltac:(rewrite Hsp; apply Hadr).
    eapply mst_step;
    [ reflexivity
    | eapply z_jr with (tgt := ra);
      [ wxf_with Hc SF_11dbc | reflexivity | exact SD_11dbc
      | gres; apply jalr_tgt_even; [exact Hev | reflexivity] ]
    | apply mst_refl ].
  - gres. repeat split; [reflexivity .. | kept_frame].
Qed.

Lemma at_off_cancel : forall sp : word, (48 <= bv_unsigned sp)%Z ->
  at_off (at_off sp (-48)) 48 = sp.
Proof.
  intros sp Hs. pose proof (bv_unsigned_in_range _ sp) as Hr.
  change (bv_modulus 64) with (2^64)%Z in Hr.
  apply bv_eq. rewrite !u_at_off by (rewrite ?u_at_off by lia; lia). lia.
Qed.

(** Entry, a body from 0x11bcc to 0x11dae, and exit compose into the contract. *)
Lemma cv_compose : forall regs mem rom (sp res : word) m2 R2,
  mem_clear mem TL TH ->
  getr regs 2 = sp -> stack_ok sp ->
  writable mem (bv_unsigned sp - 48) (bv_unsigned sp) ->
  (bv_unsigned (getr regs 1) mod 2 = 0)%Z ->
  let fp := at_off sp (-48) in
  let M := push_mem mem fp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) in
  let R1 := regupd regs 2 fp in
  msteps source_segs (mkst R1 (0x11bcc : word) M rom) (mkst R2 (0x11dae : word) m2 rom) ->
  getr R2 11 = res -> getr R2 2 = fp ->
  (forall x : reg, kept x -> getr R2 x = getr R1 x) ->
  mem_clear m2 TL TH ->
  framed m2 fp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
  returns regs rom mem m2 res.
Proof.
  intros regs mem rom sp res m2 R2 Hc Hsp Hst Hw Hev fp M R1 Hb Hres Hsp2 Hk Hc2 Hf.
  destruct Hst as [Hlo Hhi] eqn:Hst'.
  pose proof (bv_unsigned_in_range _ sp) as Hr.
  change (bv_modulus 64) with (2^64)%Z in Hr. unfold TH in Hlo.
  assert (Hfp : bv_unsigned fp = (bv_unsigned sp - 48)%Z) by (apply u_at_off; lia).
  destruct (cv_epilogue R2 m2 rom fp _ _ _ _ _ Hc2 Hsp2 Hf Hev ltac:(lia))
    as (R' & Hm & Ha0 & Hra & H8 & H9 & H18 & H19 & Hs & Hkp).
  exists R'. split.
  - eapply msteps_trans; [exact (cv_prologue regs mem rom sp Hc Hsp Hst Hw)|].
    eapply msteps_trans; [exact Hb|exact Hm].
  - rewrite Ha0, Hres. repeat split; try assumption.
    + rewrite Hs, Hsp. apply at_off_cancel. lia.
    + intros x Hx. rewrite Hkp, Hk by exact Hx. unfold R1.
      rewrite getr_other; [reflexivity|]. destruct Hx as (_ & H2 & _). exact H2.
Qed.

Lemma wat_push : forall mem fp ra s0 s1 s2 s3 (a x : word),
  wat mem a x ->
  (bv_unsigned fp + 48 <= 2^63)%Z ->
  (bv_unsigned a + 8 <= bv_unsigned fp + 8 \/ bv_unsigned fp + 48 <= bv_unsigned a)%Z ->
  (bv_unsigned a + 8 <= 2^64)%Z ->
  wat (push_mem mem fp ra s0 s1 s2 s3) a x.
Proof.
  intros. unfold wat in *. rewrite push_outside; first [assumption | cbn [Z.of_nat]; lia].
Qed.

Ltac np_case Hc H5 H7 t :=
  eexists; split;
  [ wsv Hc SF_11bcc SD_11bcc (Z_to_bv 64 (Z.land t 5)) ltac:(exact H5);
    ws Hc SF_11bd0 SD_11bd0;
    wsv Hc SF_11bd2 SD_11bd2 (Z_to_bv 64 t) ltac:(exact H7);
    wbr_ft Hc SF_11bd6 SD_11bd6 ltac:(vm_compute; reflexivity);
    ws Hc SF_11bda SD_11bda;
    wbr_tk Hc SF_11bde SD_11bde ltac:(vm_compute; reflexivity);
    apply mst_refl
  | gres; repeat split; [reflexivity .. | kept_frame] ].

(** Dispatch on the tag: a non-pointer goes straight to the exit. *)
Lemma cv_body_nonptr : forall R m rom,
  mem_clear m TL TH -> non_ptr_tag (tag (getr R 11)) ->
  exists R2,
    msteps source_segs (mkst R (0x11bcc : word) m rom) (mkst R2 (0x11dae : word) m rom) /\
    getr R2 11 = getr R 11 /\ getr R2 2 = getr R 2 /\
    (forall x : reg, kept x -> getr R2 x = getr R x).
Proof.
  intros R m rom Hc Hnp.
  pose proof (andi7 (getr R 11)) as H7. pose proof (andi5 (getr R 11)) as H5.
  destruct Hnp as [E|[E|[E|E]]]; rewrite E in H7, H5.
  - np_case Hc H5 H7 0%Z.
  - np_case Hc H5 H7 2%Z.
  - np_case Hc H5 H7 4%Z.
  - np_case Hc H5 H7 7%Z.
Qed.

(** THEOREM: a non-pointer is returned unchanged, and memory changes only in the frame. *)
Theorem copy_value_nonptr : forall regs mem rom (sp : word),
  mem_clear mem TL TH ->
  getr regs 2 = sp -> stack_ok sp ->
  writable mem (bv_unsigned sp - 48) (bv_unsigned sp) ->
  (bv_unsigned (getr regs 1) mod 2 = 0)%Z ->
  non_ptr_tag (tag (getr regs 11)) ->
  returns regs rom mem
    (push_mem mem (at_off sp (-48)) (getr regs 1) (getr regs 8) (getr regs 9)
              (getr regs 18) (getr regs 19))
    (getr regs 11).
Proof.
  intros regs mem rom sp Hc Hsp Hst Hw Hev Hnp.
  pose proof Hst as [Hlo Hhi].
  pose proof (bv_unsigned_in_range _ sp) as Hr.
  change (bv_modulus 64) with (2^64)%Z in Hr. unfold TH in Hlo.
  set (fp := at_off sp (-48)).
  assert (Hfp : bv_unsigned fp = (bv_unsigned sp - 48)%Z) by (apply u_at_off; lia).
  set (M := push_mem mem fp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  assert (HcM : mem_clear M TL TH) by (apply push_clear; [exact Hc|rewrite Hfp; unfold TH; lia|rewrite Hfp; lia]).
  assert (Hnp' : non_ptr_tag (tag (getr (regupd regs 2 fp) 11))).
  { rewrite getr_other by reg_neq_tac. exact Hnp. }
  destruct (cv_body_nonptr (regupd regs 2 fp) M rom HcM Hnp') as (R2 & Hb & Ha1 & Hs & Hk).
  eapply (cv_compose regs mem rom sp (getr regs 11) M R2); try eassumption.
  - rewrite Ha1. apply getr_other. reg_neq_tac.
  - rewrite Hs. apply getr_same. reg_neq_tac.
  - apply push_framed. change (bv_unsigned fp + 48 <= 2^63)%Z. rewrite Hfp. lia.
Qed.

End S.
