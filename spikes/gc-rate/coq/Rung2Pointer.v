(** * Rung 2: [copy_value] on a pointer into from-space.  Reaching the forwarding test,
    the already-forwarded path, and a pair whose tail isn't a pair. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.gc_rate_ns Require Import gc_rate_code GcStep GcTac GcMem Rung2Frame Rung2Paths.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

(** [Copy] (heap.c): from at 0, from_words at 8, next at 16.  [v] points into from-space;
    a pointer outside it goes to [reach_large], which this contract excludes by premise. *)
Definition in_from (from fw p : word) : Prop :=
  (bv_unsigned from <= bv_unsigned p < bv_unsigned from + 8 * bv_unsigned fw)%Z /\
  (bv_unsigned from + 8 * bv_unsigned fw < 2^64)%Z.

Lemma ltu_false : forall a b : word, (bv_unsigned b <= bv_unsigned a)%Z ->
  branch_taken BC_LTU a b = false.
Proof. intros. cbn [branch_taken]. unfold bv_ltu. apply Z.ltb_ge. exact H. Qed.

Lemma ltu_true : forall a b : word, (bv_unsigned a < bv_unsigned b)%Z ->
  branch_taken BC_LTU a b = true.
Proof. intros. cbn [branch_taken]. unfold bv_ltu. apply Z.ltb_lt. exact H. Qed.

Lemma ne_true : forall a b : word, bv_unsigned a <> bv_unsigned b ->
  branch_taken BC_NE a b = true.
Proof.
  intros. cbn [branch_taken]. unfold bv_eqb.
  rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity.
Qed.

Lemma ne_false : forall a b : word, a = b -> branch_taken BC_NE a b = false.
Proof.
  intros a b ->. cbn [branch_taken]. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
Qed.

Section S.
Context {fx : FPState}.

Ltac dispatch_prefix Hc P5 P7 t :=
  wsv Hc SF_11bcc SD_11bcc (Z_to_bv 64 (Z.land t 5)) P5;
  ws Hc SF_11bd0 SD_11bd0;
  wsv Hc SF_11bd2 SD_11bd2 (Z_to_bv 64 t) P7.

(** From the tag test to the forwarding test. *)
Lemma cv_to_test : forall R m rom (c from fw v : word) t,
  mem_clear m TL TH ->
  getr R 10 = c -> getr R 11 = v ->
  tag v = t -> is_ptr_tag t ->
  wat m c from -> wat m (at_off c 8) fw ->
  in_from from fw (ptr_of v) ->
  exists R2,
    msteps source_segs (mkst R (0x11bcc : word) m rom) (mkst R2 (0x11c00 : word) m rom) /\
    getr R2 10 = c /\ getr R2 11 = v /\ getr R2 14 = Z_to_bv 64 t /\
    getr R2 13 = from /\ getr R2 17 = ptr_of v /\ getr R2 2 = getr R 2 /\
    (forall x : reg, kept x -> getr R2 x = getr R x).
Proof.
  intros R m rom c from fw v t Hc H10 H11 Ht Hp Hfrom Hfw [Hif Hnw].
  pose proof (andi7 v) as H7. pose proof (andi5 v) as H5. rewrite Ht in H7, H5.
  pose proof (bv_unsigned_in_range _ fw) as Hfr. pose proof (bv_unsigned_in_range _ from) as Hfrr.
  change (bv_modulus 64) with (2^64)%Z in Hfr, Hfrr.
  assert (Hs : forall RR, getr RR 15 = getr RR 15) by reflexivity.
  assert (Htail : forall R0, getr R0 10 = c -> getr R0 11 = v -> getr R0 14 = Z_to_bv 64 t ->
      exists R2,
      msteps source_segs (mkst R0 (0x11be2 : word) m rom) (mkst R2 (0x11c00 : word) m rom) /\
      getr R2 10 = c /\ getr R2 11 = v /\ getr R2 14 = Z_to_bv 64 t /\
      getr R2 13 = from /\ getr R2 17 = ptr_of v /\ getr R2 2 = getr R0 2 /\
      (forall x : reg, kept x -> getr R2 x = getr R0 x)).
  { intros R0 A10 A11 A14.
    assert (Hadd : v_add (v_slli fw 3) from = Z_to_bv 64 (bv_unsigned from + 8 * bv_unsigned fw)).
    { unfold v_add, v_slli. rewrite Z.shiftl_mul_pow2 by lia.
      rewrite u_Z2bv by lia. f_equal. change (2^3)%Z with 8%Z. lia. }
    eexists. split.
    - wld Hc SF_11be2 SD_11be2 c from ltac:(rewrite A10; apply v_addi_zero) Hfrom.
      wsv Hc SF_11be4 SD_11be4 (ptr_of v) ltac:(rewrite A11; reflexivity).
      wbr_ft Hc SF_11be8 SD_11be8 ltac:(apply ltu_false; lia).
      wld Hc SF_11bec SD_11bec (at_off c 8) fw ltac:(rewrite A10; reflexivity) Hfw.
      ws Hc SF_11bee SD_11bee.
      wsv Hc SF_11bf0 SD_11bf0 (Z_to_bv 64 (bv_unsigned from + 8 * bv_unsigned fw)) ltac:(exact Hadd).
      wbr_tk Hc SF_11bf2 SD_11bf2 ltac:(apply ltu_true; rewrite u_Z2bv by lia; lia).
      apply mst_refl.
    - gres. rewrite ?A10, ?A11, ?A14. repeat split; [reflexivity .. | kept_frame]. }
  assert (Hpre : exists R0,
      msteps source_segs (mkst R (0x11bcc : word) m rom) (mkst R0 (0x11be2 : word) m rom) /\
      getr R0 10 = c /\ getr R0 11 = v /\ getr R0 14 = Z_to_bv 64 t /\ getr R0 2 = getr R 2 /\
      (forall x : reg, kept x -> getr R0 x = getr R x)).
  { destruct Hp as [E|[E|[E|E]]]; subst t; eexists; split.
    - dispatch_prefix Hc ltac:(rewrite H11, H5, E; reflexivity) ltac:(rewrite H11, H7, E; reflexivity) 1%Z.
      wbr_tk Hc SF_11bd6 SD_11bd6 ltac:(vm_compute; reflexivity). apply mst_refl.
    - gres. repeat split; [exact H10 | exact H11 | rewrite E; reflexivity | kept_frame].
    - dispatch_prefix Hc ltac:(rewrite H11, H5, E; reflexivity) ltac:(rewrite H11, H7, E; reflexivity) 3%Z.
      wbr_tk Hc SF_11bd6 SD_11bd6 ltac:(vm_compute; reflexivity). apply mst_refl.
    - gres. repeat split; [exact H10 | exact H11 | rewrite E; reflexivity | kept_frame].
    - dispatch_prefix Hc ltac:(rewrite H11, H5, E; reflexivity) ltac:(rewrite H11, H7, E; reflexivity) 5%Z.
      wbr_ft Hc SF_11bd6 SD_11bd6 ltac:(vm_compute; reflexivity).
      ws Hc SF_11bda SD_11bda.
      wbr_ft Hc SF_11bde SD_11bde ltac:(vm_compute; reflexivity). apply mst_refl.
    - gres. repeat split; [exact H10 | exact H11 | rewrite E; reflexivity | kept_frame].
    - dispatch_prefix Hc ltac:(rewrite H11, H5, E; reflexivity) ltac:(rewrite H11, H7, E; reflexivity) 6%Z.
      wbr_ft Hc SF_11bd6 SD_11bd6 ltac:(vm_compute; reflexivity).
      ws Hc SF_11bda SD_11bda.
      wbr_ft Hc SF_11bde SD_11bde ltac:(vm_compute; reflexivity). apply mst_refl.
    - gres. repeat split; [exact H10 | exact H11 | rewrite E; reflexivity | kept_frame]. }
  destruct Hpre as (R0 & Hm0 & A10 & A11 & A14 & A2 & Ak).
  destruct (Htail R0 A10 A11 A14) as (R2 & Hm2 & B10 & B11 & B14 & B13 & B17 & B2 & Bk).
  exists R2. split; [eapply msteps_trans; eassumption|].
  repeat split; try assumption.
  - rewrite B2. exact A2.
  - intros x Hx. rewrite Bk, Ak by exact Hx. reflexivity.
Qed.

End S.
