(** * Rung 2: the object-size dispatch inlined in [copy_value] (0x11c2a), which must agree
    with the [obj_words] spec of rung 1.  No stores. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.gc_rate_ns Require Import gc_rate_code GcStep GcTac GcMem Rung1ObjWords Rung2Frame Rung2Paths Rung2Pointer.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

Definition size_post {fx : FPState} (R Ry : bvmap 5 word) : Prop :=
  getr Ry 10 = getr R 10 /\ getr Ry 5 = getr R 5 /\ getr Ry 17 = getr R 17 /\
  getr Ry 14 = getr R 14 /\ getr Ry 16 = getr R 16 /\ getr Ry 2 = getr R 2 /\
  (forall x : reg, kept x -> getr Ry x = getr R x).

Ltac size_frame :=
  unfold size_post; gres; repeat split; try reflexivity; kept_frame.

Section S.
Context {fx : FPState}.

(** [11cda]: the shared tail of the strings and vectors. *)
Lemma seg_cda : forall R m rom (w : word),
  mem_clear m TL TH -> getr R 9 = w -> (bv_unsigned w < 2^60)%Z ->
  ((bv_unsigned w < 2)%Z /\ exists Ry,
     msteps source_segs (mkst R (0x11cda : word) m rom) (mkst Ry (0x11d48 : word) m rom) /\
     getr Ry 15 = Z_to_bv 64 2 /\ size_post R Ry) \/
  ((2 <= bv_unsigned w)%Z /\ exists Ry,
     msteps source_segs (mkst R (0x11cda : word) m rom) (mkst Ry (0x11d2c : word) m rom) /\
     getr Ry 11 = Z_to_bv 64 (1 + bv_unsigned w) /\ size_post R Ry).
Proof.
  intros R m rom w Hc A9 Hb.
  destruct (Z_lt_le_dec (bv_unsigned w) 2) as [Hl|Hg]; [left|right]; (split; [exact Hl || exact Hg|]).
  - eexists. split.
    + ws Hc SF_11cda SD_11cda.
      wbr_tk Hc SF_11cdc SD_11cdc ltac:(rewrite A9; apply ltu_true; 
        assert (Hu : bv_unsigned (v_addi (Z_to_bv 64 0) 2) = 2%Z) by (vm_compute; reflexivity); rewrite Hu; exact Hl).
      apply mst_refl.
    + gres. split; [bveq|size_frame].
  - assert (Hu2 : bv_unsigned (v_addi (Z_to_bv 64 0) 2) = 2%Z) by (vm_compute; reflexivity).
    assert (Hv : v_addi (v_add (v_sltiu w 1) w) 1 = Z_to_bv 64 (1 + bv_unsigned w)).
    { rewrite seqz_add_one by exact Hb. unfold at_least_two.
      assert (Hl2 : (2 <= 1 + bv_unsigned w)%Z) by lia.
      rewrite (proj2 (Z.ltb_ge _ _) Hl2). reflexivity. }
    eexists. split.
    + ws Hc SF_11cda SD_11cda.
      wbr_ft Hc SF_11cdc SD_11cdc ltac:(rewrite A9; apply ltu_false; rewrite Hu2; exact Hg).
      ws Hc SF_11ce0 SD_11ce0.
      ws Hc SF_11ce4 SD_11ce4.
      wsv Hc SF_11ce6 SD_11ce6 (Z_to_bv 64 (1 + bv_unsigned w)) ltac:(rewrite ?A9; exact Hv).
      wj Hc SF_11ce8 SD_11ce8 (0x11d2c : word).
      apply mst_refl.
    + gres. split; [reflexivity|size_frame].
Qed.

(** The jump-table dispatch, for any valid type. *)
Lemma obj_disp : forall R m rom (p h : word) k (jv tgt : word),
  mem_clear m TL TH -> getr R 17 = p -> wat m p h ->
  hdr_type (bv_unsigned h) = k -> (1 <= k <= 11)%Z ->
  ro4 (Z_to_bv 64 (0x43ae8 + 4 * (k - 1))) jv ->
  jalr_tgt (v_add (Z_to_bv 64 0x43ae8) (v_lw jv)) 0 = tgt ->
  exists Rz,
    msteps source_segs (mkst R (0x11c2a : word) m rom) (mkst Rz tgt m rom) /\
    getr Rz 9 = v_srli h 8 /\ getr Rz 11 = Z_to_bv 64 4 /\ getr Rz 15 = getr R 15 /\
    size_post R Rz.
Proof.
  intros R m rom p h k jv tgt Hc A17 Hh E Hk Hj Ht.
  pose proof (hdr_type_bits h) as Hbits. rewrite E in Hbits.
  assert (Hv1 : v_addi (v_srli (v_slli h 56) 59) (-1) = Z_to_bv 64 (k - 1)).
  { unfold v_addi. rewrite Hbits. reflexivity. }
  assert (Hslot : v_add (v_slli (Z_to_bv 64 (k - 1)) 2) (Z_to_bv 64 0x43ae8)
                  = Z_to_bv 64 (0x43ae8 + 4 * (k - 1))).
  { unfold v_add, v_slli. rewrite (u_Z2bv (k - 1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (u_Z2bv ((k - 1) * 2 ^ 2)) by lia. rewrite (u_Z2bv 0x43ae8) by lia.
    f_equal. change (2^2)%Z with 4%Z. lia. }
  assert (HJT : v_addi (v_auipc (0x11c3e : word) (Z.shiftl 50 12)) (-342) = Z_to_bv 64 0x43ae8) by bveq.
  destruct Hj as (bs & Hrd & Hbs).
  eexists. split.
  - wld Hc SF_11c2a SD_11c2a p h ltac:(rewrite A17; apply v_addi_zero) Hh.
    ws Hc SF_11c2e SD_11c2e.
    ws Hc SF_11c32 SD_11c32.
    wsv Hc SF_11c34 SD_11c34 (Z_to_bv 64 (k - 1)) ltac:(exact Hv1).
    ws Hc SF_11c36 SD_11c36.
    wbr_ft Hc SF_11c38 SD_11c38 ltac:(apply ltu_false; rewrite u_Z2bv by lia;
      assert (Hu : bv_unsigned (v_addi (Z_to_bv 64 0) 10) = 10%Z) by (vm_compute; reflexivity);
      rewrite Hu; lia).
    ws Hc SF_11c3c SD_11c3c.
    ws Hc SF_11c3e SD_11c3e.
    wsv Hc SF_11c42 SD_11c42 (Z_to_bv 64 0x43ae8) ltac:(exact HJT).
    wsv Hc SF_11c46 SD_11c46 (Z_to_bv 64 (0x43ae8 + 4 * (k - 1))) ltac:(exact Hslot).
    eapply mst_step;
    [ reflexivity
    | eapply z_lw_at with (a := Z_to_bv 64 (0x43ae8 + 4 * (k - 1))) (v := jv);
      [ wxf_with Hc SF_11c48 | reflexivity | exact SD_11c48 | reflexivity
      | gres; imm_norm; apply v_addi_zero
      | eapply read_clear;
        [ exact Hc
        | unfold TL; rewrite u_Z2bv by lia; lia
        | unfold TH; rewrite u_Z2bv by lia; cbn [Z.of_nat]; lia
        | exact Hrd ]
      | exact Hbs ]
    | norm_pc ].
    wsv Hc SF_11c4a SD_11c4a (v_srli h 8) ltac:(reflexivity).
    ws Hc SF_11c4c SD_11c4c.
    ws Hc SF_11c4e SD_11c4e.
    eapply mst_step;
    [ reflexivity
    | eapply z_jr with (tgt := tgt);
      [ wxf_with Hc SF_11c50 | reflexivity | exact SD_11c50 | gres; imm_norm; exact Ht ]
    | apply mst_refl ].
  - gres. split; [reflexivity|]. split; [bveq|]. split; [reflexivity|]. size_frame.
Qed.

Lemma size_post_trans : forall R1 R2 R3,
  size_post R1 R2 -> size_post R2 R3 -> size_post R1 R3.
Proof.
  intros R1 R2 R3 [A1 [A2 [A3 [A4 [A5 [A6 A7]]]]]] [B1 [B2 [B3 [B4 [B5 [B6 B7]]]]]].
  unfold size_post. rewrite B1, B2, B3, B4, B5, B6.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  split; [exact A5|]. split; [exact A6|].
  intros x Hx. rewrite B7, A7 by exact Hx. reflexivity.
Qed.

Lemma u_strw : forall h : word,
  bv_unsigned (v_srli (v_addi (v_srli h 8) 7) 3) = ((hdr_size (bv_unsigned h) + 7) / 8)%Z.
Proof.
  intros h. pose proof (hdr_size_range h) as Hs. pose proof (u_srli8 h) as Hn.
  unfold v_srli at 1, v_addi. rewrite Hn.
  rewrite (u_Z2bv (hdr_size (bv_unsigned h) + 7)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2^3)%Z with 8%Z.
  apply u_Z2bv.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Definition size_result (R : bvmap 5 word) m rom (n : Z) : Prop :=
  (n = 2%Z /\ exists Ry,
     msteps source_segs (mkst R (0x11c2a : word) m rom) (mkst Ry (0x11d48 : word) m rom) /\
     getr Ry 15 = Z_to_bv 64 2 /\ size_post R Ry) \/
  ((3 <= n)%Z /\ exists Ry,
     msteps source_segs (mkst R (0x11c2a : word) m rom) (mkst Ry (0x11d2c : word) m rom) /\
     getr Ry 11 = Z_to_bv 64 n /\ size_post R Ry).

(* The size words are at_least_two (1 + w): 2 when w is below 2, otherwise 1 + w. *)
Lemma vector_finish : forall R Rk m rom (w : word) n,
  mem_clear m TL TH ->
  msteps source_segs (mkst R (0x11c2a : word) m rom) (mkst Rk (0x11cda : word) m rom) ->
  size_post R Rk -> getr Rk 9 = w -> (bv_unsigned w < 2^60)%Z ->
  n = at_least_two (1 + bv_unsigned w) ->
  size_result R m rom n.
Proof.
  intros R Rk m rom w n Hc Hm Hp A9 Hb Hn.
  destruct (seg_cda Rk m rom w Hc A9 Hb) as [[Hl (Ry & Hm2 & H15 & Hq)]|[Hg (Ry & Hm2 & H11 & Hq)]].
  - left. split.
    + rewrite Hn. unfold at_least_two.
      destruct (Z.ltb_spec (1 + bv_unsigned w) 2); lia.
    + exists Ry. split; [eapply msteps_trans; eassumption|].
      split; [exact H15|]. eapply size_post_trans; eassumption.
  - right.
    assert (En : n = (1 + bv_unsigned w)%Z).
    { rewrite Hn. unfold at_least_two.
      destruct (Z.ltb_spec (1 + bv_unsigned w) 2); lia. }
    split; [lia|]. exists Ry. split; [eapply msteps_trans; eassumption|].
    split; [rewrite En; exact H11|]. eapply size_post_trans; eassumption.
Qed.

(** THEOREM: the inlined dispatch computes the [obj_words] spec for every valid type. *)
Theorem obj_size : forall R m rom (p h : word),
  mem_clear m TL TH -> getr R 17 = p -> wat m p h -> getr R 15 = Z_to_bv 64 2 ->
  (1 <= hdr_type (bv_unsigned h) <= 11)%Z ->
  size_result R m rom (obj_words_Z (bv_unsigned h)).
Proof.
  intros R m rom p h Hc A17 Hh A15 Ht.
  pose proof (hdr_size_range h) as Hs.
  remember (hdr_type (bv_unsigned h)) as t eqn:Et.
  assert (Hcase : (t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8 \/
                   t = 9 \/ t = 10 \/ t = 11)%Z) by lia.
  unfold obj_words_Z. rewrite <- Et. cbv zeta.
  destruct Hcase as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]; subst t.
  - destruct (obj_disp R m rom p h 1%Z _ (0x11cd6 : word) Hc A17 Hh E ltac:(lia) JTcv_1 ltac:(bveq))
      as (Rz & Hm & A9 & A11 & Az & Hp).
    rewrite E. simpl.
    assert (Hk : exists Rk,
       msteps source_segs (mkst Rz (0x11cd6 : word) m rom) (mkst Rk (0x11cda : word) m rom) /\
       getr Rk 9 = v_srli (v_addi (v_srli h 8) 7) 3 /\ size_post Rz Rk).
    { eexists. split.
      - wsv Hc SF_11cd6 SD_11cd6 (v_addi (v_srli h 8) 7) ltac:(rewrite A9; reflexivity).
        wsv Hc SF_11cd8 SD_11cd8 (v_srli (v_addi (v_srli h 8) 7) 3) ltac:(reflexivity).
        apply mst_refl.
      - gres. split; [reflexivity|size_frame]. }
    destruct Hk as (Rk & Hm2 & B9 & Hq).
    eapply (vector_finish R Rk m rom _ _ Hc); try eassumption.
    + eapply msteps_trans; eassumption.
    + eapply size_post_trans; eassumption.
    + rewrite u_strw. apply Z.div_lt_upper_bound; lia.
    + rewrite u_strw. reflexivity.
  - destruct (obj_disp R m rom p h 2%Z _ (0x11cd6 : word) Hc A17 Hh E ltac:(lia) JTcv_2 ltac:(bveq))
      as (Rz & Hm & A9 & A11 & Az & Hp).
    rewrite E. simpl.
    assert (Hk : exists Rk,
       msteps source_segs (mkst Rz (0x11cd6 : word) m rom) (mkst Rk (0x11cda : word) m rom) /\
       getr Rk 9 = v_srli (v_addi (v_srli h 8) 7) 3 /\ size_post Rz Rk).
    { eexists. split.
      - wsv Hc SF_11cd6 SD_11cd6 (v_addi (v_srli h 8) 7) ltac:(rewrite A9; reflexivity).
        wsv Hc SF_11cd8 SD_11cd8 (v_srli (v_addi (v_srli h 8) 7) 3) ltac:(reflexivity).
        apply mst_refl.
      - gres. split; [reflexivity|size_frame]. }
    destruct Hk as (Rk & Hm2 & B9 & Hq).
    eapply (vector_finish R Rk m rom _ _ Hc); try eassumption.
    + eapply msteps_trans; eassumption.
    + eapply size_post_trans; eassumption.
    + rewrite u_strw. apply Z.div_lt_upper_bound; lia.
    + rewrite u_strw. reflexivity.
  - destruct (obj_disp R m rom p h 3%Z _ (0x11d2c : word) Hc A17 Hh E ltac:(lia) JTcv_3 ltac:(bveq))
      as (Rz & Hm & A9 & A11 & Az & Hp).
    rewrite E. simpl. right. split; [lia|]. exists Rz. split; [exact Hm|]. split; [exact A11|exact Hp].
  - destruct (obj_disp R m rom p h 4%Z _ (0x11d48 : word) Hc A17 Hh E ltac:(lia) JTcv_4 ltac:(bveq))
      as (Rz & Hm & A9 & A11 & Az & Hp).
    rewrite E. simpl. left. split; [reflexivity|]. exists Rz. split; [exact Hm|].
    split; [rewrite Az; exact A15|exact Hp].
  - destruct (obj_disp R m rom p h 5%Z _ (0x11cda : word) Hc A17 Hh E ltac:(lia) JTcv_5 ltac:(bveq))
      as (Rz & Hm & A9 & A11 & Az & Hp).
    rewrite E. simpl.
    eapply (vector_finish R Rz m rom _ _ Hc); try eassumption.
    + rewrite u_srli8. lia.
    + rewrite u_srli8. reflexivity.
  - destruct (obj_disp R m rom p h 6%Z _ (0x11d24 : word) Hc A17 Hh E ltac:(lia) JTcv_6 ltac:(bveq))
      as (Rz & Hm & A9 & A11 & Az & Hp).
    rewrite E. simpl. right. split; [lia|]. eexists. split.
    + eapply msteps_trans; [exact Hm|].
      wsv Hc SF_11d24 SD_11d24 (Z_to_bv 64 (3 + hdr_size (bv_unsigned h))) ltac:(rewrite A9; apply val_closure).
      wj Hc SF_11d28 SD_11d28 (0x11d2c : word).
      apply mst_refl.
    + gres. split; [reflexivity|]. eapply size_post_trans; [exact Hp|size_frame].
  - destruct (obj_disp R m rom p h 7%Z _ (0x11d2a : word) Hc A17 Hh E ltac:(lia) JTcv_7 ltac:(bveq))
      as (Rz & Hm & A9 & A11 & Az & Hp).
    rewrite E. simpl. right. split; [lia|]. eexists. split.
    + eapply msteps_trans; [exact Hm|].
      ws Hc SF_11d2a SD_11d2a.
      apply mst_refl.
    + gres. split; [bveq|]. eapply size_post_trans; [exact Hp|size_frame].
  - destruct (obj_disp R m rom p h 8%Z _ (0x11d20 : word) Hc A17 Hh E ltac:(lia) JTcv_8 ltac:(bveq))
      as (Rz & Hm & A9 & A11 & Az & Hp).
    rewrite E. simpl. right. split; [lia|]. eexists. split.
    + eapply msteps_trans; [exact Hm|].
      ws Hc SF_11d20 SD_11d20.
      wj Hc SF_11d22 SD_11d22 (0x11d2c : word).
      apply mst_refl.
    + gres. split; [bveq|]. eapply size_post_trans; [exact Hp|size_frame].
  - destruct (obj_disp R m rom p h 9%Z _ (0x11c52 : word) Hc A17 Hh E ltac:(lia) JTcv_9 ltac:(bveq))
      as (Rz & Hm & A9 & A11 & Az & Hp).
    rewrite E. simpl. right. split; [lia|]. eexists. split.
    + eapply msteps_trans; [exact Hm|].
      ws Hc SF_11c52 SD_11c52.
      wj Hc SF_11c54 SD_11c54 (0x11d2c : word).
      apply mst_refl.
    + gres. split; [bveq|]. eapply size_post_trans; [exact Hp|size_frame].
  - destruct (obj_disp R m rom p h 10%Z _ (0x11c52 : word) Hc A17 Hh E ltac:(lia) JTcv_10 ltac:(bveq))
      as (Rz & Hm & A9 & A11 & Az & Hp).
    rewrite E. simpl. right. split; [lia|]. eexists. split.
    + eapply msteps_trans; [exact Hm|].
      ws Hc SF_11c52 SD_11c52.
      wj Hc SF_11c54 SD_11c54 (0x11d2c : word).
      apply mst_refl.
    + gres. split; [bveq|]. eapply size_post_trans; [exact Hp|size_frame].
  - destruct (obj_disp R m rom p h 11%Z _ (0x11c52 : word) Hc A17 Hh E ltac:(lia) JTcv_11 ltac:(bveq))
      as (Rz & Hm & A9 & A11 & Az & Hp).
    rewrite E. simpl. right. split; [lia|]. eexists. split.
    + eapply msteps_trans; [exact Hm|].
      ws Hc SF_11c52 SD_11c52.
      wj Hc SF_11c54 SD_11c54 (0x11d2c : word).
      apply mst_refl.
    + gres. split; [bveq|]. eapply size_post_trans; [exact Hp|size_frame].
Qed.

End S.
