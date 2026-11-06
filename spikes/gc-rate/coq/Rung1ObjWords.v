(** * Rung 1: [obj_words] (src/runtime/value.h), 32 instructions at 0x14e00, with a jump
    table in rodata.  No loop, no stores, no calls.

    Contract: for every header word [h], from any state whose overlay misses the
    loaded text and rodata, the function returns to its even return address with
    a0 = the C function's result, changing only a0-a3 and no memory. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec.
From LinuxProcessSemantics.Examples.gc_rate_ns Require Import gc_rate_code GcStep GcTac.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

Open Scope Z_scope.
(** The spec: a transcription of [obj_words] and [hdr_type]/[hdr_size] from value.h. *)
Definition at_least_two (w : Z) : Z := if w <? 2 then 2 else w.
Definition hdr_type (h : Z) : Z := (Z.shiftr h 3) mod 32.
Definition hdr_size (h : Z) : Z := Z.shiftr h 8.
Definition obj_words_Z (h : Z) : Z :=
  let n := hdr_size h in
  let t := hdr_type h in
  if (t =? 1) || (t =? 2) then at_least_two (1 + (n + 7) / 8)
  else if t =? 3 then 4
  else if t =? 4 then 2
  else if t =? 5 then at_least_two (1 + n)
  else if t =? 6 then 3 + n
  else if t =? 7 then 5
  else if t =? 8 then 10
  else if (t =? 9) || (t =? 10) || (t =? 11) then 3
  else 0.

Close Scope Z_scope.

Lemma mod256_div8 : forall u : Z, (0 <= u)%Z -> ((u mod 256) / 8 = (u / 8) mod 32)%Z.
Proof.
  intros u Hu.
  pose proof (Z.mod_pos_bound u 256 ltac:(lia)) as Hr.
  set (r := (u mod 256)%Z) in *.
  assert (Hq : u = ((32 * (u / 256)) * 8 + r)%Z).
  { pose proof (Z_div_mod_eq_full u 256). subst r. lia. }
  assert (Hd : (u / 8 = 32 * (u / 256) + r / 8)%Z).
  { rewrite Hq at 1. rewrite Z.div_add_l by lia. reflexivity. }
  rewrite Hd. rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia.
  rewrite Z.mod_small; [reflexivity|].
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

(** The bit extraction the compiler emits equals [hdr_type]. *)
Lemma hdr_type_bits : forall h : word,
  bv_unsigned (v_srli (v_slli h 56) 59) = hdr_type (bv_unsigned h).
Proof.
  intros h. pose proof (bv_unsigned_in_range _ h) as Hh.
  change (bv_modulus 64) with (2^64)%Z in Hh.
  unfold v_srli, v_slli, hdr_type.
  set (u := bv_unsigned h) in *.
  assert (Hin : bv_unsigned (Z_to_bv 64 (Z.shiftl u 56)) = ((u mod 256) * 2^56)%Z).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (256 * 2^56)%Z.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mul_mod_distr_r by lia. reflexivity. }
  rewrite Hin. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2^59)%Z with (2^56 * 8)%Z. change (2^3)%Z with 8%Z.
  rewrite <- Z.div_div by lia.
  rewrite Z.div_mul by lia.
  rewrite <- mod256_div8 by lia.
  apply u_Z2bv.
  - apply Z.div_pos; [|lia]. apply Z.mod_pos_bound; lia.
  - pose proof (Z.mod_pos_bound u 256 ltac:(lia)).
    apply Z.div_lt_upper_bound; lia.
Qed.

Lemma hdr_type_range : forall u, (0 <= u)%Z -> (0 <= hdr_type u < 32)%Z.
Proof. intros. unfold hdr_type. apply Z.mod_pos_bound. lia. Qed.

Lemma hdr_size_range : forall h : word,
  (0 <= hdr_size (bv_unsigned h) < 2^56)%Z.
Proof.
  intros h. pose proof (bv_unsigned_in_range _ h) as Hh.
  change (bv_modulus 64) with (2^64)%Z in Hh.
  unfold hdr_size. rewrite Z.shiftr_div_pow2 by lia. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma u_srli8 : forall h : word,
  bv_unsigned (v_srli h 8) = hdr_size (bv_unsigned h).
Proof.
  intros h. pose proof (hdr_size_range h). unfold v_srli, hdr_size in *. apply u_Z2bv; lia.
Qed.

(** The arithmetic of the variable-size cases. *)
Lemma seqz_add_one : forall (a : word), (bv_unsigned a < 2^60)%Z ->
  v_addi (v_add (v_sltiu a 1) a) 1 = Z_to_bv 64 (at_least_two (1 + bv_unsigned a)).
Proof.
  intros a Ha. pose proof (bv_unsigned_in_range _ a) as Hr.
  change (bv_modulus 64) with (2^64)%Z in Hr.
  unfold v_sltiu, at_least_two.
  change (bv_wrap 64 1) with 1%Z.
  destruct (Z.ltb_spec (bv_unsigned a) 1).
  - assert (Hz : bv_unsigned a = 0%Z) by lia. rewrite Hz.
    apply bv_eq. unfold v_addi, v_add. rewrite Hz. vm_compute. reflexivity.
  - assert (Hf : (1 + bv_unsigned a <? 2)%Z = false) by (apply Z.ltb_ge; lia). rewrite Hf.
    unfold v_addi, v_add.
    rewrite (u_Z2bv 0) by lia. rewrite (u_Z2bv (0 + bv_unsigned a)) by lia. f_equal; lia.
Qed.

Open Scope Z_scope.
Lemma val_string : forall h : word,
  v_addi (v_add (v_sltiu (v_srli (v_addi (v_srli h 8) 7) 3) 1) (v_srli (v_addi (v_srli h 8) 7) 3)) 1
  = Z_to_bv 64 (at_least_two (1 + (hdr_size (bv_unsigned h) + 7) / 8)).
Proof.
  intros h. pose proof (hdr_size_range h) as Hs. pose proof (u_srli8 h) as Hn.
  assert (Ha : bv_unsigned (v_srli (v_addi (v_srli h 8) 7) 3) = (hdr_size (bv_unsigned h) + 7) / 8).
  { unfold v_srli at 1, v_addi. rewrite Hn.
    rewrite (u_Z2bv (hdr_size (bv_unsigned h) + 7)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    apply u_Z2bv.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia. }
  rewrite seqz_add_one; rewrite Ha; [reflexivity|].
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma val_vector : forall h : word,
  v_addi (v_add (v_sltiu (v_srli h 8) 1) (v_srli h 8)) 1
  = Z_to_bv 64 (at_least_two (1 + hdr_size (bv_unsigned h))).
Proof.
  intros h. pose proof (hdr_size_range h) as Hs. pose proof (u_srli8 h) as Hn.
  rewrite seqz_add_one; rewrite Hn; [reflexivity|]. lia.
Qed.

Lemma val_closure : forall h : word,
  v_addi (v_srli h 8) 3 = Z_to_bv 64 (3 + hdr_size (bv_unsigned h)).
Proof.
  intros h. unfold v_addi. rewrite u_srli8. f_equal. lia.
Qed.

Lemma ltu_big : forall t : Z, (12 <= t < 32)%Z ->
  branch_taken BC_LTU (v_addi (Z_to_bv 64 0) 10) (Z_to_bv 64 (t - 1)) = true.
Proof.
  intros t Ht. cbn [branch_taken]. unfold bv_ltu.
  assert (H10 : bv_unsigned (v_addi (Z_to_bv 64 0) 10) = 10) by (vm_compute; reflexivity).
  rewrite H10, u_Z2bv by lia. apply Z.ltb_lt. lia.
Qed.

Close Scope Z_scope.

Section Contract.
Context {fx : FPState}.

Definition ow_kept (x : reg) : Prop := x <> 10 /\ x <> 11 /\ x <> 12 /\ x <> 13.

Ltac ow_frame :=
  let x := fresh "x" in let a := fresh in let b := fresh in let c := fresh in let d := fresh in
  intros x (a & b & c & d);
  repeat (rewrite getr_other by assumption); reflexivity.

Ltac ow_prefix Hc H10 Hv k E :=
  norm_pc;
  ws Hc SF_14e00 SD_14e00;
  ws Hc SF_14e04 SD_14e04;
  wsv Hc SF_14e06 SD_14e06 (Z_to_bv 64 (k - 1)) ltac:(rewrite H10, Hv; first [reflexivity | rewrite E; reflexivity]);
  ws Hc SF_14e08 SD_14e08.

Ltac ow_dispatch Hc JT tgt :=
  wbr_ft Hc SF_14e0a SD_14e0a ltac:(vm_compute; reflexivity);
  ws Hc SF_14e0e SD_14e0e;
  ws Hc SF_14e10 SD_14e10;
  ws Hc SF_14e14 SD_14e14;
  ws Hc SF_14e18 SD_14e18;
  wlw_ro Hc SF_14e1a SD_14e1a JT;
  ws Hc SF_14e1c SD_14e1c;
  ws Hc SF_14e20 SD_14e20;
  ws Hc SF_14e22 SD_14e22;
  wjr Hc SF_14e24 SD_14e24 tgt.

Theorem obj_words_contract :
  forall regs mem rom (h r : word),
    mem_clear mem TL TH ->
    getr regs 10 = h ->
    getr regs 1 = r ->
    (bv_unsigned r mod 2 = 0)%Z ->
    exists regs',
      msteps source_segs (mkst regs (Z_to_bv 64 0x14e00) mem rom) (mkst regs' r mem rom) /\
      getr regs' 10 = Z_to_bv 64 (obj_words_Z (bv_unsigned h)) /\
      (forall x : reg, ow_kept x -> getr regs' x = getr regs x).
Proof.
  intros regs mem rom h r Hc H10 Hra Hev.
  pose proof (hdr_type_bits h) as Hbits.
  pose proof (bv_unsigned_in_range _ h) as Hh.
  change (bv_modulus 64) with (2^64)%Z in Hh.
  pose proof (hdr_type_range (bv_unsigned h) ltac:(lia)) as Htr.
  pose proof (hdr_size_range h) as Hsr.
  pose proof (u_srli8 h) as Hn.
  remember (hdr_type (bv_unsigned h)) as t eqn:Ht.
  assert (Hv1 : v_addi (v_srli (v_slli h 56) 59) (-1) = Z_to_bv 64 (t - 1)).
  { unfold v_addi. rewrite Hbits. reflexivity. }
  assert (Hcase : (t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8 \/
                   t = 9 \/ t = 10 \/ t = 11 \/ t = 0 \/ 12 <= t)%Z) by lia.
  unfold obj_words_Z. rewrite <- Ht.
  set (n := hdr_size (bv_unsigned h)) in *.
  destruct Hcase as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]];
    try subst t.
  - eexists. split.
    + ow_prefix Hc H10 Hv1 1%Z E.
      ow_dispatch Hc JTow_1 (Z_to_bv 64 0x14e2a).
      ws Hc SF_14e2a SD_14e2a.
      ws Hc SF_14e2c SD_14e2c.
      ws Hc SF_14e2e SD_14e2e.
      ws Hc SF_14e32 SD_14e32.
      ws Hc SF_14e34 SD_14e34.
      wret Hc SF_14e36 SD_14e36 Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres. rewrite E, H10. simpl. exact (val_string h).
  - eexists. split.
    + ow_prefix Hc H10 Hv1 2%Z E.
      ow_dispatch Hc JTow_2 (Z_to_bv 64 0x14e2a).
      ws Hc SF_14e2a SD_14e2a.
      ws Hc SF_14e2c SD_14e2c.
      ws Hc SF_14e2e SD_14e2e.
      ws Hc SF_14e32 SD_14e32.
      ws Hc SF_14e34 SD_14e34.
      wret Hc SF_14e36 SD_14e36 Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres. rewrite E, H10. simpl. exact (val_string h).
  - eexists. split.
    + ow_prefix Hc H10 Hv1 3%Z E.
      ow_dispatch Hc JTow_3 (Z_to_bv 64 0x14e4c).
      wret Hc SF_14e4c SD_14e4c Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres. rewrite E. simpl. bveq.
  - eexists. split.
    + ow_prefix Hc H10 Hv1 4%Z E.
      ow_dispatch Hc JTow_4 (Z_to_bv 64 0x14e38).
      ws Hc SF_14e38 SD_14e38.
      wret Hc SF_14e3a SD_14e3a Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres. rewrite E. simpl. bveq.
  - eexists. split.
    + ow_prefix Hc H10 Hv1 5%Z E.
      ow_dispatch Hc JTow_5 (Z_to_bv 64 0x14e2e).
      ws Hc SF_14e2e SD_14e2e.
      ws Hc SF_14e32 SD_14e32.
      ws Hc SF_14e34 SD_14e34.
      wret Hc SF_14e36 SD_14e36 Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres. rewrite E, H10. simpl. exact (val_vector h).
  - eexists. split.
    + ow_prefix Hc H10 Hv1 6%Z E.
      ow_dispatch Hc JTow_6 (Z_to_bv 64 0x14e40).
      ws Hc SF_14e40 SD_14e40.
      wret Hc SF_14e44 SD_14e44 Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres. rewrite E, H10. simpl. exact (val_closure h).
  - eexists. split.
    + ow_prefix Hc H10 Hv1 7%Z E.
      ow_dispatch Hc JTow_7 (Z_to_bv 64 0x14e46).
      ws Hc SF_14e46 SD_14e46.
      wret Hc SF_14e48 SD_14e48 Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres. rewrite E. simpl. bveq.
  - eexists. split.
    + ow_prefix Hc H10 Hv1 8%Z E.
      ow_dispatch Hc JTow_8 (Z_to_bv 64 0x14e3c).
      ws Hc SF_14e3c SD_14e3c.
      wret Hc SF_14e3e SD_14e3e Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres. rewrite E. simpl. bveq.
  - eexists. split.
    + ow_prefix Hc H10 Hv1 9%Z E.
      ow_dispatch Hc JTow_9 (Z_to_bv 64 0x14e26).
      ws Hc SF_14e26 SD_14e26.
      wret Hc SF_14e28 SD_14e28 Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres. rewrite E. simpl. bveq.
  - eexists. split.
    + ow_prefix Hc H10 Hv1 10%Z E.
      ow_dispatch Hc JTow_10 (Z_to_bv 64 0x14e26).
      ws Hc SF_14e26 SD_14e26.
      wret Hc SF_14e28 SD_14e28 Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres. rewrite E. simpl. bveq.
  - eexists. split.
    + ow_prefix Hc H10 Hv1 11%Z E.
      ow_dispatch Hc JTow_11 (Z_to_bv 64 0x14e26).
      ws Hc SF_14e26 SD_14e26.
      wret Hc SF_14e28 SD_14e28 Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres. rewrite E. simpl. bveq.
  - eexists. split.
    + ow_prefix Hc H10 Hv1 0%Z E.
      wbr_tk Hc SF_14e0a SD_14e0a ltac:(vm_compute; reflexivity).
      ws Hc SF_14e4a SD_14e4a.
      wret Hc SF_14e4c SD_14e4c Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres. rewrite E. simpl. bveq.
  - eexists. split.
    + ow_prefix Hc H10 Hv1 (hdr_type (bv_unsigned h)) E.
      wbr_tk Hc SF_14e0a SD_14e0a ltac:(apply ltu_big; lia).
      ws Hc SF_14e4a SD_14e4a.
      wret Hc SF_14e4c SD_14e4c Hra Hev. apply mst_refl.
    + split; [| ow_frame].
      gres.
      repeat (rewrite (proj2 (Z.eqb_neq (hdr_type (bv_unsigned h)) _)) by lia).
      simpl. bveq.
Qed.

End Contract.
