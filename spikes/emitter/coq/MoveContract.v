(** * Route B: the contract of [spike_check_move], on its compiled bytes.

    For every operand and every memory: the function returns to [ra] with a0 = 0, 1 or 2,
    keeping the registers the ABI keeps and all memory.  If a0 = 1, the operands are in the
    domain and the halves in [at, end) are exactly a template of this move. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec.
From LinuxProcessSemantics.Examples.emitter_ns Require Import emitter_code GcStep MoveStep GcTac MoveTemplate MoveCompare.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(** Finite checks, by comparing numbers. *)
Lemma enum1 : forall (f : Z -> word) (g : Z -> Z) (n : nat),
  forallb (fun i => Z.eqb (bv_unsigned (f (Z.of_nat i))) (bv_unsigned (W (g (Z.of_nat i))))) (seq 0 n) = true ->
  forall z, 0 <= z < Z.of_nat n -> f z = W (g z).
Proof.
  intros f g n H z Hz. apply bv_eq.
  rewrite forallb_forall in H.
  specialize (H (Z.to_nat z) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. apply Z.eqb_eq. exact H.
Qed.

Lemma enum2 : forall (f : Z -> Z -> word) (g : Z -> Z -> Z) (n m : nat),
  forallb (fun i => forallb (fun j =>
     Z.eqb (bv_unsigned (f (Z.of_nat i) (Z.of_nat j))) (bv_unsigned (W (g (Z.of_nat i) (Z.of_nat j)))))
     (seq 0 m)) (seq 0 n) = true ->
  forall y z, 0 <= y < Z.of_nat n -> 0 <= z < Z.of_nat m -> f y z = W (g y z).
Proof.
  intros f g n m H y z Hy Hz. apply bv_eq.
  rewrite forallb_forall in H.
  specialize (H (Z.to_nat y) ltac:(apply in_seq; lia)).
  rewrite forallb_forall in H.
  specialize (H (Z.to_nat z) ltac:(apply in_seq; lia)).
  rewrite !Z2Nat.id in H by lia. apply Z.eqb_eq. exact H.
Qed.

Lemma enumb : forall (P : Z -> bool) (n : nat),
  forallb (fun i => P (Z.of_nat i)) (seq 0 n) = true -> forall z, 0 <= z < Z.of_nat n -> P z = true.
Proof.
  intros P n H z Hz. rewrite forallb_forall in H.
  specialize (H (Z.to_nat z) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia. exact H.
Qed.

Ltac en1 d n :=
  match goal with
  | |- ?T = Z_to_bv 64 ?G =>
    let T' := eval pattern d in T in let G' := eval pattern d in G in
    match T' with ?f _ => match G' with ?g _ =>
      refine (enum1 f g n _ d _); [vm_compute; reflexivity | lia]
    end end
  end.

Ltac en2 d s n m :=
  match goal with
  | |- ?T = Z_to_bv 64 ?G =>
    let T' := eval pattern d, s in T in let G' := eval pattern d, s in G in
    match T' with ?f _ _ => match G' with ?g _ _ =>
      refine (enum2 f g n m _ d s _ _); [vm_compute; reflexivity | lia | lia]
    end end
  end.

Lemma lor_ge : forall a b, 0 <= a -> 0 <= b -> a <= Z.lor a b /\ b <= Z.lor a b.
Proof.
  assert (L : forall a b, 0 <= a -> 0 <= b -> a <= Z.lor a b).
  { intros a b Ha Hb.
    assert (E : Z.lor a b = a + Z.ldiff b a).
    { rewrite Z.add_nocarry_lxor.
      - apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.lxor_spec, Z.ldiff_spec.
        destruct (Z.testbit a i), (Z.testbit b i); reflexivity.
      - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0.
        destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
    rewrite E. pose proof (Z.ldiff_nonneg b a) as Hn.
    assert (0 <= Z.ldiff b a) by (apply Hn; left; exact Hb). lia. }
  intros a b Ha Hb. split; [apply L; assumption | rewrite Z.lor_comm; apply L; assumption].
Qed.

Lemma lor_lt : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> Z.lor a b < 2^64.
Proof.
  intros a b Ha Hb.
  destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lor_0_r; lia|].
  apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma take1 : forall x, 0 <= x < 65536 -> take 1 x = [x].
Proof. intros x Hx. unfold take. cbn. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma take2 : forall x, 0 <= x < 2^32 -> take 2 x = split32 x.
Proof.
  intros x Hx. unfold take, split32. cbn. f_equal. f_equal.
  apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma c_ld_small : forall s, 0 <= s < 32 -> 0 <= c_ld_a0 (8 * s) < 65536.
Proof.
  intros s Hs.
  pose proof (enumb (fun s => (0 <=? c_ld_a0 (8 * s)) && (c_ld_a0 (8 * s) <? 65536)) 32 ltac:(vm_compute; reflexivity) s ltac:(lia)) as H.
  apply andb_prop in H. destruct H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
Qed.
Lemma c_sd_small : forall s, 0 <= s < 32 -> 0 <= c_sd_a0 (8 * s) < 65536.
Proof.
  intros s Hs.
  pose proof (enumb (fun s => (0 <=? c_sd_a0 (8 * s)) && (c_sd_a0 (8 * s) <? 65536)) 32 ltac:(vm_compute; reflexivity) s ltac:(lia)) as H.
  apply andb_prop in H. destruct H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
Qed.
Lemma sd_small : forall s, 0 <= s < 256 -> 0 <= sd_a0 (8 * s) < 2^32.
Proof.
  intros s Hs.
  pose proof (enumb (fun s => (0 <=? sd_a0 (8 * s)) && (sd_a0 (8 * s) <? 2^32)) 256 ltac:(vm_compute; reflexivity) s ltac:(lia)) as H.
  apply andb_prop in H. destruct H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
Qed.
Lemma ld_small : forall rd s, 0 <= rd < 32 -> 0 <= s < 256 -> 0 <= ld_s0 rd (8 * s) < 2^32.
Proof. intros rd s Hr Hs. unfold ld_s0. lia. Qed.

Section Contract.
Context {fx : FPState}.
Variables (mem rom : word -> option byte) (r : word) (K : bvmap 5 word).
Hypothesis Hc : mem_clear mem TL TH.
Hypothesis Hev : (bv_unsigned r mod 2 = 0)%Z.

Ltac okx H := let x := fresh "x" in let Hx := fresh in let Hy := fresh in
  intros x Hx; pose proof Hx as Hy;
  destruct Hy as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);
  repeat (rewrite getr_other by assumption); apply H; exact Hx.

(** The store half, at 0x36c0a (compressed) and 0x36c42 (full), given the source half. *)
Lemma store_small : forall regs a e n w d k Q,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 10 = W a -> getr regs 11 = W e -> getr regs 5 = W n -> getr regs 7 = W w ->
  getr regs 12 = W d -> getr regs 16 = W k ->
  0 <= a <= e -> e + 32 < 2^64 -> (n = 1 \/ n = 2) -> 0 <= w < 2^64 -> 0 <= d < 32 -> (k = 0 \/ k = 1) ->
  (forall i, 0 <= i -> a + 2 * i + 2 <= e -> exists v, 0 <= v < 65536 /\ half_at mem (a + 2 * i) v) ->
  (e = a + 2 * (n + 1 + k) -> emit_at mem a (take n w ++ [c_sd_a0 (8 * d)] ++ ktail k) -> Q) ->
  (k = 1 -> e = a + 2 * (n + 1) -> emit_at mem a (take n w ++ take 0 (c_sd_a0 (8 * d)) ++ ktail 1) -> Q) ->
  Run source_segs r mem rom (Result K Q) (mkst regs (0x36c0a%bv : word) mem rom).
Proof.
  intros regs a e n w d k Q Hra Hk H10 H11 H5 H7 H12 H16 Hae He Hn Hw Hd Hkk Rd Q1 Q2.
  norm_pc_run.
  ws Hc SF_36c0a SD_36c0a.
  ws Hc SF_36c0e SD_36c0e.
  ws Hc SF_36c10 SD_36c10.
  ws Hc SF_36c14 SD_36c14.
  ws Hc SF_36c16 SD_36c16.
  ws Hc SF_36c18 SD_36c18.
  ws Hc SF_36c1a SD_36c1a.
  ws Hc SF_36c1c SD_36c1c.
  wj Hc SF_36c1e SD_36c1e (0x36c60%bv : word).
  pose proof (c_sd_small d Hd) as Hb.
  apply (len_main mem rom r K Hc Hev _ a e n 1 w (c_sd_a0 (8 * d)) k).
  - gres. exact Hra.
  - okx Hk.
  - gres. exact H10.
  - gres. exact H11.
  - gres. exact H5.
  - gres. reflexivity.
  - gres. exact H7.
  - gres. rewrite H12. en1 d 32%nat.
  - gres. exact H16.
  - exact Hae.
  - exact He.
  - exact Hn.
  - left; reflexivity.
  - exact Hw.
  - lia.
  - exact Hkk.
  - exact Rd.
  - intro E. rewrite (take1 _ Hb). exact (Q1 E).
  - exact Q2.
Qed.

Lemma store_full : forall regs a e n w d k Q,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 10 = W a -> getr regs 11 = W e -> getr regs 5 = W n -> getr regs 7 = W w ->
  getr regs 12 = W d -> getr regs 16 = W k ->
  0 <= a <= e -> e + 32 < 2^64 -> (n = 1 \/ n = 2) -> 0 <= w < 2^64 -> 32 <= d < 256 -> (k = 0 \/ k = 1) ->
  (forall i, 0 <= i -> a + 2 * i + 2 <= e -> exists v, 0 <= v < 65536 /\ half_at mem (a + 2 * i) v) ->
  (e = a + 2 * (n + 2 + k) -> emit_at mem a (take n w ++ split32 (sd_a0 (8 * d)) ++ ktail k) -> Q) ->
  (k = 1 -> e = a + 2 * (n + 1) -> emit_at mem a (take n w ++ take 0 (sd_a0 (8 * d)) ++ ktail 1) -> Q) ->
  Run source_segs r mem rom (Result K Q) (mkst regs (0x36c42%bv : word) mem rom).
Proof.
  intros regs a e n w d k Q Hra Hk H10 H11 H5 H7 H12 H16 Hae He Hn Hw Hd Hkk Rd Q1 Q2.
  norm_pc_run.
  ws Hc SF_36c42 SD_36c42.
  ws Hc SF_36c46 SD_36c46.
  ws Hc SF_36c4a SD_36c4a.
  ws Hc SF_36c4c SD_36c4c.
  ws Hc SF_36c4e SD_36c4e.
  ws Hc SF_36c50 SD_36c50.
  ws Hc SF_36c52 SD_36c52.
  ws Hc SF_36c56 SD_36c56.
  ws Hc SF_36c5a SD_36c5a.
  ws Hc SF_36c5c SD_36c5c.
  ws Hc SF_36c5e SD_36c5e.
  pose proof (sd_small d ltac:(lia)) as Hb.
  apply (len_main mem rom r K Hc Hev _ a e n 2 w (sd_a0 (8 * d)) k).
  - gres. exact Hra.
  - okx Hk.
  - gres. exact H10.
  - gres. exact H11.
  - gres. exact H5.
  - gres. reflexivity.
  - gres. exact H7.
  - gres. rewrite H12. en1 d 256%nat.
  - gres. exact H16.
  - exact Hae.
  - exact He.
  - exact Hn.
  - right; reflexivity.
  - exact Hw.
  - lia.
  - exact Hkk.
  - exact Rd.
  - intro E. rewrite (take2 _ Hb). exact (Q1 E).
  - exact Q2.
Qed.

Ltac wv F D v := wsv Hc F D (W v) ltac:(vm_compute; reflexivity).

Variables (a e d s h c k : Z).
Hypothesis Hae : 0 <= a <= e.
Hypothesis He : e + 32 < 2^64.
Hypothesis Hrd : forall i, 0 <= i -> a + 2 * i + 2 <= e ->
  exists v, 0 <= v < 65536 /\ half_at mem (a + 2 * i) v.

Definition Accepted : Prop :=
  in_domain h c d s k /\
  exists store : bool, (store = false -> k = 1) /\
    e = a + 2 * Z.of_nat (length (move_template h c d s k store)) /\
    emit_at mem a (move_template h c d s k store).

Lemma home_t : forall hh n, 2 <= n < hh + 2 -> is_home hh n = true.
Proof. intros hh n H. unfold is_home. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma home_f : forall hh n, n < 2 \/ hh + 2 <= n -> is_home hh n = false.
Proof.
  intros hh n H. unfold is_home. apply andb_false_iff.
  destruct H; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Qed.

Lemma len_take : forall n w, (n = 1 \/ n = 2) -> Z.of_nat (length (take n w)) = n.
Proof. intros n w [-> | ->]; reflexivity. Qed.
Lemma len_ktail : (k = 0 \/ k = 1) -> Z.of_nat (length (ktail k)) = k.
Proof. intros [-> | ->]; reflexivity. Qed.

Lemma acc_true : forall n w ST,
  in_domain h c d s k -> is_home h d = false -> take n w = src_template h c s -> (n = 1 \/ n = 2) ->
  ST = store_template d -> e = a + 2 * (n + Z.of_nat (length ST) + k) ->
  emit_at mem a (take n w ++ ST ++ ktail k) -> Accepted.
Proof.
  intros n w ST Hdom Hhome Ht Hn HST Ee Hem. split; [exact Hdom|]. exists true.
  unfold move_template. rewrite Hhome, <- Ht, <- HST. split; [discriminate|].
  fold (ktail k). split; [|exact Hem].
  destruct Hdom as (_ & _ & _ & Hk & _).
  rewrite !length_app, !Nat2Z.inj_add, len_take by exact Hn. rewrite len_ktail by exact Hk. lia.
Qed.

Lemma acc_false : forall n w x,
  in_domain h c d s k -> is_home h d = false -> take n w = src_template h c s -> (n = 1 \/ n = 2) ->
  k = 1 -> e = a + 2 * (n + 1) ->
  emit_at mem a (take n w ++ take 0 x ++ ktail 1) -> Accepted.
Proof.
  intros n w x Hdom Hhome Ht Hn Hk Ee Hem. split; [exact Hdom|]. exists false.
  unfold move_template. rewrite Hhome, <- Ht. split; [intros _; exact Hk|]. rewrite Hk.
  cbn [app] in *. change (take 0 x) with (@nil Z) in Hem. cbn [app] in Hem.
  split; [|exact Hem].
  rewrite length_app, Nat2Z.inj_add, len_take by exact Hn. cbn. lia.
Qed.

Lemma st_small : 0 <= d < 32 -> [c_sd_a0 (8 * d)] = store_template d.
Proof. intro. unfold store_template. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. Qed.
Lemma st_full : 32 <= d -> split32 (sd_a0 (8 * d)) = store_template d.
Proof. intro. unfold store_template. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. Qed.

Lemma src_cached : (0 <= d <= 255 /\ s = c) -> src_template h c s = [c_mv 10 18].
Proof. intros [_ ->]. unfold src_template. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma src_home : s <> c -> 2 <= s < h + 2 -> src_template h c s = [c_mv 10 (18 + s)].
Proof. intros. unfold src_template. rewrite (proj2 (Z.eqb_neq _ _)) by assumption. rewrite home_t by lia. reflexivity. Qed.
Lemma src_short : s <> c -> (s < 2 \/ h + 2 <= s) -> s <= 31 -> src_template h c s = [c_ld_a0 (8 * s)].
Proof.
  intros. unfold src_template. rewrite (proj2 (Z.eqb_neq _ _)) by assumption. rewrite home_f by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.
Lemma src_long : s <> c -> (s < 2 \/ h + 2 <= s) -> 32 <= s -> src_template h c s = split32 (ld_s0 10 (8 * s)).
Proof.
  intros. unfold src_template. rewrite (proj2 (Z.eqb_neq _ _)) by assumption. rewrite home_f by lia.
  rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
Qed.

(** From 0x36c7c: a source in the frame. *)
Lemma r0_frame : forall regs,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 10 = W a -> getr regs 11 = W e -> getr regs 12 = W d -> getr regs 13 = W s ->
  getr regs 16 = W k -> getr regs 17 = W (s * 8388608) -> getr regs 5 = W 1 ->
  in_domain h c d s k -> is_home h d = false -> s <> c -> (s < 2 \/ h + 2 <= s) ->
  Run source_segs r mem rom (Result K Accepted) (mkst regs (0x36c7c%bv : word) mem rom).
Proof.
  intros regs Hra Hk H10 H11 H12 H13 H16 H17 H5 Hdom Hhome Hne Hnh.
  pose proof Hdom as (Hd & Hs & Hh & Hkk & _).
  norm_pc_run.
  wv SF_36c7c SD_36c7c 31.
  destruct (Z.le_gt_cases s 31) as [Sm|Lg].
  - wbr_ft Hc SF_36c7e SD_36c7e ltac:(apply br_ltu_f; rewrite H13; rewrite !U by lia; lia).
    ws Hc SF_36c82 SD_36c82.
    ws Hc SF_36c86 SD_36c86.
    ws Hc SF_36c88 SD_36c88.
    ws Hc SF_36c8c SD_36c8c.
    ws Hc SF_36c8e SD_36c8e.
    ws Hc SF_36c90 SD_36c90.
    ws Hc SF_36c92 SD_36c92.
    wv SF_36c96 SD_36c96 31.
    assert (Hv : 0 <= c_ld_a0 (8 * s) < 65536) by (apply c_ld_small; lia).
    assert (Ht : take 1 (c_ld_a0 (8 * s)) = src_template h c s).
    { rewrite take1 by exact Hv. symmetry. apply src_short; lia. }
    destruct (Z.le_gt_cases d 31) as [Ds|Dl].
    + wbr_tk Hc SF_36c98 SD_36c98 ltac:(apply br_geu_t; rewrite H12; rewrite !U by lia; lia).
      unfold btgt; imm_norm.
      eapply (store_small _ a e 1 (c_ld_a0 (8 * s)) d k).
      * gres. exact Hra.
      * okx Hk.
      * gres. exact H10.
      * gres. exact H11.
      * gres. exact H5.
      * gres. rewrite H13. en1 s 32%nat.
      * gres. exact H12.
      * gres. exact H16.
      * exact Hae.
      * exact He.
      * left; reflexivity.
      * lia.
      * lia.
      * exact Hkk.
      * exact Hrd.
      * intros E Hem. apply (acc_true 1 (c_ld_a0 (8 * s)) [c_sd_a0 (8 * d)]); try assumption.
        -- left; reflexivity.
        -- apply st_small; lia.
      * intros K1 E Hem. eapply (acc_false 1 (c_ld_a0 (8 * s))); try eassumption. left; reflexivity.
    + wbr_ft Hc SF_36c98 SD_36c98 ltac:(apply br_geu_f; rewrite H12; rewrite !U by lia; lia).
      wj Hc SF_36c9c SD_36c9c (0x36c42%bv : word).
      eapply (store_full _ a e 1 (c_ld_a0 (8 * s)) d k).
      * gres. exact Hra.
      * okx Hk.
      * gres. exact H10.
      * gres. exact H11.
      * gres. exact H5.
      * gres. rewrite H13. en1 s 32%nat.
      * gres. exact H12.
      * gres. exact H16.
      * exact Hae.
      * exact He.
      * left; reflexivity.
      * lia.
      * lia.
      * exact Hkk.
      * exact Hrd.
      * intros E Hem. apply (acc_true 1 (c_ld_a0 (8 * s)) (split32 (sd_a0 (8 * d)))); try assumption.
        -- left; reflexivity.
        -- apply st_full; lia.
      * intros K1 E Hem. eapply (acc_false 1 (c_ld_a0 (8 * s))); try eassumption. left; reflexivity.
  - wbr_tk Hc SF_36c7e SD_36c7e ltac:(apply br_ltu_t; rewrite H13; rewrite !U by lia; lia).
    unfold btgt; imm_norm.
    ws Hc SF_36c9e SD_36c9e.
    ws Hc SF_36ca2 SD_36ca2.
    ws Hc SF_36ca4 SD_36ca4.
    ws Hc SF_36ca6 SD_36ca6.
    wv SF_36caa SD_36caa 2.
    wv SF_36cac SD_36cac 31.
    assert (Hv : 0 <= ld_s0 10 (8 * s) < 2^32) by (apply ld_small; lia).
    assert (Ht : take 2 (ld_s0 10 (8 * s)) = src_template h c s).
    { rewrite take2 by exact Hv. symmetry. apply src_long; lia. }
    destruct (Z.le_gt_cases d 31) as [Ds|Dl].
    + wbr_ft Hc SF_36cae SD_36cae ltac:(apply br_ltu_f; rewrite H12; rewrite !U by lia; lia).
      wj Hc SF_36cb2 SD_36cb2 (0x36c0a%bv : word).
      eapply (store_small _ a e 2 (ld_s0 10 (8 * s)) d k).
      * gres. exact Hra.
      * okx Hk.
      * gres. exact H10.
      * gres. exact H11.
      * gres. reflexivity.
      * gres. rewrite H17. en1 s 256%nat.
      * gres. exact H12.
      * gres. exact H16.
      * exact Hae.
      * exact He.
      * right; reflexivity.
      * lia.
      * lia.
      * exact Hkk.
      * exact Hrd.
      * intros E Hem. apply (acc_true 2 (ld_s0 10 (8 * s)) [c_sd_a0 (8 * d)]); try assumption.
        -- right; reflexivity.
        -- apply st_small; lia.
      * intros K1 E Hem. eapply (acc_false 2 (ld_s0 10 (8 * s))); try eassumption. right; reflexivity.
    + wbr_tk Hc SF_36cae SD_36cae ltac:(apply br_ltu_t; rewrite H12; rewrite !U by lia; lia).
      unfold btgt; imm_norm.
      eapply (store_full _ a e 2 (ld_s0 10 (8 * s)) d k).
      * gres. exact Hra.
      * okx Hk.
      * gres. exact H10.
      * gres. exact H11.
      * gres. reflexivity.
      * gres. rewrite H17. en1 s 256%nat.
      * gres. exact H12.
      * gres. exact H16.
      * exact Hae.
      * exact He.
      * right; reflexivity.
      * lia.
      * lia.
      * exact Hkk.
      * exact Hrd.
      * intros E Hem. apply (acc_true 2 (ld_s0 10 (8 * s)) (split32 (sd_a0 (8 * d)))); try assumption.
        -- right; reflexivity.
        -- apply st_full; lia.
      * intros K1 E Hem. eapply (acc_false 2 (ld_s0 10 (8 * s))); try eassumption. right; reflexivity.
Qed.

Ltac cv := apply bv_eq; vm_compute; reflexivity.

Lemma r0 : forall regs,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 10 = W a -> getr regs 11 = W e -> getr regs 12 = W d -> getr regs 13 = W s ->
  getr regs 14 = W h -> getr regs 15 = W c ->
  getr regs 16 = W k -> getr regs 17 = W (s * 8388608) -> 0 <= c < 2^64 ->
  in_domain h c d s k -> is_home h d = false ->
  Run source_segs r mem rom (Result K Accepted) (mkst regs (0x36bf8%bv : word) mem rom).
Proof.
  intros regs Hra Hk H10 H11 H12 H13 H14 H15 H16 H17 Hcr Hdom Hhome.
  pose proof Hdom as (Hd & Hs & Hh & Hkk & _).
  norm_pc_run.
  wv SF_36bf8 SD_36bf8 1.
  destruct (Z.eq_dec s c) as [Eq|Ne].
  - wbr_ft Hc SF_36bfa SD_36bfa ltac:(apply br_ne_f; rewrite H13, H15; rewrite !U by lia; exact Eq).
    ws Hc SF_36bfe SD_36bfe.
    ws Hc SF_36c00 SD_36c00.
    wv SF_36c04 SD_36c04 31.
    assert (Ht : take 1 (c_mv 10 18) = src_template h c s).
    { rewrite take1 by (unfold c_mv; lia). symmetry. apply src_cached; split; [lia | exact Eq]. }
    destruct (Z.le_gt_cases d 31) as [Ds|Dl].
    + wbr_ft Hc SF_36c06 SD_36c06 ltac:(apply br_ltu_f; rewrite H12; rewrite !U by lia; lia).
      eapply (store_small _ a e 1 (c_mv 10 18) d k).
      * gres. exact Hra.
      * okx Hk.
      * gres. exact H10.
      * gres. exact H11.
      * gres. reflexivity.
      * gres. cv.
      * gres. exact H12.
      * gres. exact H16.
      * exact Hae.
      * exact He.
      * left; reflexivity.
      * unfold c_mv; lia.
      * lia.
      * exact Hkk.
      * exact Hrd.
      * intros E Hem. apply (acc_true 1 (c_mv 10 18) [c_sd_a0 (8 * d)]); try assumption.
        -- left; reflexivity.
        -- apply st_small; lia.
      * intros K1 E Hem. eapply (acc_false 1 (c_mv 10 18)); try eassumption. left; reflexivity.
    + wbr_tk Hc SF_36c06 SD_36c06 ltac:(apply br_ltu_t; rewrite H12; rewrite !U by lia; lia).
      unfold btgt; imm_norm.
      eapply (store_full _ a e 1 (c_mv 10 18) d k).
      * gres. exact Hra.
      * okx Hk.
      * gres. exact H10.
      * gres. exact H11.
      * gres. reflexivity.
      * gres. cv.
      * gres. exact H12.
      * gres. exact H16.
      * exact Hae.
      * exact He.
      * left; reflexivity.
      * unfold c_mv; lia.
      * lia.
      * exact Hkk.
      * exact Hrd.
      * intros E Hem. apply (acc_true 1 (c_mv 10 18) (split32 (sd_a0 (8 * d)))); try assumption.
        -- left; reflexivity.
        -- apply st_full; lia.
      * intros K1 E Hem. eapply (acc_false 1 (c_mv 10 18)); try eassumption. left; reflexivity.
  - wbr_tk Hc SF_36bfa SD_36bfa ltac:(apply br_ne_t; rewrite H13, H15; rewrite !U by lia; exact Ne).
    unfold btgt; imm_norm.
    wv SF_36c20 SD_36c20 2.
    destruct (Z.lt_ge_cases s 2) as [S2|S2].
    + wbr_tk Hc SF_36c22 SD_36c22 ltac:(apply br_ltu_t; rewrite H13; rewrite !U by lia; lia).
      unfold btgt; imm_norm.
      apply r0_frame; try assumption.
      * gres. exact Hra.
      * okx Hk.
      * gres. exact H10.
      * gres. exact H11.
      * gres. exact H12.
      * gres. exact H13.
      * gres. exact H16.
      * gres. exact H17.
      * gres. reflexivity.
      * left; exact S2.
    + wbr_ft Hc SF_36c22 SD_36c22 ltac:(apply br_ltu_f; rewrite H13; rewrite !U by lia; lia).
      wsv Hc SF_36c26 SD_36c26 (W (h + 2)) ltac:(rewrite H14; unfold v_addi; rewrite U by lia; reflexivity).
      destruct (Z.lt_ge_cases s (h + 2)) as [Sh|Sh].
      * wbr_ft Hc SF_36c28 SD_36c28 ltac:(apply br_geu_f; rewrite H13; rewrite !U by lia; lia).
        ws Hc SF_36c2c SD_36c2c.
        ws Hc SF_36c2e SD_36c2e.
        ws Hc SF_36c32 SD_36c32.
        ws Hc SF_36c34 SD_36c34.
        ws Hc SF_36c36 SD_36c36.
        ws Hc SF_36c38 SD_36c38.
        wv SF_36c3c SD_36c3c 31.
        assert (Ht : take 1 (c_mv 10 (18 + s)) = src_template h c s).
        { rewrite take1 by (unfold c_mv; lia). symmetry. apply src_home; lia. }
        destruct (Z.le_gt_cases d 31) as [Ds|Dl].
        -- wbr_tk Hc SF_36c3e SD_36c3e ltac:(apply br_geu_t; rewrite H12; rewrite !U by lia; lia).
           unfold btgt; imm_norm.
           eapply (store_small _ a e 1 (c_mv 10 (18 + s)) d k).
           ++ gres. exact Hra.
           ++ okx Hk.
           ++ gres. exact H10.
           ++ gres. exact H11.
           ++ gres. reflexivity.
           ++ gres. rewrite H13. en1 s 8%nat.
           ++ gres. exact H12.
           ++ gres. exact H16.
           ++ exact Hae.
           ++ exact He.
           ++ left; reflexivity.
           ++ unfold c_mv; lia.
           ++ lia.
           ++ exact Hkk.
           ++ exact Hrd.
           ++ intros E Hem. apply (acc_true 1 (c_mv 10 (18 + s)) [c_sd_a0 (8 * d)]); try assumption.
              ** left; reflexivity.
              ** apply st_small; lia.
           ++ intros K1 E Hem. eapply (acc_false 1 (c_mv 10 (18 + s))); try eassumption. left; reflexivity.
        -- wbr_ft Hc SF_36c3e SD_36c3e ltac:(apply br_geu_f; rewrite H12; rewrite !U by lia; lia).
           eapply (store_full _ a e 1 (c_mv 10 (18 + s)) d k).
           ++ gres. exact Hra.
           ++ okx Hk.
           ++ gres. exact H10.
           ++ gres. exact H11.
           ++ gres. reflexivity.
           ++ gres. rewrite H13. en1 s 8%nat.
           ++ gres. exact H12.
           ++ gres. exact H16.
           ++ exact Hae.
           ++ exact He.
           ++ left; reflexivity.
           ++ unfold c_mv; lia.
           ++ lia.
           ++ exact Hkk.
           ++ exact Hrd.
           ++ intros E Hem. apply (acc_true 1 (c_mv 10 (18 + s)) (split32 (sd_a0 (8 * d)))); try assumption.
              ** left; reflexivity.
              ** apply st_full; lia.
           ++ intros K1 E Hem. eapply (acc_false 1 (c_mv 10 (18 + s))); try eassumption. left; reflexivity.
      * wbr_tk Hc SF_36c28 SD_36c28 ltac:(apply br_geu_t; rewrite H13; rewrite !U by lia; lia).
        unfold btgt; imm_norm.
        apply r0_frame; try assumption.
        -- gres. exact Hra.
        -- okx Hk.
        -- gres. exact H10.
        -- gres. exact H11.
        -- gres. exact H12.
        -- gres. exact H13.
        -- gres. exact H16.
        -- gres. exact H17.
        -- gres. reflexivity.
        -- right; exact Sh.
Qed.

Lemma seqz_xor : forall (x y : Z), 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  v_sltiu (v_xor (W x) (W y)) 1 = if x =? y then W 1 else W 0.
Proof.
  intros x y Hx Hy. unfold v_sltiu, v_xor. rewrite (U x), (U y) by lia.
  destruct (Z.eqb_spec x y) as [->|Ne].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - assert (Hn : Z.lxor x y <> 0) by (intro Hz; apply Ne; apply Z.lxor_eq; exact Hz).
    assert (Hb : 0 <= Z.lxor x y < 2^64).
    { split; [apply Z.lxor_nonneg; lia|].
      destruct (Z.eq_dec x 0) as [->|Hx0]; [rewrite Z.lxor_0_l; lia|].
      destruct (Z.eq_dec y 0) as [->|Hy0]; [rewrite Z.lxor_0_r; lia|].
      apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia.
      eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
      apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia. }
    rewrite U by exact Hb.
    change (bv_wrap 64 1) with 1. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

(** From 0x36bc6, with the operands in the domain. *)
Lemma body : forall regs,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 10 = W a -> getr regs 11 = W e -> getr regs 12 = W d -> getr regs 13 = W s ->
  getr regs 14 = W h -> getr regs 15 = W c -> getr regs 16 = W k -> 0 <= c < 2^64 ->
  in_domain h c d s k ->
  Run source_segs r mem rom (Result K Accepted) (mkst regs (0x36bc6%bv : word) mem rom).
Proof.
  intros regs Hra Hk H10 H11 H12 H13 H14 H15 H16 Hcr Hdom.
  pose proof Hdom as (Hd & Hs & Hh & Hkk & _).
  norm_pc_run.
  wv SF_36bc6 SD_36bc6 2.
  wsv Hc SF_36bc8 SD_36bc8 (W (s * 8388608)) ltac:(rewrite H13; unfold v_slli; rewrite U by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  destruct (Z.lt_ge_cases d 2) as [D2|D2].
  - wbr_tk Hc SF_36bcc SD_36bcc ltac:(apply br_ltu_t; rewrite H12; rewrite !U by lia; lia).
    unfold btgt; imm_norm.
    apply r0; try assumption.
    + gres. exact Hra.
    + okx Hk.
    + gres. exact H10.
    + gres. exact H11.
    + gres. exact H12.
    + gres. exact H13.
    + gres. exact H14.
    + gres. exact H15.
    + gres. exact H16.
    + gres. reflexivity.
    + apply home_f. left; exact D2.
  - wbr_ft Hc SF_36bcc SD_36bcc ltac:(apply br_ltu_f; rewrite H12; rewrite !U by lia; lia).
    wsv Hc SF_36bd0 SD_36bd0 (W (h + 2)) ltac:(rewrite H14; unfold v_addi; rewrite U by lia; reflexivity).
    destruct (Z.lt_ge_cases d (h + 2)) as [Dh|Dh].
    2: { wbr_tk Hc SF_36bd4 SD_36bd4 ltac:(apply br_geu_t; rewrite H12; rewrite !U by lia; lia).
         unfold btgt; imm_norm.
         apply r0; try assumption.
         + gres. exact Hra.
         + okx Hk.
         + gres. exact H10.
         + gres. exact H11.
         + gres. exact H12.
         + gres. exact H13.
         + gres. exact H14.
         + gres. exact H15.
         + gres. exact H16.
         + gres. reflexivity.
         + apply home_f. right; exact Dh. }
    wbr_ft Hc SF_36bd4 SD_36bd4 ltac:(apply br_geu_f; rewrite H12; rewrite !U by lia; lia).
    assert (Hhd : is_home h d = true) by (apply home_t; lia).
    destruct Hkk as [K0 | K1].
    2: { wbr_tk Hc SF_36bd8 SD_36bd8 ltac:(apply br_ne_t; rewrite H16, K1; vm_compute; discriminate).
         unfold btgt; imm_norm.
         apply exit0; try assumption.
         + gres. exact Hra.
         + okx Hk. }
    wbr_ft Hc SF_36bd8 SD_36bd8 ltac:(apply br_ne_f; rewrite H16, K0; reflexivity).
    wv SF_36bdc SD_36bdc 2.
    ws Hc SF_36bde SD_36bde.
    assert (HomeT : forall L, move_template h c d s k true = L ->
              e = a + 2 * Z.of_nat (length L) -> emit_at mem a L -> Accepted).
    { intros L HL E Hem. split; [exact Hdom|]. exists true. rewrite HL.
      split; [discriminate | split; assumption]. }
    (* A frame source. *)
    assert (Frame : forall regs2,
      getr regs2 1 = r -> (forall x, kept_reg x -> getr regs2 x = getr K x) ->
      getr regs2 10 = W a -> getr regs2 11 = W e -> getr regs2 12 = W d -> getr regs2 16 = W k ->
      getr regs2 14 = W (d + 18) -> getr regs2 17 = W (s * 8388608) -> getr regs2 5 = W 2 ->
      (s < 2 \/ h + 2 <= s) ->
      Run source_segs r mem rom (Result K Accepted) (mkst regs2 (0x36cb4%bv : word) mem rom)).
    { intros regs2 Hra2 Hk2 H102 H112 H122 H162 H142 H172 H52 Hnh.
      norm_pc_run.
      ws Hc SF_36cb4 SD_36cb4.
      ws Hc SF_36cb6 SD_36cb6.
      ws Hc SF_36cba SD_36cba.
      ws Hc SF_36cbe SD_36cbe.
      ws Hc SF_36cc0 SD_36cc0.
      wj Hc SF_36cc4 SD_36cc4 (0x36cda%bv : word).
      pose proof (ld_small (18 + d) s ltac:(lia) ltac:(lia)) as Hv.
      eapply (len_home mem rom r K Hc Hev _ a e 2 (ld_s0 (18 + d) (8 * s))).
      - gres. exact Hra2.
      - okx Hk2.
      - gres. exact H102.
      - gres. exact H112.
      - gres. exact H52.
      - gres. rewrite H142, H172. en2 d s 8%nat 256%nat.
      - gres. rewrite H162, K0. reflexivity.
      - exact Hae.
      - exact He.
      - right; reflexivity.
      - lia.
      - exact Hrd.
      - intros E Hem. rewrite (take2 _ Hv) in Hem.
        apply (HomeT (split32 (ld_s0 (18 + d) (8 * s)))); try assumption.
        unfold move_template. rewrite Hhd, home_f by exact Hnh. reflexivity. }
    destruct (Z.lt_ge_cases s 2) as [S2|S2].
    + wbr_tk Hc SF_36be2 SD_36be2 ltac:(apply br_ltu_t; rewrite H13; rewrite !U by lia; lia).
      unfold btgt; imm_norm.
      apply Frame.
      * gres. exact Hra.
      * okx Hk.
      * gres. exact H10.
      * gres. exact H11.
      * gres. exact H12.
      * gres. exact H16.
      * gres. rewrite H12. unfold v_addi. rewrite U by lia. reflexivity.
      * gres. reflexivity.
      * gres. reflexivity.
      * left; exact S2.
    + wbr_ft Hc SF_36be2 SD_36be2 ltac:(apply br_ltu_f; rewrite H13; rewrite !U by lia; lia).
      destruct (Z.lt_ge_cases s (h + 2)) as [Sh|Sh].
      2: { wbr_tk Hc SF_36be6 SD_36be6 ltac:(apply br_geu_t; rewrite H13; rewrite !U by lia; lia).
           unfold btgt; imm_norm.
           apply Frame.
           * gres. exact Hra.
           * okx Hk.
           * gres. exact H10.
           * gres. exact H11.
           * gres. exact H12.
           * gres. exact H16.
           * gres. rewrite H12. unfold v_addi. rewrite U by lia. reflexivity.
           * gres. reflexivity.
           * gres. reflexivity.
           * right; exact Sh. }
      wbr_ft Hc SF_36be6 SD_36be6 ltac:(apply br_geu_f; rewrite H13; rewrite !U by lia; lia).
      destruct (Z.eq_dec s d) as [Sd|Sd].
      * wbr_ft Hc SF_36bea SD_36bea ltac:(apply br_ne_f; rewrite H13, H12; rewrite !U by lia; exact Sd).
        ws Hc SF_36bee SD_36bee.
        ws Hc SF_36bf0 SD_36bf0.
        ws Hc SF_36bf4 SD_36bf4.
        eapply run_step;
        [ reflexivity
        | eapply z_jr;
          [ wxf_with Hc SF_36bf6 | reflexivity | exact SD_36bf6
          | gres; rewrite Hra; apply jalr_tgt_even; [exact Hev | reflexivity] ]
        | ].
        apply run_done. split; [okx Hk|].
        gres. rewrite H10, H11.
        assert (Ez : v_add (W 0) (v_sltiu (v_xor (W a) (W e)) 1) = if a =? e then W 1 else W 0).
        { rewrite seqz_xor by lia. destruct (a =? e); reflexivity. }
        rewrite Ez.
        destruct (Z.eqb_spec a e) as [Eae|Nae].
        -- right. right. split; [reflexivity|].
           apply (HomeT []).
           ++ unfold move_template. rewrite Hhd, home_t by lia. rewrite (proj2 (Z.eqb_eq _ _)) by exact Sd. reflexivity.
           ++ cbn. lia.
           ++ exact I.
        -- left. reflexivity.
      * wbr_tk Hc SF_36bea SD_36bea ltac:(apply br_ne_t; rewrite H13, H12; rewrite !U by lia; exact Sd).
        unfold btgt; imm_norm.
        ws Hc SF_36cc6 SD_36cc6.
        ws Hc SF_36cc8 SD_36cc8.
        ws Hc SF_36cca SD_36cca.
        ws Hc SF_36cce SD_36cce.
        ws Hc SF_36cd0 SD_36cd0.
        ws Hc SF_36cd2 SD_36cd2.
        ws Hc SF_36cd4 SD_36cd4.
        wv SF_36cd8 SD_36cd8 1.
        assert (Hv : 0 <= c_mv (18 + d) (18 + s) < 65536) by (unfold c_mv; lia).
        eapply (len_home mem rom r K Hc Hev _ a e 1 (c_mv (18 + d) (18 + s))).
        -- gres. exact Hra.
        -- okx Hk.
        -- gres. exact H10.
        -- gres. exact H11.
        -- gres. reflexivity.
        -- gres. rewrite H12, H13. en2 d s 8%nat 8%nat.
        -- gres. rewrite H16, K0. reflexivity.
        -- exact Hae.
        -- exact He.
        -- left; reflexivity.
        -- lia.
        -- exact Hrd.
        -- intros E Hem. rewrite (take1 _ Hv) in Hem.
           apply (HomeT [c_mv (18 + d) (18 + s)]); try assumption.
           unfold move_template. rewrite Hhd, home_t by lia.
           rewrite (proj2 (Z.eqb_neq _ _)) by exact Sd. reflexivity.
Qed.

(** The whole function, from its entry. *)
Theorem check_move_contract : forall regs,
  regs = K ->
  getr regs 1 = r ->
  getr regs 10 = W a -> getr regs 11 = W e -> getr regs 12 = W d -> getr regs 13 = W s ->
  getr regs 14 = W h -> getr regs 15 = W c -> getr regs 16 = W k ->
  0 <= d < 2^64 -> 0 <= s < 2^64 -> 0 <= h < 2^64 -> 0 <= c < 2^64 -> 0 <= k < 2^64 ->
  Run source_segs r mem rom (Result K Accepted) (mkst regs (0x36b9c%bv : word) mem rom).
Proof.
  intros regs -> Hra H10 H11 H12 H13 H14 H15 H16 Hd Hs Hh Hcr Hkr.
  assert (Hk : forall x, kept_reg x -> getr K x = getr K x) by reflexivity.
  norm_pc_run.
  wsv Hc SF_36b9c SD_36b9c (W (Z.lor s d)) ltac:(rewrite H13, H12; unfold v_or; rewrite !U by lia; reflexivity).
  wv SF_36ba0 SD_36ba0 255.
  wv SF_36ba4 SD_36ba4 2.
  pose proof (lor_ge s d ltac:(lia) ltac:(lia)) as [Ls Ld].
  assert (Lr : 0 <= Z.lor s d < 2^64).
  { split; [lia|]. apply lor_lt; lia. }
  assert (Exit2 : forall regs2, getr regs2 1 = r -> (forall x, kept_reg x -> getr regs2 x = getr K x) ->
     getr regs2 17 = W 2 ->
     Run source_segs r mem rom (Result K Accepted) (mkst regs2 (0x36bc2%bv : word) mem rom)).
  { intros regs2 A B C0. apply (exit_a7 mem rom r K Hc Hev _ 2); try assumption. right; reflexivity. }
  destruct (Z.le_gt_cases (Z.lor s d) 255) as [Ok|Big].
  2: { wbr_tk Hc SF_36ba6 SD_36ba6 ltac:(apply br_ltu_t; rewrite !U by lia; lia).
       unfold btgt; imm_norm. apply Exit2; [gres; exact Hra | okx Hk | gres; reflexivity]. }
  wbr_ft Hc SF_36ba6 SD_36ba6 ltac:(apply br_ltu_f; rewrite !U by lia; lia).
  wv SF_36baa SD_36baa 6.
  destruct (Z.le_gt_cases h 6) as [Ok6|Big6].
  2: { wbr_tk Hc SF_36bac SD_36bac ltac:(apply br_ltu_t; rewrite H14; rewrite !U by lia; lia).
       unfold btgt; imm_norm. apply Exit2; [gres; exact Hra | okx Hk | gres; reflexivity]. }
  wbr_ft Hc SF_36bac SD_36bac ltac:(apply br_ltu_f; rewrite H14; rewrite !U by lia; lia).
  wv SF_36bb0 SD_36bb0 1.
  destruct (Z.le_gt_cases k 1) as [Ok1|Big1].
  2: { wbr_tk Hc SF_36bb2 SD_36bb2 ltac:(apply br_ltu_t; rewrite H16; rewrite !U by lia; lia).
       unfold btgt; imm_norm. apply Exit2; [gres; exact Hra | okx Hk | gres; reflexivity]. }
  wbr_ft Hc SF_36bb2 SD_36bb2 ltac:(apply br_ltu_f; rewrite H16; rewrite !U by lia; lia).
  destruct (Z.eq_dec h 0) as [H0|Hn0].
  - wbr_tk Hc SF_36bb6 SD_36bb6 ltac:(apply br_eq_t; rewrite H14, H0; reflexivity).
    unfold btgt; imm_norm.
    apply body.
    + gres. exact Hra.
    + okx Hk.
    + gres. exact H10.
    + gres. exact H11.
    + gres. exact H12.
    + gres. exact H13.
    + gres. exact H14.
    + gres. exact H15.
    + gres. exact H16.
    + exact Hcr.
    + unfold in_domain; repeat split; lia.
  - wbr_ft Hc SF_36bb6 SD_36bb6 ltac:(apply br_eq_f; rewrite H14; rewrite !U by lia; lia).
    wv SF_36bb8 SD_36bb8 (-1).
    wv SF_36bba SD_36bba 4294967295.
    destruct (Z.eq_dec c 4294967295) as [CN|CN].
    + wbr_tk Hc SF_36bbe SD_36bbe ltac:(apply br_eq_t; rewrite H15; rewrite !U by lia; exact CN).
      unfold btgt; imm_norm.
      apply body.
      * gres. exact Hra.
      * okx Hk.
      * gres. exact H10.
      * gres. exact H11.
      * gres. exact H12.
      * gres. exact H13.
      * gres. exact H14.
      * gres. exact H15.
      * gres. exact H16.
      * exact Hcr.
      * unfold in_domain; repeat split; lia.
    + wbr_ft Hc SF_36bbe SD_36bbe ltac:(apply br_eq_f; rewrite H15; rewrite !U by lia; exact CN).
      apply Exit2; [gres; exact Hra | okx Hk | gres; reflexivity].
Qed.
End Contract.
