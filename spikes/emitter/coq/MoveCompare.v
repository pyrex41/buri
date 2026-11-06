(** * Route B, the compare half of [spike_check_move]: from 0x36cea on, the checker reads the
    bytes and compares them with its expected words.  Contract for all words and memory. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec.
From LinuxProcessSemantics.Examples.emitter_ns Require Import emitter_code GcStep MoveStep GcTac MoveTemplate.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation W z := (Z_to_bv 64 z).

(** [v] is the 16-bit value at address [a]. *)
Definition half_at (m : word -> option byte) (a v : Z) : Prop :=
  exists bs, rdn source_segs m (W a) 2%nat = Some bs /\ bytes_le_to_Z bs = v.

Fixpoint emit_at (m : word -> option byte) (a : Z) (L : list Z) : Prop :=
  match L with
  | [] => True
  | v :: t => half_at m a v /\ emit_at m (a + 2) t
  end.

Lemma emit_at_app : forall m L1 L2 a,
  emit_at m a (L1 ++ L2) <-> emit_at m a L1 /\ emit_at m (a + 2 * Z.of_nat (length L1)) L2.
Proof.
  intros m L1 L2. induction L1 as [|v t IH]; intro a; cbn [app emit_at length].
  - rewrite Nat2Z.inj_0. replace (a + 2 * 0) with a by lia. tauto.
  - rewrite IH. rewrite Nat2Z.inj_succ.
    replace (a + 2 + 2 * Z.of_nat (length t)) with (a + 2 * Z.succ (Z.of_nat (length t))) by lia. tauto.
Qed.

Definition take (n w : Z) : list Z :=
  if n =? 0 then []
  else if n =? 1 then [w mod 65536]
  else [w mod 65536; (w / 65536) mod 65536].

Definition ktail (k : Z) : list Z := if k =? 1 then [c_mv 18 10] else [].

Definition kept_reg (x : reg) : Prop :=
  x <> 5%bv /\ x <> 6%bv /\ x <> 7%bv /\ x <> 10%bv /\ x <> 11%bv /\ x <> 12%bv /\ x <> 13%bv /\
  x <> 14%bv /\ x <> 15%bv /\ x <> 16%bv /\ x <> 17%bv.

Definition Result (K : bvmap 5 word) (Q : Prop) (regs : bvmap 5 word) : Prop :=
  (forall x : reg, kept_reg x -> getr regs x = getr K x) /\
  (getr regs 10 = W 0 \/ getr regs 10 = W 2 \/ (getr regs 10 = W 1 /\ Q)).

Lemma mask16 : forall w, 0 <= w < 2^64 ->
  v_srli (v_slli (W w) 48) 48 = W (w mod 65536).
Proof.
  intros w Hw. unfold v_srli, v_slli. rewrite (U w) by exact Hw.
  assert (Hs : bv_unsigned (W (Z.shiftl w 48)) = (w mod 65536) * 2^48).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (65536 * 2^48).
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mul_mod_distr_r by lia. reflexivity. }
  rewrite Hs. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma srl16 : forall w, 0 <= w < 2^64 -> v_srli (W w) 16 = W (w / 65536).
Proof.
  intros w Hw. unfold v_srli. rewrite (U w) by exact Hw.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma div16_range : forall w, 0 <= w < 2^64 -> 0 <= w / 65536 < 2^64.
Proof.
  intros w Hw. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Section Compare.
Context {fx : FPState}.
Variables (mem rom : word -> option byte) (r : word) (K : bvmap 5 word).
Hypothesis Hc : mem_clear mem TL TH.
Hypothesis Hev : (bv_unsigned r mod 2 = 0)%Z.

Ltac okx H := let x := fresh "x" in let Hx := fresh in let Hy := fresh in
  intros x Hx; pose proof Hx as Hy;
  destruct Hy as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);
  repeat (rewrite getr_other by assumption); apply H; exact Hx.

(* A return with a known a0, through the kept ra. *)
Ltac wfin F D Hra Hk := wret Hc F D Hra Hev; apply run_done; split; [okx Hk|].

(* Exit with 0 from 0x36d42. *)
Lemma exit0 : forall regs Q,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  Run source_segs r mem rom (Result K Q) (mkst regs (0x36d42%bv : word) mem rom).
Proof.
  intros regs Q Hra Hk. norm_pc_run.
  ws Hc SF_36d42 SD_36d42.
  eapply run_step;
  [ reflexivity
  | eapply z_jr;
    [ wxf_with Hc SF_36d44 | reflexivity | exact SD_36d44
    | gres; rewrite Hra; apply jalr_tgt_even; [exact Hev | reflexivity] ]
  | ].
  apply run_done. split; [okx Hk|]. left. gres. imm_norm. bveq.
Qed.

Lemma loop_a : forall regs cur cnt w v Q,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 11 = W cur -> getr regs 15 = W cnt -> getr regs 7 = W w ->
  0 <= cur < 2^64 - 2 -> 1 <= cnt <= 2 -> 0 <= w < 2^64 -> 0 <= v < 65536 -> half_at mem cur v ->
  (v = w mod 65536 -> forall regs2,
     getr regs2 1 = r -> (forall x, kept_reg x -> getr regs2 x = getr K x) ->
     getr regs2 11 = W (cur + 2) -> getr regs2 15 = W (cnt - 1) -> getr regs2 7 = W (w / 65536) ->
     (forall x : reg, x <> 11%bv -> x <> 15%bv -> x <> 7%bv -> x <> 13%bv -> x <> 14%bv -> x <> 15%bv ->
        getr regs2 x = getr regs x) ->
     Run source_segs r mem rom (Result K Q) (mkst regs2 (0x36d04%bv : word) mem rom)) ->
  Run source_segs r mem rom (Result K Q) (mkst regs (0x36cee%bv : word) mem rom).
Proof.
  intros regs cur cnt w v Q Hra Hk H11 HC HW Hcur Hcnt Hw Hv (bs & Hrd & Hbs) Cont.
  assert (Hm : 0 <= w mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  norm_pc_run.
  eapply run_step;
  [ reflexivity
  | eapply z_lhu_at with (a := W cur) (bs := bs) (z := v);
    [ wxf_with Hc SF_36cee | reflexivity | exact SD_36cee | reflexivity
    | gres; rewrite H11; imm_norm; apply v_addi_0 | exact Hrd | exact Hbs | exact Hv ]
  | norm_pc_run ].
  ws Hc SF_36cf2 SD_36cf2.
  wsv Hc SF_36cf6 SD_36cf6 (W (w mod 65536)) ltac:(rewrite HW; apply mask16; exact Hw).
  destruct (Z.eq_dec v (w mod 65536)) as [E|Ne].
  - wbr_ft Hc SF_36cf8 SD_36cf8 ltac:(apply br_ne_f; rewrite !U by lia; exact E).
    wsv Hc SF_36cfc SD_36cfc (W (w / 65536)) ltac:(rewrite HW; apply srl16; exact Hw).
    wsv Hc SF_36d00 SD_36d00 (W (cnt - 1)) ltac:(rewrite HC; unfold v_addi; rewrite U by lia; f_equal; lia).
    wsv Hc SF_36d02 SD_36d02 (W (cur + 2)) ltac:(rewrite H11; unfold v_addi; rewrite U by lia; reflexivity).
    apply (Cont E).
    + gres. exact Hra.
    + okx Hk.
    + gres. reflexivity.
    + gres. reflexivity.
    + gres. reflexivity.
    + intros x ? ? ? ? ? ?. repeat (rewrite getr_other by assumption). reflexivity.
  - wbr_tk Hc SF_36cf8 SD_36cf8 ltac:(apply br_ne_t; rewrite !U by lia; exact Ne).
    apply exit0.
    + gres. exact Hra.
    + okx Hk.
Qed.

Lemma loop_b : forall regs cur cnt w v Q,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 11 = W cur -> getr regs 13 = W cnt -> getr regs 12 = W w ->
  0 <= cur < 2^64 - 2 -> 1 <= cnt <= 2 -> 0 <= w < 2^64 -> 0 <= v < 65536 -> half_at mem cur v ->
  (v = w mod 65536 -> forall regs2,
     getr regs2 1 = r -> (forall x, kept_reg x -> getr regs2 x = getr K x) ->
     getr regs2 11 = W (cur + 2) -> getr regs2 13 = W (cnt - 1) -> getr regs2 12 = W (w / 65536) ->
     (forall x : reg, x <> 11%bv -> x <> 13%bv -> x <> 12%bv -> x <> 13%bv -> x <> 14%bv -> x <> 15%bv ->
        getr regs2 x = getr regs x) ->
     Run source_segs r mem rom (Result K Q) (mkst regs2 (0x36d26%bv : word) mem rom)) ->
  Run source_segs r mem rom (Result K Q) (mkst regs (0x36d12%bv : word) mem rom).
Proof.
  intros regs cur cnt w v Q Hra Hk H11 HC HW Hcur Hcnt Hw Hv (bs & Hrd & Hbs) Cont.
  assert (Hm : 0 <= w mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  norm_pc_run.
  eapply run_step;
  [ reflexivity
  | eapply z_lhu_at with (a := W cur) (bs := bs) (z := v);
    [ wxf_with Hc SF_36d12 | reflexivity | exact SD_36d12 | reflexivity
    | gres; rewrite H11; imm_norm; apply v_addi_0 | exact Hrd | exact Hbs | exact Hv ]
  | norm_pc_run ].
  ws Hc SF_36d16 SD_36d16.
  wsv Hc SF_36d1a SD_36d1a (W (w mod 65536)) ltac:(rewrite HW; apply mask16; exact Hw).
  destruct (Z.eq_dec v (w mod 65536)) as [E|Ne].
  - wbr_ft Hc SF_36d1c SD_36d1c ltac:(apply br_ne_f; rewrite !U by lia; exact E).
    wsv Hc SF_36d20 SD_36d20 (W (w / 65536)) ltac:(rewrite HW; apply srl16; exact Hw).
    wsv Hc SF_36d22 SD_36d22 (W (cnt - 1)) ltac:(rewrite HC; unfold v_addi; rewrite U by lia; f_equal; lia).
    wsv Hc SF_36d24 SD_36d24 (W (cur + 2)) ltac:(rewrite H11; unfold v_addi; rewrite U by lia; reflexivity).
    apply (Cont E).
    + gres. exact Hra.
    + okx Hk.
    + gres. reflexivity.
    + gres. reflexivity.
    + gres. reflexivity.
    + intros x ? ? ? ? ? ?. repeat (rewrite getr_other by assumption). reflexivity.
  - wbr_tk Hc SF_36d1c SD_36d1c ltac:(apply br_ne_t; rewrite !U by lia; exact Ne).
    apply exit0.
    + gres. exact Hra.
    + okx Hk.
Qed.

Lemma tail : forall regs a ns k Q,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 10 = W a -> getr regs 6 = W ns -> getr regs 16 = W k ->
  0 <= a -> a + 2 * ns + 2 < 2^64 -> 0 <= ns <= 2 -> (k = 0 \/ k = 1) ->
  (k = 1 -> exists v, 0 <= v < 65536 /\ half_at mem (a + 2 * ns) v) ->
  (k = 0 -> Q) -> (k = 1 -> half_at mem (a + 2 * ns) (c_mv 18 10) -> Q) ->
  Run source_segs r mem rom (Result K Q) (mkst regs (0x36d28%bv : word) mem rom).
Proof.
  intros regs a ns k Q Hra Hk H10 H6 H16 Ha Hb Hns Hkk Rd Q0 Q1.
  norm_pc_run.
  destruct Hkk as [ -> | -> ].
  - wbr_tk Hc SF_36d28 SD_36d28 ltac:(apply br_eq_t; rewrite H16; reflexivity).
    ws Hc SF_36d3e SD_36d3e.
    eapply run_step;
    [ reflexivity
    | eapply z_jr;
      [ wxf_with Hc SF_36d40 | reflexivity | exact SD_36d40
      | gres; rewrite Hra; apply jalr_tgt_even; [exact Hev | reflexivity] ]
    | ].
    apply run_done. split; [okx Hk|]. right. right. split; [gres; imm_norm; bveq | exact (Q0 eq_refl)].
  - destruct (Rd eq_refl) as (v & Hv & Hh). assert (Hh2 := Hh). destruct Hh2 as (bs & Hrd & Hbs).
    wbr_ft Hc SF_36d28 SD_36d28 ltac:(apply br_eq_f; rewrite H16; vm_compute; discriminate).
    wsv Hc SF_36d2c SD_36d2c (W (2 * ns)) ltac:(rewrite H6; unfold v_slli; rewrite U by lia; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
    wsv Hc SF_36d2e SD_36d2e (W (a + 2 * ns)) ltac:(rewrite H10; unfold v_add; rewrite !U by lia; reflexivity).
    eapply run_step;
    [ reflexivity
    | eapply z_lhu_at with (a := W (a + 2 * ns)) (bs := bs) (z := v);
      [ wxf_with Hc SF_36d30 | reflexivity | exact SD_36d30 | reflexivity
      | gres; imm_norm; apply v_addi_0 | exact Hrd | exact Hbs | exact Hv ]
    | norm_pc_run ].
    wsv Hc SF_36d34 SD_36d34 (W 0x9000) ltac:(vm_compute; reflexivity).
    wsv Hc SF_36d36 SD_36d36 (W (c_mv 18 10)) ltac:(vm_compute; reflexivity).
    destruct (Z.eq_dec v (c_mv 18 10)) as [E|Ne].
    + wbr_ft Hc SF_36d3a SD_36d3a ltac:(apply br_ne_f; rewrite !U by (try lia; vm_compute; split; try discriminate); exact E).
      ws Hc SF_36d3e SD_36d3e.
      eapply run_step;
      [ reflexivity
      | eapply z_jr;
        [ wxf_with Hc SF_36d40 | reflexivity | exact SD_36d40
        | gres; rewrite Hra; apply jalr_tgt_even; [exact Hev | reflexivity] ]
      | ].
      apply run_done. split; [okx Hk|]. right. right. split; [gres; imm_norm; bveq|].
      subst v. rewrite E in Hh. exact (Q1 eq_refl Hh).
    + wbr_tk Hc SF_36d3a SD_36d3a ltac:(apply br_ne_t; rewrite !U by (try lia; vm_compute; split; try discriminate); exact Ne).
      apply exit0; [gres; exact Hra | okx Hk].
Qed.

Ltac mvp H := rewrite H; unfold v_add; rewrite !U by lia; f_equal; lia.

Lemma after_a : forall regs a n ns s k Q,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 10 = W a -> getr regs 5 = W n -> getr regs 6 = W ns -> getr regs 12 = W s ->
  getr regs 16 = W k ->
  0 <= a -> a + 2 * n + 2 * ns + 2 * k + 2 < 2^64 -> 1 <= n <= 2 -> (ns = 0 \/ ns = 1 \/ ns = 2) ->
  0 <= s < 2^64 -> (k = 0 \/ k = 1) ->
  (forall i, 0 <= i < ns + k -> exists v, 0 <= v < 65536 /\ half_at mem (a + 2 * n + 2 * i) v) ->
  (emit_at mem (a + 2 * n) (take ns s ++ ktail k) -> Q) ->
  Run source_segs r mem rom (Result K Q) (mkst regs (0x36d06%bv : word) mem rom).
Proof.
  intros regs a n ns s k Q Hra Hk H10 H5 H6 H12 H16 Ha Hb Hn Hns Hs Hkk Rd Qp.
  norm_pc_run.
  wsv Hc SF_36d06 SD_36d06 (W (2 * n)) ltac:(rewrite H5; unfold v_slli; rewrite U by lia; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
  wsv Hc SF_36d08 SD_36d08 (W (a + 2 * n)) ltac:(rewrite H10; unfold v_add; rewrite !U by lia; reflexivity).
  destruct Hns as [E0 | [E1 | E2]]; subst ns.
  - wbr_tk Hc SF_36d0a SD_36d0a ltac:(apply br_eq_t; rewrite H6; reflexivity).
    eapply (tail _ (a + 2 * n) 0 k).
    + gres. exact Hra.
    + okx Hk.
    + gres. reflexivity.
    + gres. exact H6.
    + gres. exact H16.
    + lia.
    + lia.
    + lia.
    + exact Hkk.
    + intro. subst k. destruct (Rd 0 ltac:(lia)) as (v & Hv & Hh). exists v. split; [exact Hv|].
      replace (a + 2 * n + 2 * 0) with (a + 2 * n + 2 * 0) in * by lia. exact Hh.
    + intro. subst k. apply Qp. exact I.
    + intros -> Hh. apply Qp. cbn. split; [|exact I].
      replace (a + 2 * n) with (a + 2 * n + 2 * 0) by lia. exact Hh.
  - wbr_ft Hc SF_36d0a SD_36d0a ltac:(apply br_eq_f; rewrite H6; vm_compute; discriminate).
    wsv Hc SF_36d0e SD_36d0e (W (a + 2 * n)) ltac:(gres; unfold v_add; rewrite !U by lia; f_equal; lia).
    wsv Hc SF_36d10 SD_36d10 (W 1) ltac:(mvp H6).
    destruct (Rd 0 ltac:(lia)) as (v & Hv & Hh).
    replace (a + 2 * n + 2 * 0) with (a + 2 * n) in Hh by lia.
    apply (loop_b _ (a + 2 * n) 1 s v).
    + gres. exact Hra.
    + okx Hk.
    + gres. reflexivity.
    + gres. reflexivity.
    + gres. exact H12.
    + lia.
    + lia.
    + exact Hs.
    + exact Hv.
    + exact Hh.
    + intros Ev regs2 Hra2 Hk2 H112 H132 H122 Pres.
      wbr_ft Hc SF_36d26 SD_36d26 ltac:(apply br_ne_f; rewrite H132; vm_compute; reflexivity).
      assert (P10 : getr regs2 10 = W (a + 2 * n)).
      { rewrite Pres by (cbv; try discriminate). gres. reflexivity. }
      eapply (tail _ (a + 2 * n) 1 k).
      * exact Hra2.
      * exact Hk2.
      * exact P10.
      * rewrite Pres by (cbv; try discriminate). gres. exact H6.
      * rewrite Pres by (cbv; try discriminate). gres. exact H16.
      * lia.
      * lia.
      * lia.
      * exact Hkk.
      * intro. subst k. destruct (Rd 1 ltac:(lia)) as (v1 & Hv1 & Hh1). exists v1. split; [exact Hv1|]. exact Hh1.
      * intro. subst k. apply Qp. unfold take, ktail. cbn. split; [rewrite <- Ev; exact Hh | exact I].
      * intros -> Hh1. apply Qp. unfold take, ktail. cbn. split; [rewrite <- Ev; exact Hh|].
        split; [|exact I]. replace (a + 2 * n + 2) with (a + 2 * n + 2 * 1) by lia. exact Hh1.
  - wbr_ft Hc SF_36d0a SD_36d0a ltac:(apply br_eq_f; rewrite H6; vm_compute; discriminate).
    wsv Hc SF_36d0e SD_36d0e (W (a + 2 * n)) ltac:(gres; unfold v_add; rewrite !U by lia; f_equal; lia).
    wsv Hc SF_36d10 SD_36d10 (W 2) ltac:(mvp H6).
    destruct (Rd 0 ltac:(lia)) as (v & Hv & Hh).
    replace (a + 2 * n + 2 * 0) with (a + 2 * n) in Hh by lia.
    destruct (Rd 1 ltac:(lia)) as (v1 & Hv1 & Hh1).
    apply (loop_b _ (a + 2 * n) 2 s v).
    + gres. exact Hra.
    + okx Hk.
    + gres. reflexivity.
    + gres. reflexivity.
    + gres. exact H12.
    + lia.
    + lia.
    + exact Hs.
    + exact Hv.
    + exact Hh.
    + intros Ev regs2 Hra2 Hk2 H112 H132 H122 Pres.
      wbr_tk Hc SF_36d26 SD_36d26 ltac:(apply br_ne_t; rewrite H132; vm_compute; discriminate).
      unfold btgt; imm_norm.
      apply (loop_b _ (a + 2 * n + 2) 1 (s / 65536) v1).
      * exact Hra2.
      * exact Hk2.
      * exact H112.
      * exact H132.
      * exact H122.
      * lia.
      * lia.
      * apply div16_range; exact Hs.
      * exact Hv1.
      * replace (a + 2 * n + 2) with (a + 2 * n + 2 * 1) by lia. exact Hh1.
      * intros Ev1 regs3 Hra3 Hk3 H113 H133 H123 Pres3.
        wbr_ft Hc SF_36d26 SD_36d26 ltac:(apply br_ne_f; rewrite H133; vm_compute; reflexivity).
        assert (P : forall x : reg, x <> 11%bv -> x <> 13%bv -> x <> 12%bv -> x <> 14%bv -> x <> 15%bv ->
                    getr regs3 x = getr regs2 x /\ getr regs2 x = getr (regupd (regupd (regupd (regupd regs 5 (W (2 * n))) 10 (W (a + 2 * n))) 11 (W (a + 2 * n))) 13 (W 2)) x).
        { intros x ? ? ? ? ?. split; [apply Pres3 | apply Pres]; assumption. }
        assert (P10 : getr regs3 10 = W (a + 2 * n)).
        { destruct (P 10%bv) as [P1 P2]; try (cbv; discriminate). rewrite P1, P2. gres. reflexivity. }
        assert (P6 : getr regs3 6 = W 2).
        { destruct (P 6%bv) as [P1 P2]; try (cbv; discriminate). rewrite P1, P2. gres. exact H6. }
        assert (P16 : getr regs3 16 = W k).
        { destruct (P 16%bv) as [P1 P2]; try (cbv; discriminate). rewrite P1, P2. gres. exact H16. }
        eapply (tail _ (a + 2 * n) 2 k).
        -- exact Hra3.
        -- exact Hk3.
        -- exact P10.
        -- exact P6.
        -- exact P16.
        -- lia.
        -- lia.
        -- lia.
        -- exact Hkk.
        -- intro. subst k. destruct (Rd 2 ltac:(lia)) as (v2 & Hv2 & Hh2). exists v2. split; [exact Hv2|]. exact Hh2.
        -- intro. subst k. apply Qp. unfold take, ktail. cbn. split; [rewrite <- Ev; exact Hh|].
           split; [|exact I]. rewrite <- Ev1. replace (a + 2 * n + 2) with (a + 2 * n + 2 * 1) by lia. exact Hh1.
        -- intros -> Hh2. apply Qp. unfold take, ktail. cbn. split; [rewrite <- Ev; exact Hh|].
           split; [rewrite <- Ev1; replace (a + 2 * n + 2) with (a + 2 * n + 2 * 1) by lia; exact Hh1|].
           split; [|exact I]. replace (a + 2 * n + 2 + 2) with (a + 2 * n + 2 * 2) by lia. exact Hh2.
Qed.

Lemma cmp_ok : forall regs a n ns w s k Q,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 10 = W a -> getr regs 5 = W n -> getr regs 6 = W ns -> getr regs 7 = W w ->
  getr regs 12 = W s -> getr regs 16 = W k ->
  0 <= a -> a + 2 * n + 2 * ns + 2 * k + 2 < 2^64 -> (n = 1 \/ n = 2) -> (ns = 0 \/ ns = 1 \/ ns = 2) ->
  0 <= w < 2^64 -> 0 <= s < 2^64 -> (k = 0 \/ k = 1) ->
  (forall i, 0 <= i < n + ns + k -> exists v, 0 <= v < 65536 /\ half_at mem (a + 2 * i) v) ->
  (emit_at mem a (take n w ++ take ns s ++ ktail k) -> Q) ->
  Run source_segs r mem rom (Result K Q) (mkst regs (0x36cea%bv : word) mem rom).
Proof.
  intros regs a n ns w s k Q Hra Hk H10 H5 H6 H7 H12 H16 Ha Hb Hn Hns Hw Hs Hkk Rd Qp.
  norm_pc_run.
  wsv Hc SF_36cea SD_36cea (W a) ltac:(mvp H10).
  wsv Hc SF_36cec SD_36cec (W n) ltac:(mvp H5).
  destruct (Rd 0 ltac:(lia)) as (v & Hv & Hh).
  replace (a + 2 * 0) with a in Hh by lia.
  apply (loop_a _ a n w v).
  - gres. exact Hra.
  - okx Hk.
  - gres. reflexivity.
  - gres. reflexivity.
  - gres. exact H7.
  - lia.
  - lia.
  - exact Hw.
  - exact Hv.
  - exact Hh.
  - intros Ev regs2 Hra2 Hk2 H112 H152 H72 Pres.
    assert (Pv : forall x : reg, x <> 11%bv -> x <> 15%bv -> x <> 7%bv -> x <> 13%bv -> x <> 14%bv ->
                 getr regs2 x = getr regs x).
    { intros x ? ? ? ? ?. rewrite Pres by assumption. repeat (rewrite getr_other by assumption). reflexivity. }
    destruct Hn as [-> | ->].
    + wbr_ft Hc SF_36d04 SD_36d04 ltac:(apply br_ne_f; rewrite H152; vm_compute; reflexivity).
      eapply (after_a _ a 1 ns s k).
      * exact Hra2.
      * exact Hk2.
      * rewrite Pv by (cbv; discriminate). exact H10.
      * rewrite Pv by (cbv; discriminate). exact H5.
      * rewrite Pv by (cbv; discriminate). exact H6.
      * rewrite Pv by (cbv; discriminate). exact H12.
      * rewrite Pv by (cbv; discriminate). exact H16.
      * lia.
      * lia.
      * lia.
      * exact Hns.
      * exact Hs.
      * exact Hkk.
      * intros i Hi. destruct (Rd (1 + i) ltac:(lia)) as (v' & Hv' & Hh').
        exists v'. split; [exact Hv'|]. replace (a + 2 * 1 + 2 * i) with (a + 2 * (1 + i)) by lia. exact Hh'.
      * intro Hrest. apply Qp. unfold take at 1. cbn. split; [rewrite <- Ev; exact Hh|].
        replace (a + 2) with (a + 2 * 1) by lia. exact Hrest.
    + destruct (Rd 1 ltac:(lia)) as (v1 & Hv1 & Hh1).
      wbr_tk Hc SF_36d04 SD_36d04 ltac:(apply br_ne_t; rewrite H152; vm_compute; discriminate).
      unfold btgt; imm_norm.
      apply (loop_a _ (a + 2) 1 (w / 65536) v1).
      * exact Hra2.
      * exact Hk2.
      * exact H112.
      * exact H152.
      * exact H72.
      * lia.
      * lia.
      * apply div16_range; exact Hw.
      * exact Hv1.
      * replace (a + 2) with (a + 2 * 1) by lia. exact Hh1.
      * intros Ev1 regs3 Hra3 Hk3 H113 H153 H73 Pres3.
        assert (Pw : forall x : reg, x <> 11%bv -> x <> 15%bv -> x <> 7%bv -> x <> 13%bv -> x <> 14%bv ->
                     getr regs3 x = getr regs x).
        { intros x ? ? ? ? ?. rewrite Pres3 by assumption. apply Pv; assumption. }
        wbr_ft Hc SF_36d04 SD_36d04 ltac:(apply br_ne_f; rewrite H153; vm_compute; reflexivity).
        eapply (after_a _ a 2 ns s k).
        -- exact Hra3.
        -- exact Hk3.
        -- rewrite Pw by (cbv; discriminate). exact H10.
        -- rewrite Pw by (cbv; discriminate). exact H5.
        -- rewrite Pw by (cbv; discriminate). exact H6.
        -- rewrite Pw by (cbv; discriminate). exact H12.
        -- rewrite Pw by (cbv; discriminate). exact H16.
        -- lia.
        -- lia.
        -- lia.
        -- exact Hns.
        -- exact Hs.
        -- exact Hkk.
        -- intros i Hi. destruct (Rd (2 + i) ltac:(lia)) as (v' & Hv' & Hh').
           exists v'. split; [exact Hv'|]. replace (a + 2 * 2 + 2 * i) with (a + 2 * (2 + i)) by lia. exact Hh'.
        -- intro Hrest. apply Qp. unfold take at 1. cbn. split; [rewrite <- Ev; exact Hh|].
           split; [rewrite <- Ev1; replace (a + 2) with (a + 2 * 1) by lia; exact Hh1|].
           replace (a + 2 + 2) with (a + 2 * 2) by lia. exact Hrest.
Qed.

(* Return with a0 := a7, for a7 = 0 or 2. *)
Lemma exit_a7 : forall regs z Q,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 17 = W z -> (z = 0 \/ z = 2) ->
  Run source_segs r mem rom (Result K Q) (mkst regs (0x36bc2%bv : word) mem rom).
Proof.
  intros regs z Q Hra Hk H17 Hz. norm_pc_run.
  wsv Hc SF_36bc2 SD_36bc2 (W z) ltac:(rewrite H17; unfold v_add; rewrite !U by lia; f_equal; lia).
  eapply run_step;
  [ reflexivity
  | eapply z_jr;
    [ wxf_with Hc SF_36bc4 | reflexivity | exact SD_36bc4
    | gres; rewrite Hra; apply jalr_tgt_even; [exact Hev | reflexivity] ]
  | ].
  apply run_done. split; [okx Hk|]. gres.
  destruct Hz as [-> | ->]; [left | right; left]; reflexivity.
Qed.

(** The length checks, 0x36c60 on, with a store template of [ns] halves. *)
Lemma len_main : forall regs a e n ns w s k Q,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 10 = W a -> getr regs 11 = W e -> getr regs 5 = W n -> getr regs 6 = W ns ->
  getr regs 7 = W w -> getr regs 12 = W s -> getr regs 16 = W k ->
  0 <= a <= e -> e + 32 < 2^64 -> (n = 1 \/ n = 2) -> (ns = 1 \/ ns = 2) ->
  0 <= w < 2^64 -> 0 <= s < 2^64 -> (k = 0 \/ k = 1) ->
  (forall i, 0 <= i -> a + 2 * i + 2 <= e -> exists v, 0 <= v < 65536 /\ half_at mem (a + 2 * i) v) ->
  (e = a + 2 * (n + ns + k) -> emit_at mem a (take n w ++ take ns s ++ ktail k) -> Q) ->
  (k = 1 -> e = a + 2 * (n + 1) -> emit_at mem a (take n w ++ take 0 s ++ ktail 1) -> Q) ->
  Run source_segs r mem rom (Result K Q) (mkst regs (0x36c60%bv : word) mem rom).
Proof.
  intros regs a e n ns w s k Q Hra Hk H10 H11 H5 H6 H7 H12 H16 Hae He Hn Hns Hw Hs Hkk Rd Q1 Q2.
  norm_pc_run.
  wsv Hc SF_36c60 SD_36c60 (W (e - a)) ltac:(rewrite H10, H11; unfold v_sub; rewrite !U by lia; reflexivity).
  wsv Hc SF_36c62 SD_36c62 (W (n + k)) ltac:(rewrite H5, H16; unfold v_add; rewrite !U by lia; reflexivity).
  wsv Hc SF_36c66 SD_36c66 (W (n + k + ns)) ltac:(rewrite H6; unfold v_add; rewrite !U by lia; reflexivity).
  wsv Hc SF_36c68 SD_36c68 (W (2 * (n + k + ns))) ltac:(unfold v_slli; rewrite U by lia; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
  destruct (Z.eq_dec (e - a) (2 * (n + k + ns))) as [E|Ne].
  - wbr_tk Hc SF_36c6a SD_36c6a ltac:(apply br_eq_t; rewrite !U by lia; exact E).
    unfold btgt; imm_norm.
    apply (cmp_ok _ a n ns w s k).
    + gres. exact Hra.
    + okx Hk.
    + gres. exact H10.
    + gres. exact H5.
    + gres. exact H6.
    + gres. exact H7.
    + gres. exact H12.
    + gres. exact H16.
    + lia.
    + lia.
    + exact Hn.
    + lia.
    + exact Hw.
    + exact Hs.
    + exact Hkk.
    + intros i Hi. apply Rd; lia.
    + apply Q1. lia.
  - wbr_ft Hc SF_36c6a SD_36c6a ltac:(apply br_eq_f; rewrite !U by lia; exact Ne).
    destruct Hkk as [-> | ->].
    + wbr_tk Hc SF_36c6e SD_36c6e ltac:(apply br_eq_t; gres; rewrite H16; reflexivity).
      unfold btgt; imm_norm.
      apply exit0; [gres; exact Hra | okx Hk].
    + wbr_ft Hc SF_36c6e SD_36c6e ltac:(apply br_eq_f; gres; rewrite H16; vm_compute; discriminate).
      wsv Hc SF_36c72 SD_36c72 (W (2 * n)) ltac:(rewrite H5; unfold v_slli; rewrite U by lia; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
      wsv Hc SF_36c76 SD_36c76 (W (2 * n + 2)) ltac:(unfold v_addi; rewrite U by lia; reflexivity).
      wj Hc SF_36c7a SD_36c7a (0x36ce2%bv : word).
      wsv Hc SF_36ce2 SD_36ce2 (W 0) ltac:(reflexivity).
      wsv Hc SF_36ce4 SD_36ce4 (W 0) ltac:(reflexivity).
      destruct (Z.eq_dec (e - a) (2 * n + 2)) as [E2|Ne2].
      * wbr_ft Hc SF_36ce6 SD_36ce6 ltac:(apply br_ne_f; rewrite !U by lia; exact E2).
        apply (cmp_ok _ a n 0 w s 1).
        -- gres. exact Hra.
        -- okx Hk.
        -- gres. exact H10.
        -- gres. exact H5.
        -- gres. reflexivity.
        -- gres. exact H7.
        -- gres. exact H12.
        -- gres. exact H16.
        -- lia.
        -- lia.
        -- exact Hn.
        -- lia.
        -- exact Hw.
        -- exact Hs.
        -- right; reflexivity.
        -- intros i Hi. apply Rd; lia.
        -- apply Q2; [reflexivity | lia].
      * wbr_tk Hc SF_36ce6 SD_36ce6 ltac:(apply br_ne_t; rewrite !U by lia; exact Ne2).
        unfold btgt; imm_norm.
        apply (exit_a7 _ 0); [gres; exact Hra | okx Hk | gres; reflexivity | left; reflexivity].
Qed.

(** The length check of the to-home path, 0x36cda on: no store and no CACHE write. *)
Lemma len_home : forall regs a e n w Q,
  getr regs 1 = r -> (forall x, kept_reg x -> getr regs x = getr K x) ->
  getr regs 10 = W a -> getr regs 11 = W e -> getr regs 5 = W n -> getr regs 7 = W w ->
  getr regs 16 = W 0 ->
  0 <= a <= e -> e + 32 < 2^64 -> (n = 1 \/ n = 2) -> 0 <= w < 2^64 ->
  (forall i, 0 <= i -> a + 2 * i + 2 <= e -> exists v, 0 <= v < 65536 /\ half_at mem (a + 2 * i) v) ->
  (e = a + 2 * n -> emit_at mem a (take n w) -> Q) ->
  Run source_segs r mem rom (Result K Q) (mkst regs (0x36cda%bv : word) mem rom).
Proof.
  intros regs a e n w Q Hra Hk H10 H11 H5 H7 H16 Hae He Hn Hw Rd Q1.
  norm_pc_run.
  wsv Hc SF_36cda SD_36cda (W (e - a)) ltac:(rewrite H10, H11; unfold v_sub; rewrite !U by lia; reflexivity).
  wsv Hc SF_36cdc SD_36cdc (W (2 * n)) ltac:(rewrite H5; unfold v_slli; rewrite U by lia; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
  wsv Hc SF_36ce0 SD_36ce0 (W 0) ltac:(reflexivity).
  wsv Hc SF_36ce2 SD_36ce2 (W 0) ltac:(reflexivity).
  wsv Hc SF_36ce4 SD_36ce4 (W 0) ltac:(reflexivity).
  destruct (Z.eq_dec (e - a) (2 * n)) as [E|Ne].
  - wbr_ft Hc SF_36ce6 SD_36ce6 ltac:(apply br_ne_f; rewrite !U by lia; exact E).
    apply (cmp_ok _ a n 0 w 0 0).
    + gres. exact Hra.
    + okx Hk.
    + gres. exact H10.
    + gres. exact H5.
    + gres. reflexivity.
    + gres. exact H7.
    + gres. reflexivity.
    + gres. exact H16.
    + lia.
    + lia.
    + exact Hn.
    + lia.
    + exact Hw.
    + lia.
    + left; reflexivity.
    + intros i Hi. apply Rd; lia.
    + intro Hh. apply Q1; [lia|]. rewrite !app_nil_r in Hh. exact Hh.
  - wbr_tk Hc SF_36ce6 SD_36ce6 ltac:(apply br_ne_t; rewrite !U by lia; exact Ne).
    unfold btgt; imm_norm.
    apply (exit_a7 _ 0); [gres; exact Hra | okx Hk | gres; reflexivity | left; reflexivity].
Qed.
End Compare.
