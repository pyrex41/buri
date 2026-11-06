(** * Route A, rung 1: [operand_kind] (src/runtime/jit.c) on slot operands.

    The emitter's first decision for a move: where its source operand is.  The contract covers
    slot operands only; a constant operand goes through [ra_at], which this rung does not reach.
    It is a pure leaf with two loads, 12 to 16 instructions on a path.  [cached] is read at
    offset 272 and [homes] at 284 of the Emit struct, as the compiled code does. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec.
From LinuxProcessSemantics.Examples.emitter_ns Require Import emitter_code GcStep MoveStep GcTac.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation W z := (Z_to_bv 64 z).

Definition kind_of (cv hv x : Z) : Z :=
  if x =? cv then 21
  else if (2 <=? x) && (x <? hv + 2) then 21 - x
  else 151.

Lemma swrap_small : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap. rewrite bv_wrap_small.
  - change (bv_half_modulus 32) with (2^31). lia.
  - change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32). lia.
Qed.

Lemma vlw_small : forall c, 0 <= c < 2^31 -> v_lw (W c) = W c.
Proof. intros c Hc. unfold v_lw. rewrite (U c) by lia. rewrite swrap_small by lia. reflexivity. Qed.

Lemma vlw_big : forall c, 2^31 <= c < 2^32 -> 2^31 <= bv_unsigned (v_lw (W c)).
Proof.
  intros c Hc. unfold v_lw.
  assert (Hs : bv_swrap 32 c = c - 2^32).
  { unfold bv_swrap. change (bv_half_modulus 32) with (2^31). unfold bv_wrap. change (bv_modulus 32) with (2^32).
    replace (c + 2^31) with ((c - 2^31) + 1 * 2^32) by lia. rewrite Z_mod_plus_full.
    rewrite Z.mod_small by lia. lia. }
  rewrite (U c) by lia. rewrite Hs. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  replace (c - 2^32) with ((c - 2^32 + 2^64) + (-1) * 2^64) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.

Section Kind.
Context {fx : FPState}.

Lemma z_subw_at : forall sz segs regs pc mem rom w rd rs1 rs2 v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, sz) ->
  bv_eqb rd 0 = false ->
  v_subw (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w rd rs1 rs2 v Hwx Hecall Hdecode Hrd Hv. subst v.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  rewrite bv_eqb0_is_x0 in Hrd. rewrite Hrd.
  destruct (is_x0 rs1); cbv beta iota; destruct (is_x0 rs2); cbv beta iota;
    rewrite w_subw, b_npc; reflexivity.
Qed.

Definition kept_k (x : reg) : Prop := x <> 10%bv /\ x <> 12%bv /\ x <> 13%bv.

Lemma lts_f : forall x, 0 <= x < 2^31 -> branch_taken BC_LT (W x) (W 0) = false.
Proof.
  intros x Hx. cbn [branch_taken]. unfold bv_lts, bv_signed. rewrite !U by lia.
  apply Z.ltb_ge. unfold bv_swrap. rewrite bv_wrap_small.
  - rewrite bv_wrap_small; change (bv_half_modulus 64) with (2^63); [lia | change (bv_modulus 64) with (2^64); lia].
  - change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64). lia.
Qed.

Variables (mem rom : word -> option byte) (r : word).
Hypothesis Hc : mem_clear mem TL TH.
Hypothesis Hev : (bv_unsigned r mod 2 = 0)%Z.

Ltac okk regs0 := let x := fresh "x" in let Hx := fresh in
  intros x Hx; destruct Hx as (? & ? & ?); repeat (rewrite getr_other by assumption); reflexivity.

Ltac wlw F D aa vv bs Hrd Hb :=
  eapply run_step;
  [ reflexivity
  | eapply z_lw_at with (a := aa) (v := vv) (bs := bs);
    [ wxf_with Hc F | reflexivity | exact D | reflexivity
    | gres; imm_norm; unfold v_addi; rewrite U by lia; reflexivity
    | exact Hrd
    | rewrite U by lia; exact Hb ]
  | norm_pc_run ].

Theorem operand_kind_slot : forall regs e x cv hv bsc bsh,
  getr regs 1 = r -> getr regs 10 = W e -> getr regs 11 = W x ->
  0 <= e -> e + 300 < 2^64 -> 0 <= x < 2^31 -> 0 <= cv < 2^32 -> 0 <= hv <= 6 ->
  rdn source_segs mem (W (e + 272)) 4%nat = Some bsc -> bytes_le_to_Z bsc = cv ->
  rdn source_segs mem (W (e + 284)) 4%nat = Some bsh -> bytes_le_to_Z bsh = hv ->
  Run source_segs r mem rom
    (fun regs' => getr regs' 10 = W (kind_of cv hv x) /\
       (forall y, kept_k y -> getr regs' y = getr regs y))
    (mkst regs (0x1e5a0%bv : word) mem rom).
Proof.
  intros regs e x cv hv bsc bsh Hra H10 H11 He He2 Hx Hcv Hhv Rc Bc Rh Bh.
  assert (Hra2 : forall R0, getr R0 1 = r -> getr R0 1 = r) by auto.
  norm_pc_run.
  eapply run_step;
  [ reflexivity
  | eapply z_lw_at with (a := W (e + 272)) (v := W cv) (bs := bsc);
    [ wxf_with Hc SF_1e5a0 | reflexivity | exact SD_1e5a0 | reflexivity
    | gres; imm_norm; rewrite H10; unfold v_addi; rewrite U by lia; reflexivity
    | exact Rc
    | rewrite U by lia; exact Bc ]
  | norm_pc_run ].
  wsv Hc SF_1e5a4 SD_1e5a4 (W 21) ltac:(vm_compute; reflexivity).
  destruct (Z.eq_dec x cv) as [Eq|Ne].
  - assert (Hs : v_lw (W cv) = W cv) by (apply vlw_small; lia).
    wbr_tk Hc SF_1e5a6 SD_1e5a6 ltac:(apply br_eq_t; rewrite Hs, H11, !U by lia; lia).
    unfold btgt; imm_norm.
    wsv Hc SF_1e600 SD_1e600 (W 21) ltac:(vm_compute; reflexivity).
    wret Hc SF_1e602 SD_1e602 Hra Hev.
    apply run_done. split.
    + gres. unfold kind_of. rewrite (proj2 (Z.eqb_eq _ _) Eq). reflexivity.
    + okk regs.
  - assert (Hd : bv_unsigned (v_lw (W cv)) <> x).
    { destruct (Z.lt_ge_cases cv (2^31)) as [L|L].
      - rewrite vlw_small by lia. rewrite U by lia. lia.
      - pose proof (vlw_big cv ltac:(lia)). lia. }
    wbr_ft Hc SF_1e5a6 SD_1e5a6 ltac:(apply br_eq_f; rewrite H11, U by lia; lia).
    wbr_ft Hc SF_1e5aa SD_1e5aa ltac:(rewrite H11; apply lts_f; exact Hx).
    wsv Hc SF_1e5ae SD_1e5ae (W 2) ltac:(vm_compute; reflexivity).
    wsv Hc SF_1e5b0 SD_1e5b0 (W 151) ltac:(vm_compute; reflexivity).
    destruct (Z.lt_ge_cases x 2) as [X2|X2].
    + wbr_tk Hc SF_1e5b4 SD_1e5b4 ltac:(apply br_ltu_t; rewrite H11, !U by lia; lia).
      unfold btgt; imm_norm.
      wsv Hc SF_1e600 SD_1e600 (W 151) ltac:(vm_compute; reflexivity).
      wret Hc SF_1e602 SD_1e602 Hra Hev.
      apply run_done. split.
      * gres. unfold kind_of. rewrite (proj2 (Z.eqb_neq _ _) Ne).
        rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
      * okk regs.
    + wbr_ft Hc SF_1e5b4 SD_1e5b4 ltac:(apply br_ltu_f; rewrite H11, !U by lia; lia).
      eapply run_step;
      [ reflexivity
      | eapply z_lw_at with (a := W (e + 284)) (v := W hv) (bs := bsh);
        [ wxf_with Hc SF_1e5b8 | reflexivity | exact SD_1e5b8 | reflexivity
        | gres; imm_norm; rewrite H10; unfold v_addi; rewrite U by lia; reflexivity
        | exact Rh
        | rewrite U by lia; exact Bh ]
      | norm_pc_run ].
      wsv Hc SF_1e5bc SD_1e5bc (W (hv + 2)) ltac:(rewrite vlw_small by lia; unfold v_addiw; rewrite U by lia; rewrite swrap_small by lia; reflexivity).
      destruct (Z.lt_ge_cases x (hv + 2)) as [Xh|Xh].
      * wbr_tk Hc SF_1e5be SD_1e5be ltac:(apply br_ltu_t; rewrite H11, !U by lia; lia).
        unfold btgt; imm_norm.
        wsv Hc SF_1e604 SD_1e604 (W 21) ltac:(vm_compute; reflexivity).
        eapply run_step;
        [ reflexivity
        | eapply z_subw_at with (v := W (21 - x));
          [ wxf_with Hc SF_1e606 | reflexivity | exact SD_1e606 | reflexivity
          | gres; rewrite H11; unfold v_subw; rewrite !U by lia; rewrite swrap_small by lia; reflexivity ]
        | norm_pc_run ].
        wret Hc SF_1e60a SD_1e60a Hra Hev.
        apply run_done. split.
        -- gres. unfold kind_of. rewrite (proj2 (Z.eqb_neq _ _) Ne).
           rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
        -- okk regs.
      * wbr_ft Hc SF_1e5be SD_1e5be ltac:(apply br_ltu_f; rewrite H11, !U by lia; lia).
        wsv Hc SF_1e5c2 SD_1e5c2 (W 151) ltac:(vm_compute; reflexivity).
        wret Hc SF_1e5c6 SD_1e5c6 Hra Hev.
        apply run_done. split.
        -- gres. unfold kind_of. rewrite (proj2 (Z.eqb_neq _ _) Ne).
           rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
        -- okk regs.
Qed.
End Kind.
