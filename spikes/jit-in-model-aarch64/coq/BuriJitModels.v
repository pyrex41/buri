(* Shen/JIT Phase 0, AArch64 spike: sequential behavior of words from
   BuriJitWords.v. Evidence kind of every theorem: model theorem. Same scope
   limits as BuriJitWords.v, plus the premises each statement names. *)
Require Import SailStdpp.Base SailStdpp.Real SailStdpp.ConcurrencyInterfaceTypes
  SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins.
Require Import armv9_types arm_extras armv9.
From stdpp.bitvector Require Import definitions tactics.
Require Import BuriArm.BuriArmAdds BuriArm.BuriArmDecode BuriArm.BuriArmSeq BuriArm.BuriArmFastPath
  BuriArm.BuriJitWords.
Import Defs.
Open Scope Z.

Transparent Z_to_bv bv_0 bv_succ bv_pred bv_add bv_sub bv_opp bv_mul bv_divu bv_modu
  bv_divs bv_quots bv_mods bv_rems bv_shiftl bv_shiftr bv_ashiftr bv_or bv_and bv_xor
  bv_not bv_zero_extend bv_sign_extend bv_extract bv_concat bv_add_Z bv_sub_Z bv_mul_Z
  bool_to_bv bv_to_bits.

(* ---------------- sequential behavior ---------------- *)
Ltac word_iff dec :=
  split;
  [ intros H; rewrite dec in H; sx_bwd H;
    match type of H with _ /\ _ => destruct H as [-> ->] end; split; [reflexivity | reflexivity]
  | intros [-> ->]; rewrite dec; eapply sexec_eq; [sx_fwd | reflexivity] ].

Ltac word_branch_iff dec :=
  match goal with Hc : el2_cfg ?rs |- _ =>
    destruct Hc as (HF0 & HVHE & HBRBE & HSPE & HnRW & HEL & HTBI);
    destruct (vec_access_dec (register_lookup FeatureImpl rs) (num_of_Feature FEAT_PAuth)) eqn:EPA
  end;
  word_iff dec.

(* mov w0, #42 writes X0 := 42, for every state. The final value is the model's
   own expression; mov_value_is_42 computes it. *)
Definition mov_value : mword 64 :=
  zero_extend
    (if generic_eq MoveWideOp_Z MoveWideOp_N
     then not_vec (update_subrange_vec_dec (Zeros 32) (0 + 15) 0 (autocast (Ox"002A" : mword 16)))
     else update_subrange_vec_dec (Zeros 32) (0 + 15) 0 (autocast (Ox"002A" : mword 16))) 64.

Lemma mov_value_is_42 : mov_value = Ox"000000000000002A".
Proof. vm_compute. reflexivity. Qed.

Definition mov_final (rs : regstate) : regstate :=
  register_set R0 mov_value (register_set SEE 698 rs).

Theorem mov_model pc rs rs' a : Z.ltb (register_lookup SEE rs) 698 = true ->
  sexec rs (__DecodeA64 pc w_mov) rs' a <-> rs' = mov_final rs /\ a = tt.
Proof. intros Hsee. word_iff mov_decode. Qed.

(* isb changes no register beyond the decoder's SEE retry state, when branch
   recording (FEAT_BRBE) and statistical profiling (FEAT_SPE) are absent. *)
Definition isb_final (rs : regstate) : regstate := register_set SEE 483 rs.

Theorem isb_model pc rs rs' a : Z.ltb (register_lookup SEE rs) 483 = true ->
  vec_access_dec (register_lookup FeatureImpl rs) (num_of_Feature FEAT_BRBE) = false ->
  vec_access_dec (register_lookup FeatureImpl rs) (num_of_Feature FEAT_SPE) = false ->
  sexec rs (__DecodeA64 pc w_isb) rs' a <-> rs' = isb_final rs /\ a = tt.
Proof. intros Hsee HBRBE HSPE. word_iff isb_decode. Unshelve. all: exact tt. Qed.

(* ret and blr, under Búri's existing EL2 configuration premise, with
   FEAT_GCS (guarded control stack) absent. A hosted
   process runs at EL0, so these do not yet cover the process case. *)
(* The branch target, as the model's own expression; branch_target_id: it is the
   register's value. *)
Definition branch_target (x : mword 64) : mword 64 :=
  subrange_vec_dec (autocast (subrange_vec_dec x (64 - 1) 0) : mword 64) 63 0.

Lemma branch_target_id x : branch_target x = x.
Proof.
  unfold branch_target. rewrite subrange_full_64.
  pose proof (subrange_full_64 x) as H.
  rewrite (autocast_eq _ eq_refl), cast_Z_refl in H. exact H.
Qed.

Definition ret_final (rs : regstate) : regstate :=
  branch_taken BranchType_RET (branch_target (register_lookup R30 rs))
    (register_set BTypeNext ('b"00") (register_set SEE 94 rs)).

Theorem ret_model pc rs rs' a : Z.ltb (register_lookup SEE rs) 94 = true -> el2_cfg rs ->
  vec_access_dec (register_lookup FeatureImpl rs) (num_of_Feature FEAT_GCS) = false ->
  sexec rs (__DecodeA64 pc w_ret) rs' a <-> rs' = ret_final rs /\ a = tt.
Proof. intros Hsee Hc HGCS. unfold ret_final. word_branch_iff ret_decode. Qed.

Definition blr_final (rs : regstate) : regstate :=
  branch_taken BranchType_INDCALL (branch_target (register_lookup R5 rs))
    (register_set BTypeNext ('b"10")
      (register_set R30 (zero_extend (add_vec_int (register_lookup _PC rs) 4) 64) (register_set SEE 90 rs))).

Theorem blr_model pc rs rs' a : Z.ltb (register_lookup SEE rs) 90 = true -> el2_cfg rs ->
  vec_access_dec (register_lookup FeatureImpl rs) (num_of_Feature FEAT_GCS) = false ->
  sexec rs (__DecodeA64 pc w_blr) rs' a <-> rs' = blr_final rs /\ a = tt.
Proof. intros Hsee Hc HGCS. unfold blr_final. word_branch_iff blr_decode. Qed.

Print Assumptions mov_value_is_42.
Print Assumptions mov_model.
Print Assumptions isb_model.
Print Assumptions branch_target_id.
Print Assumptions ret_model.
Print Assumptions blr_model.
