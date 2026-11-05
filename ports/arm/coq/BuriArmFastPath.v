(* E2E-20 Wave D: the sail-arm Armv9.4-A model's exact sequential behaviour
   on eight of the nine Chez fast-path words (all but the load at +0x1c).

   NOT a scripts/prove module (docs/ARM-FOUNDATION.md section 12; checked by
   scripts/check-arm.sh Part B).

   For each word w at Chez offset XXXX, chez_XXXX_model is an IFF:

       sexec rs (__DecodeA64 pc w) rs' a  <->  rs' = XXXX_final rs /\ a = tt

   under the stated premises.  sexec (BuriArmSeq.v) is equivalent to
   coq-sail's own trace semantics Interface.iTrace_match restricted to a
   single-threaded register file (sexec_sound / sexec_complete).  So the
   left-to-right direction is the converse ("the model has no other
   behaviour"), and right-to-left says the behaviour exists.  Every guard the
   decoder or execute function evaluates is decided by computation or by a
   stated premise; none is assumed.

   Premises.
   * SEE below the decoder's guard value K for the word (the retry
     mechanism: SEE := K is the first write).
   * Branch words only: el2_cfg rs, the configuration the Islaris EL2 trace
     was generated under, stated on the model's registers: FEAT_AA64EL0
     implemented; FEAT_VHE, FEAT_BRBE and FEAT_SPE not implemented; PSTATE.nRW
     = 0 (AArch64); PSTATE.EL = EL2; TCR_EL2.TBI = 0.  FEAT_PAuth is NOT a
     premise: both values are covered (with PAuth the model also reads
     TCR_EL2.TBID; the final state is the same).  br x10 also needs
     InGuardedPage = false (with true, BTypeNext would be 0b11 instead of
     0b01).
   Final states are written as the model's own register writes in order.
   For the branch words the target is the model's own expression, the PC
   plus the offset truncated to 64 bits, or X10.

   Not covered here: the PC advance after a non-branch word (BuriArmPC.v);
   the load at +0x1c (its execute path goes through address translation and
   an Interface.MemRead outcome; see section 12 of ARM-FOUNDATION).

   Trusted: Coq 8.19.0, coq-sail 0.19 and the Sail-to-Coq translation of
   sail-arm 7d058164, and the three Coq standard-library Reals axioms that
   every statement mentioning __DecodeA64 inherits. *)
Require Import SailStdpp.Base.
Require Import armv9_types armv9.
From stdpp.bitvector Require Import definitions tactics.
Require Import BuriArm.BuriArmAdds BuriArm.BuriArmDecode BuriArm.BuriArmSeq.
Import Defs.
Open Scope Z.

(* stdpp marks its bitvector operations Opaque (for its own automation).
   Making them transparent in this file lets head reduction evaluate the
   model's closed bit comparisons; it changes no definition. *)
Transparent Z_to_bv bv_0 bv_succ bv_pred bv_add bv_sub bv_opp bv_mul bv_divu bv_modu
  bv_divs bv_quots bv_mods bv_rems bv_shiftl bv_shiftr bv_ashiftr bv_or bv_and bv_xor
  bv_not bv_zero_extend bv_sign_extend bv_extract bv_concat bv_add_Z bv_sub_Z bv_mul_Z
  bool_to_bv bv_to_bits.

(* ---------------------------------------------------------------- *)
(* The four PSTATE flag writes every flag-setting data-processing
   instruction performs, in the model's order N, Z, C, V. *)
Definition psN (q : mword 4) (p : ProcState) := {[ p with ProcState_N := subrange_vec_dec q 3 3 ]}.
Definition psZ (q : mword 4) (p : ProcState) := {[ p with ProcState_Z := subrange_vec_dec q 2 2 ]}.
Definition psC (q : mword 4) (p : ProcState) := {[ p with ProcState_C := subrange_vec_dec q 1 1 ]}.
Definition psV (q : mword 4) (p : ProcState) := {[ p with ProcState_V := subrange_vec_dec q 0 0 ]}.
Definition set_nzcv (q : mword 4) (rs : regstate) : regstate :=
  let p := register_lookup PSTATE rs in
  register_set PSTATE (psV q (psC q (psZ q (psN q p))))
  (register_set PSTATE (psC q (psZ q (psN q p)))
  (register_set PSTATE (psZ q (psN q p))
  (register_set PSTATE (psN q p) rs))).

Lemma nzcv_N q p : ProcState_N (psV q (psC q (psZ q (psN q p)))) = subrange_vec_dec q 3 3.
Proof. destruct p; reflexivity. Qed.
Lemma nzcv_Z q p : ProcState_Z (psV q (psC q (psZ q (psN q p)))) = subrange_vec_dec q 2 2.
Proof. destruct p; reflexivity. Qed.
Lemma nzcv_C q p : ProcState_C (psV q (psC q (psZ q (psN q p)))) = subrange_vec_dec q 1 1.
Proof. destruct p; reflexivity. Qed.
Lemma nzcv_V q p : ProcState_V (psV q (psC q (psZ q (psN q p)))) = subrange_vec_dec q 0 0.
Proof. destruct p; reflexivity. Qed.

Definition logic_flags (r : mword 64) : mword 4 :=
  concat_vec (concat_vec (vec_of_bits [access_vec_dec r 63] : mword 1) (IsZeroBit r)) ('b"00" : mword 2).

(* +0x00 cmp x23, #2 = SUBS XZR, X23, #2 *)
Definition cmp_result (x : mword 64) := AddWithCarry x (not_vec (Ox"0000000000000002" : mword 64)) ('b"1").
Definition chez_0000_final (rs : regstate) : regstate :=
  set_nzcv (snd (cmp_result (register_lookup R23 rs))) (register_set SEE 21 rs).

(* +0x08 orr x30, x0, x1 *)
Definition chez_0008_final (rs : regstate) : regstate :=
  register_set R30 (or_vec (register_lookup R0 rs) (register_lookup R1 rs)) (register_set SEE 55 rs).

(* +0x0c tst x30, #7 = ANDS XZR, X30, #7 *)
Definition tst_result (x : mword 64) : mword 64 := and_vec x (Ox"0000000000000007").
Definition chez_000c_final (rs : regstate) : regstate :=
  set_nzcv (logic_flags (tst_result (register_lookup R30 rs))) (register_set SEE 41 rs).

(* +0x14 adds x23, x0, x1 *)
Definition chez_0014_final (rs : regstate) : regstate :=
  let r := AddWithCarry (register_lookup R0 rs) (register_lookup R1 rs) ('b"0") in
  register_set R23 (fst r) (set_nzcv (snd r) (register_set SEE 15 rs)).

(* Branches.  A taken branch writes Branchtypetaken, _PC and __BranchTaken. *)
Definition branch_taken (ty : BranchType) (target : mword 64) (rs : regstate) : regstate :=
  register_set __BranchTaken true (register_set _PC target (register_set Branchtypetaken ty rs)).
Definition pc_plus (rs : regstate) (off : mword 64) : mword 64 :=
  subrange_vec_dec (add_vec (register_lookup _PC rs) off) 63 0.
Definition flag_set (b : mword 1) : bool := eq_vec b ('b"1").

(* +0x04 / +0x10 b.ne: taken iff Z = 0.  +0x18 b.vs: taken iff V = 1. *)
Definition bcond_final (taken : bool) (off : mword 64) (rs : regstate) : regstate :=
  let rs1 := register_set SEE 69 rs in
  if taken then branch_taken BranchType_DIR (pc_plus rs off) rs1 else rs1.
Definition chez_0004_final rs :=
  bcond_final (negb (flag_set (ProcState_Z (register_lookup PSTATE rs)))) (Ox"0000000000000080") rs.
Definition chez_0010_final rs :=
  bcond_final (negb (flag_set (ProcState_Z (register_lookup PSTATE rs)))) (Ox"0000000000000014") rs.
Definition chez_0018_final rs :=
  bcond_final (flag_set (ProcState_V (register_lookup PSTATE rs))) (Ox"000000000000000C") rs.

(* +0x20 br x10 *)
Definition chez_0020_final (rs : regstate) : regstate :=
  branch_taken BranchType_INDIR (subrange_vec_dec (register_lookup R10 rs) 63 0)
    (register_set BTypeNext ('b"01") (register_set SEE 92 rs)).

Definition el2_cfg (rs : regstate) : Prop :=
  let fi := register_lookup FeatureImpl rs in
  let p := register_lookup PSTATE rs in
  vec_access_dec fi (num_of_Feature FEAT_AA64EL0) = true /\
  vec_access_dec fi (num_of_Feature FEAT_VHE) = false /\
  vec_access_dec fi (num_of_Feature FEAT_BRBE) = false /\
  vec_access_dec fi (num_of_Feature FEAT_SPE) = false /\
  eq_vec (ProcState_nRW p) ('b"1") = false /\
  ProcState_EL p = 'b"10" /\
  eq_vec (_get_TCR_EL2_Type_TBI (register_lookup TCR_EL2 rs)) ('b"1") = false.

(* ---------------------------------------------------------------- *)
Ltac fin := rewrite ?subrange_full_64, ?shiftl_0_64, ?zero_extend_64;
  match goal with r : regstate |- _ => destruct r end; reflexivity.

Lemma DecodeBitMasks_7 :
  DecodeBitMasks ('b"1") ('b"000010") ('b"000000") true 64 =
  returnM (Ox"0000000000000007", Ox"0000000000000007").
Proof. vm_compute. reflexivity. Qed.

Ltac model_iff dec :=
  split;
  [ intros H; rewrite dec in H; rewrite ?DecodeShift_LSL, ?DecodeBitMasks_7 in H; sx_bwd H;
    match type of H with _ /\ _ => destruct H as [-> ->] end; split; [fin|reflexivity]
  | intros [-> ->]; rewrite dec; rewrite ?DecodeShift_LSL, ?DecodeBitMasks_7;
    eapply sexec_eq; [sx_fwd | fin] ].

Theorem chez_0000_model pc rs rs' a : Z.ltb (register_lookup SEE rs) 21 = true ->
  sexec rs (__DecodeA64 pc chez_word_0000) rs' a <-> rs' = chez_0000_final rs /\ a = tt.
Proof. intros Hsee. model_iff chez_0000_decode. Qed.

Theorem chez_0008_model pc rs rs' a : Z.ltb (register_lookup SEE rs) 55 = true ->
  sexec rs (__DecodeA64 pc chez_word_0008) rs' a <-> rs' = chez_0008_final rs /\ a = tt.
Proof. intros Hsee. model_iff chez_0008_decode. Qed.

Theorem chez_000c_model pc rs rs' a : Z.ltb (register_lookup SEE rs) 41 = true ->
  sexec rs (__DecodeA64 pc chez_word_000c) rs' a <-> rs' = chez_000c_final rs /\ a = tt.
Proof. intros Hsee. model_iff chez_000c_decode. Qed.

Theorem chez_0014_model pc rs rs' a : Z.ltb (register_lookup SEE rs) 15 = true ->
  sexec rs (__DecodeA64 pc chez_word_0014) rs' a <-> rs' = chez_0014_final rs /\ a = tt.
Proof. intros Hsee. model_iff chez_0014_decode. Qed.

Ltac branch_iff dec :=
  match goal with Hc : el2_cfg ?rs |- _ =>
    destruct Hc as (HF0 & HVHE & HBRBE & HSPE & HnRW & HEL & HTBI);
    destruct (vec_access_dec (register_lookup FeatureImpl rs) (num_of_Feature FEAT_PAuth)) eqn:EPA
  end;
  model_iff dec.

Theorem chez_0004_model pc rs rs' a : Z.ltb (register_lookup SEE rs) 69 = true -> el2_cfg rs ->
  sexec rs (__DecodeA64 pc chez_word_0004) rs' a <-> rs' = chez_0004_final rs /\ a = tt.
Proof.
  intros Hsee Hc. unfold chez_0004_final, bcond_final, flag_set.
  destruct (eq_vec (ProcState_Z (register_lookup PSTATE rs)) ('b"1")) eqn:EZ; cbn [negb];
  branch_iff chez_0004_decode.
Qed.

Theorem chez_0010_model pc rs rs' a : Z.ltb (register_lookup SEE rs) 69 = true -> el2_cfg rs ->
  sexec rs (__DecodeA64 pc chez_word_0010) rs' a <-> rs' = chez_0010_final rs /\ a = tt.
Proof.
  intros Hsee Hc. unfold chez_0010_final, bcond_final, flag_set.
  destruct (eq_vec (ProcState_Z (register_lookup PSTATE rs)) ('b"1")) eqn:EZ; cbn [negb];
  branch_iff chez_0010_decode.
Qed.

Theorem chez_0018_model pc rs rs' a : Z.ltb (register_lookup SEE rs) 69 = true -> el2_cfg rs ->
  sexec rs (__DecodeA64 pc chez_word_0018) rs' a <-> rs' = chez_0018_final rs /\ a = tt.
Proof.
  intros Hsee Hc. unfold chez_0018_final, bcond_final, flag_set.
  destruct (eq_vec (ProcState_V (register_lookup PSTATE rs)) ('b"1")) eqn:EV;
  branch_iff chez_0018_decode.
Qed.

Theorem chez_0020_model pc rs rs' a : Z.ltb (register_lookup SEE rs) 92 = true -> el2_cfg rs ->
  register_lookup InGuardedPage rs = false ->
  sexec rs (__DecodeA64 pc chez_word_0020) rs' a <-> rs' = chez_0020_final rs /\ a = tt.
Proof.
  intros Hsee Hc HG. unfold chez_0020_final. branch_iff chez_0020_decode.
Qed.

Print Assumptions chez_0000_model.
Print Assumptions chez_0004_model.
Print Assumptions chez_0008_model.
Print Assumptions chez_000c_model.
Print Assumptions chez_0010_model.
Print Assumptions chez_0014_model.
Print Assumptions chez_0018_model.
Print Assumptions chez_0020_model.
Print Assumptions DecodeBitMasks_7.
Print Assumptions nzcv_N.
Print Assumptions nzcv_Z.
Print Assumptions nzcv_C.
Print Assumptions nzcv_V.
