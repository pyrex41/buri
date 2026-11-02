(* E2E-20 Wave C: a checked trace-to-model bridge for one instruction.

   NOT a scripts/prove module.  Toolchain: Coq 8.19.0 with the Islaris pins
   (nix/arm/islaris.nix), coq-sail 0.19 src-stdpp and the sail-arm 7d058164
   arm-v9.4-a Coq model compiled IN THE SAME Coq 8.19.0 (nix/arm/sail-model.nix),
   so the Islaris trace semantics and the Sail model live in one Coq
   environment and one theorem can mention both.  Checked only by the opt-in
   scripts/check-arm.sh.

   Subject: Chez kl:buri-arm-add+0x14, word 0xab010017 (ADDS X23, X0, X1).
   * Model side: BuriArmAdds.chez_0014_decode / chez_0014_execute prove
     that the sail-arm Armv9.4-A decoder on this word is exactly the
     program adds_x23_x0_x1 behind the SEE guard, and chez_0014_adds_trace
     gives its (only) register trace: reads R0, R1, PSTATE; writes
     PSTATE.{N,Z,C,V} := the bits of the model's AddWithCarry and
     R23 := adds_sum x0 x1.
   * Trace side: isla.instructions.buri_chez_add.a14 is the isla trace that
     the Islaris theorem buri_chez_add_fast_path consumes (isla b8e614bd on
     the Armv8.5 IR, Islaris config, EL2/MMU off).  It is data here.  Its
     behaviour is given by Islaris's own small-step relation `seq_step`
     (isla.opsem), with no instruction table and no memory.

   chez_0014_bridge (universal over pc, SEE value < 15, x0, x1, PSTATE p,
   prior R23, prior PC and the rest of the isla PSTATE struct): the model's
   decoder accepts the trace adds_events (as in chez_0014_adds_trace) AND
   Islaris's semantics runs the isla trace a14 to its end, never blocking,
   from any isla register map holding those values, to exactly the map in
   which R23 and PSTATE.{N,Z,C,V} hold THE MODEL'S written values and _PC
   is advanced by 4.  Direction: every behaviour of the model on this word
   (it has exactly one register trace, by the decode/execute equations) is
   realised by a complete run of the trace, which is the direction needed to
   carry a statement about ALL trace runs (Islaris's) over to the model.
   The converse (that the trace admits no other complete run) is not
   proved here.

   Version pairing: trace = isla b8e614bd on isla-snapshots d8b31014
   armv8p5.ir (Armv8.5); model = sail-arm 7d058164 arm-v9.4-a Coq.  The
   bridge is a theorem relating THESE two artifacts for THIS word; it does
   not relate the two Sail IR versions in general.

   Not covered (explicit):
   * The _PC := _PC + 4 step of the trace comes from the IR's
     isla_footprint_no_init wrapper (`if not __PC_changed then _PC += 4`).
     The v9.4 model's counterpart is the PC advance in __InstructionExecute,
     which also runs fetch, debug, PMU, SPE, BTYPE and single-step logic;
     that part is NOT proved.  Neither is the SEE initialisation (isla's
     wrapper sets SEE := -1; here SEE < 15 is a premise).
   * The isla register-name/encoding map is part of the statement: Sail
     register R0 is isla "R0", PSTATE is an isla struct whose first four
     fields are N, Z, C, V.
   * Only this word.  The other eight fast-path words are not bridged
     (see docs/ARM-FOUNDATION.md section 11).
   Trusted: Coq 8.19.0 kernel, the Islaris opsem definitions (they are the
   semantics Islaris's adequacy theorem uses), coq-sail 0.19 and the
   Sail-to-Coq translation, plus the three Coq standard-library Reals
   axioms that every statement mentioning __DecodeA64 inherits. *)
From isla Require Import opsem automation.
Require Import isla.instructions.buri_chez_add.a14.
Require Import SailStdpp.Base.
Require Import armv9_types armv9.
Require Import BuriArm.BuriArmAdds BuriArm.BuriArmBridgeValues.
Import Defs.
Open Scope Z.

(* ---------------------------------------------------------------- *)
(* Complete, non-blocking runs of one isla trace under Islaris's seq_step. *)
Definition σ0 : seq_global_state := {| seq_instrs := ∅; seq_mem := ∅ |}.

Definition lst (t : isla_trace) (regs : reg_map) : seq_local_state :=
  {| seq_trace := t; seq_regs := regs; seq_pc_reg := "_PC"; seq_nb_state := false |}.

Inductive run_to_end : isla_trace → reg_map → reg_map → Prop :=
| RunEnd regs : run_to_end tnil regs regs
| RunStep t regs t' regs' r :
    seq_step (lst t regs) σ0 [] (lst t' regs') σ0 [] →
    run_to_end t' regs' r → run_to_end t regs r.

Lemma RunEnd' regs r : regs = r → run_to_end tnil regs r.
Proof. intros ->. constructor. Qed.

Lemma step_none t regs t' :
  trace_step t regs None t' → seq_step (lst t regs) σ0 [] (lst t' regs) σ0 [].
Proof.
  intros H. refine (SeqStep σ0 (lst t regs) None t' None (lst t' regs) σ0 _ _ _); done.
Qed.

Lemma step_read t regs t' r al v v' vr :
  trace_step t regs (Some (LReadReg r al v)) t' →
  regs !! r = Some v' → read_accessor al v' = Some vr → read_accessor al v = Some vr →
  seq_step (lst t regs) σ0 [] (lst t' regs) σ0 [].
Proof.
  intros H ???.
  refine (SeqStep σ0 (lst t regs) (Some (LReadReg r al v)) t' None (lst t' regs) σ0 _ _ _);
    [done|done|].
  eexists _, _, _. split_and!; [done|done|done|done|done|]. left. done.
Qed.

Lemma step_write t regs t' r al v v' vnew v'' :
  trace_step t regs (Some (LWriteReg r al v)) t' →
  regs !! r = Some v' → read_accessor al v = Some vnew → write_accessor al v' vnew = Some v'' →
  seq_step (lst t regs) σ0 [] (lst t' (<[r := v'']> regs)) σ0 [].
Proof.
  intros H ???.
  refine (SeqStep σ0 (lst t regs) (Some (LWriteReg r al v)) t' None
            (lst t' (<[r := v'']> regs)) σ0 _ _ _); [done|done|].
  eexists _, _, _. split_and!; done.
Qed.

Ltac norm := cbn [subst_trace subst_val_event subst_val_smt subst_val_valu subst_val_exp
  subst_val_base_val eq_var_name Z.eqb Pos.eqb List.map fst snd].
Ltac evlazy := lazy [eval_exp' mapM mbind option_bind eval_unop eval_manyop eval_binop
  option_fmap option_map fmap mret option_ret guard_or mthrow option_mfail foldl bvn_to_bv
  decide decide_rel BinNat.N.eq_dec N.eq_dec N_rec N_rect bvn_n sumbool_rec sumbool_rect
  BinPos.Pos.eq_dec Pos.eq_dec positive_rect positive_rec eq_rect eq_ind_r eq_ind eq_sym
  bvn_val N.add N.sub Pos.add Pos.succ Pos.sub_mask Pos.double_mask Pos.succ_double_mask
  Pos.pred_double Pos.double_pred_mask].
Ltac decl v := eapply RunStep; [apply step_none; apply (DeclareConstBitVecS' v)|]; norm.
Ltac defc := eapply RunStep;
  [apply step_none; eapply DefineConstS; apply eval_exp'_sound; evlazy; reflexivity|]; norm.
Ltac rd := eapply RunStep;
  [eapply step_read; [econstructor | by simplify_map_eq | reflexivity | reflexivity] |]; norm.
Ltac wr := eapply RunStep;
  [eapply step_write; [econstructor | by simplify_map_eq | reflexivity | reflexivity] |]; norm.

(* The value lemmas of BuriArmBridgeValues, restated with the exact shape
   (and implicit indices) of the terms Islaris's evaluator produces. *)
Section shapes.
Context (x0 x1 : bv 64).
Lemma isla_sum_model' :
  bv_extract 0 64 (bv_zero_extend 128 x0 + bv_zero_extend 128 x1)%bv = adds_sum x0 x1.
Proof. apply isla_sum_model. Qed.
Lemma isla_N' :
  bv_or (bv_and 0 (bv_not 1)) (bv_extract 0 1 (adds_sum x0 x1 ≫ bv_extract 0 64 (63 : bv 128))) =
  (vec_of_bits [access_vec_dec (adds_sum x0 x1) 63] : mword 1).
Proof. apply isla_N. Qed.
Lemma isla_Z' :
  ite (bool_decide (adds_sum x0 x1 = 0%bv)) (1%bv : bv 1) 0%bv =
  (if IsZero (adds_sum x0 x1) then 'b"1" else 'b"0" : mword 1).
Proof. unfold ite. apply isla_Z. Qed.
Lemma isla_C' :
  ite (bool_decide (bv_zero_extend 128 (adds_sum x0 x1) =
                    (bv_zero_extend 128 x0 + bv_zero_extend 128 x1)%bv)) (0%bv : bv 1) 1%bv =
  (if Z.eqb (uint (adds_sum x0 x1)) (@uint 64 x0 + @uint 64 x1 + uint ('b"0" : mword 1))
   then 'b"0" else 'b"1" : mword 1).
Proof. unfold ite. apply isla_C. Qed.
Lemma isla_V' :
  ite (bool_decide (bv_sign_extend 128 (adds_sum x0 x1) =
                    (bv_sign_extend 128 x0 + bv_sign_extend 128 x1)%bv)) (0%bv : bv 1) 1%bv =
  (if Z.eqb (sint (adds_sum x0 x1)) (@sint 64 x0 + @sint 64 x1 + uint ('b"0" : mword 1))
   then 'b"0" else 'b"1" : mword 1).
Proof. unfold ite. apply isla_V. Qed.
Lemma nzcv_shape :
  adds_nzcv x0 x1 =
  bv_concat 4 (bv_concat 3 (bv_concat 2
     (vec_of_bits [access_vec_dec (adds_sum x0 x1) 63] : mword 1)
     (if IsZero (adds_sum x0 x1) then 'b"1" else 'b"0" : mword 1))
     (if Z.eqb (uint (adds_sum x0 x1)) (@uint 64 x0 + @uint 64 x1 + uint ('b"0" : mword 1))
      then 'b"0" else 'b"1" : mword 1))
     (if Z.eqb (sint (adds_sum x0 x1)) (@sint 64 x0 + @sint 64 x1 + uint ('b"0" : mword 1))
      then 'b"0" else 'b"1" : mword 1).
Proof. reflexivity. Qed.
Lemma nzcv_fields p :
  ProcState_N (ps_NZCV x0 x1 p) = bv_extract 3 1 (adds_nzcv x0 x1) ∧
  ProcState_Z (ps_NZCV x0 x1 p) = bv_extract 2 1 (adds_nzcv x0 x1) ∧
  ProcState_C (ps_NZCV x0 x1 p) = bv_extract 1 1 (adds_nzcv x0 x1) ∧
  ProcState_V (ps_NZCV x0 x1 p) = bv_extract 0 1 (adds_nzcv x0 x1).
Proof. destruct p. split_and!; reflexivity. Qed.
End shapes.

(* ---------------------------------------------------------------- *)
Definition pstate_isla (n z c v : bv 1) (rest : list (string * valu)) : valu :=
  RegVal_Struct (("N", RVal_Bits n) :: ("Z", RVal_Bits z) :: ("C", RVal_Bits c) ::
                 ("V", RVal_Bits v) :: rest).

Definition isla_regs_after (x0 x1 pcv : bv 64) (p : ProcState) rest (regs : reg_map) : reg_map :=
  let q := ps_NZCV x0 x1 p in
  <["_PC" := RVal_Bits (pcv + 4)%bv]>
  (<["R23" := RVal_Bits (adds_sum x0 x1)]>
  (<["PSTATE" := pstate_isla (ProcState_N q) (ProcState_Z q) (ProcState_C q) (ProcState_V q) rest]>
   regs)).

Section bridge.
Context (x0 x1 pcv r23 : bv 64) (p : ProcState) (rest : list (string * valu)) (regs : reg_map).
Hypothesis HR0 : regs !! "R0" = Some (RVal_Bits x0).
Hypothesis HR1 : regs !! "R1" = Some (RVal_Bits x1).
Hypothesis HPC : regs !! "_PC" = Some (RVal_Bits pcv).
Hypothesis HR23 : regs !! "R23" = Some (RVal_Bits r23).
Hypothesis HPS : regs !! "PSTATE" =
  Some (pstate_isla (ProcState_N p) (ProcState_Z p) (ProcState_C p) (ProcState_V p) rest).

Lemma a14_run : run_to_end a14 regs (isla_regs_after x0 x1 pcv p rest regs).
Proof using HPC HPS HR0 HR1 HR23.
  unfold a14, pstate_isla in *.
  decl x0. rd. defc. decl x1. rd. defc. defc. defc. defc.
  defc. wr. defc. wr. defc. wr. defc. wr. defc. wr.
  decl pcv. rd. defc. wr.
  apply RunEnd'. unfold isla_regs_after, pstate_isla.
  rewrite !insert_insert.
  rewrite !isla_sum_model' !isla_N' !isla_Z' !isla_C' !isla_V'.
  (* What is left is closed by conversion: list inserts, the record updates
     of ps_NZCV, and the model's own AddWithCarry flag bits.  *)
  rewrite -!nzcv_shape.
  destruct (nzcv_fields x0 x1 p) as (-> & -> & -> & ->).
  repeat f_equal.
  all: try (apply bv_eq; reflexivity).
  all: cbn [insert list_insert]; reflexivity.
Qed.
End bridge.

Theorem chez_0014_bridge pc (see : Z) (x0 x1 pcv r23 : bv 64) (p : ProcState) rest regs :
  see < 15 →
  regs !! "R0" = Some (RVal_Bits x0) → regs !! "R1" = Some (RVal_Bits x1) →
  regs !! "_PC" = Some (RVal_Bits pcv) → regs !! "R23" = Some (RVal_Bits r23) →
  regs !! "PSTATE" =
    Some (pstate_isla (ProcState_N p) (ProcState_Z p) (ProcState_C p) (ProcState_V p) rest) →
  Interface.iTrace_match (__DecodeA64 pc chez_word_0014) (adds_events see x0 x1 p, inl tt) ∧
  run_to_end a14 regs (isla_regs_after x0 x1 pcv p rest regs).
Proof.
  intros Hsee ?????. split.
  - by apply chez_0014_adds_trace.
  - by apply a14_run with (r23 := r23).
Qed.

Print Assumptions a14_run.
Print Assumptions chez_0014_bridge.
