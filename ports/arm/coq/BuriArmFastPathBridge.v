(* E2E-20 Wave D: trace-to-model bridges for eight Chez fast-path words.

   NOT a scripts/prove module (docs/ARM-FOUNDATION.md section 12; checked by
   scripts/check-arm.sh Part B).

   Each trace below is the exact file the Islaris theorem
   buri_chez_add_fast_path consumes (isla b8e614bd, Armv8.5 IR, Islaris's EL2
   config); check-arm.sh checks every one against SHA256SUMS.  For each word
   w at Chez offset XXXX, chez_XXXX_bridge says, for every model register
   record rs and isla register map regs that agree (BuriArmBridgeLib.agree:
   R0..R30, _PC, PSTATE.{N,Z,C,V}) and every byte memory:
   (1) the trace has a complete, never-blocking run under Islaris's seq_step
       from regs, and
   (2) EVERY such run ends in a map that agrees with the model's sequential
       result chez_XXXX_final rs (BuriArmFastPath.chez_XXXX_model, an IFF),
       followed by the model's own PC step: pc_next for a word that never
       branches, pc_after (skip if __BranchTaken) for the branches
       (BuriArmPC.pc_part_not_taken / pc_part_after, InstructionExecute_pc_part).
   So, on the agreed registers, the set of complete trace runs and the set of
   model behaviours coincide in their results, in both directions.

   Premises that are not part of agree:
   * branch words: isla_el2_cfg regs, the values the trace's AssumeReg events
     require (Islaris's EL2 configuration: HCR_EL2, the CFG_ID_AA64PFR0_EL1_*
     pseudo-registers, TCR_EL2, SCR_EL3, PSTATE.EL = 2, PSTATE.nRW = 0);
     br x10 additionally InGuardedPage = false on the isla side;
   * b.cond words: __BranchTaken = false in the model record before the
     instruction (__InstructionExecute writes it false before decoding);
   * the model-side premises of chez_XXXX_model (SEE below the guard,
     el2_cfg) are needed to use the IFF, not the bridge.
   The memory is untouched: none of these traces reads or writes memory.

   Trusted: Coq 8.19.0; the Islaris opsem definitions; coq-sail 0.19 and the
   Sail-to-Coq translation of sail-arm 7d058164.  The bridges themselves are
   closed under the global context; the model IFFs carry the decoder's three
   Coq-stdlib Reals axioms.  The isla traces are data. *)
From isla Require Import opsem automation.
From isla.instructions.buri_chez_add Require Import a0 a4 a8 ac a10 a14 a18 a20.
Require Import SailStdpp.Base.
Require Import armv9_types armv9.
Require Import BuriArm.BuriArmAdds BuriArm.BuriArmBridgeValues BuriArm.BuriArmBridge.
Require Import BuriArm.BuriArmSeq BuriArm.BuriArmBridgeLib BuriArm.BuriArmFastPath BuriArm.BuriArmPC.
Require Import BuriArm.BuriArmBridgeValues2.
Import Defs.
Open Scope Z.

Ltac gpr_in := cbn; tauto.
Ltac lk := repeat first [ rewrite register_lookup_set | rewrite irrelevant_register_set; [|reflexivity] ].
Ltac agree_gprs_tac Hg :=
  repeat first [ apply agree_gprs_write; [gpr_in | reflexivity |]
               | apply agree_gprs_isla_other; [reflexivity|]
               | apply agree_gprs_model_other; [reflexivity|] ];
  exact Hg.

(* +0x08 orr x30, x0, x1 *)
Theorem chez_0008_bridge rs regs mem : agree rs regs →
  (∃ r, mrun mem a8 regs r) ∧
  (∀ r, mrun mem a8 regs r → agree (pc_next (chez_0008_final rs)) r).
Proof.
  intros (Hg & HPC & rest & HPS).
  pose proof (Hg "R0" R0 ltac:(gpr_in)) as HR0.
  pose proof (Hg "R1" R1 ltac:(gpr_in)) as HR1.
  pose proof (Hg "R30" R30 ltac:(gpr_in)) as HR30.
  cbn in HR0, HR1, HR30.
  split.
  - eexists. unfold a8.
    mdecl (register_lookup R0 rs : bv 64). mrd. mdecl (register_lookup R1 rs : bv 64). mrd.
    mdefc. mwr. mdecl (register_lookup _PC rs : bv 64). mrd. mdefc. mwr. apply MEnd.
  - intros r H. unfold a8 in *. repeat mb H.
    split; [|split].
    + agree_gprs_tac Hg.
    + rewrite lookup_insert. unfold pc_next. lk. rewrite pc_next_bv. reflexivity.
    + exists rest. rewrite lookup_insert_ne; [|done]. rewrite lookup_insert_ne; [|done].
      unfold pc_next, chez_0008_final. lk. exact HPS.
Qed.

(* +0x00 cmp x23, #2 *)
Theorem chez_0000_bridge rs regs mem : agree rs regs →
  (∃ r, mrun mem a0 regs r) ∧
  (∀ r, mrun mem a0 regs r → agree (pc_next (chez_0000_final rs)) r).
Proof.
  intros (Hg & HPC & rest & HPS).
  pose proof (Hg "R23" R23 ltac:(gpr_in)) as HR23. cbn in HR23.
  set (x := register_lookup R23 rs) in *.
  set (p := register_lookup PSTATE rs) in *.
  split.
  - eexists. unfold a0, pstate_isla in *.
    mdecl x. mrd. mdefc. mdefc. mdefc. mdefc.
    mdefc. mwr. mdefc. mwr. mdefc. mwr. mdefc. mwr.
    mdecl (register_lookup _PC rs : bv 64). mrd. mdefc. mwr. apply MEnd.
  - intros r H. unfold a0, pstate_isla in *. repeat mb H.
    rewrite !insert_insert.
    rewrite cmp_sum_isla; [|reflexivity|reflexivity].
    unfold ite. rewrite !isla_N.
    split; [|split].
    + agree_gprs_tac Hg.
    + rewrite lookup_insert. unfold pc_next. lk. rewrite pc_next_bv. reflexivity.
    + exists rest.
      rewrite lookup_insert_ne; [|done]. rewrite lookup_insert.
      unfold pc_next, chez_0000_final, set_nzcv. lk.
      rewrite nzcv_N nzcv_Z nzcv_C nzcv_V.
      rewrite cmp_C_isla; [|reflexivity|reflexivity].
      rewrite cmp_V_isla; [|reflexivity|reflexivity].
      rewrite isla_Z.
      unfold pstate_isla. repeat f_equal; apply bv_eq; reflexivity.
Qed.

(* +0x0c tst x30, #7 *)
Theorem chez_000c_bridge rs regs mem : agree rs regs →
  (∃ r, mrun mem ac regs r) ∧
  (∀ r, mrun mem ac regs r → agree (pc_next (chez_000c_final rs)) r).
Proof.
  intros (Hg & HPC & rest & HPS).
  pose proof (Hg "R30" R30 ltac:(gpr_in)) as HR30. cbn in HR30.
  set (x := register_lookup R30 rs) in *.
  set (p := register_lookup PSTATE rs) in *.
  split.
  - unfold ac, pstate_isla in *.
    destruct (bool_decide (bv_and x (BV 64 7) = 0%bv)) eqn:E0; eexists;
    mdecl x; mrd; mdefc; mdefc; mdefc.
    + eapply MStep; [apply mstep_none; apply CasesES; apply elem_of_list_here|]; norm.
      eapply MStep; [apply mstep_assert; apply eval_exp'_sound; evlazy; rewrite ?E0; reflexivity|]; norm.
      mdefc. mdefc. mwr. mdefc. mwr. mdefc. mwr. mdefc. mwr.
      mdecl (register_lookup _PC rs : bv 64). mrd. mdefc. mwr. apply MEnd.
    + eapply MStep; [apply mstep_none; apply CasesES; apply elem_of_list_further, elem_of_list_here|]; norm.
      eapply MStep; [apply mstep_assert; apply eval_exp'_sound; evlazy; rewrite ?E0; reflexivity|]; norm.
      mdefc. mdefc. mwr. mdefc. mwr. mdefc. mwr. mdefc. mwr.
      mdecl (register_lookup _PC rs : bv 64). mrd. mdefc. mwr. apply MEnd.
  - intros r H. unfold ac, pstate_isla in *. repeat mb H.
    all: rewrite !insert_insert.
    all: rewrite tst_N_isla; [|reflexivity|reflexivity].
    all: match goal with E : bool_decide _ = true |- _ => apply bool_decide_eq_true in E | _ => idtac end.
    all: split; [|split]; [agree_gprs_tac Hg | rewrite lookup_insert; unfold pc_next; lk; rewrite pc_next_bv; reflexivity |].
    all: exists rest; rewrite lookup_insert_ne; [|done]; rewrite lookup_insert;
      unfold pc_next, chez_000c_final, set_nzcv; lk; rewrite nzcv_N nzcv_Z nzcv_C nzcv_V;
      unfold logic_flags, IsZeroBit; rewrite IsZero_bool.
    + rewrite tst_result_bv (bool_decide_true _ E).
      unfold pstate_isla. repeat f_equal; apply bv_eq; reflexivity.
    + apply negb_true_iff in E. apply bool_decide_eq_false in E.
      rewrite tst_result_bv (bool_decide_false _ E).
      unfold pstate_isla. repeat f_equal; apply bv_eq; reflexivity.
Qed.

(* +0x14 adds x23, x0, x1 *)
Section adds.
Context (rs : regstate) (regs : reg_map) (mem : mem_map).

Theorem chez_0014_bridge : agree rs regs →
  (∃ r, mrun mem a14 regs r) ∧
  (∀ r, mrun mem a14 regs r → agree (pc_next (chez_0014_final rs)) r).
Proof.
  intros (Hg & HPC & rest & HPS).
  pose proof (Hg "R0" R0 ltac:(gpr_in)) as HR0.
  pose proof (Hg "R1" R1 ltac:(gpr_in)) as HR1.
  pose proof (Hg "R23" R23 ltac:(gpr_in)) as HR23.
  cbn in HR0, HR1, HR23.
  set (x0 := register_lookup R0 rs) in *. set (x1 := register_lookup R1 rs) in *.
  set (p := register_lookup PSTATE rs) in *.
  split.
  - eexists. unfold a14, pstate_isla in *.
    mdecl x0. mrd. mdefc. mdecl x1. mrd. mdefc. mdefc. mdefc. mdefc.
    mdefc. mwr. mdefc. mwr. mdefc. mwr. mdefc. mwr. mdefc. mwr.
    mdecl (register_lookup _PC rs : bv 64). mrd. mdefc. mwr. apply MEnd.
  - intros r H. unfold a14, pstate_isla in *. repeat mb H.
    rewrite !insert_insert.
    rewrite !isla_sum_model' !isla_N' !isla_Z' !isla_C' !isla_V'.
    rewrite -!nzcv_shape.
    split; [|split].
    + agree_gprs_tac Hg.
    + rewrite lookup_insert. unfold pc_next. lk. rewrite pc_next_bv. reflexivity.
    + exists rest.
      rewrite lookup_insert_ne; [|done]. rewrite lookup_insert_ne; [|done]. rewrite lookup_insert.
      unfold pc_next, chez_0014_final, set_nzcv. lk.
      rewrite nzcv_N nzcv_Z nzcv_C nzcv_V.
      unfold pstate_isla. repeat f_equal; apply bv_eq; reflexivity.
Qed.
End adds.

(* The converse direction for ADDS, as one statement: under the premises,
   every behaviour of the model's decode/execute on 0xab010017 is the single
   one (chez_0014_model), and every complete run of the isla trace agrees
   with it after the model's PC step. *)
Theorem chez_0014_exact pc rs regs mem : agree rs regs ->
  Z.ltb (register_lookup SEE rs) 15 = true ->
  (exists rs', sexec rs (__DecodeA64 pc chez_word_0014) rs' tt) /\
  (exists r, mrun mem a14 regs r) /\
  (forall rs' a r, sexec rs (__DecodeA64 pc chez_word_0014) rs' a -> mrun mem a14 regs r ->
     a = tt /\ agree (pc_next rs') r).
Proof.
  intros Hag Hsee. destruct (chez_0014_bridge rs regs mem Hag) as [Hex Hall].
  split; [|split; [exact Hex|]].
  - exists (chez_0014_final rs). apply (chez_0014_model pc rs _ tt Hsee). split; reflexivity.
  - intros rs' a r Hm Hr. apply (chez_0014_model pc rs rs' a Hsee) in Hm as [-> ->].
    split; [reflexivity|]. apply Hall, Hr.
Qed.

(* Branches: the configuration the isla traces assume. *)
Definition isla_el2_cfg (regs : reg_map) : Prop :=
  regs !! "HCR_EL2" = Some (RVal_Bits (BV 64 0x80000000)) ∧
  regs !! "CFG_ID_AA64PFR0_EL1_EL3" = Some (RVal_Bits (BV 4 1)) ∧
  regs !! "CFG_ID_AA64PFR0_EL1_EL2" = Some (RVal_Bits (BV 4 1)) ∧
  regs !! "CFG_ID_AA64PFR0_EL1_EL1" = Some (RVal_Bits (BV 4 1)) ∧
  regs !! "CFG_ID_AA64PFR0_EL1_EL0" = Some (RVal_Bits (BV 4 1)) ∧
  regs !! "TCR_EL2" = Some (RVal_Bits (BV 64 0)) ∧
  regs !! "SCR_EL3" = Some (RVal_Bits (BV 32 0x501)) ∧
  ∀ v, regs !! "PSTATE" = Some v →
    read_accessor [Field "EL"] v = Some (RVal_Bits (BV 2 2)) ∧
    read_accessor [Field "nRW"] v = Some (RVal_Bits (BV 1 0)).

Ltac masm_ps H := eapply MStep;
  [eapply mstep_assume_reg; [econstructor | eassumption | apply H] |]; norm.



Lemma subrange_63_0 (x : mword 64) : subrange_vec_dec x 63 0 = x.
Proof. exact (subrange_full_64 x). Qed.

Theorem chez_0004_bridge rs regs mem : agree rs regs → isla_el2_cfg regs →
  register_lookup __BranchTaken rs = false →
  (∃ r, mrun mem a4 regs r) ∧
  (∀ r, mrun mem a4 regs r → agree (pc_after (chez_0004_final rs)) r).
Proof.
  intros (Hg & HPC & rest & HPS) (HHCR & HC3 & HC2 & HC1 & HC0 & HTCR & HSCR & HPSf) HBT.
  destruct (HPSf _ HPS) as [HEL HnRW].
  unfold chez_0004_final, bcond_final, flag_set. rewrite eq_vec_1.
  destruct (decide (ProcState_Z (register_lookup PSTATE rs) = 1%bv)) as [HF1|HF1];
    [rewrite (bool_decide_true _ HF1) | rewrite (bool_decide_false _ HF1)]; cbn [negb]; split.
  - eexists. unfold a4, pstate_isla in *.
    masm. masm. masm. masm. masm. masm. mdecl (ProcState_Z (register_lookup PSTATE rs)).
    masm_ps HEL. masm_ps HnRW. masm. mrd. mdefc.
    eapply MStep; [apply mstep_none; apply CasesES; apply elem_of_list_further, elem_of_list_here|]; norm.
    eapply MStep; [apply mstep_assert; apply eval_exp'_sound; evlazy; rewrite (bool_decide_true _ HF1); reflexivity|]; norm.
    mdecl (register_lookup _PC rs : bv 64). mrd. mdefc. mwr. apply MEnd.
  - intros r H. unfold a4, pstate_isla in *. repeat mb H.
    all: try (exfalso; match goal with E : _ = true |- _ => rewrite (bool_decide_true _ HF1) in E; discriminate E end).
    unfold pc_after. lk. rewrite HBT. unfold pc_next.
    split; [|split].
    + agree_gprs_tac Hg.
    + rewrite lookup_insert. lk. rewrite pc_next_bv. reflexivity.
    + exists rest. rewrite lookup_insert_ne; [|done]. lk. exact HPS.
  - eexists. unfold a4, pstate_isla in *.
    masm. masm. masm. masm. masm. masm. mdecl (ProcState_Z (register_lookup PSTATE rs)).
    masm_ps HEL. masm_ps HnRW. masm. mrd. mdefc.
    eapply MStep; [apply mstep_none; apply CasesES; apply elem_of_list_here|]; norm.
    eapply MStep; [apply mstep_assert; apply eval_exp'_sound; evlazy; rewrite (bool_decide_false _ HF1); reflexivity|]; norm.
    mdecl (register_lookup _PC rs : bv 64). mrd. mdefc. mdefc. mba. mdefc. mwr. apply MEnd.
  - intros r H. unfold a4, pstate_isla in *. repeat mb H.
    all: try (exfalso; match goal with E : _ = true |- _ => rewrite (bool_decide_false _ HF1) in E; discriminate E end).
    unfold pc_after, branch_taken. lk. cbn iota.
    split; [|split].
    + agree_gprs_tac Hg.
    + rewrite lookup_insert. lk. unfold pc_plus. rewrite subrange_add_bv.
      unfold MachineWord.MachineWord.N_to_word. do 2 f_equal;
      try (apply bv_eq; rewrite !bv_add_unsigned Z_to_bv_unsigned; reflexivity).
    + exists rest. rewrite lookup_insert_ne; [|done]. lk. exact HPS.
Qed.

Theorem chez_0010_bridge rs regs mem : agree rs regs → isla_el2_cfg regs →
  register_lookup __BranchTaken rs = false →
  (∃ r, mrun mem a10 regs r) ∧
  (∀ r, mrun mem a10 regs r → agree (pc_after (chez_0010_final rs)) r).
Proof.
  intros (Hg & HPC & rest & HPS) (HHCR & HC3 & HC2 & HC1 & HC0 & HTCR & HSCR & HPSf) HBT.
  destruct (HPSf _ HPS) as [HEL HnRW].
  unfold chez_0010_final, bcond_final, flag_set. rewrite eq_vec_1.
  destruct (decide (ProcState_Z (register_lookup PSTATE rs) = 1%bv)) as [HF1|HF1];
    [rewrite (bool_decide_true _ HF1) | rewrite (bool_decide_false _ HF1)]; cbn [negb]; split.
  - eexists. unfold a10, pstate_isla in *.
    masm. masm. masm. masm. masm. masm. mdecl (ProcState_Z (register_lookup PSTATE rs)).
    masm_ps HEL. masm_ps HnRW. masm. mrd. mdefc.
    eapply MStep; [apply mstep_none; apply CasesES; apply elem_of_list_further, elem_of_list_here|]; norm.
    eapply MStep; [apply mstep_assert; apply eval_exp'_sound; evlazy; rewrite (bool_decide_true _ HF1); reflexivity|]; norm.
    mdecl (register_lookup _PC rs : bv 64). mrd. mdefc. mwr. apply MEnd.
  - intros r H. unfold a10, pstate_isla in *. repeat mb H.
    all: try (exfalso; match goal with E : _ = true |- _ => rewrite (bool_decide_true _ HF1) in E; discriminate E end).
    unfold pc_after. lk. rewrite HBT. unfold pc_next.
    split; [|split].
    + agree_gprs_tac Hg.
    + rewrite lookup_insert. lk. rewrite pc_next_bv. reflexivity.
    + exists rest. rewrite lookup_insert_ne; [|done]. lk. exact HPS.
  - eexists. unfold a10, pstate_isla in *.
    masm. masm. masm. masm. masm. masm. mdecl (ProcState_Z (register_lookup PSTATE rs)).
    masm_ps HEL. masm_ps HnRW. masm. mrd. mdefc.
    eapply MStep; [apply mstep_none; apply CasesES; apply elem_of_list_here|]; norm.
    eapply MStep; [apply mstep_assert; apply eval_exp'_sound; evlazy; rewrite (bool_decide_false _ HF1); reflexivity|]; norm.
    mdecl (register_lookup _PC rs : bv 64). mrd. mdefc. mdefc. mba. mdefc. mwr. apply MEnd.
  - intros r H. unfold a10, pstate_isla in *. repeat mb H.
    all: try (exfalso; match goal with E : _ = true |- _ => rewrite (bool_decide_false _ HF1) in E; discriminate E end).
    unfold pc_after, branch_taken. lk. cbn iota.
    split; [|split].
    + agree_gprs_tac Hg.
    + rewrite lookup_insert. lk. unfold pc_plus. rewrite subrange_add_bv.
      unfold MachineWord.MachineWord.N_to_word. do 2 f_equal;
      try (apply bv_eq; rewrite !bv_add_unsigned Z_to_bv_unsigned; reflexivity).
    + exists rest. rewrite lookup_insert_ne; [|done]. lk. exact HPS.
Qed.

Theorem chez_0018_bridge rs regs mem : agree rs regs → isla_el2_cfg regs →
  register_lookup __BranchTaken rs = false →
  (∃ r, mrun mem a18 regs r) ∧
  (∀ r, mrun mem a18 regs r → agree (pc_after (chez_0018_final rs)) r).
Proof.
  intros (Hg & HPC & rest & HPS) (HHCR & HC3 & HC2 & HC1 & HC0 & HTCR & HSCR & HPSf) HBT.
  destruct (HPSf _ HPS) as [HEL HnRW].
  unfold chez_0018_final, bcond_final, flag_set. rewrite eq_vec_1.
  destruct (decide (ProcState_V (register_lookup PSTATE rs) = 1%bv)) as [HF1|HF1];
    [rewrite (bool_decide_true _ HF1) | rewrite (bool_decide_false _ HF1)]; cbn [negb]; split.
  - eexists. unfold a18, pstate_isla in *.
    masm. masm. masm. masm. masm. masm. mdecl (ProcState_V (register_lookup PSTATE rs)).
    masm_ps HEL. masm_ps HnRW. masm. mrd. mdefc.
    eapply MStep; [apply mstep_none; apply CasesES; apply elem_of_list_here|]; norm.
    eapply MStep; [apply mstep_assert; apply eval_exp'_sound; evlazy; rewrite (bool_decide_true _ HF1); reflexivity|]; norm.
    mdecl (register_lookup _PC rs : bv 64). mrd. mdefc. mdefc. mba. mdefc. mwr. apply MEnd.
  - intros r H. unfold a18, pstate_isla in *. repeat mb H.
    all: try (exfalso; match goal with E : _ = true |- _ => rewrite (bool_decide_true _ HF1) in E; discriminate E end).
    unfold pc_after, branch_taken. lk. cbn iota.
    split; [|split].
    + agree_gprs_tac Hg.
    + rewrite lookup_insert. lk. unfold pc_plus. rewrite subrange_add_bv.
      unfold MachineWord.MachineWord.N_to_word. do 2 f_equal;
      try (apply bv_eq; rewrite !bv_add_unsigned Z_to_bv_unsigned; reflexivity).
    + exists rest. rewrite lookup_insert_ne; [|done]. lk. exact HPS.
  - eexists. unfold a18, pstate_isla in *.
    masm. masm. masm. masm. masm. masm. mdecl (ProcState_V (register_lookup PSTATE rs)).
    masm_ps HEL. masm_ps HnRW. masm. mrd. mdefc.
    eapply MStep; [apply mstep_none; apply CasesES; apply elem_of_list_further, elem_of_list_here|]; norm.
    eapply MStep; [apply mstep_assert; apply eval_exp'_sound; evlazy; rewrite (bool_decide_false _ HF1); reflexivity|]; norm.
    mdecl (register_lookup _PC rs : bv 64). mrd. mdefc. mwr. apply MEnd.
  - intros r H. unfold a18, pstate_isla in *. repeat mb H.
    all: try (exfalso; match goal with E : _ = true |- _ => rewrite (bool_decide_false _ HF1) in E; discriminate E end).
    unfold pc_after. lk. rewrite HBT. unfold pc_next.
    split; [|split].
    + agree_gprs_tac Hg.
    + rewrite lookup_insert. lk. rewrite pc_next_bv. reflexivity.
    + exists rest. rewrite lookup_insert_ne; [|done]. lk. exact HPS.
Qed.

(* +0x20 br x10 *)

Theorem chez_0020_bridge rs regs mem : agree rs regs → isla_el2_cfg regs →
  regs !! "InGuardedPage" = Some (RegVal_Base (Val_Bool false)) →
  (∃ r, mrun mem a20 regs r) ∧
  (∀ r, mrun mem a20 regs r → agree (pc_after (chez_0020_final rs)) r).
Proof.
  intros (Hg & HPC & rest & HPS) (HHCR & HC3 & HC2 & HC1 & HC0 & HTCR & HSCR & HPSf) HIG.
  destruct (HPSf _ HPS) as [HEL HnRW].
  pose proof (Hg "R10" R10 ltac:(gpr_in)) as HR10. cbn in HR10.
  split.
  - eexists. unfold a20, pstate_isla in *.
    masm. masm. masm. masm. masm. masm. masm. masm_ps HEL. masm_ps HnRW. masm.
    mdecl (register_lookup R10 rs : bv 64). mrd. mdefc. mdefc. mba. mdefc. mwr. apply MEnd.
  - intros r H. unfold a20, pstate_isla in *. repeat mb H.
    unfold pc_after, chez_0020_final, branch_taken. lk. cbn iota.
    split; [|split].
    + agree_gprs_tac Hg.
    + rewrite lookup_insert. lk. rewrite subrange_63_0. reflexivity.
    + exists rest. rewrite lookup_insert_ne; [|done]. lk. exact HPS.
Qed.

Print Assumptions chez_0008_bridge.
Print Assumptions chez_0000_bridge.
Print Assumptions chez_000c_bridge.
Print Assumptions chez_0014_bridge.
Print Assumptions chez_0014_exact.
Print Assumptions chez_0004_bridge.
Print Assumptions chez_0010_bridge.
Print Assumptions chez_0018_bridge.
Print Assumptions subrange_63_0.
Print Assumptions chez_0020_bridge.
