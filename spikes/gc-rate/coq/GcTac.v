(** * Stepping tactics and image facts for the collector proofs.  Proof-side only. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec.
From LinuxProcessSemantics.Examples.gc_rate_ns Require Import gc_rate_code GcStep.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

Lemma source_no_ro_exec : no_ro_exec source_segs = true.
Proof. vm_compute. reflexivity. Qed.

(** The loaded text and rodata: [.text] starts at 0x10080, [.rodata] ends at 0x48314. *)
Definition TL : Z := 0x10080%Z.
Definition TH : Z := 0x48314%Z.

Lemma jalr_tgt_even : forall (r : word) (z : Z),
  (bv_unsigned r mod 2 = 0)%Z -> z = 0%Z -> jalr_tgt r z = r.
Proof.
  intros r z Hr ->. apply bv_eq. unfold jalr_tgt, jalr_tgtZ.
  rewrite Z.add_0_r.
  assert (Hl : Z.land (bv_unsigned r) (-2) = bv_unsigned r).
  { change (-2)%Z with (Z.lnot 1). rewrite <- Z.ldiff_land.
    apply Z.bits_inj'. intros i Hi.
    rewrite Z.ldiff_spec.
    destruct (Z.eq_dec i 0) as [->|Hne].
    - rewrite Z.bit0_odd, Z.bit0_odd. change (Z.odd 1) with true.
      rewrite (Z_div_mod_eq_full (bv_unsigned r) 2), Hr, Z.add_0_r.
      rewrite Z.odd_mul. reflexivity.
    - assert (H1 : Z.testbit 1 i = false).
      { destruct i as [|p|p]; [lia| |lia]. destruct p; reflexivity. }
      rewrite H1, andb_true_r. reflexivity. }
  rewrite Hl. rewrite Z_to_bv_unsigned. apply bv_wrap_bv_unsigned.
Qed.

(* Like [getr_resolve], but keeps [getr regs r] for hypotheses to rewrite. *)
Ltac gres :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero.

(* Fetch from the fixed text, under a hypothesis that the overlay misses it. *)
Ltac wxf_with Hc SF :=
  eapply wx_fetch_intro with (lo := TL) (hi := TH);
    [ exact source_no_ro_exec
    | exact Hc
    | unfold TL; imm_norm; lia
    | unfold TH; imm_norm; lia
    | unfold TH; lia
    | exact SF ].

Ltac vres :=
  gres; rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_sltiu, ?alu_slli, ?alu_srli,
    ?alu_add, ?alu_sub, ?alu_or, ?alu_and;
  imm_norm; reflexivity.

(* One pure instruction: the value it computes becomes an unresolved-free term. *)
Ltac ws Hc F D :=
  eapply mst_step;
  [ reflexivity
  | lazymatch type of D with
    | _ = Some (OpImm _ _ _ _, _) => eapply z_opimm_at
    | _ = Some (ShiftImm _ _ _ _, _) => eapply z_shift_at
    | _ = Some (Op _ _ _ _, _) => eapply z_op_at
    | _ = Some (Auipc _ _, _) => eapply z_auipc_at
    end;
    [ wxf_with Hc F | reflexivity | exact D | reflexivity | vres ]
  | norm_pc ].

Ltac wj Hc F D tt :=
  eapply mst_step;
  [ reflexivity
  | eapply z_j with (tgt := tt);
    [ wxf_with Hc F | reflexivity | exact D | unfold btgt; imm_norm; bveq ]
  | norm_pc ].

Ltac wbr_tk Hc F D proof :=
  eapply mst_step;
  [ reflexivity
  | eapply z_branch_tk;
    [ wxf_with Hc F | reflexivity | exact D | gres; proof ]
  | unfold btgt; imm_norm; norm_pc ].

Ltac wbr_ft Hc F D proof :=
  eapply mst_step;
  [ reflexivity
  | eapply z_branch_ft;
    [ wxf_with Hc F | reflexivity | exact D | gres; proof ]
  | norm_pc ].

(* A pure instruction whose value is named, with a proof of the value. *)
Ltac wsv Hc F D vv prf :=
  eapply mst_step;
  [ reflexivity
  | lazymatch type of D with
    | _ = Some (OpImm _ _ _ _, _) => eapply z_opimm_at with (v := vv)
    | _ = Some (ShiftImm _ _ _ _, _) => eapply z_shift_at with (v := vv)
    | _ = Some (Op _ _ _ _, _) => eapply z_op_at with (v := vv)
    | _ = Some (Auipc _ _, _) => eapply z_auipc_at with (v := vv)
    end;
    [ wxf_with Hc F | reflexivity | exact D | reflexivity
    | gres; rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_sltiu, ?alu_slli, ?alu_srli,
        ?alu_add, ?alu_sub, ?alu_or, ?alu_and; imm_norm; prf ]
  | norm_pc ].

(* Return through ra to an even address. *)
Ltac wret Hc F D Hra Hev :=
  eapply mst_step;
  [ reflexivity
  | eapply z_jr;
    [ wxf_with Hc F | reflexivity | exact D
    | gres; rewrite Hra; apply jalr_tgt_even; [exact Hev | reflexivity] ]
  | ].

(* An indirect jump to a closed target. *)
Ltac wjr Hc F D tt :=
  eapply mst_step;
  [ reflexivity
  | eapply z_jr with (tgt := tt);
    [ wxf_with Hc F | reflexivity | exact D | gres; imm_norm; bveq ]
  | norm_pc ].

Lemma read_clear : forall segs m a n bs,
  mem_clear m TL TH -> (TL <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= TH)%Z ->
  PropExec.rdn segs (fun _ => None) a n = Some bs -> PropExec.rdn segs m a n = Some bs.
Proof.
  intros. erewrite mem_clear_read; eauto. unfold TH; lia.
Qed.

(* A closed 32-bit rodata load through a generated [ro4] fact. *)
Ltac wlw_ro Hc F D JT :=
  let bs := fresh "bs" in let Hrd := fresh "Hrd" in let Hbs := fresh "Hbs" in
  lazymatch type of JT with
  | ro4 ?aa ?vv =>
    destruct JT as (bs & Hrd & Hbs);
    eapply mst_step;
    [ reflexivity
    | eapply z_lw_at with (a := aa) (v := vv);
      [ wxf_with Hc F | reflexivity | exact D | reflexivity
      | gres; imm_norm; bveq
      | eapply read_clear;
        [ exact Hc
        | unfold TL; rewrite u_Z2bv by lia; lia
        | unfold TH; rewrite u_Z2bv by lia; cbn [Z.of_nat]; lia
        | exact Hrd ]
      | exact Hbs ]
    | norm_pc ]
  end.

(* Loads and stores of a named 64-bit word. *)
Ltac wsd Hc F D aa vv addrprf okprf :=
  eapply mst_step;
  [ reflexivity
  | eapply z_sd with (a := aa) (v := vv);
    [ wxf_with Hc F | reflexivity | exact D
    | gres; imm_norm; addrprf
    | gres; first [reflexivity | assumption]
    | okprf ]
  | norm_pc ].
