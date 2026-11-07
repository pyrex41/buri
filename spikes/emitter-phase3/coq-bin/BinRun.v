(** * Running to a return address with memory changes, the step lemmas spike 5/7 lacked, and an
    automatic stepper that finds each instruction's fetch and decode facts by its address.
    Proof-side only: nothing here is trusted. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.s9bin_ns Require Import s9bin_code BinGcStep BinMoveStep BinGcTac BinGcMem.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

Section S.
Context {fx : FPState}.

(** Runs to [r] in the image, ending with registers and memory satisfying [P]. *)
Definition RunM (r : word) rom (P : bvmap 5 word -> (word -> option byte) -> Prop) (st : machine_state) : Prop :=
  exists regs' mem', msteps source_segs st (mkst regs' r mem' rom) /\ P regs' mem'.

Lemma rm_step : forall r rom P ms ms',
  ms_svc_pending ms = None -> RiscvSemantics.step source_segs ms = MachineOk ms' ->
  RunM r rom P ms' -> RunM r rom P ms.
Proof. intros r rom P ms ms' Hn Hs (regs' & mem' & Hm & Hp). exists regs', mem'. split; [|exact Hp]. eapply mst_step; eauto. Qed.

Lemma rm_done : forall r rom (P : bvmap 5 word -> (word -> option byte) -> Prop) regs mem,
  P regs mem -> RunM r rom P (mkst regs r mem rom).
Proof. intros. exists regs, mem. split; [apply mst_refl | assumption]. Qed.

Lemma rm_mono : forall r rom (P Q : bvmap 5 word -> (word -> option byte) -> Prop) st,
  (forall regs mem, P regs mem -> Q regs mem) -> RunM r rom P st -> RunM r rom Q st.
Proof. intros r rom P Q st H (regs' & mem' & Hm & Hp). exists regs', mem'. auto. Qed.

(** A call: run the callee to the link address, then continue. *)
Lemma rm_call : forall r rom P r' Q st,
  RunM r' rom Q st -> (forall regs mem, Q regs mem -> RunM r rom P (mkst regs r' mem rom)) -> RunM r rom P st.
Proof.
  intros r rom P r' Q st (regs1 & mem1 & Hm1 & Hq) Hk. destruct (Hk _ _ Hq) as (regs2 & mem2 & Hm2 & Hp).
  exists regs2, mem2. split; [eapply msteps_trans; eauto | exact Hp].
Qed.

Lemma z_lbu_at : forall sz segs regs pc mem rom w rd rs (imm : bv 12) a (z : Z),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, sz) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 1%nat = Some [Z_to_bv 8 z] -> (0 <= z < 256)%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (Z_to_bv 64 z)) (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w rd rs imm a z Hwx Hecall Hdecode Hrd Ha Hread Hz. subst a.
  assert (Hv : zext 64 (bv_extract 0 8 (le_bytes_to_word [Z_to_bv 8 z])) = Z_to_bv 64 z).
  { rewrite le_word_1, b_extract8_id. apply bv_eq.
    unfold zext. rewrite bv_zero_extend_unsigned by lia.
    rewrite !Z_to_bv_unsigned. rewrite (bv_wrap_small 8 z) by (change (bv_modulus 8) with 256%Z; lia).
    rewrite (bv_wrap_small 64 z) by (change (bv_modulus 64) with (2^64)%Z; lia). reflexivity. }
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite Hv, b_npc.
  rewrite bv_eqb0_is_x0 in Hrd. rewrite Hrd. reflexivity.
Qed.

Lemma z_lwu_at : forall sz segs regs pc mem rom w rd rs (imm : bv 12) bs a v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, sz) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 4%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w rd rs imm bs a v Hwx Hecall Hdecode Hrd Ha Hread Hv. subst a.
  assert (Hz : zext 64 (bv_extract 0 32 v) = v).
  { pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
    pose proof (bytes_le_to_Z_bound bs) as Hb.
    pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
    rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
    apply bv_eq. unfold zext.
    rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_small.
    change (bv_modulus 32) with 4294967296%Z.
    change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb. lia. }
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc.
  rewrite bv_eqb0_is_x0 in Hrd. rewrite Hrd. reflexivity.
Qed.

Lemma z_sw : forall sz segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, sz) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc sz) (wbytes mem a (word_to_le_bytes 4 v)) rom).
Proof.
  intros sz segs regs pc mem rom w rs1 rs2 imm a v Hwx Hecall Hdecode Ha Hv Hok.
  subst a v.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low32, b_npc.
  reflexivity.
Qed.

Lemma z_shift32_at : forall sz segs regs pc mem rom w op rd rs (sh : bv 5) v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs sh, sz) ->
  bv_eqb rd 0 = false ->
  sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh)) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w op rd rs sh v Hwx Hecall Hdecode Hrd Hv. subst v.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  rewrite bv_eqb0_is_x0 in Hrd. rewrite Hrd.
  destruct (is_x0 rs); cbv beta iota; rewrite ?b_npc; reflexivity.
Qed.

Lemma z_mul_at : forall sz segs regs pc mem rom w op rd rs1 rs2 v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, sz) ->
  bv_eqb rd 0 = false ->
  mul_div op (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc sz) mem rom).
Proof.
  intros sz segs regs pc mem rom w op rd rs1 rs2 v Hwx Hecall Hdecode Hrd Hv. subst v.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  rewrite bv_eqb0_is_x0 in Hrd. rewrite Hrd.
  destruct (is_x0 rs1); destruct (is_x0 rs2); cbv beta iota; rewrite ?b_npc; reflexivity.
Qed.

End S.

Open Scope Z_scope.

(** Addresses [base + k] that do not wrap. *)
Lemma u_addi : forall (x : word) k, 0 <= bv_unsigned x + k < 2 ^ 64 -> bv_unsigned (v_addi x k) = bv_unsigned x + k.
Proof. intros. unfold v_addi. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. Qed.

Ltac addr_lia :=
  repeat match goal with
         | |- context [bv_unsigned (v_addi ?x ?k)] => rewrite (u_addi x k) by (pose proof (bv_unsigned_in_range _ x); lia)
         end;
  rewrite ?length_word_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length];
  pose proof (bv_unsigned_in_range _ (Z_to_bv 64 0)); lia.

(* The overlay still misses text and rodata after stores outside them. *)
Ltac clr :=
  lazymatch goal with
  | |- mem_clear (wbytes ?m ?a ?bs) TL TH =>
      apply mem_clear_wbytes; [clr | left; addr_lia | addr_lia]
  | |- mem_clear _ TL TH => assumption
  end.

(* [lo, hi) stays writable through stores. *)
Ltac wrt :=
  lazymatch goal with
  | |- writable (wbytes ?m ?a ?bs) ?lo ?hi => apply writable_store; wrt
  | |- writable _ _ _ => eassumption
  end.

Ltac gres_in H :=
  repeat first [ rewrite getr_same in H by reg_neq_tac | rewrite getr_other in H by reg_neq_tac ];
  rewrite ?getr_zero in H.

Ltac norm_rm := try lazymatch goal with |- RunM _ _ _ ?st => norm_pc_state st end.

(* Register equations in context (getr R r = v for the entry registers R) are applied after [gres]. *)
Ltac rsub := repeat match goal with H : getr ?R ?r = ?v |- context [getr ?R ?r] => is_var R; rewrite H end.
Ltac rsub_in E := repeat match goal with H : getr ?R ?r = ?v |- _ =>
  lazymatch type of E with context [getr R r] => is_var R; rewrite H in E end end.

Ltac vres2 :=
  gres; rsub; rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_xori, ?alu_sltiu, ?alu_slli, ?alu_srli, ?alu_srai,
    ?alu_add, ?alu_sub, ?alu_or, ?alu_and, ?alu_xor, ?alu_sltu, ?alu_sll, ?alu_srl, ?alu_sra,
    ?w_addiw, ?w_slliw, ?w_srliw, ?w_sraiw, ?m_mul;
  imm_norm; reflexivity.

Ltac wxf F :=
  eapply wx_fetch_intro with (lo := TL) (hi := TH);
    [ exact source_no_ro_exec | clr | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
    | apply Z.leb_le; vm_compute; reflexivity | exact F ].

(** One instruction at a literal pc, for every form decode and run_block use, except loads and
    stores whose memory fact needs a caller ([ldtac]) and the return.  Branches split the goal on
    the condition, naming it [Hbr]. *)
Ltac astep_with F D ldtac sttac :=
  lazymatch type of D with
  | _ = Some (OpImm _ _ _ _, _) =>
      eapply rm_step; [reflexivity | eapply z_opimm_at; [wxf F | reflexivity | exact D | reflexivity | vres2] | norm_rm]
  | _ = Some (ShiftImm _ _ _ _, _) =>
      eapply rm_step; [reflexivity | eapply z_shift_at; [wxf F | reflexivity | exact D | reflexivity | vres2] | norm_rm]
  | _ = Some (Op _ _ _ _, _) =>
      eapply rm_step; [reflexivity | eapply z_op_at; [wxf F | reflexivity | exact D | reflexivity | vres2] | norm_rm]
  | _ = Some (Lui _ _, _) =>
      eapply rm_step; [reflexivity | eapply z_lui_at; [wxf F | reflexivity | exact D | reflexivity | vres2] | norm_rm]
  | _ = Some (Auipc _ _, _) =>
      eapply rm_step; [reflexivity | eapply z_auipc_at; [wxf F | reflexivity | exact D | reflexivity | vres2] | norm_rm]
  | _ = Some (OpImm32 _ _ _, _) =>
      eapply rm_step; [reflexivity | eapply z_addiw_at; [wxf F | reflexivity | exact D | reflexivity | vres2] | norm_rm]
  | _ = Some (ShiftImm32 _ _ _ _, _) =>
      eapply rm_step; [reflexivity | eapply z_shift32_at; [wxf F | reflexivity | exact D | reflexivity | vres2] | norm_rm]
  | _ = Some (Mul _ _ _ _, _) =>
      eapply rm_step; [reflexivity | eapply z_mul_at; [wxf F | reflexivity | exact D | reflexivity | vres2] | norm_rm]
  | _ = Some (Jal 0 _, _) =>
      eapply rm_step; [reflexivity | eapply z_j; [wxf F | reflexivity | exact D | reflexivity] | norm_rm]
  | _ = Some (Branch ?c ?rs1 ?rs2 _, _) =>
      lazymatch goal with
      | |- RunM _ _ _ (mkst ?regs _ _ _) =>
          let Eb := fresh "Eb" in
          pose proof (eq_refl (branch_taken c (getr regs rs1) (getr regs rs2))) as Eb;
          gres_in Eb; rsub_in Eb;
          lazymatch type of Eb with
          | ?L = _ =>
              clear Eb; let Hbr := fresh "Hbr" in destruct L eqn:Hbr;
              [ eapply rm_step; [reflexivity | eapply z_branch_tk; [wxf F | reflexivity | exact D | gres; rsub; exact Hbr] |
                unfold btgt; imm_norm; norm_rm ]
              | eapply rm_step; [reflexivity | eapply z_branch_ft; [wxf F | reflexivity | exact D | gres; rsub; exact Hbr] |
                norm_rm ] ]
          end
      end
  | _ = Some (Load _ _ _ _ _, _) => ldtac F D
  | _ = Some (Store _ _ _ _, _) => sttac F D
  end.

Ltac pc_of :=
  lazymatch goal with
  | |- RunM _ _ _ (mkst _ ?pc _ _) => let _ := match goal with _ => check_closed_term pc end in
                                     eval vm_compute in (bv_unsigned pc)
  end.

(** After a store, the new memory becomes an opaque [m'] with its facts re-proved once: the overlay
    still misses the text, and the written range stays writable.  Steps then find them by
    [assumption] instead of walking the chain of stores. *)
Ltac forget_mem :=
  lazymatch goal with
  | |- RunM _ _ _ (mkst _ _ (wbytes ?m ?a ?bs) _) =>
      let m' := fresh "m" in let Em := fresh "Em" in
      remember (wbytes m a bs) as m' eqn:Em;
      lazymatch goal with
      | Hc : mem_clear m TL TH |- _ =>
          let Hc' := fresh "Hc" in
          assert (Hc' : mem_clear m' TL TH) by (rewrite Em; apply mem_clear_wbytes; [exact Hc | left; addr_lia | addr_lia])
      end;
      try lazymatch goal with
      | Hw : writable m ?lo ?hi |- _ =>
          let Hw' := fresh "Hw" in assert (Hw' : writable m' lo hi) by (rewrite Em; apply writable_store; exact Hw)
      end
  end.

(** Jump-table loads and jumps, and branches decided by literals: jump-table loads and jumps, and branches decided by literals. *)
Ltac kill_closed := try (match goal with H : branch_taken ?c ?x ?y = ?b |- _ =>
  check_closed_term (branch_taken c x y); vm_compute in H; discriminate end).

Ltac djt F D :=
  lazymatch goal with |- RunM _ _ _ (mkst ?regs _ _ _) =>
  lazymatch type of D with _ = Some (Load SZ4 true ?rd ?rs ?imm, _) =>
    let E := fresh "E" in
    assert (E : v_addi (getr regs rs) (bv_signed imm) = v_addi (getr regs rs) (bv_signed imm)) by reflexivity;
    gres_in E;
    lazymatch type of E with _ = ?a' =>
      clear E; let n := eval vm_compute in (bv_unsigned a') in
      jtf n ltac:(fun JT =>
        let bs := fresh "bs" in let Hrd := fresh "Hrd" in let Hbs := fresh "Hbs" in
        destruct JT as (bs & Hrd & Hbs);
        eapply rm_step; [reflexivity | eapply z_lw_at with (a := Z_to_bv 64 n);
          [ wxf F | reflexivity | exact D | reflexivity | gres; apply bv_eq; vm_compute; reflexivity
          | eapply read_clear; [clr | unfold TL; rewrite u_Z2bv by lia; lia | unfold TH; rewrite u_Z2bv by lia; cbn [Z.of_nat]; lia | exact Hrd]
          | exact Hbs ] | norm_rm ])
    end
  end end.

Ltac djr F D :=
  eapply rm_step; [reflexivity | eapply z_jr; [wxf F | reflexivity | exact D | gres; reflexivity] | norm_rm].

