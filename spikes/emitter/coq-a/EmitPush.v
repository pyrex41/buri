(** * Route A, rung 2: [push_inst16] (SLJIT), the fast path.

    SLJIT's first phase records instructions into a buffer.  This is where one compressed
    instruction of a move gets recorded: 27 instructions, with stack saves, the buffer's used
    count, the halfword, and the compiler's size.  The path that allocates a new chunk calls
    [malloc] and isn't covered: the contract requires room in the current chunk. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.emitter_ns Require Import emitter_code GcStep MoveStep GcTac GcMem.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation W z := (Z_to_bv 64 z).
Abbreviation w2 v := (word_to_le_bytes 2 v).

Section Push.
Context {fx : FPState}.

Lemma z_sh_at : forall sz segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Store SZ2 rs1 rs2 imm, sz) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 2%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc sz) (wbytes mem a (w2 v)) rom).
Proof.
  intros sz segs regs pc mem rom w rs1 rs2 imm a v Hwx Hecall Hdecode Ha Hv Hok.
  subst a v.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low16, b_npc.
  reflexivity.
Qed.

Lemma len_w2 : forall v : word, length (w2 v) = 2%nat.
Proof. intros. apply length_word_to_le_bytes. Qed.

Lemma wat_other2 : forall m (a b v x : word),
  wat m b x ->
  bv_unsigned b + 8 <= bv_unsigned a \/ bv_unsigned a + 2 <= bv_unsigned b ->
  bv_unsigned a + 2 <= 2^64 -> bv_unsigned b + 8 <= 2^64 ->
  wat (wbytes m a (w2 v)) b x.
Proof.
  intros m a b v x Hx Hd Ha Hb. unfold wat in *.
  rewrite rdn_wbytes_out; [exact Hx| | |]; rewrite ?len_w8, ?len_w2; cbn [Z.of_nat]; lia.
Qed.

Variables (mem rom : word -> option byte) (r : word).
Variables (c b u sz ins sp : Z).
Variables (v8 v9 v18 : word).

Hypothesis Hc : mem_clear mem TL TH.
Hypothesis Hev : (bv_unsigned r mod 2 = 0)%Z.

(** The layout: every address is above the text and below the top, and the regions are apart. *)
Hypothesis Lsp : TH <= sp - 32 /\ sp + 8 < 2^64.
Hypothesis Lc : TH <= c /\ c + 200 < 2^64.
Hypothesis Lb : TH <= b /\ b + 8192 < 2^64.
Hypothesis Lu : 0 <= u /\ u + 2 <= 4080.
Hypothesis Lsz : 0 <= sz < 2^63.
Hypothesis Lins : 0 <= ins < 65536.
Hypothesis Dsc : sp <= c \/ c + 136 <= sp - 32.
Hypothesis Dsb : sp <= b \/ b + 8192 <= sp - 32.
Hypothesis Dcb : c + 136 <= b \/ b + 8192 <= c.

Definition m1 := wbytes mem (W (sp - 32 + 24)) (w8 r).
Definition m2 := wbytes m1 (W (sp - 32 + 16)) (w8 v8).
Definition m3 := wbytes m2 (W (sp - 32 + 8)) (w8 v9).
Definition m4 := wbytes m3 (W (sp - 32)) (w8 v18).
Definition m5 := wbytes m4 (W (b + 8)) (w8 (W (u + 2))).
Definition m6 := wbytes m5 (W (b + 16 + u)) (w2 (W ins)).
Definition m7 := wbytes m6 (W (c + 128)) (w8 (W (sz + 1))).

Hypothesis Rbuf : wat mem (W (c + 72)) (W b).
Hypothesis Rused : wat mem (W (b + 8)) (W u).
Hypothesis Rsize : wat mem (W (c + 128)) (W sz).
Hypothesis Wsp : writable mem (sp - 32) sp.
Hypothesis Wb : writable mem b (b + 8192).
Hypothesis Wc : writable mem (c + 128) (c + 136).

Ltac unf := unfold TH in *.

Ltac waddr := unfold v_addi; rewrite U by (unf; lia); f_equal; lia.

Ltac sidez := rewrite ?U by (unf; lia); unf; lia.
Ltac rdw1 :=
  match goal with
  | |- wat (wbytes ?m ?a (word_to_le_bytes 8 ?v)) ?b ?x =>
      first [ refine (wat_other m a b v x _ _ _ _); [ | sidez | sidez | sidez ]
            | refine (wat_hit m a v _); sidez ]
  | |- wat (wbytes ?m ?a (word_to_le_bytes 2 ?v)) ?b ?x =>
      refine (wat_other2 m a b v x _ _ _ _); [ | sidez | sidez | sidez ]
  end.
Ltac rdw := unfold m7, m6, m5, m4, m3, m2, m1; repeat rdw1; try assumption.

Lemma c1 : mem_clear m1 TL TH.
Proof. apply clear_store; [exact Hc | rewrite U by (unf; lia); unf; lia | rewrite U by (unf; lia); unf; lia]. Qed.
Lemma c2 : mem_clear m2 TL TH.
Proof. apply clear_store; [exact c1 | rewrite U by (unf; lia); unf; lia | rewrite U by (unf; lia); unf; lia]. Qed.
Lemma c3 : mem_clear m3 TL TH.
Proof. apply clear_store; [exact c2 | rewrite U by (unf; lia); unf; lia | rewrite U by (unf; lia); unf; lia]. Qed.
Lemma c4 : mem_clear m4 TL TH.
Proof. apply clear_store; [exact c3 | rewrite U by (unf; lia); unf; lia | rewrite U by (unf; lia); unf; lia]. Qed.
Lemma c5 : mem_clear m5 TL TH.
Proof. apply clear_store; [exact c4 | rewrite U by (unf; lia); unf; lia | rewrite U by (unf; lia); unf; lia]. Qed.
Lemma c6 : mem_clear m6 TL TH.
Proof.
  apply mem_clear_wbytes; [exact c5 | |]; rewrite ?len_w2; cbn [Z.of_nat]; rewrite U by (unf; lia); unf; lia.
Qed.
Lemma c7 : mem_clear m7 TL TH.
Proof. apply clear_store; [exact c6 | rewrite U by (unf; lia); unf; lia | rewrite U by (unf; lia); unf; lia]. Qed.

Theorem push_inst16_fast : forall regs,
  getr regs 1 = r -> getr regs 2 = W sp -> getr regs 8 = v8 -> getr regs 9 = v9 -> getr regs 18 = v18 ->
  getr regs 10 = W c -> getr regs 11 = W ins ->
  Run source_segs r m7 rom
    (fun regs' => getr regs' 10 = W 0 /\ getr regs' 2 = W sp /\ getr regs' 8 = v8 /\
                  getr regs' 9 = v9 /\ getr regs' 18 = v18)
    (mkst regs (0x2cf06%bv : word) mem rom).
Proof.
  intros regs Hra H2 H8 H9 H18 H10 H11.
  norm_pc_run.
  wsv Hc SF_2cf06 SD_2cf06 (W (sp - 32)) ltac:(rewrite H2; unfold v_addi; rewrite U by (unf; lia); f_equal; lia).
  wsd Hc SF_2cf08 SD_2cf08 (W (sp - 32 + 24)) r ltac:(waddr) ltac:(eapply (writable_store_ok _ (sp - 32) sp); [exact Wsp | rewrite U by (unf; lia); lia | rewrite U by (unf; lia); cbn [Z.of_nat]; lia | lia]).
  fold m1.
  wsd c1 SF_2cf0a SD_2cf0a (W (sp - 32 + 16)) v8 ltac:(waddr) ltac:(eapply (writable_store_ok _ (sp - 32) sp); [unfold m1; apply writable_store; exact Wsp | rewrite U by (unf; lia); lia | rewrite U by (unf; lia); cbn [Z.of_nat]; lia | lia]).
  fold m2.
  wsd c2 SF_2cf0c SD_2cf0c (W (sp - 32 + 8)) v9 ltac:(waddr) ltac:(eapply (writable_store_ok _ (sp - 32) sp); [unfold m2, m1; repeat apply writable_store; exact Wsp | rewrite U by (unf; lia); lia | rewrite U by (unf; lia); cbn [Z.of_nat]; lia | lia]).
  fold m3.
  wsd c3 SF_2cf0e SD_2cf0e (W (sp - 32)) v18 ltac:(rewrite ?v_addi_0; reflexivity) ltac:(eapply (writable_store_ok _ (sp - 32) sp); [unfold m3, m2, m1; repeat apply writable_store; exact Wsp | rewrite U by (unf; lia); lia | rewrite U by (unf; lia); cbn [Z.of_nat]; lia | lia]).
  fold m4.
  wsv c4 SF_2cf10 SD_2cf10 (W c) ltac:(rewrite H10; unfold v_add; rewrite !U by (unf; lia); f_equal; lia).
  assert (Rd1 : wat m4 (W (c + 72)) (W b)) by rdw.
  wld c4 SF_2cf12 SD_2cf12 (W (c + 72)) (W b) ltac:(rewrite H10; waddr) Rd1.
  assert (Rd2 : wat m4 (W (b + 8)) (W u)) by rdw.
  wld c4 SF_2cf14 SD_2cf14 (W (b + 8)) (W u) ltac:(waddr) Rd2.
  wsv c4 SF_2cf16 SD_2cf16 (W (u + 2)) ltac:(unfold v_addi; rewrite U by (unf; lia); reflexivity).
  wsv c4 SF_2cf1a SD_2cf1a (W 4096) ltac:(vm_compute; reflexivity).
  wsv c4 SF_2cf1c SD_2cf1c (W 4080) ltac:(vm_compute; reflexivity).
  wsv c4 SF_2cf1e SD_2cf1e (W ins) ltac:(rewrite H11; unfold v_add; rewrite !U by (unf; lia); f_equal; lia).
  wbr_ft c4 SF_2cf20 SD_2cf20 ltac:(apply br_ltu_f; rewrite !U by (unf; lia); lia).
  wsv c4 SF_2cf24 SD_2cf24 (W (b + u)) ltac:(unfold v_add; rewrite !U by (unf; lia); reflexivity).
  wsv c4 SF_2cf28 SD_2cf28 (W (b + 16 + u)) ltac:(unfold v_addi; rewrite U by (unf; lia); f_equal; lia).
  wsd c4 SF_2cf2a SD_2cf2a (W (b + 8)) (W (u + 2)) ltac:(waddr) ltac:(eapply (writable_store_ok _ b (b + 8192)); [unfold m4, m3, m2, m1; repeat apply writable_store; exact Wb | rewrite U by (unf; lia); lia | rewrite U by (unf; lia); cbn [Z.of_nat]; lia | unf; lia]).
  fold m5.
  wj c5 SF_2cf2c SD_2cf2c (0x2cf46%bv : word).
  assert (Rd3 : wat m5 (W (c + 128)) (W sz)) by rdw.
  wld c5 SF_2cf46 SD_2cf46 (W (c + 128)) (W sz) ltac:(waddr) Rd3.
  wsv c5 SF_2cf48 SD_2cf48 (W 0) ltac:(vm_compute; reflexivity).
  eapply run_step;
  [ reflexivity
  | eapply z_sh_at with (a := W (b + 16 + u)) (v := W ins);
    [ wxf_with c5 SF_2cf4a | reflexivity | exact SD_2cf4a
    | gres; imm_norm; waddr
    | gres; reflexivity
    | eapply (writable_store_ok _ b (b + 8192));
      [ unfold m5, m4, m3, m2, m1; repeat apply writable_store; exact Wb
      | rewrite U by (unf; lia); lia | rewrite U by (unf; lia); cbn [Z.of_nat]; lia | unf; lia ] ]
  | norm_pc_run ].
  fold m6.
  wsv c6 SF_2cf4e SD_2cf4e (W (sz + 1)) ltac:(unfold v_addi; rewrite U by (unf; lia); reflexivity).
  wsd c6 SF_2cf50 SD_2cf50 (W (c + 128)) (W (sz + 1)) ltac:(waddr) ltac:(eapply (writable_store_ok _ (c + 128) (c + 136)); [unfold m6, m5, m4, m3, m2, m1; repeat apply writable_store; exact Wc | rewrite U by (unf; lia); lia | rewrite U by (unf; lia); cbn [Z.of_nat]; lia | unf; lia]).
  fold m7.
  assert (Rd4 : wat m7 (W (sp - 32 + 24)) r) by rdw.
  wld c7 SF_2cf52 SD_2cf52 (W (sp - 32 + 24)) r ltac:(waddr) Rd4.
  assert (Rd5 : wat m7 (W (sp - 32 + 16)) v8) by rdw.
  wld c7 SF_2cf54 SD_2cf54 (W (sp - 32 + 16)) v8 ltac:(waddr) Rd5.
  assert (Rd6 : wat m7 (W (sp - 32 + 8)) v9) by rdw.
  wld c7 SF_2cf56 SD_2cf56 (W (sp - 32 + 8)) v9 ltac:(waddr) Rd6.
  assert (Rd7 : wat m7 (W (sp - 32)) v18) by rdw.
  wld c7 SF_2cf58 SD_2cf58 (W (sp - 32)) v18 ltac:(rewrite ?v_addi_0; reflexivity) Rd7.
  wsv c7 SF_2cf5a SD_2cf5a (W sp) ltac:(unfold v_addi; rewrite U by (unf; lia); f_equal; lia).
  eapply run_step;
  [ reflexivity
  | eapply z_jr;
    [ wxf_with c7 SF_2cf5c | reflexivity | exact SD_2cf5c
    | gres; apply jalr_tgt_even; [exact Hev | reflexivity] ]
  | ].
  apply run_done. gres. repeat split.
Qed.

End Push.
