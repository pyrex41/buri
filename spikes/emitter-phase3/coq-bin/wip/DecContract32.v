(** * [decode] on its compiled bytes: the 32-bit half (low bits of p[0] are 11), and the whole contract.

    The proof splits on the opcode (32 values with low bits 11) and, for the six opcodes whose case
    tests funct3, on funct3.  Branches on the other bits stay symbolic.  At each return the 32
    written bytes are compared with [encb (dec32 w)] byte by byte with the bit engine. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From stdpp Require Import base decidable bitvector.definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.s9bin_ns Require Import s9bin_code BinGcStep BinMoveStep BinGcTac BinGcMem BinRun BinMem BinBits DecSpec DecPost DecContract RbContract.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope Z_scope.


Section Dec32.
Context {fx : FPState}.
Variables (R0 : bvmap 5 word) (mem0 rom : mem) (b0 b1 b2 b3 : Z).
Abbreviation o := (getr R0 10).
Abbreviation p := (getr R0 11).
Abbreviation ra := (getr R0 1).
Hypothesis Hc : mem_clear mem0 TL TH.
Hypothesis Hw : writable mem0 (bv_unsigned o) (bv_unsigned o + 32).
Hypothesis Ho : TH <= bv_unsigned o.
Hypothesis Hoh : bv_unsigned o + 32 <= 2 ^ 64.
Hypothesis Hev : bv_unsigned ra mod 2 = 0.
Hypothesis Hb0 : 0 <= b0 < 256.
Hypothesis Hb1 : 0 <= b1 < 256.
Hypothesis Hb2 : 0 <= b2 < 256.
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Rd0 : rdn source_segs mem0 (v_addi p 0) 1 = Some [Z_to_bv 8 b0].
Hypothesis Rd1 : rdn source_segs mem0 (v_addi p 1) 1 = Some [Z_to_bv 8 b1].
Hypothesis Rd2 : rdn source_segs mem0 (v_addi p 2) 1 = Some [Z_to_bv 8 b2].
Hypothesis Rd3 : rdn source_segs mem0 (v_addi p 3) 1 = Some [Z_to_bv 8 b3].

Ltac dld F D :=
  lazymatch type of D with
  | _ = Some (Load SZ1 false _ _ _, _) =>
      eapply rm_step; [reflexivity | eapply z_lbu_at; [wxf F | reflexivity | exact D | reflexivity
        | gres; imm_norm; reflexivity | eassumption | lia] | norm_rm]
  end.

Ltac sok := eapply writable_store_ok; [wrt | addr_lia | addr_lia | lia].

(* After a store at [o + k]: forget the chain, carrying the overlay, writable and template facts. *)
Ltac tpl_after :=
  lazymatch goal with
  | Em : ?m' = wbytes ?m (v_addi ?o ?k) ?bs, Ht : meq ?m (wtpl ?m0 ?o ?T), HL : length ?T = 32%nat |- _ =>
      let Ht' := fresh "Ht" in let HL' := fresh "HL" in
      assert (HL' : length (updt T k bs) = 32%nat)
        by (rewrite updt_length; [exact HL | lia | rewrite HL, length_word_to_le_bytes; lia]);
      assert (Ht' : meq m' (wtpl m0 o (updt T k bs)))
        by (rewrite Em; apply meq_step; [exact Ht | lia | rewrite length_word_to_le_bytes; lia
                                         | rewrite HL, length_word_to_le_bytes; lia | rewrite HL; cbn; lia]);
      repeat match goal with
             | H : mem_clear m _ _ |- _ => clear H | H : writable m _ _ |- _ => clear H end;
      clear Em Ht HL
  end.

Ltac dst F D :=
  lazymatch type of D with
  | _ = Some (Store SZ8 _ _ _, _) =>
      eapply rm_step; [reflexivity | eapply z_sd; [wxf F | reflexivity | exact D | gres; imm_norm; reflexivity
        | gres; reflexivity | sok] | norm_rm]
  | _ = Some (Store SZ4 _ _ _, _) =>
      eapply rm_step; [reflexivity | eapply z_sw; [wxf F | reflexivity | exact D | gres; imm_norm; reflexivity
        | gres; reflexivity | sok] | norm_rm]
  end; forget_mem; tpl_after.

Ltac dret F D :=
  eapply rm_step; [reflexivity | eapply z_jr; [wxf F | reflexivity | exact D
    | gres; apply jalr_tgt_even; [exact Hev | reflexivity]] | apply rm_done].

(* At a return: the registers by the frame conditions, and the bytes as one template. *)
Ltac dregs := intros x Hx; destruct Hx as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);
  repeat (rewrite getr_other by assumption); reflexivity.

Ltac dleaf := split; [dregs | lazymatch goal with Ht : meq _ (wtpl _ _ _) |- _ =>
  eapply meq_fin; [exact Ht | | unfold encb; rewrite ?length_app, ?length_word_to_le_bytes; cbn; lia] end].


Definition w : Z := Z.lor (Z.lor b0 (Z.shiftl b1 8)) (Z.lor (Z.shiftl b2 16) (Z.shiftl b3 24)).

Lemma Hr : forall k, 0 <= nth k [8;8;8;8] 0 /\ 0 <= nth k [b0;b1;b2;b3] 0 < 2 ^ nth k [8;8;8;8] 0.
Proof. intros [|[|[|[|k]]]]; cbn; try lia; destruct k; cbn; lia. Qed.

Ltac wbits := bits_with constr:([b0;b1;b2;b3]) constr:([8;8;8;8]) Hr.

(** Fields of [w] that steer [dec32], as functions of the bytes. *)
Lemma w_op : Z.land w 127 = Z.land b0 127.
Proof.
  apply Z.bits_inj'. intros i Hi. unfold w. rewrite !Z.land_spec, !Z.lor_spec, !Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i 7).
  - rewrite (Z.testbit_neg_r b1), (Z.testbit_neg_r b2), (Z.testbit_neg_r b3) by lia. rewrite !orb_false_r. reflexivity.
  - rewrite (tb_small 127 7 i) by lia. rewrite !andb_false_r. reflexivity.
Qed.

Lemma sr1 : 0 <= Z.shiftr b3 1 < 2 ^ 64.
Proof. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ b3); [apply Z.div_le_upper_bound; lia|lia]. Qed.
Lemma sr2 : 0 <= Z.shiftr b3 2 < 2 ^ 64.
Proof. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ b3); [apply Z.div_le_upper_bound; lia|lia]. Qed.

Lemma zwrap_eq : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_wrap 64 a = bv_wrap 64 b -> a = b.
Proof. intros a b Ha Hb H. rewrite !bv_wrap_small in H by (change (bv_modulus 64) with (2^64); lia). exact H. Qed.

Lemma bitz_rng : forall z hi lo, 0 <= lo -> 0 <= hi - lo + 1 <= 64 -> 0 <= bitz z hi lo < 2 ^ 64.
Proof.
  intros z hi lo H1 H2. unfold bitz. rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (Z.shiftr z lo) (2 ^ (hi - lo + 1)) ltac:(apply Z.pow_pos_nonneg; lia)).
  assert (2 ^ (hi - lo + 1) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma land7_rng : forall z, 0 <= Z.land z 7 < 2 ^ 64.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound z (2^3) ltac:(lia)). lia. Qed.

Ltac zfield := apply zwrap_eq; [apply bitz_rng; lia | first [apply land7_rng | apply sr1 | apply sr2] |];
  unfold w, bitz; zbits_with 64%nat constr:([b0;b1;b2;b3]) constr:([8;8;8;8]) Hr.

Lemma w_f3 : bitz w 14 12 = Z.land (Z.shiftr b1 4) 7. Proof. zfield. Qed.
Lemma w_f7 : bitz w 31 25 = Z.shiftr b3 1. Proof. zfield. Qed.
Lemma w_26 : bitz w 31 26 = Z.shiftr b3 2. Proof. zfield. Qed.

(** The compiled code's values of the same fields. *)
Definition t2m : word := v_or (v_or (v_slliw (W b3) 24) (v_slli (W b2) 16)) (v_or (v_slli (W b1) 8) (W b0)).
Lemma t0_W : v_srli (v_slli (W b1) 57) 61 = W (Z.land (Z.shiftr b1 4) 7). Proof. wbits. Qed.
Lemma f7_W : v_srliw t2m 25 = W (Z.shiftr b3 1). Proof. unfold t2m. wbits. Qed.
Lemma b26_W : v_srliw t2m 26 = W (Z.shiftr b3 2). Proof. unfold t2m. wbits. Qed.
Lemma op_W : forall c, Z.land b0 127 = c -> v_andi (W b0) 127 = W c.
Proof.
  intros c H. unfold v_andi. rewrite Z_to_bv_unsigned. rewrite (bv_wrap_small 64 b0) by (change (bv_modulus 64) with (2^64); lia).
  change (bv_wrap 64 127) with 127. rewrite H. reflexivity.
Qed.

Lemma lo3 : Z.land (Z.lor b0 (Z.shiftl b1 8)) 3 = Z.land b0 3.
Proof.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i 2) as [Hl|Hl].
  - rewrite (Z.testbit_neg_r b1) by lia. rewrite orb_false_r. reflexivity.
  - rewrite (tb_small 3 2 i) by lia. rewrite !andb_false_r. reflexivity.
Qed.

Lemma cdec32_eq : Z.land b0 3 = 3 -> cdec b0 b1 b2 b3 = dec32 w.
Proof. intros H. unfold cdec. rewrite lo3, H. reflexivity. Qed.

Ltac dgo32 :=
  repeat (let n := pc_of in fd n ltac:(fun F D =>
    lazymatch type of D with
    | _ = Some (Jalr 0 1 _, _) => dret F D
    | _ = Some (Jalr 0 _ _, _) => djr F D
    | _ = Some (Load SZ4 true _ _ _, _) => djt F D
    | _ => astep_with F D dld dst
    end); kill_closed).



Ltac lst_eq :=
  repeat (apply (f_equal2 (@cons _)); [apply (f_equal (@Some _)); apply bv_eq; rewrite ?Z_to_bv_unsigned;
                                       v_unfold; rewrite ?Z_to_bv_unsigned, ?Z_to_bv_signed;
                                       zbits_with 8%nat constr:([b0;b1;b2;b3]) constr:([8;8;8;8]) Hr | ]);
  reflexivity.

(* Facts from symbolic branches on funct7 and on bits 31..26, as [Z.eqb] facts. *)
Ltac conv_facts :=
  repeat match goal with
  | H : branch_taken _ (v_srliw ?t 25) _ = _ |- _ => change t with t2m in H; rewrite f7_W in H
  | H : branch_taken _ (v_srliw ?t 26) _ = _ |- _ => change t with t2m in H; rewrite b26_W in H
  end;
  repeat match goal with
  | H : branch_taken BC_NE (W (Z.shiftr b3 ?k)) (W 0) = ?bb |- _ =>
      rewrite bt_ne in H by (pose proof sr1; pose proof sr2; lia); cbn [negb] in H;
      first [apply negb_true_iff in H | apply negb_false_iff in H]
  | H : branch_taken BC_NE (W (Z.shiftr b3 ?k)) (Z_to_bv 64 0) = ?bb |- _ =>
      rewrite bt_ne in H by (pose proof sr1; pose proof sr2; lia); cbn [negb] in H;
      first [apply negb_true_iff in H | apply negb_false_iff in H]
  end.

Ltac dec32_leaf Hop Hf :=
  dleaf;
  let r := fresh "r" in let Er := fresh "Er" in
  remember (dec32 w) as r eqn:Er;
  unfold dec32 in Er; cbv zeta in Er; rewrite w_op, Hop in Er;
  (rewrite w_f3, Hf in Er || idtac); rewrite ?w_f7, ?w_26 in Er;
  conv_facts; rewrite ?Z.eqb_refl in Er;
  repeat match goal with H : (Z.shiftr b3 _ =? 0) = _ |- _ => rewrite H in Er end;
  cbn [Z.eqb Pos.eqb andb orb negb] in Er; subst r;
  unfold encb, lebytes, w8; cbv [updt firstn skipn app map repeat length Z.to_nat Pos.to_nat Pos.iter_op Nat.add
    word_to_le_bytes Z_to_le_bytes ik ird ir1 ir2 iimm ilen];
  lst_eq.

Ltac ors H := repeat match type of H with _ \/ _ => let H' := fresh in destruct H as [H'|H] end.

(** The 32-bit half. *)
Theorem decode32_contract : Z.land b0 3 = 3 ->
  RunM ra rom (dpost R0 mem0 (dec32 w)) (mkst R0 (Z_to_bv 64 0x3e91e) mem0 rom).
Proof.
  intros Hlo. norm_rm.
  pose proof (meq_base mem0 o 32) as Ht. assert (HL : length (repeat (@None byte) 32) = 32%nat) by reflexivity.
  pose proof Hw as Hw0. pose proof Hc as Hc0.
  do 6 (let n := pc_of in fd n ltac:(fun F D => astep_with F D dld dst)).
  (* bne a2,a5: not taken *)
  let n := pc_of in fd n ltac:(fun F D =>
    eapply rm_step; [reflexivity | eapply z_branch_ft; [wxf F | reflexivity | exact D | gres;
      revert Hlo; clear Rd0 Rd1 Rd2 Rd3; pattern b0; lazymatch goal with |- ?F b0 => refine (enum1 F ltac:(intros; cbv beta; typeclasses eauto) _ b0 Hb0) end;
      vm_compute; reflexivity] | norm_rm]).
  (* to 0x3e966: the fields, the zeroing stores, the opcode and funct3 *)
  do 15 (let n := pc_of in fd n ltac:(fun F D => astep_with F D dld dst)).
  assert (Hops : Z.land b0 127 = 3 \/ Z.land b0 127 = 7 \/ Z.land b0 127 = 11 \/ Z.land b0 127 = 15 \/ Z.land b0 127 = 19 \/ Z.land b0 127 = 23 \/ Z.land b0 127 = 27 \/ Z.land b0 127 = 31 \/ Z.land b0 127 = 35 \/ Z.land b0 127 = 39 \/ Z.land b0 127 = 43 \/ Z.land b0 127 = 47 \/ Z.land b0 127 = 51 \/ Z.land b0 127 = 55 \/ Z.land b0 127 = 59 \/ Z.land b0 127 = 63 \/ Z.land b0 127 = 67 \/ Z.land b0 127 = 71 \/ Z.land b0 127 = 75 \/ Z.land b0 127 = 79 \/ Z.land b0 127 = 83 \/ Z.land b0 127 = 87 \/ Z.land b0 127 = 91 \/ Z.land b0 127 = 95 \/ Z.land b0 127 = 99 \/ Z.land b0 127 = 103 \/ Z.land b0 127 = 107 \/ Z.land b0 127 = 111 \/ Z.land b0 127 = 115 \/ Z.land b0 127 = 119 \/ Z.land b0 127 = 123 \/ Z.land b0 127 = 127).
  { revert Hlo. clear Rd0 Rd1 Rd2 Rd3. pattern b0.
    lazymatch goal with |- ?F b0 => refine (enum1 F ltac:(intros; cbv beta; typeclasses eauto) _ b0 Hb0) end.
    vm_compute. reflexivity. }
  ors Hops; match goal with H : Z.land b0 127 = _ |- _ => rename H into Hop end;
  rewrite (op_W _ Hop);
  lazymatch type of Hop with
  | _ = ?c =>
      let nf := eval vm_compute in ((c =? 3) || (c =? 19) || (c =? 35) || (c =? 51) || (c =? 99) || (c =? 103)) in
      lazymatch nf with
      | true =>
          assert (Hfs : Z.land (Z.shiftr b1 4) 7 = 0 \/ Z.land (Z.shiftr b1 4) 7 = 1 \/ Z.land (Z.shiftr b1 4) 7 = 2 \/ Z.land (Z.shiftr b1 4) 7 = 3 \/ Z.land (Z.shiftr b1 4) 7 = 4 \/ Z.land (Z.shiftr b1 4) 7 = 5 \/ Z.land (Z.shiftr b1 4) 7 = 6 \/ Z.land (Z.shiftr b1 4) 7 = 7) by
            (clear Rd0 Rd1 Rd2 Rd3; pattern b1;
             lazymatch goal with |- ?F b1 => refine (enum1 F ltac:(intros; cbv beta; typeclasses eauto) _ b1 Hb1) end;
             vm_compute; reflexivity);
          ors Hfs; match goal with H : Z.land (Z.shiftr b1 4) 7 = _ |- _ => rename H into Hf end;
          rewrite t0_W, Hf
      | false => pose proof I as Hf
      end
  end.
  all: dgo32.
  all: try discriminate.
  all: dec32_leaf Hop Hf.
Qed.

Lemma cdec16_eq : Z.land b0 3 <> 3 -> cdec b0 b1 b2 b3 = dec16 (Z.lor b0 (Z.shiftl b1 8)).
Proof. intros H. unfold cdec. rewrite lo3. destruct (Z.eqb_spec (Z.land b0 3) 3); [contradiction|reflexivity]. Qed.

(** The whole function: every input. *)
Theorem decode_contract : RunM ra rom (dpost R0 mem0 (cdec b0 b1 b2 b3)) (mkst R0 (Z_to_bv 64 0x3e91e) mem0 rom).
Proof.
  destruct (Z.eq_dec (Z.land b0 3) 3) as [E|E].
  - rewrite (cdec32_eq E). exact (decode32_contract E).
  - rewrite (cdec16_eq E). apply decode16_contract; assumption.
Qed.

End Dec32.
