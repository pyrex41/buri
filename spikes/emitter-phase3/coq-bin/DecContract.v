(** * [decode] on its compiled bytes (0x3e91e, 352 instructions, dec16 and dec32 inlined).

    For any registers [R0] with a0 = the result pointer [o] and a1 = the input pointer [p]: the
    function returns to [ra] with the 32 bytes at [o] equal to [encb (cdec b0 b1 b2 b3)], all other
    memory unchanged, and every register except t0-t5 and a1-a7 as it was.  The bytes p[2], p[3]
    need only be readable when the low two bits of p[0] are 11. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From stdpp Require Import base decidable bitvector.definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.s9bin_ns Require Import s9bin_code BinGcStep BinMoveStep BinGcTac BinGcMem BinRun BinMem BinBits DecSpec DecPost.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope Z_scope.

Section Dec.
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
Hypothesis Rd0 : rdn source_segs mem0 (v_addi p 0) 1 = Some [Z_to_bv 8 b0].
Hypothesis Rd1 : rdn source_segs mem0 (v_addi p 1) 1 = Some [Z_to_bv 8 b1].

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

Ltac dgo :=
  repeat (let n := pc_of in fd n ltac:(fun F D =>
    lazymatch type of D with
    | _ = Some (Jalr 0 1 _, _) => dret F D
    | _ = Some (Jalr 0 _ _, _) => fail
    | _ => astep_with F D dld dst
    end)).

(* At a return: the registers by the frame conditions, and the bytes as one template. *)
Ltac dregs := intros x Hx; destruct Hx as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);
  repeat (rewrite getr_other by assumption); reflexivity.

Ltac dleaf := split; [dregs | lazymatch goal with Ht : meq _ (wtpl _ _ _) |- _ =>
  eapply meq_fin; [exact Ht | | unfold encb; rewrite ?length_app, ?length_word_to_le_bytes; cbn; lia] end].

Ltac enum16 :=
  try discriminate;
  clear Rd0 Rd1;
  repeat match goal with H : branch_taken _ _ _ = _ |- _ => revert H end;
  pattern b0, b1;
  lazymatch goal with |- ?F b0 b1 =>
    let f := constr:(fun u v : Z => ltac:(let t := eval cbv beta in (F u v) in let bb := boolify t in exact bb)) in
    refine (enum2b F f _ _ b0 b1 Hb0 Hb1);
    [ intros u v; cbv beta; impl_chain | vm_compute; reflexivity ]
  end.

Lemma lo_and3 : Z.land (Z.lor b0 (Z.shiftl b1 8)) 3 = Z.land b0 3.
Proof.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i 2) as [Hl|Hl].
  - rewrite (Z.testbit_neg_r b1) by lia. rewrite orb_false_r. reflexivity.
  - rewrite (tb_small 3 2 i) by lia. rewrite !andb_false_r. reflexivity.
Qed.

(** The compressed path: every 16-bit input. *)
Theorem decode16_contract : Z.land b0 3 <> 3 ->
  RunM ra rom (dpost R0 mem0 (dec16 (Z.lor b0 (Z.shiftl b1 8)))) (mkst R0 (Z_to_bv 64 0x3e91e) mem0 rom).
Proof.
  intros Hlo. norm_rm.
  pose proof (meq_base mem0 o 32) as Ht. assert (HL : length (repeat (@None byte) 32) = 32%nat) by reflexivity.
  pose proof Hw as Hw0. pose proof Hc as Hc0.
  do 6 (let n := pc_of in fd n ltac:(fun F D => astep_with F D dld dst)).
  (* bne a2,a5: taken, by the low bits *)
  let n := pc_of in fd n ltac:(fun F D =>
    eapply rm_step; [reflexivity | eapply z_branch_tk; [wxf F | reflexivity | exact D | gres;
      revert Hlo; clear Rd0 Rd1; pattern b0; lazymatch goal with |- ?F b0 => refine (enum1 F ltac:(intros; cbv beta; typeclasses eauto) _ b0 Hb0) end;
      vm_compute; reflexivity] | unfold btgt; imm_norm; norm_rm]).
  Time dgo.
  Time all: dleaf.
  Time all: enum16.
Qed.


End Dec.
