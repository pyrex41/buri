(** * Emitted RV64 for one code object simulates its bytecode (Shen/JIT Phase 0, spike 4).

    The machine side is Theorem's [RiscvSemantics.step] on the exact bytes the real
    emitter wrote.  The emitter is not proved: the bytes are captured from a run.  The
    theorem stops at helper calls, so the helpers' behavior is unproved too. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec MemSplit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Examples.jit_slice Require Import SliceCode SliceBytecode SliceStep SliceFacts.
Import ListNotations.
Open Scope bv_scope.

(** Helper entry points in the capture binary: [h_prim] and [h_alloc] by symbol table. *)
Definition H_PRIM : word := Z_to_bv 64 0x277c0.
Definition H_ALLOC : word := Z_to_bv 64 0x27860.

Definition le (v : word) := word_to_le_bytes 8 v.

(* ------------------------------------------------------------------ *)
(* Value facts                                                         *)
(* ------------------------------------------------------------------ *)

Lemma alu_add : forall (a : word) (imm : bv 12),
  alu64 ALU_ADD a (sext 64 imm) = v_addi a (bv_signed imm).
Proof. intros. apply b_addsext. Qed.

Lemma alu_mv : forall v : word, alu64 ALU_ADD (Z_to_bv 64 0) v = v.
Proof.
  intros v. apply bv_eq. change (alu64 ALU_ADD (Z_to_bv 64 0) v) with (Z_to_bv 64 0 + v).
  rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0%Z.
  rewrite Z.add_0_l. apply bv_wrap_bv_unsigned.
Qed.

Lemma alu_mv_r : forall v : word, alu64 ALU_ADD v (Z_to_bv 64 0) = v.
Proof.
  intros v. apply bv_eq. change (alu64 ALU_ADD v (Z_to_bv 64 0)) with (v + Z_to_bv 64 0).
  rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0%Z.
  rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

Lemma tag_land : forall u, (0 <= u)%Z -> Z.land u 7 = (u mod 8)%Z.
Proof. intros u Hu. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(** The emitted test is on x - 3, not on x, and it is the same test as [tag3 x = 3]. *)
Lemma tag_taken : forall x : word,
  branch_taken BC_NE (alu64 ALU_AND (v_addi x (-3)) (sext 64 (7 : bv 12))) (Z_to_bv 64 0)
    = negb (Z.eqb (tag3 x) TAG_PAIR).
Proof.
  intros x. cbn [branch_taken]. unfold bv_eqb, tag3, TAG_PAIR.
  f_equal.
  change (alu64 ALU_AND (v_addi x (-3)) (sext 64 (7 : bv 12)))
    with (bv_and (v_addi x (-3)) (sext 64 (7 : bv 12))).
  rewrite bv_and_unsigned.
  assert (H7 : bv_unsigned (sext 64 (7 : bv 12)) = 7%Z) by (vm_compute; reflexivity).
  rewrite H7. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  pose proof (bv_unsigned_in_range _ x) as Hx.
  unfold bv_modulus in Hx.
  unfold v_addi. rewrite Z_to_bv_unsigned.
  set (u := bv_unsigned x) in *.
  assert (Hw : (0 <= bv_wrap 64 (u + -3))%Z).
  { unfold bv_wrap, bv_modulus. apply Z.mod_pos_bound. lia. }
  rewrite (tag_land _ Hw), (tag_land u) by lia.
  unfold bv_wrap, bv_modulus.
  rewrite Z.mod_mod_divide by (exists (2^61)%Z; reflexivity).
  rewrite <- (Zplus_mod_idemp_l u (-3) 8).
  pose proof (Z.mod_pos_bound u 8 ltac:(lia)) as Hr.
  destruct (Z.modulo u 8) as [|p|p] eqn:Hm; [reflexivity | | lia].
  assert (Hc : (Z.pos p = 1 \/ Z.pos p = 2 \/ Z.pos p = 3 \/ Z.pos p = 4 \/ Z.pos p = 5 \/ Z.pos p = 6 \/ Z.pos p = 7)%Z) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|H]]]]]]; rewrite H; reflexivity.
Qed.

Lemma tag_low : forall x : word, tag3 x = TAG_PAIR -> (3 <= bv_unsigned x)%Z.
Proof.
  intros x H. unfold tag3, TAG_PAIR in H.
  pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx.
  rewrite tag_land in H by lia.
  pose proof (Z.mod_le (bv_unsigned x) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma ltu_taken : forall (l h : word), (bv_unsigned h + 16 < 2^64)%Z ->
  branch_taken BC_LTU l (v_addi h 16) = Z.ltb (bv_unsigned l) (bv_unsigned h + 16).
Proof.
  intros l h Hh. cbn [branch_taken]. unfold bv_ltu.
  rewrite v_addi_nneg by lia. reflexivity.
Qed.

Section Rel.
Variable segs : list Segment.
Variable fp vm : word.

(** Layout: the frame, the VM's first fields, the bump room and the code don't overlap,
    and no heap word overlaps the frame or the bump room. *)
Definition apart (a n b k : Z) : Prop := (a + n <= b \/ b + k <= a)%Z.

Definition slot_at (k : nat) : word := v_addi fp (8 * Z.of_nat k).

Record Layout (st : bstate) : Prop := {
  l_fp : (bv_unsigned fp + 48 < 2^64)%Z;
  l_vm : (bv_unsigned vm + 64 < 2^64)%Z;
  l_hp : (bv_unsigned (bhp st) + 16 < 2^64)%Z;
  l_fv : apart (bv_unsigned fp) 48 (bv_unsigned vm) 64;
  l_fh : apart (bv_unsigned fp) 48 (bv_unsigned (bhp st)) 16;
  l_vh : apart (bv_unsigned vm) 64 (bv_unsigned (bhp st)) 16;
  l_fc : apart (bv_unsigned fp) 48 code_base code_len;
  l_vc : apart (bv_unsigned vm) 64 code_base code_len;
  l_hc : apart (bv_unsigned (bhp st)) 16 code_base code_len;
  l_heap : forall a v, bheap st a = Some v ->
    (bv_unsigned a + 8 <= 2^64)%Z /\
    apart (bv_unsigned a) 8 (bv_unsigned fp) 48 /\
    apart (bv_unsigned a) 8 (bv_unsigned vm) 64 /\
    apart (bv_unsigned a) 8 (bv_unsigned (bhp st)) 16
}.

(** Memory holds the live slots, the heap limit, and the heap. *)
Record MemRel (live : nat) (st : bstate) (m : word -> option byte) : Prop := {
  m_slots : forall k, (k < live)%nat -> rdn segs m (slot_at k) 8 = Some (le (bslots st k));
  m_limit : rdn segs m (v_addi vm 8) 8 = Some (le (bhlimit st));
  m_heap : forall a v, bheap st a = Some v -> rdn segs m a 8 = Some (le v)
}.

(** Every location the emitted code stores to is mapped and writable. *)
Record Writable (st : bstate) (m : word -> option byte) : Prop := {
  w_s4 : store_ok segs m (slot_at 4) 8 = true;
  w_h0 : store_ok segs m (bhp st) 8 = true;
  w_h8 : store_ok segs m (v_addi (bhp st) 8) 8 = true;
  w_v0 : store_ok segs m vm 8 = true;
  w_v16 : store_ok segs m (v_addi vm 16) 8 = true;
  w_v24 : store_ok segs m (v_addi vm 24) 8 = true;
  w_v56 : store_ok segs m (v_addi vm 56) 8 = true
}.

(** The entry relation: registers per src/runtime/jit.c ([FP] s0, [VMR] s1, [CACHE] s2,
    [HP] s3, [COUNT] a2), slots, heap limit and heap.  A pair in slot 2 has a head. *)
Record Rel (st : bstate) (regs : bvmap 5 word) (m : word -> option byte) : Prop := {
  r_fp : getr regs 8 = fp;
  r_vm : getr regs 9 = vm;
  r_cache : getr regs 18 = bslots st 2;
  r_hp : getr regs 19 = bhp st;
  r_count : getr regs 12 = Z_to_bv 64 2;
  r_layout : Layout st;
  r_mem : MemRel 6 st m;
  r_write : Writable st m;
  r_code : CodeOK segs m;
  r_pair : tag3 (bslots st 2) = TAG_PAIR -> exists v, bheap st (vadd (bslots st 2) (-3)) = Some v
}.

Definition Preserved (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, r <> 1 -> r <> 5 -> r <> 6 -> r <> 10 -> r <> 11 -> r <> 13 -> r <> 18 -> r <> 19 ->
    getr regs' r = getr regs r.

Section Outcome.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variable regs0 : bvmap 5 word.

(** What the machine state must be, for each bytecode outcome.  After a return only slots
    0-4 are required, since the code keeps slot 5 in [CACHE] and the frame is finished. *)
Definition Outcome (r : bresult) (ms : machine_state) : Prop :=
  match r with
  | BReturn v st' => exists regs' m',
      ms = mkst regs' (jalr_tgt (bslots st' 0) 0) m' rom /\
      getr regs' 10 = v /\ getr regs' 19 = bhp st' /\
      Preserved regs0 regs' /\ MemRel 5 st' m' /\ CodeOK segs m'
  | BRaise op x st' => exists regs' m',
      ms = mkst regs' H_PRIM m' rom /\
      getr regs' 10 = vm /\ getr regs' 11 = Z_to_bv 64 op /\ getr regs' 1 = at_ 94 /\
      getr regs' 19 = bhp st' /\ getr regs' 18 = x /\ Preserved regs0 regs' /\
      rdn segs m' vm 8 = Some (le (bhp st')) /\
      rdn segs m' (v_addi vm 16) 8 = Some (le fp) /\
      rdn segs m' (v_addi vm 24) 8 = Some (le (v_addi fp 48)) /\
      rdn segs m' (v_addi vm 56) 8 = Some (le x) /\
      MemRel 6 st' m' /\ CodeOK segs m'
  | BCollect n st' => exists regs' m',
      ms = mkst regs' H_ALLOC m' rom /\
      getr regs' 10 = vm /\ getr regs' 11 = Z_to_bv 64 n /\ getr regs' 1 = at_ 132 /\
      getr regs' 19 = bhp st' /\ getr regs' 18 = bslots st' 4 /\ Preserved regs0 regs' /\
      rdn segs m' vm 8 = Some (le (bhp st')) /\
      rdn segs m' (v_addi vm 16) 8 = Some (le fp) /\
      rdn segs m' (v_addi vm 24) 8 = Some (le (v_addi fp 48)) /\
      MemRel 5 st' m' /\ CodeOK segs m'
  | BStuck => False
  end.

(* ------------------------------------------------------------------ *)
(* Steps with explicit results, so the register file stays small        *)
(* ------------------------------------------------------------------ *)

Lemma j_opimm_v : forall regs o o' mem op rd rs (imm : bv 12) sz w v,
  wx_fetch segs mem (at_ o) w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, sz) ->
  (o + sz = o')%Z -> is_x0 rd = false ->
  alu64 op (getr regs rs) (sext 64 imm) = v ->
  RiscvSemantics.step segs (mkst regs (at_ o) mem rom) =
  MachineOk (mkst (regupd regs rd v) (at_ o') mem rom).
Proof. intros. subst v. eapply j_opimm; eauto. Qed.

Lemma j_op_v : forall regs o o' mem op rd rs1 rs2 sz w v,
  wx_fetch segs mem (at_ o) w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, sz) ->
  (o + sz = o')%Z -> is_x0 rd = false ->
  alu64 op (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs (at_ o) mem rom) =
  MachineOk (mkst (regupd regs rd v) (at_ o') mem rom).
Proof. intros. subst v. eapply j_op; eauto. Qed.

End Outcome.

(* ------------------------------------------------------------------ *)
(* The three paths                                                     *)
(* ------------------------------------------------------------------ *)

Section Paths.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variable st : bstate.
Variable regs : bvmap 5 word.
Variable m : word -> option byte.
Hypothesis R : Rel st regs m.

Ltac dj :=
  unfold slot_at, le, apart in *;
  rewrite ?length_word_to_le_bytes;
  repeat (rewrite v_addi_nneg by (cbn [Z.of_nat Z.mul] in *; lia));
  cbn [Z.of_nat Z.mul] in *; lia.

Ltac gr H1 H2 H3 H4 H5 :=
  repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero, ?H1, ?H2, ?H3, ?H4, ?H5.

Local Ltac rdtac :=
  repeat first
    [ rewrite rdn_wbytes_hit8 by dj
    | rewrite rdn_wbytes_out by dj ].

Local Ltac wxc :=
  apply wx_at;
  [ repeat (apply code_ok_wbytes; [ | dj | dj ]); apply (r_code _ _ _ R)
  | lia | vm_compute; discriminate | reflexivity ].

Local Ltac swok S :=
  repeat eapply store_ok_mono; try apply S.

Local Ltac pres := intros r0 ?N1 ?N2 ?N3 ?N4 ?N5 ?N6 ?N7 ?N8;
  repeat (rewrite getr_other by assumption); reflexivity.

Local Ltac heapd Lheap a v Ha :=
  let H := fresh in pose proof (Lheap a v Ha) as H; destruct H as (?Hah & ?Haf & ?Hav & ?Hap).

Local Ltac codes C := repeat (apply code_ok_wbytes; [ | dj | dj ]); exact C.

(** Entry: arity check, then the tag test on slot 2. *)
Local Ltac prefix H1 H2 H3 H4 H5 x :=
  eapply steps_step;
  [ eapply (j_opimm_v rom) with (o' := 2%Z) (v := Z_to_bv 64 2);
    [ wxc | exact E_0 | exact D_0 | reflexivity | reflexivity
    | gr H1 H2 H3 H4 H5; rewrite alu_add; bveq ] | ];
  eapply steps_step;
  [ eapply j_br_ft with (o' := 6%Z);
    [ wxc | exact E_2 | exact D_2 | reflexivity
    | gr H1 H2 H3 H4 H5; reflexivity ] | ];
  eapply steps_step;
  [ eapply (j_opimm_v rom) with (o' := 10%Z) (v := v_addi x (-3));
    [ wxc | exact E_6 | exact D_6 | reflexivity | reflexivity
    | gr H1 H2 H3 H4 H5; rewrite alu_add; reflexivity ] | ];
  eapply steps_step;
  [ eapply (j_opimm_v rom) with (o' := 14%Z)
      (v := alu64 ALU_AND (v_addi x (-3)) (sext 64 (7 : bv 12)));
    [ wxc | exact E_10 | exact D_10 | reflexivity | reflexivity
    | gr H1 H2 H3 H4 H5; reflexivity ] | ].

Theorem path_error :
  tag3 (bslots st 2) <> TAG_PAIR ->
  exists ms, steps segs (mkst regs (at_ 0) m rom) ms /\
    Outcome rom regs (BRaise P_HD (bslots st 2) st) ms.
Proof.
  intros Htag.
  destruct R as [Hfp Hvm Hc Hh Hcnt L M W C Pr].
  destruct L as [Lf Lv Lh Lfv Lfh Lvh Lfc Lvc Lhc Lheap].
  destruct W as [W4 W0 W8 V0 V16 V24 V56].
  set (x := bslots st 2) in *.
  assert (S2 : rdn segs m (v_addi fp 16) 8 = Some (le x)) by exact (m_slots _ _ _ M 2 ltac:(lia)).
  eexists. split.
  - prefix Hfp Hvm Hc Hh Hcnt x.
    (* 0x0e: not a pair, to the slow path at 0x42 *)
    eapply steps_step;
    [ eapply j_br_tk with (o' := 66%Z);
      [ wxc | exact E_14 | exact D_14 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt;
        rewrite tag_taken;
        cbv zeta; destruct (Z.eqb_spec (tag3 x) TAG_PAIR) as [He|He];
        [ exfalso; exact (Htag He) | reflexivity ] ] | ].
    (* publish the frame pointer *)
    eapply steps_step;
    [ eapply j_sd with (o' := 68%Z) (a := v_addi vm 16) (v := fp);
      [ wxc | exact E_66 | exact D_66 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | exact V16 ] | ].
    eapply steps_step;
    [ eapply (j_opimm_v rom) with (o' := 72%Z) (v := v_addi fp 48);
      [ wxc | exact E_68 | exact D_68 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; rewrite alu_add; reflexivity ] | ].
    eapply steps_step;
    [ eapply j_sd with (o' := 74%Z) (a := v_addi vm 24) (v := v_addi fp 48);
      [ wxc | exact E_72 | exact D_72 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | eapply store_ok_mono; [ apply wbytes_grows | exact V24 ] ] | ].
    (* the argument, read back from its slot *)
    eapply steps_step;
    [ eapply j_ld with (o' := 78%Z) (v := x);
      [ wxc | exact E_74 | exact D_74 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; imm_norm; rdtac; exact S2 ] | ].
    eapply steps_step;
    [ eapply j_sd with (o' := 82%Z) (a := v_addi vm 56) (v := x);
      [ wxc | exact E_78 | exact D_78 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | repeat (eapply store_ok_mono; [ apply wbytes_grows | ]); exact V56 ] | ].
    eapply steps_step;
    [ eapply (j_op_v rom) with (o' := 84%Z) (v := vm);
      [ wxc | exact E_82 | exact D_82 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; apply alu_mv ] | ].
    eapply steps_step;
    [ eapply (j_opimm_v rom) with (o' := 86%Z) (v := Z_to_bv 64 P_HD);
      [ wxc | exact E_84 | exact D_84 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; rewrite alu_add; bveq ] | ].
    eapply steps_step;
    [ eapply j_sd with (o' := 90%Z) (a := vm) (v := bhp st);
      [ wxc | exact E_86 | exact D_86 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; imm_norm; apply v_addi_0
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | repeat (eapply store_ok_mono; [ apply wbytes_grows | ]); exact V0 ] | ].
    eapply steps_step;
    [ eapply (j_jal_link) with (o' := 94%Z) (tgt := H_PRIM);
      [ wxc | exact E_90 | exact D_90 | reflexivity | bveq ] | ].
    apply steps_refl.
  - cbn [Outcome]. do 2 eexists. split; [ reflexivity | ].
    repeat apply conj.
    + gr Hfp Hvm Hc Hh Hcnt; reflexivity.
    + gr Hfp Hvm Hc Hh Hcnt; reflexivity.
    + gr Hfp Hvm Hc Hh Hcnt; reflexivity.
    + gr Hfp Hvm Hc Hh Hcnt; reflexivity.
    + gr Hfp Hvm Hc Hh Hcnt; reflexivity.
    + unfold Preserved. pres.
    + rdtac; reflexivity.
    + rdtac; reflexivity.
    + rdtac; reflexivity.
    + rdtac; reflexivity.
    + constructor.
      * intros k Hk. rdtac. exact (m_slots _ _ _ M k Hk).
      * rdtac. exact (m_limit _ _ _ M).
      * intros a v Ha. heapd Lheap a v Ha. rdtac. exact (m_heap _ _ _ M a v Ha).
    + codes C.
Qed.

(** The tag test passes and the head has been read, so slot 4 is set. *)
Theorem path_alloc : forall h,
  tag3 (bslots st 2) = TAG_PAIR ->
  bheap st (vadd (bslots st 2) (-3)) = Some h ->
  (bv_unsigned (bhlimit st) < bv_unsigned (bhp st) + 16)%Z ->
  exists ms, steps segs (mkst regs (at_ 0) m rom) ms /\
    Outcome rom regs (BCollect 2 (set_slot st 4 h)) ms.
Proof.
  intros h Htag Hhead Hlim.
  destruct R as [Hfp Hvm Hc Hh Hcnt L M W C Pr].
  destruct L as [Lf Lv Lh Lfv Lfh Lvh Lfc Lvc Lhc Lheap].
  destruct W as [W4 W0 W8 V0 V16 V24 V56].
  set (x := bslots st 2) in *.
  assert (S4 : store_ok segs m (v_addi fp 32) 8 = true) by exact W4.
  pose proof (tag_low x Htag) as Hx3.
  assert (Hr : rdn segs m (v_addi x (-3)) 8 = Some (le h)) by exact (m_heap _ _ _ M _ _ Hhead).
  eexists. split.
  - prefix Hfp Hvm Hc Hh Hcnt x.
    eapply steps_step;
    [ eapply j_br_ft with (o' := 18%Z);
      [ wxc | exact E_14 | exact D_14 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt;
        rewrite tag_taken; rewrite Htag; reflexivity ] | ].
    eapply steps_step;
    [ eapply j_ld with (o' := 22%Z) (v := h);
      [ wxc | exact E_18 | exact D_18 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; imm_norm; exact Hr ] | ].
    eapply steps_step;
    [ eapply j_sd with (o' := 24%Z) (a := v_addi fp 32) (v := h);
      [ wxc | exact E_22 | exact D_22 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | exact S4 ] | ].
    eapply steps_step;
    [ eapply (j_op_v rom) with (o' := 26%Z) (v := h);
      [ wxc | exact E_24 | exact D_24 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; apply alu_mv ] | ].
    eapply steps_step;
    [ eapply (j_opimm_v rom) with (o' := 30%Z) (v := v_addi (bhp st) 16);
      [ wxc | exact E_26 | exact D_26 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; rewrite alu_add; reflexivity ] | ].
    eapply steps_step;
    [ eapply j_ld with (o' := 34%Z) (v := bhlimit st);
      [ wxc | exact E_30 | exact D_30 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; imm_norm; rdtac; exact (m_limit _ _ _ M) ] | ].
    (* 0x22: no room, to the slow path at 0x70 *)
    eapply steps_step;
    [ eapply j_br_tk with (o' := 112%Z);
      [ wxc | exact E_34 | exact D_34 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; rewrite ltu_taken by lia; apply Z.ltb_lt; exact Hlim ] | ].
    eapply steps_step;
    [ eapply j_sd with (o' := 114%Z) (a := v_addi vm 16) (v := fp);
      [ wxc | exact E_112 | exact D_112 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | repeat (eapply store_ok_mono; [ apply wbytes_grows | ]); exact V16 ] | ].
    eapply steps_step;
    [ eapply (j_opimm_v rom) with (o' := 118%Z) (v := v_addi fp 48);
      [ wxc | exact E_114 | exact D_114 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; rewrite alu_add; reflexivity ] | ].
    eapply steps_step;
    [ eapply j_sd with (o' := 120%Z) (a := v_addi vm 24) (v := v_addi fp 48);
      [ wxc | exact E_118 | exact D_118 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | repeat (eapply store_ok_mono; [ apply wbytes_grows | ]); exact V24 ] | ].
    eapply steps_step;
    [ eapply (j_op_v rom) with (o' := 122%Z) (v := vm);
      [ wxc | exact E_120 | exact D_120 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; apply alu_mv ] | ].
    eapply steps_step;
    [ eapply (j_opimm_v rom) with (o' := 124%Z) (v := Z_to_bv 64 2);
      [ wxc | exact E_122 | exact D_122 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; rewrite alu_add; bveq ] | ].
    eapply steps_step;
    [ eapply j_sd with (o' := 128%Z) (a := vm) (v := bhp st);
      [ wxc | exact E_124 | exact D_124 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; imm_norm; apply v_addi_0
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | repeat (eapply store_ok_mono; [ apply wbytes_grows | ]); exact V0 ] | ].
    eapply steps_step;
    [ eapply (j_jal_link) with (o' := 132%Z) (tgt := H_ALLOC);
      [ wxc | exact E_128 | exact D_128 | reflexivity | bveq ] | ].
    apply steps_refl.
  - cbn [Outcome]. do 2 eexists. split; [ reflexivity | ].
    repeat apply conj.
    + gr Hfp Hvm Hc Hh Hcnt; reflexivity.
    + gr Hfp Hvm Hc Hh Hcnt; reflexivity.
    + gr Hfp Hvm Hc Hh Hcnt; reflexivity.
    + gr Hfp Hvm Hc Hh Hcnt; reflexivity.
    + gr Hfp Hvm Hc Hh Hcnt; reflexivity.
    + unfold Preserved. pres.
    + rdtac; reflexivity.
    + rdtac; reflexivity.
    + rdtac; reflexivity.
    + constructor.
      * intros k Hk. destruct (Nat.eq_dec k 4) as [->|Hn].
        -- change (slot_at 4) with (v_addi fp 32). rdtac. reflexivity.
        -- cbn [bslots set_slot].
           replace (Nat.eqb k 4) with false by (symmetry; apply Nat.eqb_neq; exact Hn).
           rdtac. exact (m_slots _ _ _ M k ltac:(lia)).
      * cbn [bhlimit set_slot]. rdtac. exact (m_limit _ _ _ M).
      * intros a v Ha. cbn [bheap set_slot] in Ha. heapd Lheap a v Ha. rdtac. exact (m_heap _ _ _ M a v Ha).
    + codes C.
Qed.

(** The fast path: the head is read, a pair is bump-allocated, and its address returned. *)
Theorem path_return : forall h,
  tag3 (bslots st 2) = TAG_PAIR ->
  bheap st (vadd (bslots st 2) (-3)) = Some h ->
  (bv_unsigned (bhp st) + 16 <= bv_unsigned (bhlimit st))%Z ->
  let st' := set_slot (heap_cons (set_slot st 4 h) h (bslots st 3)) 5 (vadd (bhp st) TAG_PAIR) in
  exists ms, steps segs (mkst regs (at_ 0) m rom) ms /\
    Outcome rom regs (BReturn (vadd (bhp st) TAG_PAIR) st') ms.
Proof.
  intros h Htag Hhead Hlim st'.
  destruct R as [Hfp Hvm Hc Hh Hcnt L M W C Pr].
  destruct L as [Lf Lv Lh Lfv Lfh Lvh Lfc Lvc Lhc Lheap].
  destruct W as [W4 W0 W8 V0 V16 V24 V56].
  set (x := bslots st 2) in *.
  assert (S4 : store_ok segs m (v_addi fp 32) 8 = true) by exact W4.
  pose proof (tag_low x Htag) as Hx3.
  assert (Hr : rdn segs m (v_addi x (-3)) 8 = Some (le h)) by exact (m_heap _ _ _ M _ _ Hhead).
  assert (S3 : rdn segs m (v_addi fp 24) 8 = Some (le (bslots st 3))) by exact (m_slots _ _ _ M 3 ltac:(lia)).
  assert (S0 : rdn segs m (v_addi fp 0) 8 = Some (le (bslots st 0))) by exact (m_slots _ _ _ M 0 ltac:(lia)).
  eexists. split.
  - prefix Hfp Hvm Hc Hh Hcnt x.
    eapply steps_step;
    [ eapply j_br_ft with (o' := 18%Z);
      [ wxc | exact E_14 | exact D_14 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt;
        rewrite tag_taken; rewrite Htag; reflexivity ] | ].
    eapply steps_step;
    [ eapply j_ld with (o' := 22%Z) (v := h);
      [ wxc | exact E_18 | exact D_18 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; imm_norm; exact Hr ] | ].
    eapply steps_step;
    [ eapply j_sd with (o' := 24%Z) (a := v_addi fp 32) (v := h);
      [ wxc | exact E_22 | exact D_22 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | exact S4 ] | ].
    eapply steps_step;
    [ eapply (j_op_v rom) with (o' := 26%Z) (v := h);
      [ wxc | exact E_24 | exact D_24 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; apply alu_mv ] | ].
    eapply steps_step;
    [ eapply (j_opimm_v rom) with (o' := 30%Z) (v := v_addi (bhp st) 16);
      [ wxc | exact E_26 | exact D_26 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; rewrite alu_add; reflexivity ] | ].
    eapply steps_step;
    [ eapply j_ld with (o' := 34%Z) (v := bhlimit st);
      [ wxc | exact E_30 | exact D_30 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; imm_norm; rdtac; exact (m_limit _ _ _ M) ] | ].
    eapply steps_step;
    [ eapply j_br_ft with (o' := 38%Z);
      [ wxc | exact E_34 | exact D_34 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; rewrite ltu_taken by lia; apply Z.ltb_ge; exact Hlim ] | ].
    eapply steps_step;
    [ eapply j_sd with (o' := 42%Z) (a := bhp st) (v := h);
      [ wxc | exact E_38 | exact D_38 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; imm_norm; apply v_addi_0
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | repeat (eapply store_ok_mono; [ apply wbytes_grows | ]); exact W0 ] | ].
    eapply steps_step;
    [ eapply j_ld with (o' := 46%Z) (v := bslots st 3);
      [ wxc | exact E_42 | exact D_42 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; imm_norm; rdtac; exact S3 ] | ].
    eapply steps_step;
    [ eapply j_sd with (o' := 50%Z) (a := v_addi (bhp st) 8) (v := bslots st 3);
      [ wxc | exact E_46 | exact D_46 | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; reflexivity
      | repeat (eapply store_ok_mono; [ apply wbytes_grows | ]); exact W8 ] | ].
    eapply steps_step;
    [ eapply (j_opimm_v rom) with (o' := 54%Z) (v := v_addi (bhp st) 3);
      [ wxc | exact E_50 | exact D_50 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; rewrite alu_add; reflexivity ] | ].
    eapply steps_step;
    [ eapply (j_op_v rom) with (o' := 56%Z) (v := v_addi (bhp st) 3);
      [ wxc | exact E_54 | exact D_54 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; apply alu_mv ] | ].
    eapply steps_step;
    [ eapply (j_opimm_v rom) with (o' := 58%Z) (v := v_addi (bhp st) 16);
      [ wxc | exact E_56 | exact D_56 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; rewrite alu_add; reflexivity ] | ].
    eapply steps_step;
    [ eapply (j_op_v rom) with (o' := 60%Z) (v := v_addi (bhp st) 3);
      [ wxc | exact E_58 | exact D_58 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; apply alu_mv ] | ].
    eapply steps_step;
    [ eapply j_ld with (o' := 64%Z) (v := bslots st 0);
      [ wxc | exact E_60 | exact D_60 | reflexivity | reflexivity
      | gr Hfp Hvm Hc Hh Hcnt; imm_norm; rdtac; exact S0 ] | ].
    eapply steps_step;
    [ eapply j_ret; [ wxc | exact E_64 | exact D_64 ] | ].
    apply steps_refl.
  - cbn [Outcome]. do 2 eexists. split.
    { f_equal. gr Hfp Hvm Hc Hh Hcnt. reflexivity. }
    repeat apply conj.
    + gr Hfp Hvm Hc Hh Hcnt; reflexivity.
    + gr Hfp Hvm Hc Hh Hcnt; reflexivity.
    + unfold Preserved. pres.
    + constructor.
      * intros k Hk. unfold st'. cbn [bslots set_slot heap_cons].
        replace (Nat.eqb k 5) with false by (symmetry; apply Nat.eqb_neq; lia).
        destruct (Nat.eq_dec k 4) as [->|Hn].
        -- change (slot_at 4) with (v_addi fp 32). rdtac. reflexivity.
        -- replace (Nat.eqb k 4) with false by (symmetry; apply Nat.eqb_neq; exact Hn).
           rdtac. exact (m_slots _ _ _ M k ltac:(lia)).
      * unfold st'. cbn [bhlimit set_slot heap_cons]. rdtac. exact (m_limit _ _ _ M).
      * intros a v Ha. unfold st' in Ha. cbn [bheap set_slot heap_cons] in Ha.
        destruct (decide (a = bhp st)) as [E1|N1].
        -- rewrite bool_decide_eq_true_2 in Ha by exact E1.
           subst a. injection Ha as <-. rdtac. reflexivity.
        -- rewrite bool_decide_eq_false_2 in Ha by exact N1.
           destruct (decide (a = vadd (bhp st) 8)) as [E2|N2].
           ++ rewrite bool_decide_eq_true_2 in Ha by exact E2.
              subst a. injection Ha as <-.
              change (vadd (bhp st) 8) with (v_addi (bhp st) 8). rdtac. reflexivity.
           ++ rewrite bool_decide_eq_false_2 in Ha by exact N2.
              heapd Lheap a v Ha. rdtac. exact (m_heap _ _ _ M a v Ha).
    + codes C.
Qed.

(** The refinement statement: from any state in the relation, the machine reaches a state
    related to what the bytecode does. *)
Theorem slice_refines :
  exists ms, steps segs (mkst regs (at_ 0) m rom) ms /\ Outcome rom regs (brun slice_prog st) ms.
Proof.
  destruct (Z.eq_dec (tag3 (bslots st 2)) TAG_PAIR) as [Ht|Ht].
  - destruct (r_pair _ _ _ R Ht) as [h Hh].
    destruct (Z_lt_le_dec (bv_unsigned (bhlimit st)) (bv_unsigned (bhp st) + 16)) as [Hl|Hl].
    + destruct (path_alloc h Ht Hh Hl) as [ms [Hs Ho]]. exists ms. split; [exact Hs|].
      unfold slice_prog. cbn [brun].
      apply Z.eqb_eq in Ht. rewrite Ht. rewrite Hh. cbn [set_slot bhlimit bhp].
      apply Z.ltb_lt in Hl. rewrite Hl. exact Ho.
    + destruct (path_return h Ht Hh Hl) as [ms [Hs Ho]]. exists ms. split; [exact Hs|].
      unfold slice_prog. cbn [brun].
      apply Z.eqb_eq in Ht. rewrite Ht. rewrite Hh. cbn [set_slot bhlimit bhp].
      replace (Z.ltb (bv_unsigned (bhlimit st)) (bv_unsigned (bhp st) + 16)) with false
        by (symmetry; apply Z.ltb_ge; exact Hl).
      exact Ho.
  - destruct (path_error Ht) as [ms [Hs Ho]]. exists ms. split; [exact Hs|].
    unfold slice_prog. cbn [brun].
    replace (Z.eqb (tag3 (bslots st 2)) TAG_PAIR) with false
      by (symmetry; apply Z.eqb_neq; exact Ht).
    exact Ho.
Qed.

End Paths.
End Rel.

Print Assumptions slice_refines.
