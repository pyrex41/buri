(** * One bytecode instruction at a time: accepted bytes follow the bytecode (Shen/JIT Phase 0, spike 8). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Examples.emitter_p3_ns Require Import CfDefs CfStep CfRun CfSound.
Import ListNotations.
Open Scope bv_scope.

Lemma tag_taken : forall x : word,
  branch_taken BC_NE (alu64 ALU_AND (v_addi x (-3)) (sext 64 (7 : bv 12))) (Z_to_bv 64 0)
    = negb (Z.eqb (tag3 x) 3).
Proof.
  intros x. cbn [branch_taken]. unfold bv_eqb, tag3.
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
  assert (Hl : forall v, (0 <= v)%Z -> Z.land v 7 = (v mod 8)%Z)
    by (intros v Hv; change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  rewrite (Hl _ Hw), (Hl u) by lia.
  unfold bv_wrap, bv_modulus.
  rewrite Z.mod_mod_divide by (exists (2^61)%Z; reflexivity).
  rewrite <- (Zplus_mod_idemp_l u (-3) 8).
  pose proof (Z.mod_pos_bound u 8 ltac:(lia)) as Hr.
  destruct (Z.modulo u 8) as [|p|p] eqn:Hm; [reflexivity | | lia].
  assert (Hc : (Z.pos p = 1 \/ Z.pos p = 2 \/ Z.pos p = 3 \/ Z.pos p = 4 \/ Z.pos p = 5 \/ Z.pos p = 6 \/ Z.pos p = 7)%Z) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|H]]]]]]; rewrite H; reflexivity.
Qed.

Lemma bv_eqb_sym : forall n (a b : bv n), bv_eqb a b = bv_eqb b a.
Proof. intros. unfold bv_eqb. apply Z.eqb_sym. Qed.

Section StepSim.
Context {fx : FPState}.
Variable c : cfg.
Variable cell_of : Z -> option Z.
Variable segs : list Segment.
Variable rom : word -> option byte.
Variable regs0 : bvmap 5 word.
Variables fp vm : word.
Variable keq : word -> word -> bool.
Variables vtrue vfalse : word.
Hypothesis Htrue : tag3 vtrue <> 3%Z.
Hypothesis Hfalse : tag3 vfalse <> 3%Z.
Hypothesis Hkeq : forall x y, identity_tag (tag3 x) = true -> keq x y = bv_eqb x y /\ keq y x = bv_eqb x y.
Hypothesis WfK : forall i w, ckinds c i = Some (KImm w) -> (0 <= w < 2^64)%Z.
Variable p : list binstr.
Variable cut : nat -> Z.
Variable inv : nat -> option CS.
Variable fuel : nat.
Hypothesis ACC : check_all c cell_of p cut inv fuel = true.

Abbreviation Rel := (Rel c segs regs0 fp vm).
Abbreviation E st := (E fp vm st (Z_to_bv 64 0) (Z_to_bv 64 0)).

Lemma acc_at : forall i ins, nth_error p i = Some ins -> check_at c cell_of p cut inv fuel i = true.
Proof.
  intros i ins H. unfold check_all in ACC. rewrite forallb_forall in ACC. apply ACC.
  apply in_seq. split; [lia|]. pose proof (proj1 (nth_error_Some p i) ltac:(rewrite H; discriminate)). lia.
Qed.

Lemma acc_end : inv (length p) = None.
Proof.
  unfold check_all in ACC. rewrite forallb_forall in ACC.
  pose proof (ACC (length p) ltac:(apply in_seq; lia)) as H. unfold check_at in H.
  destruct (inv (length p)); [|reflexivity].
  rewrite (proj2 (nth_error_None p (length p)) (le_n _)) in H. discriminate.
Qed.

Lemma tag3_bound : forall x, (0 <= tag3 x < 8)%Z.
Proof. intros x. unfold tag3. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma abs_op_eval : forall s st regs m o,
  Rel s st regs m -> known (abs_op c o) = true -> eval (E st) (abs_op c o) = opval st o.
Proof.
  intros s st regs m o R K. destruct o as [n|i]; cbn [abs_op opval] in *.
  - cbn [eval base_val CfSound.E e_st]. apply v_addi_0.
  - destruct (ckinds c i) as [[w|ad t]|] eqn:Hk; try discriminate.
    + rewrite eval_const. symmetry. eapply r_imm; eassumption.
    + cbn [eval base_val CfSound.E e_st]. apply v_addi_0.
Qed.

Lemma wfv_mono : forall st st' x, (forall a v, bheap st a = Some v -> bheap st' a = Some v) ->
  wfv st x -> wfv st' x.
Proof.
  intros st st' x Hm H Ht. destruct (H Ht) as ([a Ha] & [b Hb]). split; eexists; apply Hm; eassumption.
Qed.

Lemma op_wf : forall s st regs m o, Rel s st regs m -> wfv st (opval st o).
Proof. intros s st regs m [n|i] R; cbn [opval]; [apply (r_wf _ _ _ _ _ _ _ _ _ R) | apply (r_wfc _ _ _ _ _ _ _ _ _ R)]. Qed.

(** What the next machine state is, for each bytecode outcome. *)
Definition AtNext (j : nat) (st' : bstate) (ms : machine_state) : Prop :=
  (j < length p)%nat /\
  exists s' regs' m', inv j = Some s' /\ ms = mkst regs' (at_ c (cut j)) m' rom /\ Rel s' st' regs' m'.

Definition AtRet (v : word) (st : bstate) (ms : machine_state) : Prop :=
  exists regs' m', ms = mkst regs' (jalr_tgt (bslots st 0) 0) m' rom /\
    getr regs' 10 = v /\ getr regs' 8 = fp /\ getr regs' 9 = vm /\ getr regs' 19 = bhp st /\
    (forall r : reg, scratch (bv_unsigned r) = false -> getr regs' r = getr regs0 r) /\
    (forall a x, bheap st a = Some x -> rdn segs m' a 8 = Some (le x)) /\
    CodeOK c segs m'.

(** At the allocator call, and what returning by its contract leads to. *)
Definition AtAlloc (s : CS) (st : bstate) (i : nat) (words : Z) (ms : machine_state) : Prop :=
  exists regs' m' next, ms = mkst regs' (Z_to_bv 64 (h_alloc c)) m' rom /\
    rdn segs m' (v_addi vm 0) 8 = Some (le (bhp st)) /\
    getr regs' 10 = vm /\ getr regs' 11 = Z_to_bv 64 words /\ getr regs' 1 = at_ c next /\
    getr regs' 8 = fp /\ getr regs' 9 = vm /\
    rdn segs m' (v_addi vm 16) 8 = Some (le fp) /\
    rdn segs m' (v_addi vm 24) 8 = Some (le (v_addi fp (8 * cframe c))) /\
    (forall r : reg, scratch (bv_unsigned r) = false -> getr regs' r = getr regs0 r) /\
    CodeOK c segs m' /\
    (forall st2 status regs2 m2, After c segs regs0 fp vm s st2 status regs2 m2 ->
       exists ms2, steps segs (mkst regs2 (at_ c next) m2 rom) ms2 /\
         ((status = Z_to_bv 64 26 /\ exists r2 m3, ms2 = mkst r2 (Z_to_bv 64 (c_unwind c)) m3 rom) \/
          (exists r2 m3, ms2 = mkst r2 (at_ c (cut i)) m3 rom /\ Rel s st2 r2 m3))).

Lemma run_from : forall s st regs m o stop r,
  Rel s st regs m -> run c cell_of (sP s) fuel o stop (y0 s) = Some r ->
  exists ms, steps segs (mkst regs (at_ c o) m rom) ms /\ Ends c segs rom regs0 (E st) r stop ms.
Proof.
  intros s st regs m o stop r R H.
  eapply (run_sound c cell_of (sP s) segs rom regs0 (E st)).
  - eapply lay_env. exact (r_lay _ _ _ _ _ _ _ _ _ R).
  - exact (r_P _ _ _ _ _ _ _ _ _ R).
  - exact (r_wf _ _ _ _ _ _ _ _ _ R).
  - exact (r_proc _ _ _ _ _ _ _ _ _ R).
  - exact H.
  - eapply (rel_inv c segs rom). exact R.
Qed.

Lemma lay_keep : forall st st', bhp st' = bhp st -> bhlimit st' = bhlimit st -> bheap st' = bheap st ->
  Lay c (E st) st -> Lay c (E st') st'.
Proof.
  intros st st' H1 H2 H3 [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13].
  constructor; cbn [CfSound.E e_fp e_vm] in *; rewrite ?H1, ?H2, ?H3; assumption.
Qed.

Lemma wr_keep : forall st st' m, bhp st' = bhp st -> bhlimit st' = bhlimit st ->
  Wr c segs (E st) st m -> Wr c segs (E st) st' m.
Proof.
  intros st st' m H1 H2 [W1 W2 W3]. constructor; cbn [CfSound.E e_fp e_vm] in *; rewrite ?H1, ?H2; assumption.
Qed.

(** A block that leaves the heap alone, and writes at most slot [d]. *)
Lemma post_keep : forall s t y d v plus st st' regs m regs1 m1,
  Rel s st regs1 m1 ->
  post_ok c s y d v 0 plus t = true ->
  Inv c segs regs0 (E st) y regs m ->
  bheap st' = bheap st -> bhp st' = bhp st -> bhlimit st' = bhlimit st -> bconsts st' = bconsts st ->
  (forall n, same_opt_d d n = false -> bslots st' n = bslots st n) ->
  (forall n, same_opt_d d n = true -> known v = true -> bslots st' n = eval (E st) v) ->
  ((0 <= plus < 64)%Z -> same_opt_d d plus = false -> tag3 (bslots st' plus) = 3%Z) ->
  (forall n, wfv st (bslots st' n)) ->
  Rel t st' regs m.
Proof.
  intros s t y d v plus st st' regs m regs1 m1 R Hp I Hh Hhp Hl Hc Hs Hd Hplus Hwf.
  assert (Hwf' : forall x, wfv st x -> wfv st' x) by (intros x; apply wfv_mono; intros a w; rewrite Hh; auto).
  eapply post_sound with (st := st) (y := y) (d := d) (v := v) (delta := 0%Z) (plus := plus); try eassumption.
  - rewrite Hhp. symmetry. apply v_addi_0.
  - rewrite Hhp. lia.
  - eapply lay_keep; try eassumption. eapply lay_env. exact (r_lay _ _ _ _ _ _ _ _ _ R).
  - intros a x Hx. rewrite Hh in Hx. exact (i_heap _ _ _ _ _ _ _ I a x Hx).
  - exact (r_P _ _ _ _ _ _ _ _ _ R).
  - intros n. apply Hwf'. apply Hwf.
  - intros i. rewrite Hc. apply Hwf'. exact (r_wfc _ _ _ _ _ _ _ _ _ R i).
  - intros a x Hx. rewrite Hh in Hx. apply Hwf'. exact (r_wfh _ _ _ _ _ _ _ _ _ R a x Hx).
  - eapply wr_keep; try eassumption. exact (i_wr _ _ _ _ _ _ _ I).
  - exact (r_imm _ _ _ _ _ _ _ _ _ R).
  - exact (r_tag _ _ _ _ _ _ _ _ _ R).
  - intros i ad Hk. rewrite Hh, Hc. exact (r_proc _ _ _ _ _ _ _ _ _ R i ad Hk).
Qed.

Lemma set_slot_fields : forall st d v,
  bheap (set_slot st d v) = bheap st /\ bhp (set_slot st d v) = bhp st /\
  bhlimit (set_slot st d v) = bhlimit st /\ bconsts (set_slot st d v) = bconsts st.
Proof. intros. repeat split; reflexivity. Qed.

Lemma set_slot_other : forall st d v n, same_opt_d (Some d) n = false -> bslots (set_slot st d v) n = bslots st n.
Proof.
  intros st d v n H. cbn [same_opt_d] in H. cbn [set_slot bslots]. rewrite Z.eqb_sym, H. reflexivity.
Qed.

Lemma set_slot_same : forall st d v n, same_opt_d (Some d) n = true -> bslots (set_slot st d v) n = v.
Proof.
  intros st d v n H. cbn [same_opt_d] in H. cbn [set_slot bslots]. rewrite Z.eqb_sym, H. reflexivity.
Qed.

Lemma wf_set : forall s st regs m d v n, Rel s st regs m -> wfv st v -> wfv st (bslots (set_slot st d v) n).
Proof.
  intros s st regs m d v n R Hv. cbn [set_slot bslots]. destruct (Z.eqb n d); [exact Hv|].
  exact (r_wf _ _ _ _ _ _ _ _ _ R n).
Qed.

Lemma post_at_inv : forall s y d v delta plus j,
  post_at c inv s y d v delta plus j = true -> exists t, inv j = Some t /\ post_ok c s y d v delta plus t = true.
Proof. intros. unfold post_at in H. destruct (inv j); [eauto | discriminate]. Qed.

Lemma at_next_bound : forall j t, inv j = Some t -> (j <= length p)%nat -> (j < length p)%nat.
Proof.
  intros j t H Hj. destruct (Nat.eq_dec j (length p)) as [->|Ne]; [rewrite acc_end in H; discriminate | lia].
Qed.

(** The state after a block that writes at most slot [d] and leaves the heap alone. *)
Lemma sim_set : forall s st regs m j y d w a plus m' regs',
  Rel s st regs m -> (j <= length p)%nat ->
  Inv c segs regs0 (E st) y regs' m' ->
  post_at c inv s y (Some d) a 0 plus j = true ->
  (known a = true -> eval (E st) a = w) -> wfv st w ->
  ((0 <= plus < 64)%Z -> same_opt_d (Some d) plus = false -> tag3 (bslots st plus) = 3%Z) ->
  AtNext j (set_slot st d w) (mkst regs' (at_ c (cut j)) m' rom).
Proof.
  intros s st regs m j y d w a plus m' regs' R Hj I Hp Hw Hwf Hplus.
  destruct (post_at_inv _ _ _ _ _ _ _ Hp) as (t & Ht & Hpo).
  split; [eapply at_next_bound; eassumption|].
  exists t, regs', m'. split; [exact Ht|]. split; [reflexivity|].
  destruct (set_slot_fields st d w) as (F1 & F2 & F3 & F4).
  eapply post_keep; try eassumption.
  - apply set_slot_other.
  - intros n Hn Hk. rewrite set_slot_same by exact Hn. symmetry. apply Hw. exact Hk.
  - intros Hp0 Hn. rewrite set_slot_other by exact Hn. apply Hplus; assumption.
  - intros n. eapply wf_set; eassumption.
Qed.

Lemma sim_none : forall s st regs m j y m' regs',
  Rel s st regs m -> (j <= length p)%nat ->
  Inv c segs regs0 (E st) y regs' m' ->
  post_at c inv s y None Unk 0 (-1) j = true ->
  AtNext j st (mkst regs' (at_ c (cut j)) m' rom).
Proof.
  intros s st regs m j y m' regs' R Hj I Hp.
  destruct (post_at_inv _ _ _ _ _ _ _ Hp) as (t & Ht & Hpo).
  split; [eapply at_next_bound; eassumption|].
  exists t, regs', m'. split; [exact Ht|]. split; [reflexivity|].
  eapply post_keep; try eassumption; try reflexivity.
  - intros n Hn Hk. discriminate.
  - intros Hp0. lia.
  - intros n. exact (r_wf _ _ _ _ _ _ _ _ _ R n).
Qed.

Lemma find_label_lt : forall q l k li, find_label q l k = Some li -> (li < k + length q)%nat.
Proof.
  induction q as [|ins q IH]; intros l k li H; cbn [find_label] in H; [discriminate|].
  cbn [length]. destruct ins; try (apply IH in H; lia).
  destruct (Z.eqb l l0); [injection H as <-; lia | apply IH in H; lia].
Qed.

Lemma target_spec : forall i l t li, target p cut i l t = Some li ->
  find_label p l 0 = Some li /\ cut li = t /\ (li < length p)%nat.
Proof.
  intros i l t li H. unfold target in H. destruct (find_label p l 0) as [k|] eqn:Hf; [|discriminate].
  destruct (Nat.ltb i k && Z.eqb (cut k) t)%bool eqn:Hb; [|discriminate].
  injection H as <-. apply andb_true_iff in Hb as [_ Hb]. apply Z.eqb_eq in Hb.
  pose proof (find_label_lt _ _ _ _ Hf). split; [reflexivity|]. split; [exact Hb | lia].
Qed.

End StepSim.
