(** * The allocation case: [cons], its fast path, and its call to the allocator (Shen/JIT Phase 0, spike 8). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Examples.emitter_p3_ns Require Import CfDefs CfStep CfRun CfSound CfStepSim CfCases.
Import ListNotations.
Open Scope bv_scope.

Lemma apart_sub : forall a n b k b' k', apart a n b k -> (b <= b')%Z -> (b' + k' <= b + k)%Z -> apart a n b' k'.
Proof. unfold apart. intros. lia. Qed.

Lemma apart_subl : forall a n b k a' n', apart a n b k -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> apart a' n' b k.
Proof. unfold apart. intros. lia. Qed.

Lemma bv_neq_u : forall x y : word, bv_unsigned x <> bv_unsigned y -> x <> y.
Proof. intros x y H E. subst. contradiction. Qed.

Section Cons.
Context {fx : FPState}.
Variable c : cfg.
Variable cell_of : Z -> option Z.
Variable segs : list Segment.
Variable rom : word -> option byte.
Variable regs0 : bvmap 5 word.
Variables fp vm : word.
Variable keq : word -> word -> bool.
Variables vtrue vfalse : word.
Hypothesis WfK : forall i w, ckinds c i = Some (KImm w) -> (0 <= w < 2^64)%Z.
Variable p : list binstr.
Variable cut : nat -> Z.
Variable inv : nat -> option CS.
Variable fuel : nat.
Hypothesis ACC : check_all c cell_of p cut inv fuel = true.

Abbreviation Rel := (Rel c segs regs0 fp vm).
Abbreviation E st := (E fp vm st (Z_to_bv 64 0) (Z_to_bv 64 0)).
Abbreviation AtNext := (AtNext c segs rom regs0 fp vm p cut inv).
Abbreviation AtAlloc := (AtAlloc c segs rom regs0 fp vm cut).
Abbreviation steps := (steps segs).
Abbreviation RUN := (run_from c cell_of segs rom regs0 fp vm fuel).

Section Heap.
Variable st : bstate.
Variables d : Z.
Variables va vb : word.
Abbreviation hp := (bhp st).
Abbreviation lim := (bhlimit st).
Abbreviation st' := (heap_cons st d va vb).
Hypothesis L : Lay c (E st) st.
Hypothesis Room : (u hp + 16 <= u lim)%Z.

Lemma u_hp8 : u (v_addi hp 8) = (u hp + 8)%Z.
Proof. pose proof (l_lim _ _ _ L). apply u_add; lia. Qed.
Lemma u_hp16 : u (v_addi hp 16) = (u hp + 16)%Z.
Proof. pose proof (l_lim _ _ _ L). apply u_add; lia. Qed.

Lemma old_apart : forall x v, bheap st x = Some v -> x <> hp /\ x <> v_addi hp 8.
Proof.
  intros x v H. pose proof (l_heap _ _ _ L x v H) as (_ & _ & _ & A & _). unfold apart in A.
  pose proof u_hp8. split; apply bv_neq_u; unfold u in *; lia.
Qed.

Lemma cons_heap : forall x v, bheap st' x = Some v ->
  (x = hp /\ v = va) \/ (x = v_addi hp 8 /\ v = vb) \/ bheap st x = Some v.
Proof.
  intros x v H. cbn [heap_cons bheap] in H.
  destruct (bool_decide (x = hp)) eqn:E1; [apply bool_decide_eq_true in E1; injection H as <-; auto|].
  destruct (bool_decide (x = v_addi hp 8)) eqn:E2; [apply bool_decide_eq_true in E2; injection H as <-; auto|].
  auto.
Qed.

Lemma cons_keeps : forall x v, bheap st x = Some v -> bheap st' x = Some v.
Proof.
  intros x v H. destruct (old_apart x v H) as (N1 & N2). cbn [heap_cons bheap].
  rewrite (bool_decide_eq_false_2 _ N1), (bool_decide_eq_false_2 _ N2). exact H.
Qed.

Lemma cons_at0 : bheap st' hp = Some va.
Proof. cbn [heap_cons bheap]. rewrite bool_decide_eq_true_2 by reflexivity. reflexivity. Qed.

Lemma cons_at8 : bheap st' (v_addi hp 8) = Some vb.
Proof.
  cbn [heap_cons bheap]. pose proof u_hp8.
  rewrite (bool_decide_eq_false_2 (v_addi hp 8 = hp)) by (apply bv_neq_u; unfold u in *; lia).
  rewrite bool_decide_eq_true_2 by reflexivity. reflexivity.
Qed.

Lemma lay_cons : Lay c (E st') st'.
Proof.
  pose proof u_hp8 as U8. pose proof u_hp16 as U16.
  destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13]. cbn [CfSound.E e_fp e_vm] in *.
  constructor; cbn [heap_cons bhp bhlimit bheap CfSound.E e_fp e_vm e_st] in *.
  - exact L1.
  - exact L2.
  - exact L3.
  - fold (v_addi hp 16) in *. unfold u in *. lia.
  - exact L5.
  - exact L6.
  - eapply apart_sub; [exact L7 | unfold u in *; lia | unfold u in *; lia].
  - eapply apart_sub; [exact L8 | unfold u in *; lia | unfold u in *; lia].
  - exact L9.
  - exact L10.
  - eapply apart_subl; [exact L11 | unfold u in *; lia | unfold u in *; lia].
  - intros a v H.
    destruct (bool_decide (a = hp)) eqn:E1.
    + apply bool_decide_eq_true in E1. subst a. unfold apart in *. unfold u in *. repeat split; lia.
    + destruct (bool_decide (a = v_addi hp 8)) eqn:E2.
      * apply bool_decide_eq_true in E2. subst a. unfold apart in *. unfold u in *. repeat split; lia.
      * pose proof (L12 a v H) as (H1 & H2 & H3 & H4 & H5). repeat split; try assumption.
        eapply apart_sub; [exact H4 | unfold u in *; lia | unfold u in *; lia].
  - intros i ad t H. pose proof (L13 i ad t H) as (H1 & H2 & H3 & H4 & H5). repeat split; try assumption; try lia.
    eapply apart_sub; [exact H4 | unfold u in *; lia | unfold u in *; lia].
Qed.

Lemma wfv_cons : forall x, wfv st x -> wfv st' x.
Proof. intros x. apply wfv_mono. apply cons_keeps. Qed.

Lemma wfv_pair : wfv st' (v_addi hp 3).
Proof.
  intros _. rewrite !vadd2. split.
  - exists va. replace (3 + -3)%Z with 0%Z by lia. rewrite v_addi_0. apply cons_at0.
  - exists vb. replace (3 + 5)%Z with 8%Z by lia. apply cons_at8.
Qed.

End Heap.

Lemma cons_next : forall s st regs m i y d a b regs' m',
  Rel s st regs m -> (i < length p)%nat ->
  Inv c segs regs0 (E st) y regs' m' ->
  cons_post c inv s i y d a b = true ->
  AtNext (S i) (heap_cons st d (opval st a) (opval st b)) (mkst regs' (at_ c (cut (S i))) m' rom).
Proof.
  intros s st regs m i y d a b regs' m' R Hi I Hc.
  unfold cons_post in Hc.
  apply andb_true_iff in Hc as [Hc Hp]. apply andb_true_iff in Hc as [Hc Hb8].
  apply andb_true_iff in Hc as [Hc Ha0]. apply andb_true_iff in Hc as [Ka Kb].
  apply same_eq in Ha0. apply same_eq in Hb8.
  destruct (post_at_inv c inv _ _ _ _ _ _ _ Hp) as (t & Ht & Hpo).
  pose proof Hpo as Hpo'. apply post_parts in Hpo' as (_ & _ & _ & _ & _ & _ & PR0 & PR).
  pose proof (i_room _ _ _ _ _ _ _ I) as (Rm0 & Rm1). cbn [CfSound.E e_st] in Rm1.
  pose proof (r_lay _ _ _ _ _ _ _ _ _ R) as L0.
  assert (L : Lay c (E st) st) by (eapply lay_env; exact L0).
  assert (Room : (u (bhp st) + 16 <= u (bhlimit st))%Z) by lia.
  pose proof (abs_op_eval c segs regs0 fp vm s st regs m a R Ka) as Ea.
  pose proof (abs_op_eval c segs regs0 fp vm s st regs m b R Kb) as Eb.
  split; [eapply (at_next_bound c cell_of rom vfalse p cut inv fuel ACC); [exact Ht | lia]|].
  exists t, regs', m'. split; [exact Ht|]. split; [reflexivity|].
  eapply post_sound with (st := st) (y := y) (d := Some d) (v := Lin KHp 3) (delta := 16%Z) (plus := (-1)%Z); try eassumption.
  - intros n Hn. cbn [same_opt_d] in Hn. cbn [heap_cons bslots]. rewrite Z.eqb_sym, Hn. reflexivity.
  - intros n Hn _. cbn [same_opt_d] in Hn. cbn [heap_cons bslots]. rewrite Z.eqb_sym, Hn. reflexivity.
  - reflexivity.
  - cbn [heap_cons bhp]. apply (u_hp16 st (opval st b) L Room).
  - reflexivity.
  - reflexivity.
  - eapply lay_env. apply (lay_cons st d (opval st a) (opval st b) L Room).
  - intros x v Hx. destruct (cons_heap st d _ _ x v Hx) as [(-> & ->)|[(-> & ->)|Ho]].
    + destruct (i_H _ _ _ _ _ _ _ I 0%Z ltac:(rewrite Ha0; exact Ka)) as (_ & _ & _ & Hr).
      rewrite v_addi_0, Ha0, Ea in Hr. exact Hr.
    + destruct (i_H _ _ _ _ _ _ _ I 8%Z ltac:(rewrite Hb8; exact Kb)) as (_ & _ & _ & Hr).
      rewrite Hb8, Eb in Hr. exact Hr.
    + exact (i_heap _ _ _ _ _ _ _ I x v Ho).
  - exact (r_P _ _ _ _ _ _ _ _ _ R).
  - intros. lia.
  - intros n. cbn [heap_cons bslots]. destruct (Z.eqb n d).
    + apply (wfv_pair st d (opval st a) (opval st b) L Room).
    + apply (wfv_cons st d (opval st a) (opval st b) L Room). exact (r_wf _ _ _ _ _ _ _ _ _ R n).
  - intros i0. apply (wfv_cons st d (opval st a) (opval st b) L Room). exact (r_wfc _ _ _ _ _ _ _ _ _ R i0).
  - intros x v Hx. apply (wfv_cons st d (opval st a) (opval st b) L Room).
    destruct (cons_heap st d _ _ x v Hx) as [(_ & ->)|[(_ & ->)|Ho]].
    + eapply op_wf; exact R.
    + eapply op_wf; exact R.
    + exact (r_wfh _ _ _ _ _ _ _ _ _ R x v Ho).
  - destruct (i_wr _ _ _ _ _ _ _ I) as [W1 W2 W3]. constructor; cbn [CfSound.E e_fp e_vm heap_cons bhp bhlimit] in *.
    + exact W1.
    + exact W2.
    + intros k Hk Hl. rewrite vadd2. pose proof (u_hp16 st (opval st b) L Room) as U. fold (v_addi (bhp st) 16) in Hl.
      rewrite U in Hl. apply W3; [lia | ]. cbn [CfSound.E e_st]. lia.
  - exact (r_imm _ _ _ _ _ _ _ _ _ R).
  - exact (r_tag _ _ _ _ _ _ _ _ _ R).
  - intros i0 ad Hk. destruct (r_proc _ _ _ _ _ _ _ _ _ R i0 ad Hk) as (v & Hv). exists v.
    cbn [heap_cons bconsts]. exact (cons_keeps st d _ _ L Room _ _ Hv).
  - exact cell_of.
  - exact rom.
  - exact fp.
Qed.

Abbreviation EA st2 status := (CfSound.E fp vm st2 status (Z_to_bv 64 0)).

Lemma inv_after : forall s st2 status regs2 m2,
  After c segs regs0 fp vm s st2 status regs2 m2 ->
  Inv c segs regs0 (EA st2 status) (y_after s) regs2 m2.
Proof.
  intros s st2 status regs2 m2 A. destruct A as [a_fp0 a_vm0 a_status0 a_keep0 a_lay0 a_M0 a_lim0 a_hp0 a_heap0 a_cell0 a_imm0 a_tag0 a_code0 a_P0 a_wf0 a_wfc0 a_wfh0 a_wr0 a_proc0]. constructor; cbn [y_after yA yF yH yV yroom].
  - intros r Hk.
    assert (Hr : forall k, bv_unsigned r = k -> r = Z_to_bv 5 k) by (intros k Hk'; apply u_eq; exact Hk').
    remember (bv_unsigned r) as rn eqn:Er.
    destruct (Z.eqb_spec rn 0) as [->|E1]; [rewrite (Hr 0%Z eq_refl); rewrite eval_const; reflexivity|].
    destruct (Z.eqb_spec rn 8) as [->|E2];
      [rewrite (Hr 8%Z eq_refl); cbn [eval base_val CfSound.E e_fp]; rewrite v_addi_0; exact a_fp0|].
    destruct (Z.eqb_spec rn 9) as [->|E3];
      [rewrite (Hr 9%Z eq_refl); cbn [eval base_val CfSound.E e_vm]; rewrite v_addi_0; exact a_vm0|].
    destruct (Z.eqb_spec rn 10) as [->|E4];
      [rewrite (Hr 10%Z eq_refl); cbn [eval base_val CfSound.E e_status]; rewrite v_addi_0; exact a_status0|].
    discriminate.
  - exact a_keep0.
  - intros n Hk Hn. unfold frame0 in *.
    destruct (Z.leb 0 n && Z.ltb n 64 && Z.testbit (sM s) n)%bool eqn:Hb; [|discriminate].
    apply andb_true_iff in Hb as [Hb H3]. apply andb_true_iff in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    destruct (a_M0 n (conj H1 H2) H3) as (_ & Hd).
    cbn [eval base_val CfSound.E e_st]. rewrite v_addi_0. exact Hd.
  - intros k Hk. discriminate.
  - intros k Hk. destruct (Z.eqb_spec k 8) as [Ek|Ek].
    + subst k. split; [lia|]. cbn [eval base_val CfSound.E e_st]. rewrite v_addi_0. exact a_lim0.
    + destruct (Z.eqb_spec k 0) as [Ek0|Ek0].
      * subst k. split; [lia|]. cbn [eval base_val CfSound.E e_st e_vm]. rewrite !v_addi_0. rewrite v_addi_0 in a_hp0. exact a_hp0.
      * exfalso. revert Hk. destruct (Z.eqb_spec k 8); [contradiction|]. destruct (Z.eqb_spec k 0); [contradiction|]. discriminate.
  - exact a_heap0.
  - exact a_cell0.
  - exact a_code0.
  - cbn [CfSound.E e_st]. pose proof (l_hp _ _ _ a_lay0). lia.
  - reflexivity.
  - eapply wr_env. exact a_wr0.
Qed.

Lemma rel_resume : forall s st2 status regs2 m2 y regs3 m3,
  After c segs regs0 fp vm s st2 status regs2 m2 ->
  Inv c segs regs0 (EA st2 status) y regs3 m3 ->
  same (yA y 8) (Lin KFp 0) = true -> same (yA y 9) (Lin KVm 0) = true -> same (yA y 19) (Lin KHp 0) = true ->
  reg_post None Unk y 18 (sC s) = true -> reg_post None Unk y 20 (sK0 s) = true ->
  reg_post None Unk y 21 (sK1 s) = true ->
  sR s = 0%Z -> frame_kept s y = true ->
  Rel s st2 regs3 m3.
Proof.
  intros s st2 status regs2 m2 y regs3 m3 A I H8 H9 H19 HC HK0 HK1 HR HF.
  apply same_eq in H8. apply same_eq in H9. apply same_eq in H19.
  pose proof I as [IA IK IF IH IV Ihp Icl Icd Irm IV8 IW].
  destruct A as [a_fp0 a_vm0 a_status0 a_keep0 a_lay0 a_M0 a_lim0 a_hp0 a_heap0 a_cell0 a_imm0 a_tag0 a_code0 a_P0 a_wf0 a_wfc0 a_wfh0 a_wr0 a_proc0]. constructor.
  - rewrite (A_at c segs regs0 _ _ _ _ 8 8 _ I eq_refl H8 eq_refl). cbn [eval base_val CfSound.E e_fp]. apply v_addi_0.
  - rewrite (A_at c segs regs0 _ _ _ _ 9 9 _ I eq_refl H9 eq_refl). cbn [eval base_val CfSound.E e_vm]. apply v_addi_0.
  - rewrite (A_at c segs regs0 _ _ _ _ 19 19 _ I eq_refl H19 eq_refl). cbn [eval base_val CfSound.E e_st]. apply v_addi_0.
  - exact (reg_post_sound c segs regs0 fp vm _ _ _ 18 18 _ _ _ _ _ _ _ I eq_refl HC (fun _ _ => eq_refl) (fun _ H _ => ltac:(discriminate H))).
  - exact (reg_post_sound c segs regs0 fp vm _ _ _ 20 20 _ _ _ _ _ _ _ I eq_refl HK0 (fun _ _ => eq_refl) (fun _ H _ => ltac:(discriminate H))).
  - exact (reg_post_sound c segs regs0 fp vm _ _ _ 21 21 _ _ _ _ _ _ _ I eq_refl HK1 (fun _ _ => eq_refl) (fun _ H _ => ltac:(discriminate H))).
  - exact IK.
  - eapply lay_env. exact a_lay0.
  - intros n Hn Ht. destruct (a_M0 n Hn Ht) as (Hlt & _). split; [exact Hlt|].
    unfold frame_kept in HF. rewrite forallb_forall in HF.
    assert (Hin : In n slots64) by (unfold slots64; apply in_map_iff; exists (Z.to_nat n); split; [lia | apply in_seq; lia]). pose proof (HF n Hin) as Hq. rewrite Ht in Hq. cbn [negb orb] in Hq. apply same_eq in Hq.
    pose proof (IF n ltac:(rewrite Hq; reflexivity) (conj (proj1 Hn) Hlt)) as Hrd.
    rewrite Hq in Hrd. unfold slot_at in Hrd. cbn [eval base_val CfSound.E e_st e_fp] in Hrd. rewrite v_addi_0 in Hrd. exact Hrd.
  - destruct (IV 8%Z ltac:(rewrite IV8; reflexivity)) as (_ & Hrd). rewrite IV8 in Hrd.
    cbn [eval base_val CfSound.E e_st e_vm] in Hrd. rewrite v_addi_0 in Hrd. exact Hrd.
  - exact Ihp.
  - exact Icl.
  - exact a_imm0.
  - exact a_tag0.
  - exact Icd.
  - exact a_P0.
  - rewrite HR. pose proof (l_hp _ _ _ a_lay0). lia.
  - exact a_wf0.
  - exact a_wfc0.
  - exact a_wfh0.
  - eapply wr_env. exact IW.
  - exact a_proc0.
Qed.

Lemma eval_mkc' : forall e z, eval e (mkc z) = Z_to_bv 64 z.
Proof. intros. apply eval_mkc. Qed.

(** The allocator call, from the state where the room check failed. *)
Lemma slow_path : forall s st i y1 t words regs1 m1 regsR mR,
  Rel s st regsR mR -> Inv c segs regs0 (E st) y1 regs1 m1 ->
  check_slow c cell_of cut fuel s i y1 t words = true ->
  exists ms, steps (mkst regs1 (at_ c t) m1 rom) ms /\ AtAlloc s st i words ms.
Proof.
  intros s st i y1 t words regs1 m1 regsR mR R I Hs. unfold check_slow in Hs.
  destruct (run c cell_of (sP s) fuel t (-1) y1) as [r|] eqn:Hr; [|discriminate].
  destruct r as [| | |callee next y'| |]; try discriminate.
  apply andb_true_iff in Hs as [Hs Hres]. apply andb_true_iff in Hs as [Hs Hfk].
  apply andb_true_iff in Hs as [Hs H19]. apply andb_true_iff in Hs as [Hs H9].
  apply andb_true_iff in Hs as [Hs H8]. apply andb_true_iff in Hs as [Hs H11].
  apply andb_true_iff in Hs as [Hs H10]. apply andb_true_iff in Hs as [Hs V0].
  apply andb_true_iff in Hs as [Hs V24]. apply andb_true_iff in Hs as [Hcal V16].
  apply Z.eqb_eq in Hcal.
  apply same_eq in H19. apply same_eq in H9. apply same_eq in H8. apply same_eq in H11. apply same_eq in H10.
  apply same_eq in V0. apply same_eq in V24. apply same_eq in V16.
  destruct (run_sound c cell_of (sP s) segs rom regs0 (E st)
              ltac:(eapply lay_env; exact (r_lay _ _ _ _ _ _ _ _ _ R))
              (r_P _ _ _ _ _ _ _ _ _ R) (r_wf _ _ _ _ _ _ _ _ _ R) (r_proc _ _ _ _ _ _ _ _ _ R)
              fuel t (-1) y1 _ regs1 m1 Hr I) as (ms & Hst & Hend).
  cbn [Ends] in Hend. destruct Hend as (regs' & m' & -> & I' & Hra).
  exists (mkst regs' (Z_to_bv 64 callee) m' rom). split; [exact Hst|].
  exists regs', m', next. rewrite Hcal. split; [reflexivity|].
  split; [destruct (i_V _ _ _ _ _ _ _ I' 0%Z ltac:(rewrite V0; reflexivity)) as (_ & Hd); rewrite V0 in Hd;
          cbn [eval base_val CfSound.E e_st e_vm] in Hd; rewrite !v_addi_0 in Hd; rewrite v_addi_0; exact Hd|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 10 10 _ I' eq_refl H10 eq_refl); cbn [eval base_val CfSound.E e_vm]; apply v_addi_0|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 11 11 _ I' eq_refl H11 eq_refl); apply eval_mkc|].
  split; [exact Hra|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 8 8 _ I' eq_refl H8 eq_refl); cbn [eval base_val CfSound.E e_fp]; apply v_addi_0|].
  split; [rewrite (A_at c segs regs0 _ _ _ _ 9 9 _ I' eq_refl H9 eq_refl); cbn [eval base_val CfSound.E e_vm]; apply v_addi_0|].
  split; [destruct (i_V _ _ _ _ _ _ _ I' 16%Z ltac:(rewrite V16; reflexivity)) as (_ & Hd); rewrite V16 in Hd;
          cbn [eval base_val CfSound.E e_fp e_vm] in Hd; rewrite v_addi_0 in Hd; exact Hd|].
  split; [destruct (i_V _ _ _ _ _ _ _ I' 24%Z ltac:(rewrite V24; reflexivity)) as (_ & Hd); rewrite V24 in Hd;
          cbn [eval base_val CfSound.E e_fp e_vm] in Hd; exact Hd|].
  split; [exact (i_keep _ _ _ _ _ _ _ I')|].
  split; [exact (i_code _ _ _ _ _ _ _ I')|].
  (* Resuming after the allocator returns by its contract. *)
  intros st2 status regs2 m2 A.
  unfold check_resume in Hres.
  destruct (run c cell_of (sP s) fuel next (-1) (y_after s)) as [r2|] eqn:Hr2; [|discriminate].
  destruct r2 as [| | | | |cc a b t2 y2 rest]; try discriminate.
  destruct cc; try discriminate. destruct rest as [z0 | back y | z1 | z2 z3 z4 | zj zk | z5 z6 z7 z8 z9 z10]; try discriminate.
  apply andb_true_iff in Hres as [Hres HK1]. apply andb_true_iff in Hres as [Hres HK0].
  apply andb_true_iff in Hres as [Hres HC]. apply andb_true_iff in Hres as [Hres K19].
  apply andb_true_iff in Hres as [Hres K9]. apply andb_true_iff in Hres as [Hres K8].
  apply andb_true_iff in Hres as [Hres HF]. apply andb_true_iff in Hres as [Hres HR].
  apply andb_true_iff in Hres as [Hres Hback]. apply andb_true_iff in Hres as [Hres Hunw].
  apply andb_true_iff in Hres as [Ha Hb].
  apply same_eq in Ha. apply same_eq in Hb. apply Z.eqb_eq in Hunw. apply Z.eqb_eq in Hback. apply Z.eqb_eq in HR.
  subst a b.
  destruct (run_sound c cell_of (sP s) segs rom regs0 (EA st2 status)
              ltac:(eapply lay_env; exact (a_lay _ _ _ _ _ _ _ _ _ _ A))
              (a_P _ _ _ _ _ _ _ _ _ _ A) (a_wf _ _ _ _ _ _ _ _ _ _ A) (a_proc _ _ _ _ _ _ _ _ _ _ A)
              fuel next (-1) (y_after s) _ regs2 m2 Hr2 (inv_after s st2 status regs2 m2 A)) as (ms2 & Hst2 & Hend2).
  exists ms2. split; [exact Hst2|].
  cbn [Ends branch_taken] in Hend2.
  rewrite eval_mkc in Hend2. cbn [eval base_val CfSound.E e_status] in Hend2. rewrite v_addi_0 in Hend2.
  destruct Hend2 as [(Htk & r2 & m3 & -> & _)|(Hnt & r2 & m3 & -> & I3)].
  - left. split.
    + unfold bv_eqb in Htk. apply Z.eqb_eq in Htk. apply bv_eq. exact Htk.
    + exists r2, m3. f_equal. unfold at_. rewrite Hunw. reflexivity.
  - right. exists r2, m3. split; [rewrite Hback; reflexivity|].
    eapply rel_resume; eassumption.
Qed.

Theorem sim_cons : forall i s st regs m d a b,
  nth_error p i = Some (ICons d a b) -> inv i = Some s -> Rel s st regs m ->
  exists ms, steps (mkst regs (at_ c (cut i)) m rom) ms /\
  (AtNext (S i) (heap_cons st d (opval st a) (opval st b)) ms \/ exists words, AtAlloc s st i words ms).
Proof.
  intros i s st regs m d a b Hn Hi R.
  pose proof (acc_at c cell_of rom vfalse p cut inv fuel ACC i _ Hn) as Hacc. unfold check_at in Hacc.
  rewrite Hi, Hn in Hacc.
  pose proof (proj1 (nth_error_Some p i) ltac:(rewrite Hn; discriminate)) as Hlt.
  destruct (run c cell_of (sP s) fuel (cut i) (cut (S i)) (y0 s)) as [r|] eqn:Hr; [|discriminate].
  destruct (RUN s st regs m _ _ _ R Hr) as (ms & Hs & Hend).
  destruct r as [y | z1 z2 | z3 | z4 z5 z6 | zj zk | cc la lb t y1 rest]; try discriminate.
  - (* room already reserved *)
    apply andb_true_iff in Hacc as [HR Hc].
    cbn [Ends] in Hend. destruct Hend as (regs' & m' & -> & I).
    exists (mkst regs' (at_ c (cut (S i))) m' rom). split; [exact Hs|]. left.
    eapply cons_next; eassumption.
  - destruct cc; try discriminate. destruct rest as [y | z1 z2 | z3 | z4 z5 z6 | zj zk | z7 z8 z9 z10 z11 z12]; try discriminate.
    destruct lb as [bb k|n|]; try discriminate. destruct bb; try discriminate.
    apply andb_true_iff in Hacc as [Hacc Hc]. apply andb_true_iff in Hacc as [Hacc Hsl].
    apply andb_true_iff in Hacc as [Hacc HR]. apply andb_true_iff in Hacc as [Hacc _].
    apply andb_true_iff in Hacc as [Hacc _]. apply andb_true_iff in Hacc as [Hla _].
    apply same_eq in Hla. subst la.
    cbn [Ends] in Hend.
    destruct Hend as [(_ & regs1 & m1 & -> & I1)|(_ & regs' & m' & -> & I)].
    + destruct (slow_path s st i y1 t (k / 8) regs1 m1 regs m R I1 Hsl) as (ms2 & Hs2 & Ha).
      exists ms2. split; [eapply steps_trans; eassumption|]. right. eauto.
    + exists (mkst regs' (at_ c (cut (S i))) m' rom). split; [exact Hs|]. left.
      eapply cons_next; eassumption.
Qed.

End Cons.
