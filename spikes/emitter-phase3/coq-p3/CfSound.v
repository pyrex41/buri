(** * Accepted bytes refine their bytecode on all paths (Shen/JIT Phase 0, spike 8).

    [sim] is the theorem: for any function the checker accepts, from any machine state related to
    a bytecode state at any accepted point, the machine's real steps follow the bytecode until it
    returns, or until it calls the allocator.  At that call [Resume] says what happens if the
    allocator keeps its contract.  The allocator's contract is the only thing assumed about it.

    Neither the emitter nor the C checker appears here.  The theorem is about the Rocq function
    [check_all]. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Examples.emitter_p3_ns Require Import CfDefs CfStep CfRun.
Import ListNotations.
Open Scope bv_scope.

Section Sound.
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
(** The kernel's [=] on a value whose tag means identity is word equality. *)
Hypothesis Hkeq : forall x y, identity_tag (tag3 x) = true ->
  keq x y = bv_eqb x y /\ keq y x = bv_eqb x y.

Definition E (st : bstate) (status count : word) : env := mkE st fp vm status count.
Abbreviation E0 st := (E st (Z_to_bv 64 0) (Z_to_bv 64 0)).

Record Rel (s : CS) (st : bstate) (regs : bvmap 5 word) (m : word -> option byte) : Prop := {
  r_fp : getr regs 8 = fp;
  r_vm : getr regs 9 = vm;
  r_hp : getr regs 19 = bhp st;
  r_c : forall n, sC s = Some n -> getr regs 18 = bslots st n;
  r_k0 : forall n, sK0 s = Some n -> getr regs 20 = bslots st n;
  r_k1 : forall n, sK1 s = Some n -> getr regs 21 = bslots st n;
  r_keep : forall r : reg, scratch (bv_unsigned r) = false -> getr regs r = getr regs0 r;
  r_lay : Lay c (E0 st) st;
  r_M : forall n, (0 <= n < 64)%Z -> Z.testbit (sM s) n = true ->
    (n < cframe c)%Z /\ rdn segs m (v_addi fp (8 * n)) 8 = Some (le (bslots st n));
  r_lim : rdn segs m (v_addi vm 8) 8 = Some (le (bhlimit st));
  r_heap : forall a v, bheap st a = Some v -> rdn segs m a 8 = Some (le v);
  r_cell : forall i ad t, ckinds c i = Some (KPtr ad t) ->
    rdn segs m (Z_to_bv 64 ad) 8 = Some (le (bconsts st i));
  r_imm : forall i w, ckinds c i = Some (KImm w) -> bconsts st i = Z_to_bv 64 w;
  r_tag : forall i ad t, ckinds c i = Some (KPtr ad t) -> tag3 (bconsts st i) = t;
  r_code : CodeOK c segs m;
  r_P : forall n, (0 <= n < 64)%Z -> Z.testbit (sP s) n = true -> tag3 (bslots st n) = 3%Z;
  r_R : (0 <= sR s)%Z /\ (u (bhp st) + 8 * sR s <= u (bhlimit st))%Z;
  r_wf : forall n, wfv st (bslots st n);
  r_wfc : forall i, wfv st (bconsts st i);
  r_wfh : forall a v, bheap st a = Some v -> wfv st v;
  r_wr : Wr c segs (E0 st) st m;
  r_proc : forall i ad, ckinds c i = Some (KPtr ad 5) -> exists v, bheap st (v_addi (bconsts st i) 3) = Some v
}.

(** What the allocator's return must establish: its contract, stated for the bytes after the call. *)
Record After (s : CS) (st : bstate) (status : word) (regs : bvmap 5 word) (m : word -> option byte) : Prop := {
  a_fp : getr regs 8 = fp;
  a_vm : getr regs 9 = vm;
  a_status : getr regs 10 = status;
  a_keep : forall r : reg, scratch (bv_unsigned r) = false -> getr regs r = getr regs0 r;
  a_lay : Lay c (E0 st) st;
  a_M : forall n, (0 <= n < 64)%Z -> Z.testbit (sM s) n = true ->
    (n < cframe c)%Z /\ rdn segs m (v_addi fp (8 * n)) 8 = Some (le (bslots st n));
  a_lim : rdn segs m (v_addi vm 8) 8 = Some (le (bhlimit st));
  a_hp : rdn segs m (v_addi vm 0) 8 = Some (le (bhp st));
  a_heap : forall a v, bheap st a = Some v -> rdn segs m a 8 = Some (le v);
  a_cell : forall i ad t, ckinds c i = Some (KPtr ad t) ->
    rdn segs m (Z_to_bv 64 ad) 8 = Some (le (bconsts st i));
  a_imm : forall i w, ckinds c i = Some (KImm w) -> bconsts st i = Z_to_bv 64 w;
  a_tag : forall i ad t, ckinds c i = Some (KPtr ad t) -> tag3 (bconsts st i) = t;
  a_code : CodeOK c segs m;
  a_P : forall n, (0 <= n < 64)%Z -> Z.testbit (sP s) n = true -> tag3 (bslots st n) = 3%Z;
  a_wf : forall n, wfv st (bslots st n);
  a_wfc : forall i, wfv st (bconsts st i);
  a_wfh : forall a v, bheap st a = Some v -> wfv st v;
  a_wr : Wr c segs (E0 st) st m;
  a_proc : forall i ad, ckinds c i = Some (KPtr ad 5) -> exists v, bheap st (v_addi (bconsts st i) 3) = Some v
}.

Lemma wr_env : forall st st' a b a' b' m,
  Wr c segs (E st a b) st' m -> Wr c segs (E st' a' b') st' m.
Proof. intros st st' a b a' b' m [W1 W2 W3]. constructor; assumption. Qed.

Lemma lay_env : forall st st' a b a' b',
  Lay c (E st a b) st' -> Lay c (E st' a' b') st'.
Proof. intros st st' a b a' b' [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13]. constructor; assumption. Qed.

Lemma val_lin0 : forall e b, base_eqb b KConst = false -> eval e (Lin b 0) = base_val e b.
Proof. intros. cbn [eval]. apply v_addi_0. Qed.

Lemma u_eq : forall r : reg, forall k, bv_unsigned r = k -> r = Z_to_bv 5 k.
Proof. intros r k H. apply bv_eq. rewrite Z_to_bv_unsigned, <- H. symmetry. apply bv_wrap_bv_unsigned. Qed.

Lemma known_y0_cases : forall (a : Z -> aval) (r : Z), True.
Proof. auto. Qed.

Lemma rel_inv : forall s st regs m status count,
  Rel s st regs m -> Inv c segs regs0 (E st status count) (y0 s) regs m.
Proof.
  intros s st regs m status count R. pose proof (r_k0 _ _ _ _ R) as RK0. pose proof (r_k1 _ _ _ _ R) as RK1.
  destruct R. constructor; cbn [y0 yA yF yH yV yroom].
  - intros r Hk.
    assert (Hr : forall k, bv_unsigned r = k -> r = Z_to_bv 5 k) by (intros k Hk'; apply u_eq; exact Hk').
    remember (bv_unsigned r) as rn eqn:Er.
    destruct (Z.eqb_spec rn 0) as [->|E1]; [rewrite (Hr 0%Z eq_refl); rewrite eval_const; reflexivity|].
    destruct (Z.eqb_spec rn 8) as [->|E2];
      [rewrite (Hr 8%Z eq_refl); cbn [eval base_val E e_fp]; rewrite v_addi_0; exact r_fp0|].
    destruct (Z.eqb_spec rn 9) as [->|E3];
      [rewrite (Hr 9%Z eq_refl); cbn [eval base_val E e_vm]; rewrite v_addi_0; exact r_vm0|].
    destruct (Z.eqb_spec rn 18) as [->|E4].
    { rewrite (Hr 18%Z eq_refl). destruct (sC s) as [n|] eqn:Ec; [|discriminate].
      cbn [eval base_val E e_st]. rewrite v_addi_0. apply r_c0. reflexivity. }
    destruct (Z.eqb_spec rn 19) as [->|E5];
      [rewrite (Hr 19%Z eq_refl); cbn [eval base_val E e_st]; rewrite v_addi_0; exact r_hp0|].
    destruct (Z.eqb_spec rn 20) as [->|E6].
    { rewrite (Hr 20%Z eq_refl). destruct (sK0 s) as [n|] eqn:Ec; [|discriminate].
      cbn [optslot eval base_val E e_st]. rewrite v_addi_0. apply RK0. reflexivity. }
    destruct (Z.eqb_spec rn 21) as [->|E7].
    { rewrite (Hr 21%Z eq_refl). destruct (sK1 s) as [n|] eqn:Ec; [|discriminate].
      cbn [optslot eval base_val E e_st]. rewrite v_addi_0. apply RK1. reflexivity. }
    discriminate.
  - exact r_keep0.
  - intros n Hk Hn. unfold frame0 in *.
    destruct (Z.leb 0 n && Z.ltb n 64 && Z.testbit (sM s) n)%bool eqn:Hb; [|discriminate].
    apply andb_true_iff in Hb as [Hb H3]. apply andb_true_iff in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    destruct (r_M0 n (conj H1 H2) H3) as (_ & Hd).
    cbn [eval base_val E e_st]. rewrite v_addi_0. exact Hd.
  - intros k Hk. discriminate.
  - intros k Hk. destruct (Z.eqb_spec k 8) as [Ek|Ek].
    + subst k. split; [lia|]. cbn [eval base_val E e_st]. rewrite v_addi_0. exact r_lim0.
    + exfalso. revert Hk. destruct (Z.eqb_spec k 8); [contradiction | discriminate].
  - exact r_heap0.
  - exact r_cell0.
  - exact r_code0.
  - cbn [E e_st]. destruct r_R0. split; lia.
  - reflexivity.
  - eapply wr_env. exact r_wr0.
Qed.

Lemma slots64_in : forall n, (0 <= n < 64)%Z -> In n slots64.
Proof.
  intros n Hn. unfold slots64. apply in_map_iff. exists (Z.to_nat n). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma A_at : forall e y regs m (r : reg) k a, Inv c segs regs0 e y regs m ->
  bv_unsigned r = k -> yA y k = a -> known a = true -> getr regs r = eval e a.
Proof. intros e y regs m r k a I Hr Ha Hk. subst. apply (i_A _ _ _ _ _ _ _ I). exact Hk. Qed.

Lemma post_parts : forall s y d v delta plus t, post_ok c s y d v delta plus t = true ->
  same (yA y 8) (Lin KFp 0) = true /\ same (yA y 9) (Lin KVm 0) = true /\ same (yA y 19) (Lin KHp delta) = true /\
  reg_post d v y 18 (sC t) = true /\ reg_post d v y 20 (sK0 t) = true /\ reg_post d v y 21 (sK1 t) = true /\
  forallb (fun n => negb (Z.testbit (sM t) n) ||
    (Z.ltb n (cframe c) && (if same_opt_d d n then same (yF y n) v else same (yF y n) (Lin (KSlot n) 0)))) slots64 = true /\
  forallb (fun n => negb (Z.testbit (sP t) n) ||
    (negb (same_opt_d d n) && (Z.testbit (sP s) n || Z.eqb n plus))) slots64 = true /\
  (0 <= sR t)%Z /\ (8 * sR t + delta <= yroom y)%Z.
Proof.
  intros s y d v delta plus t H. unfold post_ok in H.
  apply andb_true_iff in H as [H H8]. apply andb_true_iff in H as [H H7].
  apply andb_true_iff in H as [H H6]. apply andb_true_iff in H as [H H5].
  apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H H3b]. apply andb_true_iff in H as [H H3a].
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H7. apply Z.leb_le in H8. tauto.
Qed.

(** CACHE and the kept registers after a block (spike 9). *)
Lemma reg_post_sound : forall y d v (r : reg) rn o st st' status count regs m,
  Inv c segs regs0 (E st status count) y regs m -> bv_unsigned r = rn -> reg_post d v y rn o = true ->
  (forall n, same_opt_d d n = false -> bslots st' n = bslots st n) ->
  (forall n, same_opt_d d n = true -> known v = true -> bslots st' n = eval (E st status count) v) ->
  forall n, o = Some n -> getr regs r = bslots st' n.
Proof.
  intros y d v r rn o st st' status count regs m I Hr PC Hs Hd n Hn. subst o. unfold reg_post in PC.
  destruct (same_opt_d d n) eqn:Ed.
  - pose proof (same_eq _ _ PC) as Es. pose proof (same_known _ _ PC) as Kk.
    rewrite (A_at _ _ _ _ r rn _ I Hr Es) by (rewrite Es in Kk; exact Kk).
    rewrite (Hd n Ed) by (rewrite Es in Kk; exact Kk). reflexivity.
  - pose proof (same_eq _ _ PC) as Es. rewrite (A_at _ _ _ _ r rn _ I Hr Es eq_refl).
    rewrite (Hs n Ed). cbn [eval base_val E e_st]. apply v_addi_0.
Qed.

(** The canonical state after a block. *)
Lemma post_sound : forall s t y d v delta plus st st' status count regs m,
  post_ok c s y d v delta plus t = true ->
  Inv c segs regs0 (E st status count) y regs m ->
  (forall n, same_opt_d d n = false -> bslots st' n = bslots st n) ->
  (forall n, same_opt_d d n = true -> known v = true -> bslots st' n = eval (E st status count) v) ->
  bhp st' = v_addi (bhp st) delta -> u (bhp st') = (u (bhp st) + delta)%Z ->
  bhlimit st' = bhlimit st -> bconsts st' = bconsts st ->
  Lay c (E st' status count) st' ->
  (forall a x, bheap st' a = Some x -> rdn segs m a 8 = Some (le x)) ->
  (forall n, (0 <= n < 64)%Z -> Z.testbit (sP s) n = true -> tag3 (bslots st n) = 3%Z) ->
  ((0 <= plus < 64)%Z -> same_opt_d d plus = false -> tag3 (bslots st' plus) = 3%Z) ->
  (forall n, wfv st' (bslots st' n)) -> (forall i, wfv st' (bconsts st' i)) ->
  (forall a x, bheap st' a = Some x -> wfv st' x) ->
  Wr c segs (E st status count) st' m ->
  (forall i w, ckinds c i = Some (KImm w) -> bconsts st i = Z_to_bv 64 w) ->
  (forall i ad tg, ckinds c i = Some (KPtr ad tg) -> tag3 (bconsts st i) = tg) ->
  (forall i ad, ckinds c i = Some (KPtr ad 5) -> exists v, bheap st' (v_addi (bconsts st' i) 3) = Some v) ->
  Rel t st' regs m.
Proof.
  intros s t y d v delta plus st st' status count regs m Hp I Hs Hd Hh Uh Hl Hc Ly Hheap HP Hplus Wf Wfc Wfh Wr' Him Htg Hpr.
  destruct (post_parts _ _ _ _ _ _ _ Hp) as (P8 & P9 & P19 & PC & PK0 & PK1 & PM & PP & PR0 & PR).
  apply same_eq in P8. apply same_eq in P9. apply same_eq in P19.
  pose proof I as [A K Fr Hhh V Hpp Cl Cd Rm V8 W].
  constructor.
  - rewrite (A_at _ _ _ _ 8 8 _ I eq_refl P8 eq_refl). cbn [eval base_val E e_fp]. apply v_addi_0.
  - rewrite (A_at _ _ _ _ 9 9 _ I eq_refl P9 eq_refl). cbn [eval base_val E e_vm]. apply v_addi_0.
  - rewrite (A_at _ _ _ _ 19 19 _ I eq_refl P19 eq_refl). rewrite Hh. reflexivity.
  - exact (reg_post_sound _ _ _ 18 18 _ _ _ _ _ _ _ I eq_refl PC Hs Hd).
  - exact (reg_post_sound _ _ _ 20 20 _ _ _ _ _ _ _ I eq_refl PK0 Hs Hd).
  - exact (reg_post_sound _ _ _ 21 21 _ _ _ _ _ _ _ I eq_refl PK1 Hs Hd).
  - exact K.
  - eapply lay_env. exact Ly.
  - intros n Hn Ht. rewrite forallb_forall in PM. pose proof (PM n (slots64_in n Hn)) as Hq.
    rewrite Ht in Hq. cbn [negb orb] in Hq. apply andb_true_iff in Hq as [Hq1 Hq2]. apply Z.ltb_lt in Hq1.
    split; [exact Hq1|].
    destruct (same_opt_d d n) eqn:Ed.
    + pose proof (same_eq _ _ Hq2) as Es. pose proof (same_known _ _ Hq2) as Kk.
      pose proof (Fr n Kk (conj (proj1 Hn) Hq1)) as Hrd. unfold slot_at in Hrd. cbn [E e_fp] in Hrd.
      rewrite (Hd n Ed) by (rewrite Es in Kk; exact Kk). rewrite <- Es. exact Hrd.
    + pose proof (same_eq _ _ Hq2) as Es.
      assert (Kk : known (yF y n) = true) by (rewrite Es; reflexivity).
      pose proof (Fr n Kk (conj (proj1 Hn) Hq1)) as Hrd. unfold slot_at in Hrd. cbn [E e_fp] in Hrd.
      rewrite Es in Hrd. cbn [eval base_val E e_st] in Hrd. rewrite v_addi_0 in Hrd.
      rewrite (Hs n Ed). exact Hrd.
  - rewrite Hl. destruct (V 8%Z ltac:(rewrite V8; reflexivity)) as (_ & Hrd). rewrite V8 in Hrd.
    cbn [eval base_val E e_st e_vm] in Hrd. rewrite v_addi_0 in Hrd. exact Hrd.
  - exact Hheap.
  - intros i ad tg Hk. rewrite Hc. eapply Cl. exact Hk.
  - intros i w Hk. rewrite Hc. eapply Him. exact Hk.
  - intros i ad tg Hk. rewrite Hc. eapply Htg. exact Hk.
  - exact Cd.
  - intros n Hn Ht. rewrite forallb_forall in PP. pose proof (PP n (slots64_in n Hn)) as Hq.
    rewrite Ht in Hq. cbn [negb orb] in Hq. apply andb_true_iff in Hq as [Hq1 Hq2].
    apply negb_true_iff in Hq1.
    apply orb_true_iff in Hq2 as [Hq2|Hq2].
    + rewrite (Hs n Hq1). apply HP; assumption.
    + apply Z.eqb_eq in Hq2. subst n. apply Hplus; assumption.
  - destruct Rm as (Rm0 & Rm1). cbn [E e_st] in Rm1. rewrite Uh, Hl. split; lia.
  - exact Wf.
  - exact Wfc.
  - exact Wfh.
  - eapply wr_env. exact Wr'.
  - exact Hpr.
Qed.

End Sound.
