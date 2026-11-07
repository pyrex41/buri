(** * Soundness of the symbolic run of one block in Theorem's model (Shen/JIT Phase 0, spike 8).
    Proof-side. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Examples.emitter_p3_ns Require Import CfDefs CfStep.
Import ListNotations.
Open Scope bv_scope.

Definition le (v : word) := word_to_le_bytes 8 v.
Definition apart (a n b k : Z) : Prop := (a + n <= b \/ b + k <= a)%Z.

Definition u (x : word) : Z := bv_unsigned x.

(* ---- values ---- *)

Lemma vadd2 : forall (x : word) k i, v_addi (v_addi x k) i = v_addi x (k + i).
Proof.
  intros. apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned.
  rewrite bv_wrap_add_idemp_l. f_equal. lia.
Qed.

Lemma eval_const : forall e k, eval e (Lin KConst k) = Z_to_bv 64 k.
Proof.
  intros. cbn [eval base_val]. apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 0) with 0%Z. f_equal.
Qed.

Lemma eval_mkc : forall e z, eval e (mkc z) = Z_to_bv 64 z.
Proof.
  intros. unfold mkc. rewrite eval_const. apply bv_eq. rewrite !Z_to_bv_unsigned.
  apply bv_wrap_bv_wrap. lia.
Qed.

Lemma eval_u : forall e (w : word), eval e (Lin KConst (bv_unsigned w)) = w.
Proof.
  intros. rewrite eval_const. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_bv_unsigned.
Qed.

Lemma add_k_sound : forall e a i, known (add_k a i) = true ->
  eval e (add_k a i) = v_addi (eval e a) i.
Proof.
  intros e a i H. destruct a as [b k|n|]; cbn in H; try discriminate.
  destruct b; cbn [add_k];
    try (cbn [eval]; rewrite vadd2; reflexivity).
  rewrite eval_mkc, eval_const. apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned.
  rewrite bv_wrap_add_idemp_l. reflexivity.
Qed.

Lemma known_add_k : forall a i, known (add_k a i) = true -> known a = true.
Proof. intros [b k|n|] i H; try reflexivity; discriminate. Qed.

Lemma alu_add_v : forall (a : word) (imm : bv 12),
  alu64 ALU_ADD a (sext 64 imm) = v_addi a (bv_signed imm).
Proof. intros. apply b_addsext. Qed.

Lemma alu_add_c : forall (x y : word) k, x = Z_to_bv 64 k -> alu64 ALU_ADD x y = v_addi y k.
Proof.
  intros x y k ->. change (alu64 ALU_ADD (Z_to_bv 64 k) y) with (Z_to_bv 64 k + y).
  apply bv_eq. unfold v_addi. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  rewrite bv_wrap_add_idemp_l, (Z.add_comm k). reflexivity.
Qed.

Lemma alu_add_r : forall (x y : word) k, y = Z_to_bv 64 k -> alu64 ALU_ADD x y = v_addi x k.
Proof.
  intros x y k ->. change (alu64 ALU_ADD x (Z_to_bv 64 k)) with (x + Z_to_bv 64 k).
  apply b_npc.
Qed.

Lemma aval_add_case : forall a b,
  (exists k, a = Lin KConst k /\ aval_add a b = add_k b k) \/
  (exists k, b = Lin KConst k /\ aval_add a b = add_k a k) \/ aval_add a b = Unk.
Proof.
  intros [ba ka|na|] [bb kb|nb|];
    try (destruct ba; try (left; eexists; split; reflexivity));
    try (destruct bb; try (right; left; eexists; split; reflexivity));
    right; right; reflexivity.
Qed.

Lemma aval_add_sound : forall e a b x y,
  known (aval_add a b) = true ->
  (known a = true -> x = eval e a) -> (known b = true -> y = eval e b) ->
  alu64 ALU_ADD x y = eval e (aval_add a b).
Proof.
  intros e a b x y H Ha Hb.
  destruct (aval_add_case a b) as [(k & -> & E)|[(k & -> & E)|E]]; rewrite E in *.
  - rewrite add_k_sound by exact H. rewrite Hb by (eapply known_add_k; exact H).
    apply alu_add_c. rewrite Ha by reflexivity. apply eval_const.
  - rewrite add_k_sound by exact H. rewrite Ha by (eapply known_add_k; exact H).
    apply alu_add_r. rewrite Hb by reflexivity. apply eval_const.
  - discriminate.
Qed.

Lemma same_eq : forall a b, same a b = true -> a = b.
Proof.
  intros [ba ka|na|] [bb kb|nb|] H; cbn in H; try discriminate.
  - apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H2. subst kb. f_equal.
    destruct ba, bb; cbn in H1; try discriminate; try reflexivity;
      apply Z.eqb_eq in H1; subst; reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
Qed.

Lemma same_known : forall a b, same a b = true -> known a = true.
Proof. intros [ba ka|na|] b H; [reflexivity | reflexivity | destruct b; discriminate]. Qed.

Section Block.
Context {fx : FPState}.
Variable c : cfg.
Variable cell_of : Z -> option Z.
Variable st_P : Z.
Variable segs : list Segment.
Variable rom : word -> option byte.
Variable regs0 : bvmap 5 word.
Variable e : env.

Abbreviation st := (e_st e).
Abbreviation fp := (e_fp e).
Abbreviation vm := (e_vm e).
Abbreviation hp := (bhp (e_st e)).
Abbreviation lim := (bhlimit (e_st e)).
Abbreviation F := (cframe c).
Abbreviation clen := (code_len c).

Definition wfv (x : bstate) (v : word) : Prop :=
  tag3 v = 3%Z -> (exists a, bheap x (v_addi v (-3)) = Some a) /\ (exists b, bheap x (v_addi v 5) = Some b).

(** The layout is about one bytecode state. *)
Record Lay (x : bstate) : Prop := {
  l_F : (0 <= F <= 64)%Z;
  l_fp : (u fp + 8 * F < 2^62)%Z;
  l_vm : (u vm + 64 < 2^62)%Z;
  l_hp : (u (bhp x) <= u (bhlimit x))%Z;
  l_lim : (u (bhlimit x) + 8192 < 2^62)%Z;
  l_fv : apart (u fp) (8 * F) (u vm) 64;
  l_fh : apart (u fp) (8 * F) (u (bhp x)) (u (bhlimit x) - u (bhp x));
  l_vh : apart (u vm) 64 (u (bhp x)) (u (bhlimit x) - u (bhp x));
  l_fc : apart (u fp) (8 * F) (cbase c) clen;
  l_vc : apart (u vm) 64 (cbase c) clen;
  l_hc : apart (u (bhp x)) (u (bhlimit x) - u (bhp x)) (cbase c) clen;
  l_heap : forall a v, bheap x a = Some v ->
    (u a + 8 <= 2^64)%Z /\ apart (u a) 8 (u fp) (8 * F) /\ apart (u a) 8 (u vm) 64 /\
    apart (u a) 8 (u (bhp x)) (u (bhlimit x) - u (bhp x)) /\ apart (u a) 8 (cbase c) clen;
  l_cell : forall i ad t, ckinds c i = Some (KPtr ad t) ->
    (0 <= ad /\ ad + 8 < 2^64)%Z /\ apart ad 8 (u fp) (8 * F) /\ apart ad 8 (u vm) 64 /\
    apart ad 8 (u (bhp x)) (u (bhlimit x) - u (bhp x)) /\ apart ad 8 (cbase c) clen
}.

Definition slot_at (n : Z) : word := v_addi fp (8 * n).

(** Every location the code stores to is mapped and writable. *)
Record Wr (x : bstate) (m : word -> option byte) : Prop := {
  w_f : forall n, (0 <= n < F)%Z -> store_ok segs m (slot_at n) 8 = true;
  w_v : forall k, (k = 0 \/ k = 16 \/ k = 24)%Z -> store_ok segs m (v_addi vm k) 8 = true;
  w_h : forall k, (0 <= k)%Z -> (u (bhp x) + k + 8 <= u (bhlimit x))%Z ->
          store_ok segs m (v_addi (bhp x) k) 8 = true
}.

Record Inv (y : Y) (regs : bvmap 5 word) (m : word -> option byte) : Prop := {
  i_A : forall r : reg, known (yA y (bv_unsigned r)) = true -> getr regs r = eval e (yA y (bv_unsigned r));
  i_keep : forall r : reg, scratch (bv_unsigned r) = false -> getr regs r = getr regs0 r;
  i_F : forall n, known (yF y n) = true -> (0 <= n < F)%Z -> rdn segs m (slot_at n) 8 = Some (le (eval e (yF y n)));
  i_H : forall k, known (yH y k) = true ->
    (0 <= k)%Z /\ (k mod 8 = 0)%Z /\ (u hp + k + 8 <= u lim)%Z /\ rdn segs m (v_addi hp k) 8 = Some (le (eval e (yH y k)));
  i_V : forall k, known (yV y k) = true ->
    (k = 0 \/ k = 8 \/ k = 16 \/ k = 24)%Z /\ rdn segs m (v_addi vm k) 8 = Some (le (eval e (yV y k)));
  i_heap : forall a v, bheap st a = Some v -> rdn segs m a 8 = Some (le v);
  i_cell : forall i ad t, ckinds c i = Some (KPtr ad t) ->
    rdn segs m (Z_to_bv 64 ad) 8 = Some (le (bconsts st i));
  i_code : CodeOK c segs m;
  i_room : (0 <= yroom y)%Z /\ (u hp + yroom y <= u lim)%Z;
  i_V8 : yV y 8 = Lin KHlim 0;
  i_wr : Wr st m
}.

Hypothesis L : Lay st.
Hypothesis HP : forall n, (0 <= n < 64)%Z -> Z.testbit st_P n = true -> tag3 (bslots st n) = 3%Z.
Hypothesis HWF : forall n, wfv st (bslots st n).
(** Spike 9: a procedure constant has its entry word in the heap. *)
Hypothesis HPROC : forall i ad, ckinds c i = Some (KPtr ad 5) -> exists v, bheap st (v_addi (bconsts st i) 3) = Some v.

Fixpoint Ends (r : res) (stop : Z) (ms : machine_state) : Prop :=
  match r with
  | RDone y => exists regs m, ms = mkst regs (at_ c stop) m rom /\ Inv y regs m
  | RJump t y => exists regs m, ms = mkst regs (at_ c t) m rom /\ Inv y regs m
  | RRet y => exists regs m,
      ms = mkst regs (jalr_tgt (bslots st 0) 0) m rom /\ Inv y regs m
  | RIJump a y => exists regs m, ms = mkst regs (jalr_tgt (eval e a) 0) m rom /\ Inv y regs m
  | RCall callee next y => exists regs m,
      ms = mkst regs (Z_to_bv 64 callee) m rom /\ Inv y regs m /\ getr regs 1 = at_ c next
  | RBr cc a b t y rest =>
      (branch_taken cc (eval e a) (eval e b) = true /\
       exists regs m, ms = mkst regs (at_ c t) m rom /\ Inv y regs m) \/
      (branch_taken cc (eval e a) (eval e b) = false /\ Ends rest stop ms)
  end.

Lemma u_inj : forall r r' : reg, bv_unsigned r = bv_unsigned r' -> r = r'.
Proof. intros. apply bv_eq. exact H. Qed.

Lemma inv_setr : forall y regs m (rd : reg) v w,
  Inv y regs m -> is_x0 rd = false -> scratch (bv_unsigned rd) = true ->
  (known v = true -> w = eval e v) ->
  Inv (setr y (bv_unsigned rd) v) (regupd regs rd w) m.
Proof.
  intros y regs m rd v w I Hx Hs Hw. destruct I as [A K Fr H V Hp Cl Cd Rm V8 W].
  constructor; try assumption.
  - intros r Hk. cbn [setr yA] in *. unfold upd in *. destruct (Z.eqb_spec (bv_unsigned r) (bv_unsigned rd)) as [Er|Er].
    + apply u_inj in Er. subst r.
      rewrite getr_same by (intro E; subst rd; discriminate Hx). apply Hw. exact Hk.
    + rewrite getr_other by (intro E; subst; contradiction). apply A. exact Hk.
  - intros r Hr. rewrite getr_other.
    + apply K. exact Hr.
    + intro E. subst r. congruence.
Qed.

Local Lemma wr_inv : forall y (rd : reg) v k r,
  wr y rd v k = Some r ->
  is_x0 rd = false /\ scratch (bv_unsigned rd) = true /\ k (setr y (bv_unsigned rd) v) = Some r.
Proof.
  intros y rd v k r H. unfold wr in H.
  destruct (is_x0 rd), (scratch (bv_unsigned rd)); cbn in H; try discriminate.
  auto.
Qed.

(* ---- stores ---- *)

Lemma le_len : forall v, length (le v) = 8%nat.
Proof. intros. apply length_word_to_le_bytes. Qed.

Lemma rd_keep : forall m (a b : word) v n,
  (u b + 8 <= u a \/ u a + 8 <= u b)%Z -> (u a + 8 <= 2^64)%Z -> (u b + 8 <= 2^64)%Z ->
  rdn segs m b 8 = Some n -> rdn segs (wbytes m a (le v)) b 8 = Some n.
Proof.
  intros m a b v n Hd Ha Hb H. rewrite <- H. apply rdn_wbytes_out.
  - unfold u in *. rewrite le_len. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. simpl Z.of_nat. lia.
  - unfold u in *. simpl Z.of_nat. lia.
  - unfold u in *. rewrite le_len. simpl Z.of_nat. lia.
Qed.

Lemma rd_hit : forall m (a : word) v,
  (u a + 8 <= 2^64)%Z -> rdn segs (wbytes m a (le v)) a 8 = Some (le v).
Proof. intros. apply rdn_wbytes_hit8. exact H. Qed.

Lemma u_add : forall (x : word) k, (0 <= k)%Z -> (u x + k < 2^64)%Z -> u (v_addi x k) = (u x + k)%Z.
Proof. intros. apply v_addi_nneg; assumption. Qed.

Lemma u_slot : forall n, (0 <= n < F)%Z -> u (slot_at n) = (u fp + 8 * n)%Z.
Proof.
  intros n Hn. pose proof (l_fp _ L). unfold slot_at. apply u_add; lia.
Qed.

Lemma u_vm : forall k, (0 <= k <= 64)%Z -> u (v_addi vm k) = (u vm + k)%Z.
Proof. intros k Hk. pose proof (l_vm _ L). apply u_add; lia. Qed.

Lemma u_hp : forall k, (0 <= k)%Z -> (u hp + k + 8 <= u lim)%Z -> u (v_addi hp k) = (u hp + k)%Z.
Proof. intros k Hk Hl. pose proof (l_lim _ L). apply u_add; lia. Qed.

Lemma u_cell : forall ad, (0 <= ad /\ ad + 8 < 2^64)%Z -> u (Z_to_bv 64 ad) = ad.
Proof. intros ad [H1 H2]. apply u_Z2bv; lia. Qed.

Lemma wr_grow : forall x m a v, Wr x m -> Wr x (wbytes m a (le v)).
Proof.
  intros x m a v [Wf Wv Wh]. constructor; intros.
  - eapply store_ok_mono; [apply wbytes_grows | apply Wf; assumption].
  - eapply store_ok_mono; [apply wbytes_grows | apply Wv; assumption].
  - eapply store_ok_mono; [apply wbytes_grows | apply Wh; assumption].
Qed.

Local Ltac lay :=
  pose proof (l_F _ L); pose proof (l_fp _ L); pose proof (l_vm _ L); pose proof (l_hp _ L);
  pose proof (l_lim _ L); pose proof (l_fv _ L); pose proof (l_fh _ L); pose proof (l_vh _ L);
  pose proof (l_fc _ L); pose proof (l_vc _ L); pose proof (l_hc _ L).

(** A store to an address outside the heap words, the cells and the code keeps those, and the room. *)
Lemma inv_store_common : forall y regs m (a : word) v,
  Inv y regs m ->
  (u a + 8 <= 2^64)%Z ->
  (forall b w, bheap st b = Some w -> u b + 8 <= u a \/ u a + 8 <= u b)%Z ->
  (forall i ad t, ckinds c i = Some (KPtr ad t) -> ad + 8 <= u a \/ u a + 8 <= ad)%Z ->
  (u a + 8 <= cbase c \/ cbase c + clen <= u a)%Z ->
  (forall b w, bheap st b = Some w -> rdn segs (wbytes m a (le v)) b 8 = Some (le w)) /\
  (forall i ad t, ckinds c i = Some (KPtr ad t) ->
     rdn segs (wbytes m a (le v)) (Z_to_bv 64 ad) 8 = Some (le (bconsts st i))) /\
  CodeOK c segs (wbytes m a (le v)) /\ Wr st (wbytes m a (le v)).
Proof.
  intros y regs m a v I Ha Hh Hc Hd. destruct I.
  split; [|split; [|split]].
  - intros b w Hb. pose proof (l_heap _ L b w Hb) as (Hb8 & _).
    apply rd_keep; [ | exact Ha | exact Hb8 | apply i_heap0; exact Hb ].
    specialize (Hh b w Hb). lia.
  - intros i ad t Hk. pose proof (l_cell _ L i ad t Hk) as (Hb & _).
    rewrite <- (i_cell0 i ad t Hk). apply rdn_wbytes_out.
    + rewrite le_len. simpl Z.of_nat. pose proof (u_cell ad Hb) as Uc. specialize (Hc i ad t Hk).
      unfold u in *. lia.
    + simpl Z.of_nat. pose proof (u_cell ad Hb). unfold u in *. lia.
    + rewrite le_len. simpl Z.of_nat. unfold u in *. lia.
  - apply code_ok_wbytes; [ exact i_code0 | | ]; rewrite le_len; simpl Z.of_nat; unfold u in *; lia.
  - apply wr_grow. exact i_wr0.
Qed.

Local Ltac aparts :=
  unfold apart in *; lia.

Lemma upd_same : forall f k v, upd f k v k = v.
Proof. intros. unfold upd. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma upd_other : forall f k v j, j <> k -> upd f k v j = f j.
Proof. intros. unfold upd. destruct (Z.eqb_spec j k); [contradiction | reflexivity]. Qed.

Lemma inv_store_frame : forall y regs m n v w,
  Inv y regs m -> (0 <= n < F)%Z -> (known v = true -> w = eval e v) ->
  Inv (mkY (yA y) (upd (yF y) n v) (yH y) (yV y) (yroom y)) regs (wbytes m (slot_at n) (le w)).
Proof.
  intros y regs m n v w I Hn Hw. lay.
  pose proof (u_slot n Hn) as Us.
  assert (Ha : (u (slot_at n) + 8 <= 2^64)%Z) by lia.
  destruct (inv_store_common y regs m (slot_at n) w I Ha) as (C1 & C2 & C3 & C4).
  { intros b z Hb. pose proof (l_heap _ L b z Hb) as (_ & Ha1 & _). aparts. }
  { intros i ad t Hk. pose proof (l_cell _ L i ad t Hk) as (_ & Ha1 & _). aparts. }
  { aparts. }
  destruct I as [A K Fr Hh V Hp Cl Cd Rm V8 W]. constructor; cbn [yA yF yH yV yroom]; try assumption.
  - intros n' Hk Hn'. destruct (Z.eqb_spec n' n) as [Ee|Ne].
    + subst n'. rewrite upd_same in Hk |- *. rewrite Hw by exact Hk. apply rd_hit. exact Ha.
    + rewrite upd_other in Hk |- * by exact Ne. pose proof (u_slot n' Hn') as Us'.
      apply rd_keep; [ lia | exact Ha | lia | apply Fr; assumption ].
  - intros k Hk. destruct (Hh k Hk) as (Q0 & Q8 & Q1 & Q2). split; [exact Q0|]. split; [exact Q8|]. split; [exact Q1|].
    pose proof (u_hp k Q0 Q1) as Uh. apply rd_keep; [ aparts | exact Ha | lia | exact Q2 ].
  - intros k Hk. destruct (V k Hk) as (Q0 & Q2). split; [exact Q0|].
    assert (Hk64 : (0 <= k <= 64)%Z) by lia. pose proof (u_vm k Hk64) as Uv.
    apply rd_keep; [ aparts | exact Ha | lia | exact Q2 ].
Qed.

Lemma inv_store_vm : forall y regs m k v w,
  Inv y regs m -> (k = 0 \/ k = 16 \/ k = 24)%Z -> (known v = true -> w = eval e v) ->
  Inv (mkY (yA y) (yF y) (yH y) (upd (yV y) k v) (yroom y)) regs (wbytes m (v_addi vm k) (le w)).
Proof.
  intros y regs m k v w I Hkk Hw. lay.
  assert (Hk64 : (0 <= k <= 64)%Z) by lia. pose proof (u_vm k Hk64) as Uv.
  assert (Ha : (u (v_addi vm k) + 8 <= 2^64)%Z) by lia.
  destruct (inv_store_common y regs m (v_addi vm k) w I Ha) as (C1 & C2 & C3 & C4).
  { intros b z Hb. pose proof (l_heap _ L b z Hb) as (_ & _ & Ha1 & _). aparts. }
  { intros i ad t Hc. pose proof (l_cell _ L i ad t Hc) as (_ & _ & Ha1 & _). aparts. }
  { aparts. }
  destruct I as [A K Fr Hh V Hp Cl Cd Rm V8 W]. constructor; cbn [yA yF yH yV yroom]; try assumption.
  - intros n' Hk Hn'. pose proof (u_slot n' Hn') as Us'.
    apply rd_keep; [ aparts | exact Ha | lia | apply Fr; assumption ].
  - intros j Hj. destruct (Hh j Hj) as (Q0 & Q8 & Q1 & Q2). split; [exact Q0|]. split; [exact Q8|]. split; [exact Q1|].
    pose proof (u_hp j Q0 Q1) as Uh. apply rd_keep; [ aparts | exact Ha | lia | exact Q2 ].
  - intros j Hj. destruct (Z.eqb_spec j k) as [Ee|Ne].
    + subst j. rewrite upd_same in Hj |- *. split; [lia|]. rewrite Hw by exact Hj. apply rd_hit. exact Ha.
    + rewrite upd_other in Hj |- * by exact Ne. destruct (V j Hj) as (Q0 & Q2). split; [exact Q0|].
      assert (Hj64 : (0 <= j <= 64)%Z) by lia. pose proof (u_vm j Hj64) as Uj.
      apply rd_keep; [ lia | exact Ha | lia | exact Q2 ].
  - rewrite upd_other by lia. exact V8.
Qed.

Lemma inv_store_hp : forall y regs m k v w,
  Inv y regs m -> (0 <= k)%Z -> (k mod 8 = 0)%Z -> (k + 8 <= yroom y)%Z -> (known v = true -> w = eval e v) ->
  Inv (mkY (yA y) (yF y) (upd (yH y) k v) (yV y) (yroom y)) regs (wbytes m (v_addi hp k) (le w)).
Proof.
  intros y regs m k v w I Hk0 Hk8 Hk Hw. lay.
  pose proof (i_room _ _ _ I) as (Rm0 & Rm1).
  assert (Hl : (u hp + k + 8 <= u lim)%Z) by lia.
  pose proof (u_hp k Hk0 Hl) as Uh.
  assert (Ha : (u (v_addi hp k) + 8 <= 2^64)%Z) by lia.
  destruct (inv_store_common y regs m (v_addi hp k) w I Ha) as (C1 & C2 & C3 & C4).
  { intros b z Hb. pose proof (l_heap _ L b z Hb) as (_ & _ & _ & Ha1 & _). aparts. }
  { intros i ad t Hc. pose proof (l_cell _ L i ad t Hc) as (_ & _ & _ & Ha1 & _). aparts. }
  { aparts. }
  destruct I as [A K Fr Hh V Hp Cl Cd Rm V8 W]. constructor; cbn [yA yF yH yV yroom]; try assumption.
  - intros n' Hn0 Hn'. pose proof (u_slot n' Hn') as Us'.
    apply rd_keep; [ aparts | exact Ha | lia | apply Fr; assumption ].
  - intros j Hj. destruct (Z.eqb_spec j k) as [Ee|Ne].
    + subst j. rewrite upd_same in Hj |- *. split; [lia|]. split; [exact Hk8|]. split; [lia|]. rewrite Hw by exact Hj. apply rd_hit. exact Ha.
    + rewrite upd_other in Hj |- * by exact Ne. destruct (Hh j Hj) as (Q0 & Q8 & Q1 & Q2). split; [exact Q0|]. split; [exact Q8|]. split; [exact Q1|].
      pose proof (u_hp j Q0 Q1) as Uj.
      apply rd_keep; [ lia | exact Ha | lia | exact Q2 ].
  - intros j Hj. destruct (V j Hj) as (Q0 & Q2). split; [exact Q0|].
    assert (Hj64 : (0 <= j <= 64)%Z) by lia. pose proof (u_vm j Hj64) as Uj.
    apply rd_keep; [ aparts | exact Ha | lia | exact Q2 ].
Qed.

(* ---- loads ---- *)

Lemma load_sound : forall y regs m a v,
  Inv y regs m -> load' c cell_of st_P y a = Some v -> known v = true /\
  rdn segs m (eval e a) 8 = Some (le (eval e v)).
Proof.
  intros y regs m a v I H. destruct I as [A K Fr Hh V Hp Cl Cd Rm V8 W].
  destruct a as [b k|n|]; cbn [load' load] in H; try discriminate.
  destruct b; cbn [load' load] in H; try discriminate.
  - (* constant: a cell *)
    destruct (cell_of k) as [i|]; try discriminate.
    destruct (ckinds c i) as [[w|ad t]|] eqn:Hk; try discriminate.
    destruct (Z.eqb_spec ad k) as [->|_]; try discriminate.
    injection H as <-. split; [reflexivity|].
    rewrite eval_const. cbn [eval base_val]. rewrite v_addi_0. eapply Cl. exact Hk.
  - (* a pair's field *)
    destruct (Z.leb 0 n && Z.ltb n 64 && Z.testbit st_P n)%bool eqn:Hn; try discriminate.
    apply andb_true_iff in Hn as [Hn Ht]. apply andb_true_iff in Hn as [H0 H1].
    apply Z.leb_le in H0. apply Z.ltb_lt in H1.
    pose proof (HP n (conj H0 H1) Ht) as Htag.
    destruct (HWF n Htag) as ([va Ea] & [vb Eb]).
    destruct (Z.eqb_spec k (-3)) as [->|_].
    + injection H as <-. split; [reflexivity|]. cbn [eval base_val].
      rewrite v_addi_0, Ea. apply Hp. exact Ea.
    + destruct (Z.eqb_spec k 5) as [->|_]; try discriminate.
      injection H as <-. split; [reflexivity|]. cbn [eval base_val].
      rewrite v_addi_0, Eb. apply Hp. exact Eb.
  - (* the frame *)
    destruct (Z.leb 0 k && Z.ltb k (8 * F) && Z.eqb (k mod 8) 0)%bool eqn:Hn; try discriminate.
    apply andb_true_iff in Hn as [Hn Ht]. apply andb_true_iff in Hn as [H0 H1].
    apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.eqb_eq in Ht.
    destruct (known (yF y (k / 8))) eqn:Hk; try discriminate.
    injection H as <-. split; [exact Hk|].
    assert (Hk8 : (k = 8 * (k / 8))%Z) by (apply Z.div_exact; lia).
    assert (Hr : (0 <= k / 8 < F)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    pose proof (Fr (k / 8)%Z Hk Hr) as Hd. unfold slot_at in Hd. rewrite <- Hk8 in Hd.
    cbn [eval base_val]. exact Hd.
  - (* the VM *)
    destruct (Z.eqb k 0 || Z.eqb k 8)%bool eqn:Hn; try discriminate.
    destruct (known (yV y k)) eqn:Hk; try discriminate.
    injection H as <-. split; [exact Hk|]. destruct (V k Hk) as (_ & Hd). exact Hd.
  - (* spike 9: a procedure's entry word *)
    destruct (Z.eqb_spec k 3) as [->|_]; try discriminate.
    destruct (ckinds c i) as [[w|ad t]|] eqn:Hk; try discriminate.
    destruct (Z.eqb_spec t 5) as [->|_]; try discriminate.
    injection H as <-. split; [reflexivity|].
    destruct (HPROC i ad Hk) as (v & Hv). cbn [eval base_val]. rewrite v_addi_0, Hv. apply Hp. exact Hv.
Qed.

Lemma store_sound : forall y y' regs m a v w,
  Inv y regs m -> store c y a v = Some y' -> (known v = true -> w = eval e v) ->
  known a = true /\
  store_ok segs m (eval e a) 8 = true /\
  Inv y' regs (wbytes m (eval e a) (word_to_le_bytes 8 w)).
Proof.
  intros y y' regs m a v w I H Hw.
  destruct a as [b k|n|]; cbn [store] in H; try discriminate.
  pose proof (i_wr _ _ _ I) as [Wf Wv Wh].
  destruct b; cbn [store] in H; try discriminate.
  - destruct (Z.leb 0 k && Z.ltb k (8 * F) && Z.eqb (k mod 8) 0)%bool eqn:Hn; try discriminate.
    apply andb_true_iff in Hn as [Hn Ht]. apply andb_true_iff in Hn as [H0 H1].
    apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.eqb_eq in Ht.
    injection H as <-.
    assert (Hk8 : (k = 8 * (k / 8))%Z) by (apply Z.div_exact; lia).
    assert (Hr : (0 <= k / 8 < F)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Ea : eval e (Lin KFp k) = slot_at (k / 8)) by (unfold slot_at; rewrite <- Hk8; reflexivity).
    rewrite Ea. split; [reflexivity|]. split; [apply Wf; exact Hr|].
    eapply inv_store_frame; eassumption.
  - destruct (Z.eqb k 0 || Z.eqb k 16 || Z.eqb k 24)%bool eqn:Hn; try discriminate.
    injection H as <-.
    assert (Hk : (k = 0 \/ k = 16 \/ k = 24)%Z).
    { apply orb_true_iff in Hn as [Hn|Hn]; [apply orb_true_iff in Hn as [Hn|Hn]|];
        apply Z.eqb_eq in Hn; lia. }
    split; [reflexivity|]. split; [apply Wv; exact Hk|].
    eapply inv_store_vm; eassumption.
  - destruct (Z.leb 0 k && Z.leb (k + 8) (yroom y) && Z.eqb (k mod 8) 0)%bool eqn:Hn; try discriminate.
    apply andb_true_iff in Hn as [Hn H8]. apply andb_true_iff in Hn as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.eqb_eq in H8.
    injection H as <-. split; [reflexivity|].
    pose proof (i_room _ _ _ I) as (Rm0 & Rm1).
    split; [apply Wh; lia|].
    eapply inv_store_hp; eassumption.
Qed.

Lemma ltu_taken : forall (l h : word) k, (0 <= k)%Z -> (u h + k < 2^64)%Z ->
  branch_taken BC_LTU l (v_addi h k) = Z.ltb (u l) (u h + k).
Proof.
  intros l h k Hk Hh. cbn [branch_taken]. unfold bv_ltu, u.
  rewrite v_addi_nneg by (unfold u in *; lia). reflexivity.
Qed.

Lemma inv_note : forall cc a b y regs m,
  Inv y regs m -> branch_taken cc (eval e a) (eval e b) = false -> Inv (note_room cc a b y) regs m.
Proof.
  intros cc a b y regs m I Hb. unfold note_room.
  destruct cc; try exact I.
  destruct a as [ba ka|na|]; try exact I. destruct ba; try exact I.
  destruct ka; try exact I.
  destruct b as [bb kb|nb|]; try exact I. destruct bb; try exact I.
  destruct (Z.leb 0 kb && Z.leb kb 4096)%bool eqn:Hk; [|exact I].
  apply andb_true_iff in Hk as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
  pose proof (l_lim _ L) as Hl. pose proof (l_hp _ L) as Hh.
  cbn [eval base_val] in Hb. rewrite v_addi_0 in Hb.
  rewrite ltu_taken in Hb by (try lia). apply Z.ltb_ge in Hb.
  destruct I as [A K Fr H V Hp Cl Cd Rm V8 W]. constructor; cbn [yA yF yH yV yroom]; try assumption.
  split; [exact H0 | exact Hb].
Qed.

Lemma load_known : forall y a v, load' c cell_of st_P y a = Some v -> known a = true.
Proof. intros y [b k|n|] v H; [reflexivity | cbn in H; discriminate | cbn in H; discriminate]. Qed.

Lemma known_store : forall y a v y', store c y a v = Some y' -> known a = true.
Proof. intros y [b k|n|] v y' H; [reflexivity | cbn in H; discriminate | cbn in H; discriminate]. Qed.

Lemma hold_const : forall y regs m (r : reg) k,
  Inv y regs m -> yA y (bv_unsigned r) = Lin KConst k -> getr regs r = Z_to_bv 64 k.
Proof.
  intros y regs m r k I E. rewrite (i_A _ _ _ I r) by (rewrite E; reflexivity).
  rewrite E. apply eval_const.
Qed.

Local Lemma is_x0_one : forall rd : reg, bv_unsigned rd = 1%Z -> rd = 1.
Proof. intros rd H. apply bv_eq. rewrite H. reflexivity. Qed.

Theorem run_sound : forall f o stop y r regs m,
  run c cell_of st_P f o stop y = Some r -> Inv y regs m ->
  exists ms, steps segs (mkst regs (at_ c o) m rom) ms /\ Ends r stop ms.
Proof.
  induction f as [|f IH]; intros o stop y r regs m H I; cbn [run] in H; [discriminate|].
  destruct (Z.eqb_spec o stop) as [<-|Hne].
  { injection H as <-. exists (mkst regs (at_ c o) m rom). split; [constructor|]. cbn [Ends]. eauto. }
  destruct (in_code c o) eqn:Hic; cbn [negb] in H; [|discriminate].
  destruct (is_ecall (code_word c o)) eqn:He; [discriminate|].
  destruct (decode_any (code_word c o)) as [[i sz]|] eqn:Hd; [|discriminate].
  apply andb_true_iff in Hic as [Hic He2]. apply andb_true_iff in Hic as [He0 He1].
  apply Z.leb_le in He0. apply Z.leb_le in He1. apply Z.eqb_eq in He2.
  pose proof (wx_at c segs m o (i_code _ _ _ I) He0 He1 He2) as Hwx.
  destruct i; try discriminate H.
  - (* lui *)
    destruct (wr_inv _ _ _ _ _ H) as (Hx & Hs & Hr).
    destruct (IH _ _ _ _ _ _ Hr (inv_setr y regs m rd _ (v_lui (Z.shiftl (bv_signed imm) 12)) I Hx Hs
       (fun _ => eq_sym (eval_u e _)))) as (ms & Hm & Hn).
    exists ms. split; [|exact Hn]. eapply steps_step; [|exact Hm].
    eapply j_lui; [exact Hwx | exact He | exact Hd | reflexivity | exact Hx].
  - (* auipc *)
    destruct (wr_inv _ _ _ _ _ H) as (Hx & Hs & Hr).
    destruct (IH _ _ _ _ _ _ Hr (inv_setr y regs m rd _ (v_auipc (at_ c o) (Z.shiftl (bv_signed imm) 12)) I Hx Hs
       (fun _ => eq_sym (eval_u e _)))) as (ms & Hm & Hn).
    exists ms. split; [|exact Hn]. eapply steps_step; [|exact Hm].
    eapply j_auipc; [exact Hwx | exact He | exact Hd | reflexivity | exact Hx].
  - (* jal *)
    destruct (is_x0 rd) eqn:Hx.
    + injection H as <-. eexists. split.
      * eapply steps_step; [eapply j_jal0; [exact Hwx | exact He | exact Hd | exact Hx] | constructor].
      * cbn [Ends]. eauto.
    + destruct (Z.eqb_spec (bv_unsigned rd) 1) as [Er|_]; [|discriminate].
      apply is_x0_one in Er. subst rd.
      injection H as <-. eexists. split.
      * eapply steps_step; [eapply j_jal1; [exact Hwx | exact He | exact Hd | exact Hx | reflexivity] | constructor].
      * cbn [Ends]. do 2 eexists. split; [|split].
        -- f_equal. unfold at_. f_equal. lia.
        -- apply (inv_setr y regs m 1 (mkc (cbase c + (o + sz))) (at_ c (o + sz)) I Hx eq_refl).
           intros _. rewrite eval_mkc. reflexivity.
        -- apply getr_same. discriminate.
  - (* jalr *)
    destruct (is_x0 rd) eqn:Hx.
    + assert (Hk : known (yA y (bv_unsigned rs1)) = true /\ bv_signed imm = 0%Z /\
                     ((r = RRet y /\ yA y (bv_unsigned rs1) = Lin (KSlot 0) 0) \/ r = RIJump (yA y (bv_unsigned rs1)) y)).
      { destruct (yA y (bv_unsigned rs1)) as [b k|n|]; try discriminate.
        destruct b; try discriminate.
        - destruct n as [|p|p]; try discriminate. destruct k as [|p|p]; try discriminate.
          destruct (Z.eqb_spec (bv_signed imm) 0) as [Ei|_]; [|discriminate].
          injection H as <-. split; [reflexivity|]. split; [exact Ei|]. left. auto.
        - destruct k as [|p|p]; try discriminate.
          destruct (Z.eqb_spec (bv_signed imm) 0) as [Ei|_]; [|discriminate].
          injection H as <-. split; [reflexivity|]. split; [exact Ei|]. right. reflexivity. }
      destruct Hk as (Hk & Ei & [(-> & Ea)| ->]).
      * eexists. split.
        -- eapply steps_step; [eapply j_jalr0; [exact Hwx | exact He | exact Hd | exact Hx] | constructor].
        -- cbn [Ends]. do 2 eexists. split; [|exact I].
           rewrite (i_A _ _ _ I rs1 Hk). rewrite Ea, Ei.
           cbn [eval base_val]. rewrite v_addi_0. reflexivity.
      * eexists. split.
        -- eapply steps_step; [eapply j_jalr0; [exact Hwx | exact He | exact Hd | exact Hx] | constructor].
        -- cbn [Ends]. do 2 eexists. split; [|exact I].
           rewrite (i_A _ _ _ I rs1 Hk). rewrite Ei. reflexivity.
    + destruct (Z.eqb_spec (bv_unsigned rd) 1) as [Er|_]; [|discriminate].
      apply is_x0_one in Er. subst rd.
      destruct (yA y (bv_unsigned rs1)) as [b k|n|] eqn:Ea; try discriminate.
      destruct b; try discriminate.
      injection H as <-. eexists. split.
      * eapply steps_step; [eapply j_jalr1; [exact Hwx | exact He | exact Hd | exact Hx | reflexivity] | constructor].
      * cbn [Ends]. do 2 eexists. split; [|split].
        -- rewrite (hold_const y regs m rs1 k I Ea). f_equal.
           apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_bv_unsigned.
        -- apply (inv_setr y regs m 1 (mkc (cbase c + (o + sz))) (at_ c (o + sz)) I Hx eq_refl).
           intros _. rewrite eval_mkc. reflexivity.
        -- apply getr_same. discriminate.
  - (* branch *)
    cbn zeta in H.
    set (a := yA y (bv_unsigned rs1)) in *. set (b := yA y (bv_unsigned rs2)) in *.
    destruct (known a) eqn:Ka; cbn [andb] in H; [|discriminate].
    destruct (known b) eqn:Kb; [|discriminate].
    destruct (run c cell_of st_P f (o + sz) stop (note_room c0 a b y)) as [rest|] eqn:Hr; [|discriminate].
    injection H as <-.
    pose proof (i_A _ _ _ I rs1 Ka) as Ga. pose proof (i_A _ _ _ I rs2 Kb) as Gb.
    destruct (branch_taken c0 (eval e a) (eval e b)) eqn:Ht.
    + eexists. split.
      * eapply steps_step; [eapply j_br_tk; [exact Hwx | exact He | exact Hd | reflexivity | rewrite Ga, Gb; exact Ht] | constructor].
      * cbn [Ends]. left. split; [exact Ht|]. eauto.
    + destruct (IH _ _ _ _ _ _ Hr (inv_note c0 a b y regs m I Ht)) as (ms & Hm & Hn).
      exists ms. split.
      * eapply steps_step; [eapply j_br_ft; [exact Hwx | exact He | exact Hd | reflexivity | rewrite Ga, Gb; exact Ht] | exact Hm].
      * cbn [Ends]. right. split; [exact Ht | exact Hn].
  - (* load *)
    destruct sz0; try discriminate. destruct signed; try discriminate.
    destruct (load' c cell_of st_P y (add_k (yA y (bv_unsigned rs1)) (bv_signed imm))) as [v|] eqn:Hl; [|discriminate].
    destruct (wr_inv _ _ _ _ _ H) as (Hx & Hs & Hr).
    destruct (load_sound y regs m _ v I Hl) as (Kv & Rd).
    pose proof (load_known _ _ _ Hl) as Ka.
    rewrite add_k_sound in Rd by exact Ka.
    rewrite <- (i_A _ _ _ I rs1 (known_add_k _ _ Ka)) in Rd.
    destruct (IH _ _ _ _ _ _ Hr (inv_setr y regs m rd v (eval e v) I Hx Hs (fun _ => eq_refl))) as (ms & Hm & Hn).
    exists ms. split; [|exact Hn]. eapply steps_step; [|exact Hm].
    eapply j_ld; [exact Hwx | exact He | exact Hd | reflexivity | exact Hx | exact Rd].
  - (* store *)
    destruct sz0; try discriminate.
    destruct (store c y (add_k (yA y (bv_unsigned rs1)) (bv_signed imm)) (yA y (bv_unsigned rs2))) as [y'|] eqn:Hl; [|discriminate].
    pose proof (known_store _ _ _ _ Hl) as Ka.
    destruct (store_sound y y' regs m _ _ (getr regs rs2) I Hl (i_A _ _ _ I rs2)) as (_ & Sok & I').
    rewrite add_k_sound in Sok, I' by exact Ka.
    rewrite <- (i_A _ _ _ I rs1 (known_add_k _ _ Ka)) in Sok, I'.
    destruct (IH _ _ _ _ _ _ H I') as (ms & Hm & Hn).
    exists ms. split; [|exact Hn]. eapply steps_step; [|exact Hm].
    eapply j_sd; [exact Hwx | exact He | exact Hd | reflexivity | reflexivity | reflexivity | exact Sok].
  - (* opimm *)
    destruct op; try discriminate.
    + (* add *)
      destruct (wr_inv _ _ _ _ _ H) as (Hx & Hs & Hr).
      assert (Hv : known (add_k (yA y (bv_unsigned rs1)) (bv_signed imm)) = true ->
                   alu64 ALU_ADD (getr regs rs1) (sext 64 imm) = eval e (add_k (yA y (bv_unsigned rs1)) (bv_signed imm))).
      { intros Kk. rewrite add_k_sound by exact Kk.
        rewrite <- (i_A _ _ _ I rs1 (known_add_k _ _ Kk)). apply alu_add_v. }
      destruct (IH _ _ _ _ _ _ Hr (inv_setr y regs m rd _ _ I Hx Hs Hv)) as (ms & Hm & Hn).
      exists ms. split; [|exact Hn]. eapply steps_step; [|exact Hm].
      eapply j_opimm; [exact Hwx | exact He | exact Hd | reflexivity | exact Hx].
    + (* and *)
      destruct (wr_inv _ _ _ _ _ H) as (Hx & Hs & Hr).
      assert (Hv : known (aval_and (yA y (bv_unsigned rs1)) (bv_signed imm)) = true ->
                   alu64 ALU_AND (getr regs rs1) (sext 64 imm) = eval e (aval_and (yA y (bv_unsigned rs1)) (bv_signed imm))).
      { intros Kk. destruct (yA y (bv_unsigned rs1)) as [b k|n|] eqn:Ea; try discriminate.
        destruct b; try discriminate. cbn [aval_and] in *.
        destruct (Z.eqb_spec k (-3)) as [->|_]; [|discriminate].
        destruct (Z.eqb_spec (bv_signed imm) 7) as [Ei|_]; [|discriminate]. cbn [andb eval].
        rewrite (i_A _ _ _ I rs1) by (rewrite Ea; reflexivity). rewrite Ea. cbn [eval base_val].
        assert (Eim : imm = (7 : bv 12)) by (apply bv_eq_signed; rewrite Ei; reflexivity).
        rewrite Eim. reflexivity. }
      destruct (IH _ _ _ _ _ _ Hr (inv_setr y regs m rd _ _ I Hx Hs Hv)) as (ms & Hm & Hn).
      exists ms. split; [|exact Hn]. eapply steps_step; [|exact Hm].
      eapply j_opimm; [exact Hwx | exact He | exact Hd | reflexivity | exact Hx].
  - (* shift *)
    destruct op; try discriminate.
    destruct (wr_inv _ _ _ _ _ H) as (Hx & Hs & Hr).
    assert (Hv : known (const_op (fun x => alu64 ALU_SLL x (zext 64 shamt)) (yA y (bv_unsigned rs1))) = true ->
                 alu64 ALU_SLL (getr regs rs1) (zext 64 shamt) =
                 eval e (const_op (fun x => alu64 ALU_SLL x (zext 64 shamt)) (yA y (bv_unsigned rs1)))).
    { intros Kk. destruct (yA y (bv_unsigned rs1)) as [b k|n|] eqn:Ea; try discriminate.
      destruct b; try discriminate. cbn [const_op]. rewrite eval_u.
      rewrite (hold_const y regs m rs1 k I Ea). reflexivity. }
    destruct (IH _ _ _ _ _ _ Hr (inv_setr y regs m rd _ _ I Hx Hs Hv)) as (ms & Hm & Hn).
    exists ms. split; [|exact Hn]. eapply steps_step; [|exact Hm].
    eapply j_shift; [exact Hwx | exact He | exact Hd | reflexivity | exact Hx].
  - (* op *)
    destruct op; try discriminate.
    + (* add *)
      destruct (wr_inv _ _ _ _ _ H) as (Hx & Hs & Hr).
      assert (Hv : known (aval_add (yA y (bv_unsigned rs1)) (yA y (bv_unsigned rs2))) = true ->
                   alu64 ALU_ADD (getr regs rs1) (getr regs rs2) =
                   eval e (aval_add (yA y (bv_unsigned rs1)) (yA y (bv_unsigned rs2)))).
      { intros Kk. apply aval_add_sound; [exact Kk | apply (i_A _ _ _ I) | apply (i_A _ _ _ I)]. }
      destruct (IH _ _ _ _ _ _ Hr (inv_setr y regs m rd _ _ I Hx Hs Hv)) as (ms & Hm & Hn).
      exists ms. split; [|exact Hn]. eapply steps_step; [|exact Hm].
      eapply j_op; [exact Hwx | exact He | exact Hd | reflexivity | exact Hx].
    + (* xor *)
      destruct (wr_inv _ _ _ _ _ H) as (Hx & Hs & Hr).
      assert (Hv : known (aval_xor (yA y (bv_unsigned rs1)) (yA y (bv_unsigned rs2))) = true ->
                   alu64 ALU_XOR (getr regs rs1) (getr regs rs2) =
                   eval e (aval_xor (yA y (bv_unsigned rs1)) (yA y (bv_unsigned rs2)))).
      { intros Kk. destruct (yA y (bv_unsigned rs1)) as [b k|n|] eqn:Ea; try discriminate.
        destruct b; try discriminate.
        destruct (yA y (bv_unsigned rs2)) as [b2 k2|n2|] eqn:Eb; try discriminate.
        destruct b2; try discriminate. cbn [aval_xor]. rewrite eval_u.
        rewrite (hold_const y regs m rs1 k I Ea), (hold_const y regs m rs2 k2 I Eb). reflexivity. }
      destruct (IH _ _ _ _ _ _ Hr (inv_setr y regs m rd _ _ I Hx Hs Hv)) as (ms & Hm & Hn).
      exists ms. split; [|exact Hn]. eapply steps_step; [|exact Hm].
      eapply j_op; [exact Hwx | exact He | exact Hd | reflexivity | exact Hx].
Qed.

End Block.
