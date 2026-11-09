(* Shen/JIT Phase 1: basic metatheory of the bytecode semantics. These are theorems
   about the model in JitBytecode.v only; they say nothing about the binary. *)
From Coq Require Import List ZArith NArith PArith Bool Lia String.
From Buri Require Import JitFloat JitBytecode.
Import ListNotations.
Module JitMeta.
Import JitBytecode.JitBytecode.
Local Open Scope string_scope.

(* The transition relation the semantics defines: internal steps, and IO steps that
   take the environment's response as an input. *)
Inductive step (E : env) (pt : tree (prim * nat)) : machine -> option (jreq * jres) -> machine -> Prop :=
 | StepTau : forall m m', next E pt m = MTau m' -> step E pt m None m'
 | StepIO : forall m q k r, next E pt m = MIO q k -> step E pt m (Some (q, r)) (k r).

Definition final_in (E : env) (pt : tree (prim * nat)) (m : machine) (o : final) : Prop :=
 exists m', next E pt m = MFinal o m'.
Definition stuck_in (E : env) (pt : tree (prim * nat)) (m : machine) (w : stuck) : Prop :=
 next E pt m = MStuck w.

(* Determinism: an internal step has one result, and an IO step has one request and,
   for each response, one result. *)
Theorem step_deterministic_tau : forall E pt m m1 m2,
 step E pt m None m1 -> step E pt m None m2 -> m1 = m2.
Proof.
 intros E pt m m1 m2 H1 H2. inversion H1; subst. inversion H2; subst. congruence.
Qed.

Theorem step_deterministic_io : forall E pt m q1 q2 r1 r2 m1 m2,
 step E pt m (Some (q1, r1)) m1 -> step E pt m (Some (q2, r2)) m2 -> q1 = q2 /\ (r1 = r2 -> m1 = m2).
Proof.
 intros E pt m q1 q2 r1 r2 m1 m2 H1 H2.
 inversion H1; subst. inversion H2; subst.
 match goal with H : next _ _ _ = MIO _ _, H' : next _ _ _ = MIO _ _ |- _ =>
   rewrite H in H'; inversion H'; subst end.
 split; [reflexivity | intro; subst; reflexivity].
Qed.

Theorem step_tau_excludes_io : forall E pt m m1 q r m2,
 step E pt m None m1 -> step E pt m (Some (q, r)) m2 -> False.
Proof.
 intros E pt m m1 q r m2 H1 H2. inversion H1; subst. inversion H2; subst. congruence.
Qed.

(* Explicit stuck classification: every state has exactly one kind of move. There is no
   fifth case, and each stuck state names its reason. *)
Theorem move_classification : forall E pt m,
 (exists m', next E pt m = MTau m') \/
 (exists q k, next E pt m = MIO q k) \/
 (exists o m', next E pt m = MFinal o m') \/
 (exists w, next E pt m = MStuck w).
Proof.
 intros E pt m. destruct (next E pt m) eqn:H; eauto 6.
Qed.

Theorem final_not_stuck : forall E pt m o w, final_in E pt m o -> stuck_in E pt m w -> False.
Proof. unfold final_in, stuck_in. intros E pt m o w [m' H] H'. congruence. Qed.

Theorem step_not_stuck : forall E pt m l m' w, step E pt m l m' -> stuck_in E pt m w -> False.
Proof.
 unfold stuck_in. intros E pt m l m' w H H'. inversion H; subst; congruence.
Qed.

Theorem final_unique : forall E pt m o1 o2, final_in E pt m o1 -> final_in E pt m o2 -> o1 = o2.
Proof. unfold final_in. intros E pt m o1 o2 [a A] [b B]. congruence. Qed.

(* Excluded primitives stop the machine with a named reason, whatever their operands:
   they cannot silently take a meaning in the named build. *)
Theorem excluded_prims_stuck : forall E pt m d p args,
 is_excluded p = true -> prim_step E pt m d p args = MStuck (RExcluded p).
Proof.
 intros E pt m d p args H.
 destruct p; try discriminate H; destruct args as [|a [|b [|c args]]]; reflexivity.
Qed.

(* Fetching falls off only at the end of the instruction list. *)
Theorem next_empty_rest : forall E pt m, m_rest m = [] -> next E pt m = MStuck RFallOff.
Proof. intros E pt m H. unfold next. rewrite H. reflexivity. Qed.

(* Maps: the lookup laws the machine relies on. *)
Theorem tget_tset_same : forall A (k : positive) (x : A) m, tget k (tset k x m) = Some x.
Proof.
 intros A k. induction k; intros x m; destruct m; cbn; try apply IHk; reflexivity.
Qed.

Lemma tget_leaf : forall A (k : positive), tget k (@Leaf A) = None.
Proof. intros; destruct k; reflexivity. Qed.

Theorem tget_tset_other : forall A (k j : positive) (x : A) m,
 k <> j -> tget k (tset j x m) = tget k m.
Proof.
 intros A k. induction k; intros j x m Hne; destruct j; destruct m; cbn;
  rewrite ?tget_leaf; try reflexivity;
  try (apply IHk; congruence);
  try (rewrite IHk by congruence; rewrite ?tget_leaf; reflexivity);
  try congruence.
Qed.

(* A step of `move` does what the table says. *)
Theorem move_writes : forall E pt m d s v r,
 m_rest m = IMove d s :: r -> sread (set_rest m r) s = Some v ->
 exists m', next E pt m = MTau m' /\ m_rest m' = r /\
   tget (skey (m_fp m + d)) (m_stack m') = Some v.
Proof.
 intros E pt m d s v r Hr Hs.
 unfold next. rewrite Hr. cbv zeta. rewrite Hs.
 eexists. split; [reflexivity|]. split; [reflexivity|].
 cbn. unfold swrite. cbn. apply tget_tset_same.
Qed.

(* jump-if-false on a value that is not a Boolean raises: it never branches. *)
Theorem jump_if_false_requires_boolean : forall E pt m o l r v,
 m_rest m = IJumpIfFalse o l :: r ->
 read_op (set_rest m r) o = Some v ->
 (forall b, v <> VBool b) ->
 next E pt m = raise_v (set_rest m r) "~S is not a boolean" v.
Proof.
 intros E pt m o l r v Hr Hop Hb.
 unfold next. rewrite Hr. cbv zeta. rewrite Hop.
 destruct v; try reflexivity. exfalso. eapply Hb; reflexivity.
Qed.

(* A return with no continuation ends the run with that value. *)
Theorem return_at_top : forall m v, m_conts m = [] -> do_return m v = MFinal (FReturn v) m.
Proof. intros m v H. unfold do_return. rewrite H. reflexivity. Qed.

(* Raising with no handler ends the run with an error; with a handler, the run goes on. *)
Theorem raise_no_handler_final : forall m msg v,
 m_handlers m = [] -> exists e m', raise m msg v = MFinal (FError e) m'.
Proof.
 intros m msg v H. unfold raise. rewrite H. cbn. eauto.
Qed.

(* Sealing: installing a definition of a sealed name raises and leaves the bindings. *)
Theorem install_sealed_refused : forall pt m d name c,
 tget name (m_sealed m) = Some tt ->
 install pt m d (VPair (VSym S_defun) (VPair (VSym name) (VPair c VNil))) =
   raise_v m "~S is sealed and cannot be redefined" (VSym name).
Proof.
 intros pt m d name c H. unfold install. cbn [vlist option_map].
 rewrite Pos.eqb_refl. rewrite H. reflexivity.
Qed.

(* 0.6: shen-jit.write-bytes asks the environment to write the buffer's bytes from I, all N of them
   in one request, and returns N; a failed write raises (to a handler, or ends the run, as raise_s
   says; the machine the continuation gives is then the raise's). *)
Theorem write_bytes_io : forall E pt m d l i n ls h,
 tget ls (m_heap m) = Some (OStream h SOut true) ->
 (0 <= i)%Z -> (0 < n)%Z -> (i + n <= Z.of_nat (List.length (bytes_of m l)))%Z ->
 exists k, prim_step E pt m d PWriteBytes [VBytes l; VFix i; VFix n; VStream ls] =
   MIO (JWrites h (firstn (Z.to_nat n) (skipn (Z.to_nat i) (bytes_of m l)))) k /\
   k JDone = set_stack m (swrite m d (VFix n)) /\
   k JFailed = match raise_s m "shen-jit.write-bytes: the write failed" with MTau m' => m' | _ => m end.
Proof.
 intros E pt m d l i n ls h Hs Hi Hn Hl. cbn [prim_step].
 replace (orb (orb (Z.ltb i 0) (Z.ltb n 0)) (Z.ltb (Z.of_nat (List.length (bytes_of m l))) (i + n))) with false
   by (symmetry; repeat rewrite Bool.orb_false_iff; repeat split; apply Z.ltb_ge; lia).
 rewrite Hs. replace (Z.eqb n 0) with false by (symmetry; apply Z.eqb_neq; lia).
 eexists. split; [reflexivity|]. split; reflexivity.
Qed.

(* Writing no bytes asks nothing of the environment. *)
Theorem write_bytes_empty : forall E pt m d l i ls h,
 tget ls (m_heap m) = Some (OStream h SOut true) ->
 (0 <= i <= Z.of_nat (List.length (bytes_of m l)))%Z ->
 prim_step E pt m d PWriteBytes [VBytes l; VFix i; VFix 0; VStream ls] = ret_to m d (VFix 0).
Proof.
 intros E pt m d l i ls h Hs Hi. cbn [prim_step].
 replace (orb (orb (Z.ltb i 0) (Z.ltb 0 0)) (Z.ltb (Z.of_nat (List.length (bytes_of m l))) (i + 0))) with false
   by (symmetry; repeat rewrite Bool.orb_false_iff; repeat split; apply Z.ltb_ge; lia).
 rewrite Hs. reflexivity.
Qed.

(* 0.6: a read error in read-byte raises, where end of file gives -1. *)
Theorem read_byte_error_raises : forall E pt m d ls h,
 tget ls (m_heap m) = Some (OStream h SIn true) ->
 exists k, prim_step E pt m d PReadByte [VStream ls] = MIO (JRead h) k /\
   k JEof = set_stack m (swrite m d (VFix (-1))) /\
   k JReadFailed = match raise_s m "read-byte: the read failed" with MTau m' => m' | _ => m end.
Proof.
 intros E pt m d ls h Hs. cbn [prim_step]. rewrite Hs.
 eexists. split; [reflexivity|]. split; reflexivity.
Qed.

(* 0.6: n->string makes the UTF-8 bytes of a scalar value past a byte. *)
Theorem n_to_string_utf8 : forall E pt m d,
 prim_step E pt m d PNString [VFix 255] = ret_to m d (VStr [255%N]) /\
 prim_step E pt m d PNString [VFix 955] = ret_to m d (VStr [206%N; 187%N]) /\
 prim_step E pt m d PNString [VFix 128512] = ret_to m d (VStr [240%N; 159%N; 152%N; 128%N]) /\
 prim_step E pt m d PNString [VFix 55296] =
   raise_v m "n->string: ~S is not a byte or a Unicode scalar value" (VFix 55296).
Proof. intros. repeat split; reflexivity. Qed.

End JitMeta.
