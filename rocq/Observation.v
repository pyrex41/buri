(* E2E-04: common observation vocabulary, maximal behaviors and behavior
   refinement. Internal steps are the only unobservable transitions. Program
   resource failure, structured errors, environment events and evaluator budget
   exhaustion are distinct constructors; no later layer can merge them by
   choosing a smaller vocabulary, because refinement is defined over this one. *)
From Coq Require Import List ZArith NArith.
Import ListNotations.
Module Observation.

(* Text is a sequence of Unicode scalar values (code points), not bytes. *)
Definition text := list N.
(* Bytes are naturals; well-formed bytes are below 256 (see byte_ok). *)
Definition byte := N.
Definition byte_ok (b : byte) := (b < 256)%N.

Inductive direction := DIn | DOut.
Inductive io_error :=
 | ENoEntity | EPermission | EBadHandle | ENoSpace | EClosed
 | EShortWrite           (* a write that transferred fewer bytes than requested *)
 | EProtocol             (* the environment answered with an ill-typed response *)
 | EOther (code : N).

(* A program request and the environment's response form one IO event.
   Partial reads return fewer bytes than requested; partial writes report a
   count below the request length; failures carry an explicit error. *)
Inductive request :=
 | QOpen (path : text) (d : direction)
 | QClose (h : N)
 | QRead (h : N) (max : N)
 | QWrite (h : N) (bytes : list byte)
 | QTime (clock : text)
 | QRandom (bound : N).
Inductive response :=
 | ROpened (h : N) | RClosed
 | RRead (bytes : list byte) | REof
 | RWrote (count : N)
 | RFailed (e : io_error)
 | RTime (t : Z) | RRandom (n : N).

Inductive signal := SigInt | SigTerm | SigKill | SigHup | SigOther (n : N).
(* Environment-initiated events: they are labels, never program results. *)
Inductive env_event := Signal (s : signal) | Cancel.

Inductive event := EvIO (q : request) (r : response) | EvEnv (e : env_event).
Inductive label := Tau | Obs (e : event).
Definition trace := list event.
Definition trace_of (l : label) : trace := match l with Tau => [] | Obs e => [e] end.

(* Failed or partial writes are an observable class of events. *)
Definition write_failed (e : event) := match e with
 | EvIO (QWrite _ bs) (RFailed _) => True
 | EvIO (QWrite _ bs) (RWrote n) => (n < N.of_nat (length bs))%N
 | _ => False end.

Inductive resource := RHeap | RStack.
(* Terminal program outcomes, parametric in values V and error payloads X. *)
Inductive outcome (V X : Type) :=
 | Normal (v : V)
 | Error (x : X)
 | ResourceOut (r : resource)
 | Exit (code : Z)
 | Killed (s : signal)
 | Cancelled.
Arguments Normal {V X} v. Arguments Error {V X} x. Arguments ResourceOut {V X} r.
Arguments Exit {V X} code. Arguments Killed {V X} s. Arguments Cancelled {V X}.

CoInductive stream := SCons (e : event) (rest : stream).
Fixpoint prepend (t : trace) (s : stream) : stream :=
 match t with [] => s | e :: t => SCons e (prepend t s) end.

(* Maximal behaviors. Diverges t: after trace t the program performs infinitely
   many internal steps and no further observation. Reacts: infinitely many
   observations. GoesWrong: an explicit undefined/stuck state was reached. *)
Inductive behavior (V X : Type) :=
 | Terminates (t : trace) (o : outcome V X)
 | Diverges (t : trace)
 | Reacts (s : stream)
 | GoesWrong (t : trace).
Arguments Terminates {V X} t o. Arguments Diverges {V X} t.
Arguments Reacts {V X} s. Arguments GoesWrong {V X} t.

Inductive in_stream (e : event) : stream -> Prop :=
 | in_here s : in_stream e (SCons e s)
 | in_later e' s : in_stream e s -> in_stream e (SCons e' s).

Definition occurs {V X} (e : event) (b : behavior V X) : Prop := match b with
 | Terminates t _ | Diverges t | GoesWrong t => In e t
 | Reacts s => in_stream e s end.

Inductive prefix_of {V X} (t : trace) : behavior V X -> Prop :=
 | pre_term u o : prefix_of t (Terminates (t ++ u) o)
 | pre_div u : prefix_of t (Diverges (t ++ u))
 | pre_wrong u : prefix_of t (GoesWrong (t ++ u))
 | pre_react s : prefix_of t (Reacts (prepend t s)).

CoInductive stream_bisim : stream -> stream -> Prop :=
 | bisim_cons e s1 s2 : stream_bisim s1 s2 -> stream_bisim (SCons e s1) (SCons e s2).

(* Analysis verdicts are produced by evaluators/checkers, not by programs.
   VExhausted is evaluator or proof-search budget exhaustion: it is never a
   program behavior, and is distinct from Unknown, Unsupported and Rejected. *)
Inductive verdict (V X : Type) :=
 | VDone (t : trace) (o : outcome V X)
 | VWrong (t : trace)
 | VExhausted (t : trace)
 | VUnknown | VUnsupported | VRejected.
Arguments VDone {V X} t o. Arguments VWrong {V X} t. Arguments VExhausted {V X} t.
Arguments VUnknown {V X}. Arguments VUnsupported {V X}. Arguments VRejected {V X}.

(* What each verdict licenses about a behavior set B. Exhaustion only says that
   some behavior extends the trace already observed. *)
Definition verdict_sound {V X} (B : behavior V X -> Prop) (r : verdict V X) : Prop :=
 match r with
 | VDone t o => B (Terminates t o)
 | VWrong t => B (GoesWrong t)
 | VExhausted t => exists b, B b /\ prefix_of t b
 | VUnknown | VUnsupported | VRejected => True end.

Section Refinement.
Variables (V1 X1 V2 X2 : Type) (RV : V1 -> V2 -> Prop) (RX : X1 -> X2 -> Prop).

Inductive outcome_match : outcome V1 X1 -> outcome V2 X2 -> Prop :=
 | om_normal v w : RV v w -> outcome_match (Normal v) (Normal w)
 | om_error x y : RX x y -> outcome_match (Error x) (Error y)
 | om_resource r : outcome_match (ResourceOut r) (ResourceOut r)
 | om_exit c : outcome_match (Exit c) (Exit c)
 | om_killed s : outcome_match (Killed s) (Killed s)
 | om_cancel : outcome_match Cancelled Cancelled.

(* Strict refinement: identical observable traces, related outcomes. *)
Inductive refines : behavior V1 X1 -> behavior V2 X2 -> Prop :=
 | ref_term t o1 o2 : outcome_match o1 o2 -> refines (Terminates t o1) (Terminates t o2)
 | ref_div t : refines (Diverges t) (Diverges t)
 | ref_react s1 s2 : stream_bisim s1 s2 -> refines (Reacts s1) (Reacts s2)
 | ref_wrong t : refines (GoesWrong t) (GoesWrong t).

(* Resource-relaxed refinement: additionally a target may stop with a named
   program resource failure after a prefix of a source behavior. This is the
   only permitted early stop and it is itself observable. *)
Inductive refines_res : behavior V1 X1 -> behavior V2 X2 -> Prop :=
 | rr_strict b1 b2 : refines b1 b2 -> refines_res b1 b2
 | rr_resource t r b2 : prefix_of t b2 -> refines_res (Terminates t (ResourceOut r)) b2.

Definition program_refines (T : behavior V1 X1 -> Prop) (S : behavior V2 X2 -> Prop) :=
 forall b, T b -> exists b', S b' /\ refines b b'.
Definition program_refines_res (T : behavior V1 X1 -> Prop) (S : behavior V2 X2 -> Prop) :=
 forall b, T b -> exists b', S b' /\ refines_res b b'.
End Refinement.
Arguments outcome_match {V1 X1 V2 X2} RV RX.
Arguments refines {V1 X1 V2 X2} RV RX.
Arguments refines_res {V1 X1 V2 X2} RV RX.
Arguments program_refines {V1 X1 V2 X2} RV RX.
Arguments program_refines_res {V1 X1 V2 X2} RV RX.

Lemma bisim_in_stream : forall e s1 s2, stream_bisim s1 s2 -> in_stream e s1 -> in_stream e s2.
Proof.
 intros e s1 s2 B I; revert s2 B; induction I; intros s2 B; inversion B; subst.
 - constructor.
 - constructor; apply IHI; assumption.
Qed.

Lemma in_prepend : forall e t s, In e t -> in_stream e (prepend t s).
Proof.
 intros e t s; induction t as [|a t IH]; cbn; intros H; [contradiction|].
 destruct H as [H|H]; [subst; constructor|constructor; apply IH; exact H].
Qed.

Lemma prefix_occurs : forall V X e t (b : behavior V X), prefix_of t b -> In e t -> occurs e b.
Proof.
 intros V X e t b P I; destruct P; cbn; try (apply in_or_app; left; exact I).
 apply in_prepend; exact I.
Qed.

Section Lemmas.
Variables (V1 X1 V2 X2 : Type) (RV : V1 -> V2 -> Prop) (RX : X1 -> X2 -> Prop).

Lemma refines_occurs : forall b1 b2 e, refines RV RX b1 b2 -> occurs e b1 -> occurs e b2.
Proof.
 intros b1 b2 e R O; destruct R; cbn in *; auto.
 eapply bisim_in_stream; eauto.
Qed.

Lemma refines_res_occurs : forall b1 b2 e, refines_res RV RX b1 b2 -> occurs e b1 -> occurs e b2.
Proof.
 intros b1 b2 e R O; destruct R.
 - eapply refines_occurs; eauto.
 - eapply prefix_occurs; eauto.
Qed.

(* Refinement cannot hide a source-visible error: a target error is matched by
   a source error with related payload after the identical trace. *)
Theorem refinement_preserves_errors : forall T S t x,
 program_refines RV RX T S -> T (Terminates t (Error x)) ->
 exists y, S (Terminates t (Error y)) /\ RX x y.
Proof.
 intros T S t x R H; destruct (R _ H) as [b [Sb Rb]].
 inversion Rb; subst. inversion H3; subst. eauto.
Qed.

Theorem refinement_preserves_errors_res : forall T S t x,
 program_refines_res RV RX T S -> T (Terminates t (Error x)) ->
 exists y, S (Terminates t (Error y)) /\ RX x y.
Proof.
 intros T S t x R H; destruct (R _ H) as [b [Sb Rb]].
 inversion Rb; subst. inversion H0; subst. inversion H4; subst. eauto.
Qed.

(* Every target observation, in particular every failed or partial write,
   also occurs in a refined source behavior. *)
Theorem refinement_preserves_events : forall T S b e,
 program_refines_res RV RX T S -> T b -> occurs e b ->
 exists b', S b' /\ occurs e b'.
Proof.
 intros T S b e R H O; destruct (R _ H) as [b' [Sb Rb]].
 exists b'; split; [exact Sb|]. eapply refines_res_occurs; eauto.
Qed.

Corollary refinement_preserves_failed_writes : forall T S b e,
 program_refines_res RV RX T S -> T b -> occurs e b -> write_failed e ->
 exists b', S b' /\ occurs e b' /\ write_failed e.
Proof.
 intros T S b e R H O W; destruct (refinement_preserves_events T S b e R H O) as [b' [Sb Ob]].
 eauto.
Qed.

(* A silent internal loop is not related to any terminating, reacting or
   wrong behavior, even under resource-relaxed refinement. *)
Theorem divergence_not_hidden : forall t b2,
 refines_res RV RX (Diverges t) b2 -> b2 = Diverges t.
Proof. intros t b2 R; inversion R; subst; inversion H; reflexivity. Qed.

Theorem diverging_target_needs_diverging_source : forall T S t,
 program_refines_res RV RX T S -> T (Diverges t) -> S (Diverges t).
Proof.
 intros T S t R H; destruct (R _ H) as [b [Sb Rb]].
 rewrite <- (divergence_not_hidden t b Rb); exact Sb.
Qed.

Definition all_terminate {V X} (S : behavior V X -> Prop) :=
 forall b, S b -> exists t o, b = Terminates t o.

Corollary terminating_source_forbids_divergence : forall T S t,
 program_refines_res RV RX T S -> all_terminate S -> ~ T (Diverges t).
Proof.
 intros T S t R A H. destruct (A _ (diverging_target_needs_diverging_source T S t R H)) as [u [o E]].
 discriminate.
Qed.

(* Strict refinement also cannot introduce a resource failure. *)
Theorem strict_refinement_preserves_resource_failure : forall T S t r,
 program_refines RV RX T S -> T (Terminates t (ResourceOut r)) ->
 S (Terminates t (ResourceOut r)).
Proof.
 intros T S t r R H; destruct (R _ H) as [b [Sb Rb]].
 inversion Rb; subst; inversion H3; subst; exact Sb.
Qed.
End Lemmas.

(* Verdict soundness: budget exhaustion never asserts divergence. Given any
   behavior set with a behavior extending t, VExhausted t is sound, whatever
   that behavior is: termination, divergence, reaction or going wrong. *)
Theorem exhaustion_claims_only_prefix : forall V X (B : behavior V X -> Prop) t b,
 B b -> prefix_of t b -> verdict_sound B (VExhausted t).
Proof. intros; cbn; eauto. Qed.

(* Generic labeled transition systems and their maximal behaviors. *)
Section LTS.
Variables (S V X : Type) (step : S -> label -> S -> Prop) (final : S -> outcome V X -> Prop).

Inductive star : S -> trace -> S -> Prop :=
 | star_refl s : star s [] s
 | star_step s l s' t s'' : step s l s' -> star s' t s'' -> star s (trace_of l ++ t) s''.

CoInductive silent_forever : S -> Prop :=
 | sf_step s s' : step s Tau s' -> silent_forever s' -> silent_forever s.

CoInductive reacts_forever : S -> stream -> Prop :=
 | rf_step s t s' T : star s t s' -> t <> [] -> reacts_forever s' T -> reacts_forever s (prepend t T).

Definition stuck (s : S) := (forall l s', ~ step s l s') /\ (forall o, ~ final s o).

Inductive behaves (s : S) : behavior V X -> Prop :=
 | beh_term t s' o : star s t s' -> final s' o -> behaves s (Terminates t o)
 | beh_div t s' : star s t s' -> silent_forever s' -> behaves s (Diverges t)
 | beh_react T : reacts_forever s T -> behaves s (Reacts T)
 | beh_wrong t s' : star s t s' -> stuck s' -> behaves s (GoesWrong t).

(* Closed deterministic systems: one successor and no step from final states. *)
Definition deterministic := forall s l1 s1 l2 s2,
 step s l1 s1 -> step s l2 s2 -> l1 = l2 /\ s1 = s2.
Definition final_inert := forall s o l s', final s o -> ~ step s l s'.
Definition final_unique := forall s o1 o2, final s o1 -> final s o2 -> o1 = o2.

Lemma star_trans : forall a t b u c, star a t b -> star b u c -> star a (t ++ u) c.
Proof.
 intros a t b u c H; revert u c; induction H; intros u c K; [exact K|].
 rewrite <- app_assoc; econstructor; eauto.
Qed.

Section Det.
Hypotheses (D : deterministic) (FI : final_inert) (FU : final_unique).

Lemma silent_forever_inert : forall s o, silent_forever s -> ~ final s o.
Proof. intros s o H F; destruct H as [s s' St _]; exact (FI _ _ _ _ F St). Qed.

Lemma silent_forever_stuck : forall s, silent_forever s -> ~ stuck s.
Proof. intros s H [N _]; destruct H as [s s' St _]; exact (N _ _ St). Qed.

Lemma silent_forever_unique_step : forall s l s', silent_forever s -> step s l s' ->
 l = Tau /\ silent_forever s'.
Proof.
 intros s l s' H St; destruct H as [s s1 St1 H1].
 destruct (D _ _ _ _ _ St St1) as [E1 E2]; subst; auto.
Qed.

Lemma silent_forever_star : forall s t s', silent_forever s -> star s t s' ->
 t = [] /\ silent_forever s'.
Proof.
 intros s t s' H St; induction St; [auto|].
 destruct (silent_forever_unique_step _ _ _ H H0) as [E H1]; subst.
 destruct (IHSt H1) as [E2 H2]; subst; auto.
Qed.

(* Determinism makes termination exclusive with divergence. A program can be
   given only one maximal behavior class; an internal loop cannot be reported
   as termination and vice versa. *)
Lemma star_final_after_silent : forall s t s' o t' s'',
 star s t s' -> final s' o -> star s t' s'' -> silent_forever s'' -> False.
Proof.
 intros s t s' o t' s'' A; revert t' s''; induction A as [s|s l s1 t s2 St A IH];
   intros t' s'' F B SF.
 - inversion B; subst.
   + exact (silent_forever_inert _ _ SF F).
   + exact (FI _ _ _ _ F H).
 - inversion B; subst.
   + destruct (silent_forever_star _ _ _ SF (star_step _ _ _ _ _ St A)) as [_ H].
     exact (silent_forever_inert _ _ H F).
   + destruct (D _ _ _ _ _ St H) as [E1 E2]; subst. eapply IH; eauto.
Qed.

Lemma star_halt_after_silent : forall s t s', star s t s' -> (forall l s2, ~ step s' l s2) ->
 forall t' s'', star s t' s'' -> silent_forever s'' -> False.
Proof.
 intros s t s' A N; induction A as [s|s l s1 t s2 St A IH]; intros t' s'' B SF.
 - inversion B; subst.
   + destruct SF as [x y St SF]; exact (N _ _ St).
   + exact (N _ _ H).
 - inversion B; subst.
   + destruct (silent_forever_star _ _ _ SF (star_step _ _ _ _ _ St A)) as [_ H].
     destruct H as [x y St2 _]; exact (N _ _ St2).
   + destruct (D _ _ _ _ _ St H) as [E1 E2]; subst. eapply IH; eauto.
Qed.

Theorem wrong_excludes_divergence : forall s t t',
 behaves s (GoesWrong t) -> ~ behaves s (Diverges t').
Proof.
 intros s t t' H K.
 inversion H as [| | |t0 s1 A [N _]]; subst; inversion K as [|t1 s2 B SF| |]; subst.
 exact (star_halt_after_silent s t s1 A N t' s2 B SF).
Qed.

Theorem terminates_excludes_divergence : forall s t o t',
 behaves s (Terminates t o) -> ~ behaves s (Diverges t').
Proof.
 intros s t o t' H K.
 inversion H as [t0 s1 o0 A F| | |]; subst; inversion K as [|t1 s2 B SF| |]; subst.
 exact (star_final_after_silent s t s1 o t' s2 A F B SF).
Qed.

Lemma star_det_final : forall s t1 s1 o1 t2 s2 o2,
 star s t1 s1 -> final s1 o1 -> star s t2 s2 -> final s2 o2 -> t1 = t2 /\ o1 = o2.
Proof.
 intros s t1 s1 o1 t2 s2 o2 A; revert t2 s2; induction A as [s|s l s' t s'' St A IH];
   intros t2 s2 F B G.
 - inversion B; subst; [split; [reflexivity|eapply FU; eauto]|].
   exfalso; exact (FI _ _ _ _ F H).
 - inversion B; subst; [exfalso; exact (FI _ _ _ _ G St)|].
   destruct (D _ _ _ _ _ St H) as [E1 E2]; subst.
   destruct (IH _ _ F H0 G) as [E3 E4]; subst; auto.
Qed.

Theorem terminates_unique : forall s t1 o1 t2 o2,
 behaves s (Terminates t1 o1) -> behaves s (Terminates t2 o2) -> t1 = t2 /\ o1 = o2.
Proof.
 intros s t1 o1 t2 o2 H K.
 inversion H as [t0 s1 o0 A F| | |]; subst; inversion K as [t3 s2 o3 B G| | |]; subst.
 exact (star_det_final s t1 s1 o1 t2 s2 o2 A F B G).
Qed.
End Det.
End LTS.
Arguments star {S} step.
Arguments silent_forever {S} step.
Arguments reacts_forever {S} step.
Arguments stuck {S V X} step final.
Arguments behaves {S V X} step final.
Arguments deterministic {S} step.
Arguments final_inert {S V X} step final.
Arguments final_unique {S V X} final.
End Observation.
