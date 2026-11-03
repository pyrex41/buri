(* E2E-20 Wave D: a sequential register-state reading of the model's
   instruction monad, proved equivalent to coq-sail's own trace semantics.

   NOT a scripts/prove module (toolchain: docs/ARM-FOUNDATION.md section 12;
   checked by scripts/check-arm.sh Part B).

   coq-sail gives an iMon tree its meaning by Interface.iTrace_match: a
   trace is a list of events, and a register read event may carry ANY value.
   A single-threaded register file is the special case in which every read
   returns the value last written.  `seq_ok rs evs rs'` says that the event
   list evs is consistent with that reading, starting from the model's own
   register record `regstate` rs and ending in rs'.  `sexec rs m rs' a` is the
   same thing as an inductive relation over the tree m.

   sexec_sound / sexec_complete: sexec rs m rs' a holds IFF some trace evs
   with no Choose events (coq-sail's pure_iTrace_aux) matches m with result
   inl a and is seq_ok from rs to rs'.  So a theorem stated with sexec is a
   theorem about iTrace_match, restricted only by the single-threaded
   register-file premise.  Events other than register reads/writes and Choose
   (memory, barriers, exceptions as ExtraOutcome, ...) are allowed and carry
   any answer, exactly as in iTrace_match; they leave the register record
   unchanged.

   Everything here is closed under the global context. *)
Require Import SailStdpp.Base.
Require Import armv9_types armv9.
Import Defs.
Open Scope Z.

Notation Ev := (Interface.iEvent (fun _ : Type => exception)).
Notation Mon A := (Interface.iMon (fun _ : Type => exception) A).

(* Neither a register access nor a Choose (and not a terminating outcome). *)
Definition other_oc {T} (oc : @Interface.outcome (fun _ : Type => exception) T) : bool :=
  match oc with
  | Interface.RegRead _ _ | Interface.RegWrite _ _ _ | Interface.Choose _
  | Interface.GenericFail _ | Interface.Discard => false
  | _ => true
  end.

Fixpoint seq_ok (rs : regstate) (evs : list Ev) (rs' : regstate) : Prop :=
  match evs with
  | nil => rs' = rs
  | cons (Interface.IEvent oc v) tl =>
      match oc in @Interface.outcome _ T return T -> Prop with
      | Interface.RegRead r _ => fun v => register_lookup r rs = v /\ seq_ok rs tl rs'
      | Interface.RegWrite r _ x => fun _ => seq_ok (register_set r x rs) tl rs'
      | _ => fun _ => seq_ok rs tl rs'
      end v
  end.

Inductive sexec {A} : regstate -> Mon A -> regstate -> A -> Prop :=
| SRet rs a : sexec rs (Interface.Ret a) rs a
| SRead rs T (r : register T) ak k rs' a :
    sexec rs (k (register_lookup r rs)) rs' a ->
    sexec rs (Interface.Next (Interface.RegRead r ak) k) rs' a
| SWrite rs T (r : register T) ak (x : T) k rs' a :
    sexec (register_set r x rs) (k tt) rs' a ->
    sexec rs (Interface.Next (Interface.RegWrite r ak x) k) rs' a
| SChoose rs ty k (v : choose_type ty) rs' a :
    sexec rs (k v) rs' a -> sexec rs (Interface.Next (Interface.Choose ty) k) rs' a
| SOther rs T (oc : @Interface.outcome (fun _ : Type => exception) T) (v : T) k rs' a :
    other_oc oc = true -> sexec rs (k v) rs' a -> sexec rs (Interface.Next oc k) rs' a.

Lemma sexec_sound {A} rs (m : Mon A) rs' a :
  sexec rs m rs' a ->
  exists evs, Interface.iTrace_match m (evs, inl a) /\ Interface.pure_iTrace_aux evs /\ seq_ok rs evs rs'.
Proof.
  induction 1 as [rs a|rs T r ak k rs' a _ [evs (?&?&?)]|rs T r ak x k rs' a _ [evs (?&?&?)]
                 |rs ty k v rs' a _ [evs (?&?&?)]|rs T oc v k rs' a Ho _ [evs (?&?&?)]].
  - exists nil. split; [constructor|]. split; reflexivity.
  - exists (Interface.IEvent (Interface.RegRead r ak) (register_lookup r rs) :: evs).
    split; [constructor; assumption|]. split; [assumption|]. split; [reflexivity|assumption].
  - exists (Interface.IEvent (Interface.RegWrite r ak x) tt :: evs).
    split; [constructor; assumption|]. split; assumption.
  - exists evs. split; [econstructor; eassumption|]. split; assumption.
  - exists (Interface.IEvent oc v :: evs). split; [constructor; assumption|].
    destruct oc; try discriminate Ho; split; assumption.
Qed.

Lemma sexec_complete {A} rs (m : Mon A) evs a rs' :
  Interface.pure_iTrace_aux evs -> Interface.iTrace_match m (evs, inl a) -> seq_ok rs evs rs' ->
  sexec rs m rs' a.
Proof.
  intros Hp Hm. remember (evs, inl a) as tr eqn:Htr. revert rs evs Hp Htr.
  induction Hm as [T oc f obj tl res Hm IH|ty f v tr Hm IH|b|f s]; intros rs evs Hp Htr Hs.
  - injection Htr as <- ->. destruct oc; cbn in Hs, Hp.
    all: try solve [destruct Hp | destruct obj].
    1: destruct Hs as [<- Hs]; eapply SRead; exact (IH _ _ Hp eq_refl Hs).
    1: destruct obj; eapply SWrite; exact (IH _ _ Hp eq_refl Hs).
    all: eapply SOther; [reflexivity | exact (IH _ _ Hp eq_refl Hs)].
  - eapply SChoose. apply (IH _ _ Hp Htr Hs).
  - injection Htr as <- <-. cbn in Hs. subst rs'. constructor.
  - discriminate Htr.
Qed.

(* Inversion without dependent-equality axioms: compute what the last step
   of a derivation must have been from the head of the tree. *)
Definition sexec_inv {A} rs (m : Mon A) rs' (a : A) : Prop :=
  match m with
  | Interface.Ret b => rs' = rs /\ a = b
  | Interface.Next oc k =>
      match oc in @Interface.outcome _ T return (T -> Mon A) -> Prop with
      | Interface.RegRead r _ => fun k => sexec rs (k (register_lookup r rs)) rs' a
      | Interface.RegWrite r _ x => fun k => sexec (register_set r x rs) (k tt) rs' a
      | Interface.Choose ty => fun k => exists v, sexec rs (k v) rs' a
      | Interface.GenericFail _ | Interface.Discard => fun _ => False
      | _ => fun k => exists v, sexec rs (k v) rs' a
      end k
  end.

Lemma sexec_invert {A} rs (m : Mon A) rs' a : sexec rs m rs' a -> sexec_inv rs m rs' a.
Proof.
  destruct 1 as [|? ? ? ? ? ? ? H|? ? ? ? ? ? ? ? H|? ? ? v ? ? H|? ? oc v ? ? ? Ho H]; cbn.
  - split; reflexivity.
  - exact H.
  - exact H.
  - exists v; exact H.
  - destruct oc; try discriminate Ho; exists v; exact H.
Qed.

Lemma sexec_eq {A} rs (m : Mon A) rs1 rs' a : sexec rs m rs1 a -> rs1 = rs' -> sexec rs m rs' a.
Proof. intros H ->. exact H. Qed.

(* ---------------------------------------------------------------- *)
(* Tactics.  They only build or take apart derivations; every step is
   checked by the kernel.  Both work on the head of the tree (hnf), so the
   model's functions are unfolded lazily and only as far as execution
   reaches.  A Boolean the head is stuck on is decided only by a premise in
   the context (up to conversion), never assumed. *)
Ltac sx_cbn := lazy beta iota zeta delta [bind bind0 returnM returnm stdpp.base.mret Interface.iMon_mret_inst Interface.iMon_bind];
  repeat first [ rewrite register_lookup_set | rewrite irrelevant_register_set by reflexivity ].
Ltac sx_cbn_in H := lazy beta iota zeta delta [bind bind0 returnM returnm stdpp.base.mret Interface.iMon_mret_inst Interface.iMon_bind] in H;
  repeat first [ rewrite register_lookup_set in H | rewrite irrelevant_register_set in H by reflexivity ].

(* Rewrite with equational premises (t = c, t not a variable). *)
Ltac sx_rw := repeat match goal with
  | H : ?t = ?c |- context [?t] =>
      lazymatch t with true => fail | false => fail | _ =>
        tryif is_var t then fail else
        lazymatch c with context [t] => fail | _ => rewrite H end end
  end.
Ltac sx_rw_in H := repeat match goal with
  | E : ?t = ?c |- _ =>
      lazymatch type of H with context [t] =>
      lazymatch t with true => fail | false => fail | _ =>
        tryif is_var t then fail else
        lazymatch c with context [t] => fail | _ => rewrite E in H end end end
  end.

(* The scrutinee the head of a tree is stuck on. *)
Ltac sx_head m := lazymatch m with
  | Interface.iMon_bind ?x _ => sx_head x
  | bind ?x _ => sx_head x
  | bind0 ?x _ => sx_head x
  | if ?b then _ else _ => constr:(b)
  | match ?x with Some _ => _ | None => _ end => constr:(x)
  | try_catch ?x _ => sx_head x
  | catch_early_return ?x => sx_head x
  | liftR ?x => sx_head x
  | _ _ _ ?x _ => sx_head x   (* an unfolded iMon_bind fixpoint *)
  end.

(* Forward: build a run, reading each register from the current record. *)
Ltac sx_fwd_step :=
  sx_cbn; sx_rw; sx_cbn;
  match goal with
  | |- sexec ?rs ?m ?rs' ?a =>
      let m' := eval hnf in m in change (sexec rs m' rs' a);
      first [ apply SRet
            | eapply SRead
            | eapply SWrite
            | simple refine (SChoose _ _ _ _ _ _ _); [cbv [choose_type]; exact inhabitant|]
            | eapply SOther; [reflexivity|] ]
  end.
Ltac sx_decide_goal :=
  match goal with |- sexec _ ?m _ _ =>
    let b := sx_head m in
    first [ let E := fresh in assert (E : b = true) by (assumption || (vm_compute; reflexivity)); rewrite E; clear E
          | let E := fresh in assert (E : b = false) by (assumption || (vm_compute; reflexivity)); rewrite E; clear E ]
  end.
Ltac sx_fwd := repeat (first [ sx_fwd_step | sx_cbn; sx_rw; sx_cbn; sx_decide_goal ]); try (sx_cbn; sx_rw).

(* Backward: from a run hypothesis, peel one step. *)
Ltac sx_bwd_step H :=
  sx_cbn_in H; sx_rw_in H; sx_cbn_in H;
  match type of H with
  | sexec ?rs ?m ?rs' ?a =>
      let m' := eval hnf in m in
      lazymatch m' with Interface.Ret _ => idtac | Interface.Next _ _ => idtac end;
      change (sexec rs m' rs' a) in H;
      apply sexec_invert in H; cbn beta iota delta [sexec_inv] in H;
      lazymatch type of H with
      | False => destruct H
      | ex _ => let v := fresh "v" in destruct H as [v H]
      | _ => idtac
      end
  end.
Ltac sx_decide_hyp H :=
  match type of H with sexec _ ?m _ _ =>
    let b := sx_head m in
    first [ let E := fresh in assert (E : b = true) by (assumption || (vm_compute; reflexivity)); rewrite E in H; clear E
          | let E := fresh in assert (E : b = false) by (assumption || (vm_compute; reflexivity)); rewrite E in H; clear E ]
  end.
(* An option-valued scrutinee no premise decides (the model's enumeration
   pick for an undefined value): split; the None branch fails. *)
Ltac sx_split_hyp H :=
  match type of H with sexec _ ?m _ _ =>
    let x := sx_head m in
    lazymatch type of x with option _ => destruct x eqn:? end
  end.
Ltac sx_bwd H :=
  repeat (first [ sx_bwd_step H | sx_cbn_in H; sx_rw_in H; sx_cbn_in H; sx_decide_hyp H | sx_cbn_in H; sx_split_hyp H ]).

Print Assumptions sexec_sound.
Print Assumptions sexec_complete.
Print Assumptions sexec_invert.
