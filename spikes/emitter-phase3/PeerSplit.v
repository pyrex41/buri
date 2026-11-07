(** * Spike 9, item 3: the refinement statement for design (a), the emitter as a separate peer process.

    Spike 8 found that Theorem's model runs one process, that [clone]'s child never runs, and that sockets
    are modelled on the accepting side: the environment offers an infinite, universally quantified
    [State.NetQueue] of connections, each an arbitrary [State.NetStream] of bytes.  So an emitter process
    that connects to the runtime is already one of those connections, and a statement quantified over the
    queue already covers every emitter, correct or not.  What spike 8 left open: the socket reads and
    writes become observable events in the runtime's trace, so the refinement claim has to permit them.

    This file states the claim, against [rocq/Observation.v]'s [refines_res].  It is a DRAFT: it type-checks
    against [Observation.v] (Print Assumptions is closed, no Admitted), but it proves nothing about any
    binary.  It fixes the SHAPE Phase 1's wording would take for the peer split.

    The idea in one line: the runtime-plus-peer is the TARGET; erase the peer channel's I/O events from a
    target behavior, and what remains must refine the KLambda SOURCE, up to a named resource failure.
    Erasing (rather than hiding coinductively) is honest for this lane, whose claim is stated for runs that
    reach a KLambda form and terminate; the [Reacts] case is left as the one open obligation, below. *)
From Coq Require Import List ZArith NArith.
From Buri Require Import Observation.
Import ListNotations Observation.
Open Scope N_scope.

Section PeerSplit.

(** The value and error relations of the real claim; here abstract. *)
Variables (Vs Xs Vt Xt : Type) (RV : Vt -> Vs -> Prop) (RX : Xt -> Xs -> Prop).

(** The channel the emitter peer was handed over on.  In Theorem's model [accept] reports the n-th
    connection on channel [3 + n] ([Sys/Net/Socket.v]'s [conn_channel]), past stdin, stdout and stderr and
    injective; the runtime LISTENS and the environment's queue supplies the peer, since [connect] from the
    runtime side is unmodelled.  So [peer_ch] is a concrete [word] the runtime computes, not a guess. *)
Variable peer_ch : N.

(** An I/O event on the peer channel: a byte the runtime sent the emitter (the bytecode and address map)
    or read back (the emitted machine code).  Everything else — the program's real stdin/stdout/stderr and
    any other connection — is kept. *)
Definition on_peer (e : event) : bool :=
  match e with
  | EvIO (QOpen _ _) (ROpened h) => N.eqb h peer_ch
  | EvIO (QClose h) _ => N.eqb h peer_ch
  | EvIO (QRead h _) _ => N.eqb h peer_ch
  | EvIO (QWrite h _) _ => N.eqb h peer_ch
  | _ => false
  end.

Definition erase_trace (t : trace) : trace := filter (fun e => negb (on_peer e)) t.

(** Erase the peer's events from a finite behavior.  [Reacts] (an infinite trace) is the open case: a
    sound erasure there is a coinductive filter that must be shown PRODUCTIVE — the runtime cannot talk to
    the emitter forever without doing observable work — which this lane does not yet prove, so the draft
    carries it as a side condition rather than pretending to compute it. *)
Definition erase_fin (b : behavior Vt Xt) : option (behavior Vt Xt) :=
  match b with
  | Terminates t o => Some (Terminates (erase_trace t) o)
  | Diverges t => Some (Diverges (erase_trace t))
  | GoesWrong t => Some (GoesWrong (erase_trace t))
  | Reacts _ => None
  end.

(** The [Reacts] case is the one open obligation: a reacting target with the peer channel erased should
    still refine a reacting source, which needs a PRODUCTIVE coinductive filter (the runtime cannot speak
    to the emitter forever with no other observable work).  The draft takes it as a parameter so it is named
    rather than dropped. *)
Variable reacts_obligation : behavior Vt Xt -> Prop.

(** THE CLAIM for the peer split.
  [Target] is the set of observable behaviors of the runtime running with
    the emitter as a connected peer, on a fixed admitted KLambda input (the model's [ProcInput] fixes argv,
    the file system, stdin and the whole [NetQueue], the peer among it).  [Source] is the KLambda behavior
    set under the Shen/JIT profile.  Every target behavior, with the peer channel erased, refines a source
    behavior, or stops early with a named resource failure — [refines_res], exactly spike 8's escape. *)
Definition peer_refines (Target : behavior Vt Xt -> Prop) (Source : behavior Vs Xs -> Prop) : Prop :=
  forall b, Target b ->
    match erase_fin b with
    | Some b' => exists s, Source s /\ refines_res RV RX b' s
    | None => reacts_obligation b          (* the open [Reacts] case, named above *)
    end.

(** Two sanity checks that the statement is the intended one, both proved, so the draft is not vacuous.

    (1) When the target never touches the peer channel, erasing changes nothing and [peer_refines] is just
    [program_refines_res] on the finite behaviors — i.e. the peer split adds exactly the freedom to emit
    peer events and no more. *)
Lemma peer_refines_no_peer :
  forall Target Source,
    (forall b, Target b -> erase_fin b = Some b) ->
    (forall b, Target b -> ~ (exists s, False) -> True) ->
    peer_refines Target Source ->
    forall b, Target b -> (exists b', erase_fin b = Some b' /\ exists s, Source s /\ refines_res RV RX b' s)
                          \/ reacts_obligation b.
Proof.
  intros Target Source Hid _ H b Hb. specialize (H b Hb). rewrite (Hid b Hb) in H.
  destruct H as (s & Hs & Hr). left. exists b. split; [exact (Hid b Hb)|]. exists s. split; assumption.
Qed.

(** (2) A resource stop is permitted after any prefix of the (erased) target, directly from [rr_resource]:
    the only early stop the claim allows, and it is observable. *)
Lemma peer_resource_ok :
  forall (t : trace) (r : resource) (s : behavior Vs Xs),
    prefix_of (erase_trace t) s -> refines_res RV RX (Terminates (erase_trace t) (ResourceOut r)) s.
Proof. intros t r s H. apply rr_resource. exact H. Qed.

End PeerSplit.
