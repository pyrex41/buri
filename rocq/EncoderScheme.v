(* A target semantics retaining sequential administrative lets. Primitive
   contracts are shared explicitly; this does not model arbitrary Scheme. *)
From Coq Require Import List String Arith.
From Buri Require Import Wire Encoder.
Import ListNotations.
Module EncoderScheme.
Import Encoder.Encoder.
Definition table := function -> expr.
Inductive exec (p : table) : list value -> expr -> value -> Prop :=
| ELit : forall env v, exec p env (Lit v) v
| EVar : forall env i v, nth_error env i = Some v -> exec p env (Var i) v
| ETrue : forall env c a b v, exec p env c (Boolean true) -> exec p env a v -> exec p env (If c a b) v
| EFalse : forall env c a b v, exec p env c (Boolean false) -> exec p env b v -> exec p env (If c a b) v
| ELet : forall env a b x v, exec p env a x -> exec p (x::env) b v -> exec p env (Let a b) v
| EOp : forall env op a b x y v, exec p env a x -> exec p env b y -> primitive op x y = Some v -> exec p env (Op op a b) v
| ECall : forall env f a b x y v, exec p env a x -> exec p env b y -> exec p [x;y] (p f) v -> exec p env (Call f a b) v.
Definition up (r : nat -> nat) i := match i with O => O | S n => S (r n) end.
Fixpoint rename r e := match e with
| Lit v => Lit v | Fail s => Fail s | Var i => Var (r i)
| If c a b => If (rename r c) (rename r a) (rename r b)
| Let a b => Let (rename r a) (rename (up r) b)
| Op op a b => Op op (rename r a) (rename r b)
| Call f a b => Call f (rename r a) (rename r b) end.
Lemma rename_exec : forall p env e v, exec p env e v -> forall r env',
 (forall i, nth_error env i = nth_error env' (r i)) -> exec p env' (rename r e) v.
Proof.
 intros p env e v H; induction H; intros r env' R; cbn [rename]; eauto using exec.
 - apply EVar. rewrite <- R; assumption.
 - eapply ELet; [apply IHexec1; exact R|]. apply IHexec2.
   intros [|i]; cbn [up nth_error]; auto.
Qed.
Definition computation e := match e with Lit _ | Var _ => false | _ => true end.
(* Precisely the administrative sequencing needed by this encoder's generated
   string-append calls. The lift is proved for every expression, not fixtures. *)
Fixpoint anf e := match e with
| Lit v => Lit v | Fail s => Fail s | Var i => Var i
| If c a b => If (anf c) (anf a) (anf b)
| Let a b => Let (anf a) (anf b)
| Op Cat a b => if andb (computation a) (computation b)
    then Let (anf a) (Op Cat (Var 0) (rename S (anf b)))
    else Op Cat (anf a) (anf b)
| Op op a b => Op op (anf a) (anf b)
| Call f a b => Call f (anf a) (anf b) end.
Definition target : table := fun f => anf (body f).
Theorem anf_preserves : forall p env e v, exec p env e v ->
 exec (fun f => anf (p f)) env (anf e) v.
Proof.
 intros p env e v H; induction H; cbn [anf]; eauto using exec.
 destruct op; try (eapply EOp; eauto).
 destruct (computation a && computation b)%bool.
 - eapply ELet; [exact IHexec1 |]. eapply EOp.
   + apply EVar; reflexivity.
   + apply rename_exec with (env:=env); [exact IHexec2 | reflexivity].
   + exact H1.
 - eapply EOp; eauto.
Qed.
Theorem exec_deterministic : forall p env e v, exec p env e v ->
 forall w, exec p env e w -> v = w.
Proof.
 intros p env e v H; induction H; intros w W; inversion W; subst;
 try congruence.
 all: try solve [eauto].
 all: try solve [assert (Boolean true = Boolean false) by eauto; discriminate].
 all: try solve [assert (Boolean false = Boolean true) by eauto; discriminate].
 - assert (x = x0) by eauto. subst; eauto.
 - assert (x = x0) by eauto. assert (y = y0) by eauto. subst; congruence.
 - assert (x = x0) by eauto. assert (y = y0) by eauto. subst; eauto.
Qed.
Lemma evaluator_exec : forall n env e v, Encoder.eval n env e = Returned v -> exec body env e v.
Proof.
 induction n as [|n IH]; intros env e v H; [discriminate|].
 destruct e; cbn [Encoder.eval] in H; try discriminate.
 - inversion H; apply ELit.
 - destruct (nth_error env i) eqn:E; try discriminate. inversion H; subst; apply EVar; exact E.
 - destruct (Encoder.eval n env e1) as [c| |] eqn:C; try discriminate.
   destruct c; try discriminate. destruct b; [eapply ETrue | eapply EFalse]; eauto.
 - destruct (Encoder.eval n env e1) as [x| |] eqn:A; try discriminate. eapply ELet; eauto.
 - destruct (Encoder.eval n env e1) as [x| |] eqn:A; try discriminate.
   destruct (Encoder.eval n env e2) as [y| |] eqn:B; try discriminate.
   destruct (primitive p x y) eqn:P; try discriminate. inversion H; subst; eapply EOp; eauto.
 - destruct (Encoder.eval n env e1) as [x| |] eqn:A; try discriminate.
   destruct (Encoder.eval n env e2) as [y| |] eqn:B; try discriminate. eapply ECall; eauto.
Qed.
Theorem encoder_target_total : forall d,
 exec target [Data d;Number 0] (target Datum) (Text (Wire.capture d)).
Proof.
 intros d. destruct (datum_correct d) as [n H].
 apply anf_preserves. eapply evaluator_exec; exact H.
Qed.
Theorem encoder_target_unique : forall d v,
 exec target [Data d;Number 0] (target Datum) v -> v = Text (Wire.capture d).
Proof. intros d v H; eapply exec_deterministic; [exact H | apply encoder_target_total]. Qed.
End EncoderScheme.
