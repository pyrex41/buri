(* Shen/JIT Phase 2, pass split: the normal form of src/lowerer/lower.shen (d3348ce), the IR
   between its `norm` pass and its emission (`code`/`expr`). The node shapes are those documented
   above `shen-jit.lower.norm`, plus what norm-cond, open-call, fn-call, unified-now, bound-now
   and the inliner build from them:

     [const V] [var X] [if C X Y] [and X Y] [or X Y] [let X V Body] [do X Y]
     [lambda X Body] [freeze Body] [prim Op Args] [call F Args]
     [apply F] [apply F X] [trap X E Handler]

   `erase` gives a node its meaning as resolved KLambda (KLSyntax.expr). It is exact where KL can
   say the same thing, and None where it cannot; where the lowerer relies on something KL does not
   define (port primitives), erase still yields a named call but `port_prims` lists it, because
   such a call means nothing until the primitive has a specification. The open obligations erase
   leaves are listed at the end of this file and in docs/SHEN-JIT.md ("Pass split: the normal
   form"). Nothing here says the normal form is related to the source definition: that is the
   front end's equivalence (wave 2). No axioms. *)
From Coq Require Import List ZArith NArith String Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitLowerRel JitLowerCheck.
Import ListNotations.
Module JitNorm.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort.
Import JitLowerRel.JitLowerRel JitLowerCheck.JitLowerCheck.

(* ---------- the IR ---------- *)
(* Constants carry any KL value: a folded list constant ([const [a b c]], made by lower.shen's
   `prim` from a cons of constants, or the inline body that open-call's guard compares) is a
   VCons, and lower.shen's last norm clause makes a constant of any value, including closures and
   absvectors that reach eval-kl at run time. *)
Inductive nexpr :=
 | NConst (v : value)
 | NVar (x : name)
 | NIf (c a b : nexpr)
 | NAnd (a b : nexpr)
 | NOr (a b : nexpr)
 | NLet (x : name) (v body : nexpr)
 | NDo (a b : nexpr)
 | NLambda (x : name) (body : nexpr)
 | NFreeze (body : nexpr)
 | NPrim (op : name) (args : list nexpr)
 | NCall (f : name) (args : list nexpr)
 | NApply0 (f : nexpr)
 | NApply1 (f a : nexpr)
 | NTrap (body : nexpr) (e : name) (handler : nexpr).

(* Induction with a hypothesis for every argument of a prim or call. *)
Section NInd.
Variable Q : nexpr -> Prop.
Hypothesis H_const : forall v, Q (NConst v).
Hypothesis H_var : forall x, Q (NVar x).
Hypothesis H_if : forall c a b, Q c -> Q a -> Q b -> Q (NIf c a b).
Hypothesis H_and : forall a b, Q a -> Q b -> Q (NAnd a b).
Hypothesis H_or : forall a b, Q a -> Q b -> Q (NOr a b).
Hypothesis H_let : forall x v b, Q v -> Q b -> Q (NLet x v b).
Hypothesis H_do : forall a b, Q a -> Q b -> Q (NDo a b).
Hypothesis H_lambda : forall x b, Q b -> Q (NLambda x b).
Hypothesis H_freeze : forall b, Q b -> Q (NFreeze b).
Hypothesis H_prim : forall op l, Forall Q l -> Q (NPrim op l).
Hypothesis H_call : forall f l, Forall Q l -> Q (NCall f l).
Hypothesis H_apply0 : forall f, Q f -> Q (NApply0 f).
Hypothesis H_apply1 : forall f a, Q f -> Q a -> Q (NApply1 f a).
Hypothesis H_trap : forall b e h, Q b -> Q h -> Q (NTrap b e h).
Fixpoint nexpr_ind' (n : nexpr) : Q n :=
 let all := fix all (l : list nexpr) : Forall Q l := match l with
   | [] => Forall_nil Q | a :: l => Forall_cons a (nexpr_ind' a) (all l) end in
 match n with
 | NConst v => H_const v | NVar x => H_var x
 | NIf c a b => H_if c a b (nexpr_ind' c) (nexpr_ind' a) (nexpr_ind' b)
 | NAnd a b => H_and a b (nexpr_ind' a) (nexpr_ind' b)
 | NOr a b => H_or a b (nexpr_ind' a) (nexpr_ind' b)
 | NLet x v b => H_let x v b (nexpr_ind' v) (nexpr_ind' b)
 | NDo a b => H_do a b (nexpr_ind' a) (nexpr_ind' b)
 | NLambda x b => H_lambda x b (nexpr_ind' b)
 | NFreeze b => H_freeze b (nexpr_ind' b)
 | NPrim op l => H_prim op l (all l)
 | NCall f l => H_call f l (all l)
 | NApply0 f => H_apply0 f (nexpr_ind' f)
 | NApply1 f a => H_apply1 f a (nexpr_ind' f) (nexpr_ind' a)
 | NTrap b e h => H_trap b e h (nexpr_ind' b) (nexpr_ind' h) end.
End NInd.

(* ---------- fixed names ---------- *)
Definition cons_name : name := kw "cons".
(* norm-cond's end of chain; not a KL name (loader.c maps it to PRIM_RAISE_COND). *)
Definition raise_cond_name : name := kw "raise-cond".
(* The inliner's marker, [let shen-jit.lower.inlining [const F] Body] (inline-frozen): the
   emitter compiles it as Body alone (lower.expr; `mark` adds nothing at stage 0). *)
Definition inlining_name : name := kw "shen-jit.lower.inlining".
(* The variable a `do` binds in its erasure. lower.shen never makes it; erase checks that the
   second expression does not mention it anyway. *)
Definition do_name : name := kw "shen-jit.norm.do".

(* ---------- meaning ---------- *)
(* A constant with a literal is that literal. ESym is a literal of resolved syntax: eval_move
   returns VSym s whatever the environment binds, so a symbol constant cannot be captured by a
   variable in scope, and erase needs no check for it (`erase_const_eval` below is the proof).
   A pair has no literal: it erases to the cons chain that builds it, which is a different
   expression; `erase_const_eval` proves the chain evaluates to the constant, in any environment,
   given that `cons` names the primitive and the stack has room for it. Values with no literal
   syntax (closures, vectors, streams, partial applications, exceptions): None. *)
Fixpoint erase_const (v : value) : option expr := match v with
 | VNum n => Some (ENum n) | VStr t => Some (EStr t) | VSym s => Some (ESym s)
 | VBool b => Some (EBool b) | VNil => Some ENil
 | VCons a d => match erase_const a, erase_const d with
   | Some ea, Some ed => Some (ECall cons_name [ea; ed]) | _, _ => None end
 | _ => None end.

Definition is_sym (e : expr) : bool := match e with ESym _ => true | _ => false end.
(* The inlining marker, droppable: its value is a symbol constant and the body never mentions
   the name (vars lists every variable occurrence, bound or free). *)
Definition marker (x : name) (ev eb : expr) : bool :=
 text_eqb x inlining_name && is_sym ev && negb (bound (vars eb) x).

(* `erase sc n`, sc the variables in scope (the parameters, at a definition's top).
   - [var X]: EVar X, and None if X is not in scope (no witness of a closed definition has one).
   - [if] [and] [or] [lambda] [freeze]: the special form.
   - [let X V B]: ELet, except the inlining marker, which is its body when `marker` holds.
   - [do X Y]: evaluate X, discard it, then Y in tail position: ELet do_name X Y, None if Y
     mentions do_name. Not (ECall do [X; Y]), which would put Y in an argument position and make
     the meaning depend on the global function `do`.
   - [prim raise-cond []]: ECond [], which raises XCondFail as norm-cond's end does.
   - [prim Op Args] for a KL primitive Op: ECall Op Args, None if the count is not Op's arity.
     A named call is what a primitive call is in KLSemantics: it resolves Op in gfuns, which
     JitLowerStep's store invariant (fr_prim/fr_name) binds to FPrim Op.
   - [prim Op Args] for any other Op (shen-jit.*, write-string, char-stream?, ...): ECall Op
     Args, listed by `port_prims`. KL's store defines no such name, so the call raises
     XUndefinedFun until the port's primitive is specified.
   - [call F Args]: ECall F Args.
   - [apply F]: EApp F [], the thaw of a frozen value (apply_value VFrozen []), also norm-apply's
     zero-argument dynamic call. [apply F X]: EApp F [X], one argument.
   - [trap X E H]: ETrap X (lambda E H), H in scope of E: throw_move applies the handler to the
     exception value. *)
Fixpoint erase (sc : list name) (n : nexpr) {struct n} : option expr :=
 let args := fix args (l : list nexpr) : option (list expr) := match l with
   | [] => Some []
   | a :: l => match erase sc a, args l with Some e, Some es => Some (e :: es) | _, _ => None end end in
 match n with
 | NConst v => erase_const v
 | NVar x => if bound sc x then Some (EVar x) else None
 | NIf c a b => match erase sc c, erase sc a, erase sc b with
   | Some ec, Some ea, Some eb => Some (EIf ec ea eb) | _, _, _ => None end
 | NAnd a b => match erase sc a, erase sc b with Some ea, Some eb => Some (EAnd ea eb) | _, _ => None end
 | NOr a b => match erase sc a, erase sc b with Some ea, Some eb => Some (EOr ea eb) | _, _ => None end
 | NLet x v b => match erase sc v, erase (x :: sc) b with
   | Some ev, Some eb => if marker x ev eb then Some eb else Some (ELet x ev eb)
   | _, _ => None end
 | NDo a b => match erase sc a, erase sc b with
   | Some ea, Some eb => if bound (vars eb) do_name then None else Some (ELet do_name ea eb)
   | _, _ => None end
 | NLambda x b => option_map (ELam x) (erase (x :: sc) b)
 | NFreeze b => option_map EFreeze (erase sc b)
 | NPrim op l =>
   if text_eqb op raise_cond_name then match l with [] => Some (ECond []) | _ => None end
   else match args l with
     | Some es => match prim_of_name op with
       | Some p => if Nat.eqb (List.length es) (prim_arity p) then Some (ECall op es) else None
       | None => Some (ECall op es) end
     | None => None end
 | NCall f l => option_map (ECall f) (args l)
 | NApply0 f => option_map (fun ef => EApp ef []) (erase sc f)
 | NApply1 f a => match erase sc f, erase sc a with Some ef, Some ea => Some (EApp ef [ea]) | _, _ => None end
 | NTrap b x h => match erase sc b, erase (x :: sc) h with
   | Some eb, Some eh => Some (ETrap eb (ELam x eh)) | _, _ => None end end.

(* ---------- what an erasure depends on ---------- *)
(* The primitives with no KL specification that a node uses: each needs a primitive spec and a
   ledger entry before code using it can mean anything. *)
Fixpoint port_prims (n : nexpr) : list name :=
 let all := fix all (l : list nexpr) : list name := match l with
   | [] => [] | a :: l => port_prims a ++ all l end in
 match n with
 | NConst _ | NVar _ => []
 | NIf c a b => port_prims c ++ port_prims a ++ port_prims b
 | NAnd a b | NOr a b | NDo a b | NApply1 a b | NLet _ a b | NTrap a _ b => port_prims a ++ port_prims b
 | NLambda _ b | NFreeze b | NApply0 b => port_prims b
 | NPrim op l => (if text_eqb op raise_cond_name then [] else
                  match prim_of_name op with Some _ => [] | None => [op] end) ++ all l
 | NCall _ l => all l end.

(* How many pair constants a node has: each erases to a cons chain. *)
Fixpoint folded (n : nexpr) : nat :=
 let all := fix all (l : list nexpr) : nat := match l with
   | [] => 0 | a :: l => folded a + all l end in
 match n with
 | NConst (VCons _ _) => 1
 | NConst _ | NVar _ => 0
 | NIf c a b => folded c + folded a + folded b
 | NAnd a b | NOr a b | NDo a b | NApply1 a b | NLet _ a b | NTrap a _ b => folded a + folded b
 | NLambda _ b | NFreeze b | NApply0 b => folded b
 | NPrim _ l | NCall _ l => all l end.

(* ---------- sanity ---------- *)
Definition atom (v : value) : bool := match v with
 | VNum _ | VStr _ | VSym _ | VBool _ | VNil => true | _ => false end.
Fixpoint data (v : value) : bool := match v with
 | VCons a d => data a && data d | v => atom v end.

Lemma erase_const_defined : forall v, data v = true -> exists e, erase_const v = Some e.
Proof.
 induction v; cbn; intro H; try discriminate; eauto.
 apply andb_true_iff in H as [Ha Hd].
 destruct (IHv1 Ha) as [ea ->]; destruct (IHv2 Hd) as [ed ->]; eauto.
Qed.
Lemma erase_const_data : forall v e, erase_const v = Some e -> data v = true.
Proof.
 induction v; cbn; intros e H; try discriminate; auto.
 destruct (erase_const v1) eqn:E1; [|discriminate]; destruct (erase_const v2) eqn:E2; [|discriminate].
 rewrite (IHv1 _ eq_refl), (IHv2 _ eq_refl); reflexivity.
Qed.
(* An atom's erasure is its literal. *)
Lemma erase_const_atom : forall v e, atom v = true -> erase_const v = Some e -> lit_val e = Some v.
Proof. destruct v; cbn; intros e A H; try discriminate; inversion H; reflexivity. Qed.
(* No erased constant mentions a variable. *)
Lemma erase_const_closed : forall v e, erase_const v = Some e -> vars e = [].
Proof.
 induction v; cbn; intros e H; try discriminate; try (inversion H; reflexivity).
 destruct (erase_const v1) eqn:E1; [|discriminate]; destruct (erase_const v2) eqn:E2; [|discriminate].
 inversion H; subst; cbn. rewrite (IHv1 _ eq_refl), (IHv2 _ eq_refl). reflexivity.
Qed.

(* Evaluating an erased constant. `taus` is any number of internal steps of the port machine
   (KLPort.next_r; agreed_rules is KLSemantics itself, KLPort.next_r_agreed). *)
Inductive taus (R : port_rules) (P : profile) : config -> config -> Prop :=
 | taus_refl c : taus R P c c
 | taus_step c c1 c2 : next_r R P c = MTau c1 -> taus R P c1 c2 -> taus R P c c2.
Lemma taus_trans : forall R P a b c, taus R P a b -> taus R P b c -> taus R P a c.
Proof. intros R P a b c H; induction H; intros; [auto|econstructor; eauto]. Qed.

(* Frames a cons chain pushes, and room for them below the profile's stack bound. *)
Fixpoint cdepth (v : value) : nat := match v with
 | VCons a d => S (Nat.max (cdepth a) (cdepth d)) | _ => 0 end.
Definition room (P : profile) (d : nat) (k : list frame) : Prop :=
 match stack_limit P with None => True | Some n => (List.length k + d <= n)%nat end.

(* A constant's erasure evaluates to the constant, in any lexical environment (so no variable
   captures a symbol constant), to any continuation, leaving the store as it was. For a pair,
   given that `cons` names the primitive and the stack has room for the chain's frames. This
   discharges, for the expression level, the obligation the cons-chain erasure creates; that the
   emitted constant behaves the same is the emission relation's business. *)
Theorem erase_const_eval : forall R P v e rho k st,
 erase_const v = Some e -> lookup cons_name (gfuns st) = Some (FPrim PCons) -> room P (cdepth v) k ->
 taus R P (Cfg (Eval rho e) k st) (Cfg (Ret v) k st).
Proof.
 intros R P. induction v; intros e rho k st H Lc Rm; cbn in H; try discriminate;
 try (inversion H; subst; econstructor; [reflexivity|constructor]).
 destruct (erase_const v1) as [ea|] eqn:E1; [|discriminate].
 destruct (erase_const v2) as [ed|] eqn:E2; [|discriminate]. inversion H; subst; clear H.
 set (k1 := KCallArgs cons_name [] [ed] rho :: k).
 assert (Push : push P (KCallArgs cons_name [] [ed] rho) k (Eval rho ea) st = Cfg (Eval rho ea) k1 st).
 { unfold push, room in *. destruct (stack_limit P) as [n|]; [|reflexivity]. cbn [cdepth] in Rm.
   replace (Nat.leb n (List.length k)) with false by (symmetry; apply Nat.leb_gt; lia). reflexivity. }
 assert (R1 : room P (cdepth v1) k1).
 { unfold room in *; subst k1; destruct (stack_limit P); cbn [cdepth List.length] in *; auto; lia. }
 assert (R2 : room P (cdepth v2) (KCallArgs cons_name [v1] [] rho :: k)).
 { unfold room in *; destruct (stack_limit P); cbn [cdepth List.length] in *; auto; lia. }
 apply taus_step with (c1 := Cfg (Eval rho ea) k1 st).
 { unfold next_r, eval_move_r, eval_move; cbn [ctl kont mem]. f_equal. exact Push. }
 eapply taus_trans; [apply (IHv1 _ rho k1 st eq_refl Lc R1)|].
 econstructor. { reflexivity. }
 eapply taus_trans; [apply (IHv2 _ rho _ st eq_refl Lc R2)|].
 econstructor; [|constructor].
 cbn [next_r ctl kont mem ret_move_r rev app]. unfold call_named_r. rewrite Lc.
 unfold arity_mismatch. cbn [prim_arity List.length]. rewrite Nat.eqb_refl, andb_false_r. reflexivity.
Qed.

(* Nodes that are KL as written: atomic constants, variables in scope, the special forms, KL
   primitives at their arity, named and dynamic calls, traps; no do, no pair constant, no
   port primitive, no raise-cond, no let of the marker's name. Their erasure always exists, and
   it is the direct translation. *)
Fixpoint kl_shaped (sc : list name) (n : nexpr) : bool :=
 let all := fix all (l : list nexpr) : bool := match l with
   | [] => true | a :: l => kl_shaped sc a && all l end in
 match n with
 | NConst v => atom v
 | NVar x => bound sc x
 | NIf c a b => kl_shaped sc c && kl_shaped sc a && kl_shaped sc b
 | NAnd a b | NOr a b | NApply1 a b => kl_shaped sc a && kl_shaped sc b
 | NLet x v b => negb (text_eqb x inlining_name) && kl_shaped sc v && kl_shaped (x :: sc) b
 | NDo _ _ => false
 | NLambda x b => kl_shaped (x :: sc) b
 | NFreeze b | NApply0 b => kl_shaped sc b
 | NPrim op l => match prim_of_name op with
   | Some p => negb (text_eqb op raise_cond_name) && Nat.eqb (List.length l) (prim_arity p) && all l
   | None => false end
 | NCall _ l => all l
 | NTrap b x h => kl_shaped sc b && kl_shaped (x :: sc) h end.

Lemma args_length : forall (f : nexpr -> option expr) l es,
 (fix args (l : list nexpr) : option (list expr) := match l with
   | [] => Some [] | a :: l => match f a, args l with Some e, Some es => Some (e :: es) | _, _ => None end end) l = Some es ->
 List.length es = List.length l.
Proof.
 intros f; induction l as [|a l IH]; intros es H; [inversion H; reflexivity|].
 destruct (f a); [|discriminate]. destruct (_ l) eqn:E; [|discriminate]. inversion H; subst.
 cbn; f_equal; apply IH; reflexivity.
Qed.

Lemma args_defined : forall (f : nexpr -> option expr) (g : nexpr -> bool) l,
 Forall (fun n => g n = true -> exists e, f n = Some e) l ->
 (fix all (l : list nexpr) : bool := match l with [] => true | a :: l => g a && all l end) l = true ->
 exists es, (fix args (l : list nexpr) : option (list expr) := match l with
   | [] => Some [] | a :: l => match f a, args l with Some e, Some es => Some (e :: es) | _, _ => None end end) l = Some es.
Proof.
 intros f g l H. induction H as [|a l Ha Hl IHl]; intro K; [eauto|].
 apply andb_true_iff in K as [Ka Kl]. destruct (Ha Ka) as [e ->]. destruct (IHl Kl) as [es ->]. eauto.
Qed.

Theorem erase_kl_shaped : forall n sc, kl_shaped sc n = true -> exists e, erase sc n = Some e.
Proof.
 induction n using nexpr_ind'; intros sc K; cbn [kl_shaped erase] in K |- *;
 repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_true_iff in H as [? ?] end;
 try discriminate.
 - destruct v; cbn in K |- *; try discriminate; eexists; reflexivity.
 - rewrite K; eauto.
 - destruct (IHn1 sc) as [? ->]; auto; destruct (IHn2 sc) as [? ->]; auto; destruct (IHn3 sc) as [? ->]; auto; eauto.
 - destruct (IHn1 sc) as [? ->]; auto; destruct (IHn2 sc) as [? ->]; auto; eauto.
 - destruct (IHn1 sc) as [? ->]; auto; destruct (IHn2 sc) as [? ->]; auto; eauto.
 - destruct (IHn1 sc) as [ev ->]; auto; destruct (IHn2 (x :: sc)) as [eb ->]; auto.
   destruct (marker x ev eb); eauto.
 - destruct (IHn (x :: sc)) as [? ->]; auto; cbn; eauto.
 - destruct (IHn sc) as [? ->]; auto; cbn; eauto.
 - destruct (prim_of_name op) as [p|] eqn:Pn; [|discriminate].
   repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_true_iff in H as [? ?] end.
   match goal with H : negb (text_eqb op raise_cond_name) = true |- _ => apply negb_true_iff in H; rewrite H end.
   destruct (args_defined (erase sc) (kl_shaped sc) l) as [es Hes];
     [eapply Forall_impl; [|exact H]; cbn; intros a Ha; apply Ha|assumption|].
   rewrite Hes; cbv beta iota; rewrite (args_length _ _ _ Hes).
   match goal with H : Nat.eqb _ _ = true |- _ => rewrite H end. eauto.
 - destruct (args_defined (erase sc) (kl_shaped sc) l) as [es Hes];
     [eapply Forall_impl; [|exact H]; cbn; intros a Ha; apply Ha|exact K|].
   rewrite Hes. cbn. eauto.
 - destruct (IHn sc) as [? ->]; auto; cbn; eauto.
 - destruct (IHn1 sc) as [? ->]; auto; destruct (IHn2 sc) as [? ->]; auto; eauto.
 - destruct (IHn1 sc) as [? ->]; auto; destruct (IHn2 (e :: sc)) as [? ->]; auto; eauto.
Qed.

(* The two places erase is not the direct translation, exactly. *)
Lemma erase_marker : forall sc x v b ev eb, erase sc v = Some ev -> erase (x :: sc) b = Some eb ->
 erase sc (NLet x v b) = Some (if marker x ev eb then eb else ELet x ev eb).
Proof. intros sc x v b ev eb Hv Hb. cbn [erase]. rewrite Hv, Hb. destruct (marker x ev eb); reflexivity. Qed.
Lemma marker_dead : forall x ev eb, marker x ev eb = true ->
 x = inlining_name /\ (exists s, ev = ESym s) /\ ~ In x (vars eb).
Proof.
 intros x ev eb H. unfold marker in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
 apply text_eqb_eq in H1. split; [auto|split].
 - destruct ev; try discriminate; eauto.
 - intro I. apply negb_true_iff in H3. unfold bound in H3.
   assert (existsb (text_eqb x) (vars eb) = true) by (apply existsb_exists; exists x; split; [auto|apply text_eqb_refl]).
   congruence.
Qed.
Lemma erase_do : forall sc a b e, erase sc (NDo a b) = Some e ->
 exists ea eb, erase sc a = Some ea /\ erase sc b = Some eb /\ e = ELet do_name ea eb /\ ~ In do_name (vars eb).
Proof.
 intros sc a b e H. cbn [erase] in H.
 destruct (erase sc a) as [ea|] eqn:Ea; [|discriminate]; destruct (erase sc b) as [eb|] eqn:Eb; [|discriminate].
 destruct (bound (vars eb) do_name) eqn:B; [discriminate|]. inversion H; subst.
 exists ea, eb. split; [auto|split; [auto|split; [auto|]]].
 intro I. unfold bound in B.
 assert (existsb (text_eqb do_name) (vars eb) = true) by (apply existsb_exists; exists do_name; split; [auto|apply text_eqb_refl]).
 congruence.
Qed.

(* Erase is not injective, and the checker does not need it to be: it relates code to the
   erasure, whatever node it came from. A folded constant and the cons it was folded from erase
   alike, and so do a call and a prim of the same name. *)
Example erase_not_injective_fold :
 erase [] (NConst (VCons (VNum (NInt 1)) VNil)) = erase [] (NPrim cons_name [NConst (VNum (NInt 1)); NConst VNil]).
Proof. reflexivity. Qed.
Example erase_not_injective_call :
 erase [] (NCall cons_name [NConst (VNum (NInt 1)); NConst VNil]) = erase [] (NPrim cons_name [NConst (VNum (NInt 1)); NConst VNil]).
Proof. reflexivity. Qed.

(* ---------- open obligations (stated, not assumed) ----------
   - Emission of a pair constant: lower.shen emits (const d k) with a pair in the constant
     table; JitLowerRel's C_lit admits atoms only, so check_fn rejects such code. Owner: the
     emission relation (JitLowerRel), not erase.
   - [do X Y] as ELet do_name X Y: the emitter computes Y with top unchanged where C_let raises
     top for the body, so check_fn rejects most do. Owner: the emission relation.
   - Port primitives (`port_prims`): shen-jit.inlined? (open-call's guard) and shen-jit.arity?
     (fn-call's test) are C primitives (src/runtime/prims.c) reading a function's current code
     object; each needs a primitive spec under which the guard's two branches agree. The other
     shen-jit.* prims (pvar?, same?, ...) need specs too.
   - Port functions called by name (shen-jit.eval-kl, shen-jit.unify=, shen-jit.unify=!,
     shen-jit.undo, shen.bindv; src/port/shen-jit.kl) are ordinary KL defuns, so their calls
     mean what the store's definitions say. Relating them to the source form (eval-kl, is/is!,
     shen.bind!) is the front end's obligation; shen-jit.eval-kl returns any non-pair as is,
     where KL's eval-kl raises XEvalKL on a closure or vector, a semantic difference for the
     ledger, not a pending proof.
   - The front end itself: that erase (norm (share Body)) is equivalent to Body (wave 2). *)
End JitNorm.
