(* E2E-07: the captured buri.primitive and buri.literal? (shen/klambda.shen)
   under the Native oracle semantics, for every saturated primitive call of the
   KL-PURE-1 primitive table. Each lemma is about the decoded captured body. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native KLambdaEvaluatorCapture.
Import ListNotations Native.Native.
Module KLambdaEvaluatorPrimitives.
Import KLambdaEvaluatorCapture.KLambdaEvaluatorCapture.
Open Scope string_scope.

(* Literal data: what [literal V] may carry (buri.literal?). *)
Fixpoint data (v : rv) : Prop := match v with
 | RInt _ | RBool _ | RStr _ | RSym _ | RNil => True
 | RPair a d => data a /\ data d
 | RClosure _ _ _ | RFunction _ _ | RThunk _ _ => False end.

Definition dom := WRaise "primitive-domain-or-arity".
(* The specification each saturated primitive clause is proved to compute. *)
Definition prim_spec (op : string) (vs : list rv) : verdict := match op, vs with
 | "+", [RInt x; RInt y] => WRet (RInt (x + y))
 | "-", [RInt x; RInt y] => WRet (RInt (x - y))
 | "*", [RInt x; RInt y] => WRet (RInt (x * y))
 | "<", [RInt x; RInt y] => WRet (RBool (Z.ltb x y))
 | "cons", [a; b] => WRet (RPair a b)
 | "hd", [RPair a _] => WRet a
 | "tl", [RPair _ b] => WRet b
 | "cons?", [RPair _ _] => WRet (RBool true)
 | "cons?", [_] => WRet (RBool false)
 | "number?", [RInt _] => WRet (RBool true)
 | "number?", [_] => WRet (RBool false)
 | "string?", [RStr _] => WRet (RBool true)
 | "string?", [_] => WRet (RBool false)
 | _, _ => dom end.


(* Bodies are reduced by the VM with the callee oracle abstracted as [rec];
   R : rec = ask k lets a callee result be read through its own lemma. *)
Ltac site R H f := match type of H with context [?rec f ?xs] => is_var rec;
 let E := fresh "E" in destruct (rec f xs) as [?u|] eqn:E; [rewrite R in E; vm_compute in H|vm_compute in H; discriminate] end.
Ltac assert_site R H := site R H constr:("kl:_scm.assert-boolean");
 match goal with E : ask _ "kl:_scm.assert-boolean" _ = _ |- _ =>
   let b := fresh "b" in apply ask_assert in E; destruct E as (b & -> & ->); destruct b; vm_compute in H end.

Lemma ask_prim2 : forall k op a b r, In op ["+"; "-"; "*"; "<"; "cons"] ->
 ask k "kl:buri.primitive" [Symbol op; L [enc a; enc b]] = Some r -> r = enc_verdict (prim_spec op [a; b]).
Proof.
 intros [|k] op a b r I H; [discriminate|]. rewrite (ask_unfold _ _ _ _ d_primitive_lk) in H.
 generalize dependent H; generalize (ask k) as rec; intros rec H.
 cbn [In] in I. destruct I as [<-|[<-|[<-|[<-|[<-|[]]]]]]; destruct a, b; vm_compute in H;
 injection H as <-; vm_compute; reflexivity.
Qed.
Lemma ask_prim1 : forall k op a r, In op ["hd"; "tl"; "cons?"; "number?"; "string?"] ->
 ask k "kl:buri.primitive" [Symbol op; L [enc a]] = Some r -> r = enc_verdict (prim_spec op [a]).
Proof.
 intros [|k] op a r I H; [discriminate|]. rewrite (ask_unfold _ _ _ _ d_primitive_lk) in H.
 generalize dependent H; generalize (ask k) as rec; intros rec H.
 cbn [In] in I. destruct I as [<-|[<-|[<-|[<-|[<-|[]]]]]]; destruct a; vm_compute in H;
 injection H as <-; vm_compute; reflexivity.
Qed.

Lemma ask_literal : forall k a u, ask k "kl:buri.literal?" [enc a] = Some u -> u = Boolean false \/ data a.
Proof.
 induction k as [|k IH]; intros a u H; [discriminate|].
 rewrite (ask_unfold _ _ _ _ d_literal_lk) in H. remember (ask k) as rec eqn:R in H.
 destruct a as [| | | | |a1 a2| | |]; try (right; exact I);
   [|vm_compute in H; left; injection H as <-; reflexivity ..].
 change (enc (RPair a1 a2)) with (L [Symbol "pair"; enc a1; enc a2]) in H.
 remember (enc a1) as A1 eqn:EA1; remember (enc a2) as A2 eqn:EA2. vm_compute in H.
 site R H constr:("kl:buri.literal?"). match goal with E : ask k _ [A1] = Some ?u1 |- _ =>
   rewrite EA1 in E; pose proof (IH a1 u1 E) as L1; clear E end.
 assert_site R H; [|left; injection H as <-; reflexivity].
 site R H constr:("kl:buri.literal?"). match goal with E : ask k _ [A2] = Some ?u2 |- _ =>
   rewrite EA2 in E; pose proof (IH a2 u2 E) as L2; clear E end.
 assert_site R H; injection H as <-; [|left; reflexivity].
 right; split; [destruct L1; [discriminate|assumption]|destruct L2; [discriminate|assumption]].
Qed.

(* KLambda structural equality (KLValue.kl_eq) on klambda.shen values: pairs
   left to right, a function value (closure, [function ...], thunk) is unequal
   to every non-function value, equality of two function values is undefined
   (None). The captured buri.equal computes exactly this (ask_equal_rv). *)
Definition fnv (v : rv) : bool := match v with
 | RClosure _ _ _ | RFunction _ _ | RThunk _ _ => true | _ => false end.
Fixpoint eqv (a b : rv) : option bool := match a, b with
 | RPair a1 a2, RPair b1 b2 => match eqv a1 b1 with Some true => eqv a2 b2 | r => r end
 | _, _ => if fnv a then (if fnv b then None else Some false)
   else if fnv b then Some false else Some (same (enc a) (enc b)) end.
Definition eqr (o : option bool) : value := match o with Some b => Boolean b | None => Symbol "unsupported" end.
Definition eq_spec (a b : rv) : verdict := match eqv a b with Some x => WRet (RBool x) | None => WUnsupported end.

Lemma ask_fnv : forall k a u, ask k "kl:buri.function-value?" [enc a] = Some u -> u = Boolean (fnv a).
Proof.
 intros [|k] a u H; [discriminate|]. rewrite (ask_unfold _ _ _ _ d_fnv_lk) in H.
 generalize dependent H; generalize (ask k) as rec; intros rec H.
 destruct a; vm_compute in H; injection H as <-; reflexivity.
Qed.
Ltac eqsite R H := match type of H with context [?rec "kl:=" ?xs] => is_var rec;
 let E := fresh "E" in let u := fresh "u" in destruct (rec "kl:=" xs) as [u|] eqn:E;
 [rewrite R in E; apply ask_equal in E; rewrite E in H; clear E u; vm_compute in H|vm_compute in H; discriminate] end.
Lemma ask_equal_leaf : forall k x y A B r, ask k "kl:buri.equal-leaf" [Boolean x; Boolean y; A; B] = Some r ->
 r = if x then (if y then Symbol "unsupported" else Boolean false)
     else if y then Boolean false else Boolean (same A B).
Proof.
 intros [|k] x y A B r H; [discriminate|]. rewrite (ask_unfold _ _ _ _ d_equal_leaf_lk) in H.
 remember (ask k) as rec eqn:R. destruct x, y; vm_compute in H; repeat eqsite R H;
 injection H as <-; reflexivity.
Qed.
Lemma ask_equal_pair : forall k u A B r, ask k "kl:buri.equal-pair" [u; A; B] = Some r ->
 (u = Boolean true /\ exists j, j < k /\ ask j "kl:buri.equal" [A; B] = Some r) \/ (u <> Boolean true /\ r = u).
Proof.
 intros [|k] u A B r H; [discriminate|]. rewrite (ask_unfold _ _ _ _ d_equal_pair_lk) in H.
 remember (ask k) as rec eqn:R.
 destruct u as [| | | | | | [|] | | |]; vm_compute in H; repeat eqsite R H;
 first [left; split; [reflexivity|exists k; split; [lia|subst rec; exact H]]
       |right; split; [discriminate|injection H as <-; reflexivity]].
Qed.
Lemma ask_eq_verdict : forall k o r, ask k "kl:buri.equality-verdict" [eqr o] = Some r ->
 r = enc_verdict (match o with Some x => WRet (RBool x) | None => WUnsupported end).
Proof.
 intros [|k] o r H; [discriminate|]. rewrite (ask_unfold _ _ _ _ d_eq_verdict_lk) in H.
 generalize dependent H; generalize (ask k) as rec; intros rec H.
 destruct o as [[|]|]; vm_compute in H; injection H as <-; reflexivity.
Qed.
Ltac fsite R H A B := match type of H with context [?rec "kl:buri.function-value?" ?xs] => is_var rec;
 let E := fresh "E" in let u := fresh "u" in destruct (rec "kl:buri.function-value?" xs) as [u|] eqn:E;
 [rewrite R in E; first [apply (ask_fnv _ A) in E | apply (ask_fnv _ B) in E]; rewrite E in H; clear E u; vm_compute in H
 |vm_compute in H; discriminate] end.
Ltac lsite R H := match type of H with context [?rec "kl:buri.equal-leaf" ?xs] => is_var rec;
 let E := fresh "E" in let u := fresh "u" in destruct (rec "kl:buri.equal-leaf" xs) as [u|] eqn:E;
 [rewrite R in E; apply ask_equal_leaf in E; rewrite E in H; clear E u|vm_compute in H; discriminate] end.
Lemma ask_equal_rv : forall k a b u, ask k "kl:buri.equal" [enc a; enc b] = Some u -> u = eqr (eqv a b).
Proof.
 intro k; induction k as [k IHk] using (well_founded_induction lt_wf). intros a b u H.
 destruct k as [|k]; [discriminate|]. rewrite (ask_unfold _ _ _ _ d_equal_fn_lk) in H.
 remember (ask k) as rec eqn:R.
 destruct a as [| | | | |a1 a2| | |]; destruct b as [| | | | |b1 b2| | |];
 match goal with |- _ = eqr (eqv ?A ?B) =>
 first [
   match A with RPair _ _ => match B with RPair _ _ => idtac end end
 | vm_compute in H; repeat fsite R H A B; lsite R H;
   injection H as <-; vm_compute; reflexivity ] end.
 change (enc (RPair a1 a2)) with (L [Symbol "pair"; enc a1; enc a2]) in H.
 change (enc (RPair b1 b2)) with (L [Symbol "pair"; enc b1; enc b2]) in H.
 remember (enc a1) as A1 eqn:EA1; remember (enc a2) as A2 eqn:EA2.
 remember (enc b1) as B1 eqn:EB1; remember (enc b2) as B2 eqn:EB2. vm_compute in H.
 destruct (rec "kl:buri.equal" [A1; B1]) as [u1|] eqn:E1; [|discriminate].
 rewrite R, EA1, EB1 in E1. apply (IHk k (le_n _)) in E1. subst u1.
 destruct (rec "kl:buri.equal-pair" _) as [u2|] eqn:E2; [|discriminate]. injection H as <-.
 rewrite R in E2. apply ask_equal_pair in E2. cbn [eqv].
 destruct (eqv a1 b1) as [[|]|]; cbn in E2 |- *;
 destruct E2 as [[U (j & L & E)]|[N ->]];
 first [discriminate U | (exfalso; apply N; reflexivity) | reflexivity
       | (rewrite EA2, EB2 in E; apply (IHk j) in E; [exact E|lia])].
Qed.

Lemma ask_prim_equal : forall k a b r, ask k "kl:buri.primitive" [Symbol "="; L [enc a; enc b]] = Some r ->
 r = enc_verdict (eq_spec a b).
Proof.
 intros [|k] a b r H; [discriminate|]. rewrite (ask_unfold _ _ _ _ d_primitive_lk) in H.
 remember (ask k) as rec eqn:R. remember (enc a) as A eqn:EA; remember (enc b) as B eqn:EB.
 vm_compute in H.
 destruct (rec "kl:buri.equal" [A; B]) as [u|] eqn:E; [|discriminate].
 rewrite R, EA, EB in E. apply ask_equal_rv in E. subst u. rewrite R in H.
 apply ask_eq_verdict in H. unfold eq_spec. exact H.
Qed.
End KLambdaEvaluatorPrimitives.
