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

Lemma ask_prim_equal : forall k a b r, ask k "kl:buri.primitive" [Symbol "="; L [enc a; enc b]] = Some r ->
 r = enc_verdict WUnsupported \/
 (data a /\ data b /\ r = enc_verdict (WRet (RBool (same (enc a) (enc b))))).
Proof.
 intros [|k] a b r H; [discriminate|]. rewrite (ask_unfold _ _ _ _ d_primitive_lk) in H.
 remember (ask k) as rec eqn:R. remember (enc a) as A eqn:EA; remember (enc b) as B eqn:EB.
 vm_compute in H.
 site R H constr:("kl:buri.literal?"). match goal with E : ask k _ [A] = Some ?u1 |- _ =>
   rewrite EA in E; pose proof (ask_literal k a u1 E) as L1; clear E end.
 assert_site R H; [|left; injection H as <-; reflexivity].
 site R H constr:("kl:buri.literal?"). match goal with E : ask k _ [B] = Some ?u2 |- _ =>
   rewrite EB in E; pose proof (ask_literal k b u2 E) as L2; clear E end.
 assert_site R H; [|left; injection H as <-; reflexivity].
 site R H constr:("kl:="). match goal with E : ask k "kl:=" [A; B] = Some ?q |- _ =>
   pose proof (ask_equal k A B q E) as Q; clear E; subst q end.
 right. split; [destruct L1; [discriminate|assumption]|split; [destruct L2; [discriminate|assumption]|]].
 injection H as <-. subst A B. vm_compute. reflexivity.
Qed.
End KLambdaEvaluatorPrimitives.
