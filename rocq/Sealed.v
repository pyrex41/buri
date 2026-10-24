(* Syntactic dependency closure for the actual lexical capsule. Library
   primitives and Chez lexical binding remain explicit native assumptions. *)
From Coq Require Import List String Bool.
From Buri Require Import Wire EncoderFrontend ObservedEncoder.
Import ListNotations.
Open Scope string_scope.
Module Sealed.
Import EncoderFrontend.EncoderFrontend.
Definition primitives := ["eqv?";"equal?";"null?";"pair?";"car";"cdr";
 "+";"-";"*";"/";">=";"<";"string-append";"string-ref";"string";"substring";
 "string-length";"char->integer";"integer?";"exact?";"number?";
 "floor";"boolean?";"symbol?";"symbol->string";"number->string";"error"].
Definition member s xs := existsb (String.eqb s) xs.
Fixpoint names xs := match xs with
 | [] => Some []
 | Sym s::xs => match names xs with Some ns => Some (s::ns) | _ => None end
 | _ => None end.
Definition join (a b : option (list string)) :=
 match a,b with Some x,Some y => Some (x++y)%list | _,_ => None end.
Fixpoint bindings xs := match xs with
 | [] => Some []
 | x::xs => match elements x,bindings xs with
   | Some [Sym s;e],Some bs => Some ((s,e)::bs) | _,_ => None end end.
(* Only the immutable expression forms below are admitted. Procedure bodies
   are traversed even when never called; there is no hidden callback body. *)
Fixpoint refs fuel scope e : option (list string) := match fuel with
 | O => None
 | S n =>
   let many := fix many xs := match xs with
     | [] => Some [] | x::xs => join (refs n scope x) (many xs) end in
   match e with
   | Num _ | TextNode _ => Some []
   | Sym s => Some (if member s scope then [] else [s])
   | _ => match elements e with
     | Some [Sym "quote";_] => Some []
     | Some [Sym "lambda";args;body] => match elements args with
       | Some xs => match names xs with
         | Some ns => refs n (ns++scope)%list body | _ => None end
       | _ => None end
     | Some [Sym "let";bs;body] => match elements bs with
       | Some xs => match bindings xs with
         | Some pairs => join (many (map snd pairs)) (refs n (map fst pairs++scope)%list body)
         | _ => None end | _ => None end
     | Some [Sym "let*";bs;body] => match elements bs with
       | Some xs => match bindings xs with
         | Some pairs =>
           (fix sequential ps sc := match ps with
            | [] => refs n sc body
            | (s,x)::ps => join (refs n sc x) (sequential ps (s::sc)) end) pairs scope
         | _ => None end | _ => None end
     | Some [Sym "letrec";bs;body] => match elements bs with
       | Some xs => match bindings xs with
         | Some pairs => let sc := (map fst pairs++scope)%list in
           join ((fix each ps := match ps with
             | [] => Some []
             | (_,x)::ps => match elements x with
               | Some [Sym "lambda";_;_] => join (refs n sc x) (each ps)
               | _ => None end end) pairs) (refs n sc body)
         | _ => None end | _ => None end
     | Some [Sym "if";c;a;b] => many [c;a;b]
     | Some (Sym "and"::xs) | Some (Sym "or"::xs) => many xs
     | Some (Sym s::xs) =>
       if member s ["lambda";"let";"let*";"letrec";"quote";"if";"set!";"define"]
       then None else many (Sym s::xs)
     | _ => None end end end.
Definition guard fuel e := match refs fuel [] e with
 | Some deps => forallb (fun s => member s primitives) deps | _ => false end.
Lemma member_exact : forall s xs, member s xs = true <-> In s xs.
Proof.
 intros s xs; unfold member; rewrite existsb_exists. split.
 - intros [x [I E]]. apply String.eqb_eq in E; subst; auto.
 - intro I; exists s; split; auto. apply String.eqb_refl.
Qed.
Theorem guard_sound : forall fuel e, guard fuel e = true ->
 exists deps, refs fuel [] e = Some deps /\ Forall (fun s => In s primitives) deps.
Proof.
 intros fuel e H; unfold guard in H. destruct (refs fuel [] e) as [ds|] eqn:R; try discriminate.
 exists ds; split; auto. apply Forall_forall; intros s I.
 apply forallb_forall with (x:=s) in H; auto. apply member_exact; exact H.
Qed.
Theorem guard_complete : forall fuel e deps,
 refs fuel [] e = Some deps -> Forall (fun s => In s primitives) deps -> guard fuel e = true.
Proof.
 intros fuel e ds R H; unfold guard; rewrite R. apply forallb_forall; intros s I.
 apply member_exact. rewrite Forall_forall in H; auto.
Qed.
(* Dependency resolution is invariant under arbitrary changes outside the
   admitted library boundary. This is not a theorem about Chez machine code. *)
Theorem resolution_noninterference : forall (V : Type) fuel e deps (before after : string -> V),
 guard fuel e = true -> refs fuel [] e = Some deps ->
 (forall s, In s primitives -> before s = after s) ->
 map before deps = map after deps.
Proof.
 intros V fuel e ds a b G R H. destruct (guard_sound _ _ G) as [xs [E F]].
 rewrite R in E; inversion E; subst. apply map_ext_in; intros s I.
 apply H. rewrite Forall_forall in F; auto.
Qed.
Theorem no_dynamic_authority : forall fuel e deps,
 guard fuel e = true -> refs fuel [] e = Some deps ->
 ~ In "eval" deps /\ ~ In "set!" deps /\ ~ In "interaction-environment" deps /\
 ~ In "shen-global-get" deps /\ ~ In "fork-thread" deps.
Proof.
 intros fuel e ds G R. destruct (guard_sound _ _ G) as [xs [E F]].
 rewrite R in E; inversion E; subst. rewrite Forall_forall in F.
 assert (N : forall s, member s primitives = false -> ~ In s xs).
 { intros s M I; apply F in I; apply member_exact in I; congruence. }
 repeat split; apply N; reflexivity.
Qed.
End Sealed.

Module SealedCapture.
Import EncoderFrontend.EncoderFrontend.
Definition L := fold_right Pair Nil.
Fixpoint node_eqb a b := match a,b with
 | Nil,Nil => true
 | Sym s,Sym t | TextNode s,TextNode t => String.eqb s t
 | Num n,Num m => Nat.eqb n m
 | Pair a b,Pair c d => node_eqb a c && node_eqb b d
 | _,_ => false end.
Theorem node_eqb_sound : forall a b, node_eqb a b = true -> a = b.
Proof.
 induction a; destruct b; cbn; intro H; try discriminate; try reflexivity;
 try (apply String.eqb_eq in H; subst; reflexivity);
 try (apply PeanoNat.Nat.eqb_eq in H; subst; reflexivity).
 apply andb_true_iff in H as [H1 H2]; f_equal; auto.
Qed.
Definition binding pair := match elements pair with
 | Some [_;target] => match elements target with
   | Some [Sym "define";Pair (Sym name) args;body] => Some (L [Sym name;L [Sym "lambda";args;body]])
   | _ => None end | _ => None end.
Definition targets root := match elements root with
 | Some [a;b;c] => match binding a,binding b,binding c with
   | Some x,Some y,Some z => Some (L [x;y;z]) | _,_,_ => None end
 | _ => None end.
Definition app s xs := L (Sym s::xs).
Definition lam args body := app "lambda" [L (map Sym args);body].
(* The shims are pinned as syntax too: an attacker cannot shadow a primitive
   or substitute another body while retaining a closed dependency graph. *)
Definition helper_template := L [
 L [Sym "non-rational-/";lam ["x";"y"] (app "/" [Sym "x";Sym "y"])];
 L [Sym "kl:floor";lam ["x"] (app "floor" [Sym "x"])];
 L [Sym "kl:=";lam ["x";"y"] (app "equal?" [Sym "x";Sym "y"])];
 L [Sym "kl:_scm.assert-boolean";lam ["x"]
   (app "if" [app "boolean?" [Sym "x"];Sym "x";
     app "error" [app "quote" [Sym "sealed-encoder"];TextNode "Expected boolean"]])];
 L [Sym "kl:buri.exact-integer?";lam ["x"]
   (app "and" [app "number?" [Sym "x"];app "integer?" [Sym "x"];app "exact?" [Sym "x"]])];
 L [Sym "kl:symbol?";lam ["x"] (app "symbol?" [Sym "x"])];
 L [Sym "kl:str";lam ["x"] (app "if" [app "symbol?" [Sym "x"];
   app "symbol->string" [Sym "x"];app "number->string" [Sym "x";Num 10]])]].
Definition linked capsule records := match elements capsule,targets records with
 | Some [head;bs;entry],Some ts => match elements bs with
   | Some all => node_eqb head (Sym "letrec") && node_eqb entry (Sym "kl:buri.wire") &&
       node_eqb (L (firstn 7 all)) helper_template && node_eqb (L (skipn 7 all)) ts
   | _ => false end | _,_ => false end.
Theorem linked_exact : forall capsule records, linked capsule records = true ->
 exists bs all ts, elements capsule = Some [Sym "letrec";bs;Sym "kl:buri.wire"] /\
 elements bs = Some all /\ targets records = Some ts /\
 L (firstn 7 all) = helper_template /\ L (skipn 7 all) = ts.
Proof.
 intros c r H; unfold linked in H.
 destruct (elements c) as [xs|] eqn:C; try discriminate.
 destruct xs as [|a [|b [|d [|extra rest]]]]; try discriminate.
 destruct (targets r) as [ts|] eqn:T; try discriminate.
 destruct (elements b) as [bs|] eqn:B; try discriminate.
 apply andb_true_iff in H as [H E]. apply andb_true_iff in H as [H HT].
 apply andb_true_iff in H as [A D].
 apply node_eqb_sound in A; apply node_eqb_sound in D; subst.
 exists b,bs,ts; repeat split; auto; apply node_eqb_sound; assumption.
Qed.
Definition syntax := ["lambda";"let";"let*";"letrec";"if";"and";"or";"quote"].
Definition imports := L (map Sym (syntax ++ Sealed.primitives)%list).
Definition unpack bits := match Wire.decode_text bits with
 | Some (Wire.Cons (Wire.Atom false "buri-sealed-1") (Wire.Cons tagged Wire.Nil)) =>
   EncoderFrontend.untag 300 tagged
 | _ => None end.
Definition check bits := match unpack bits with
 | Some root => match elements root with
   | Some [capsule;records;imps] =>
     match ObservedEncoder.check_program 300 records with
     | Some _ => Sealed.guard 300 capsule && linked capsule records && node_eqb imps imports
     | _ => false end
   | _ => false end | _ => false end.
Theorem check_sound : forall bits, check bits = true ->
 exists root capsule records sp tp deps,
 unpack bits = Some root /\ elements root = Some [capsule;records;imports] /\
 ObservedEncoder.check_program 300 records = Some (sp,tp) /\
 linked capsule records = true /\
 Sealed.refs 300 [] capsule = Some deps /\
 Forall (fun s => In s Sealed.primitives) deps /\
 EncoderNames.EncoderNames.program_resolves sp /\ ObservedEncoder.target_resolves tp.
Proof.
 intros bits H; unfold check in H.
 destruct (unpack bits) as [root|] eqn:U; try discriminate.
 destruct (elements root) as [xs|] eqn:E; try discriminate.
 destruct xs as [|c [|r [|i [|extra rest]]]]; try discriminate.
 destruct (ObservedEncoder.check_program 300 r) as [[sp tp]|] eqn:P; try discriminate.
 apply andb_true_iff in H as [H I]; apply andb_true_iff in H as [G K].
 apply node_eqb_sound in I; subst.
 destruct (Sealed.guard_sound _ _ G) as [deps [R F]].
 pose proof (ObservedEncoder.check_program_coverage _ _ _ _ P) as C.
 destruct (ObservedEncoder.coverage_resolves _ _ _ _ C) as [S T].
 exists root,c,r,sp,tp,deps; repeat split; auto.
Qed.
End SealedCapture.
