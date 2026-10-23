(* Formal admitted grammar and generic validator for captured source/output
   data. Neither de Bruijn indices nor semantic claims come from an exporter. *)
From Coq Require Import List ListDec String Ascii ZArith.
From Buri Require Import NativeArithmetic Wire Resolve Normalize.
Import ListNotations.
Open Scope string_scope.
Module NativeValidation.
Import Wire.Wire Resolve.Resolve.

Definition digit c : option Z :=
 let n := nat_of_ascii c in
 if andb (Nat.leb 48 n) (Nat.leb n 57) then Some (Z.of_nat (n-48)) else None.
Fixpoint digits (s : string) (acc : Z) : option Z :=
 match s with
 | EmptyString => Some acc
 | String c rest => match digit c with Some d => digits rest (10*acc+d)%Z | None => None end
 end.
Definition integer s : option Z :=
 match s with
 | EmptyString => None
 | String c rest =>
   if ascii_dec c "-"%char then
     match rest with EmptyString => None | _ => match digits rest 0 with Some z => Some (-z)%Z | None => None end end
   else digits s 0
 end.
Definition letter c := let n := nat_of_ascii c in
 orb (andb (Nat.leb 65 n) (Nat.leb n 90)) (andb (Nat.leb 97 n) (Nat.leb n 122)).
Definition initial c := orb (letter c) (Ascii.eqb c "_"%char).
Definition subsequent c := orb (initial c)
 (orb (Ascii.eqb c "."%char) (orb (Ascii.eqb c "-"%char)
  (andb (Nat.leb 48 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 57)))).
Fixpoint name_tail s := match s with EmptyString => true | String c rest => andb (subsequent c) (name_tail rest) end.
Definition name_ok s := match s with
 | EmptyString => false
 | String c rest => andb (initial c) (andb (name_tail rest)
    (negb (existsb (String.eqb s) ["true";"false";"let";"let*";"lambda";"if";"cond";"and";"or";"trap-error";"freeze";"thaw";"defun"])))
 end.
Inductive language := KLambda | Scheme.
Definition combine (op : named -> named -> named) (a b : option named) :=
 match a,b with Some av,Some bv => Some (op av bv) | _,_ => None end.

Fixpoint decode_expr fuel lang d : option named :=
 match fuel with
 | O => None
 | S n => match d with
   | Atom true text => match integer text with Some z => Some (Num z) | None => None end
   | Atom false x => if name_ok x then Some (Name x) else None
   | Cons (Atom false op) args =>
     match op,args with
     | "+", Cons a (Cons b Nil) => combine Plus (decode_expr n lang a) (decode_expr n lang b)
     | "-", Cons a (Cons b Nil) => combine Minus (decode_expr n lang a) (decode_expr n lang b)
     | "*", Cons a (Cons b Nil) => combine Times (decode_expr n lang a) (decode_expr n lang b)
     | "let", Cons (Atom false x) (Cons a (Cons b Nil)) =>
         match lang with KLambda => if name_ok x then combine (Let x) (decode_expr n lang a) (decode_expr n lang b) else None | _ => None end
     | "let", Cons (Cons (Cons (Atom false x) (Cons a Nil)) Nil) (Cons b Nil) =>
         match lang with Scheme => if name_ok x then combine (Let x) (decode_expr n lang a) (decode_expr n lang b) else None | _ => None end
     | "let*", Cons bindings (Cons body Nil) =>
         match lang with Scheme => decode_bindings n bindings body | _ => None end
     | _,_ => None
     end
   | _ => None end
 end
with decode_bindings fuel bindings body : option named :=
 match fuel with
 | O => None
 | S n => match bindings with
   | Nil => decode_expr n Scheme body
   | Cons (Cons (Atom false x) (Cons a Nil)) rest =>
       if name_ok x then combine (Let x) (decode_expr n Scheme a) (decode_bindings n rest body) else None
   | _ => None end
 end.
Fixpoint decode_scope d : option (list string) :=
 match d with
 | Nil => Some []
 | Cons (Atom false x) rest =>
   if name_ok x then match decode_scope rest with Some xs => Some (x::xs) | None => None end else None
 | _ => None end.
Record entry := Entry {
 label : string; scope : list string; source : named; target : named
}.
Fixpoint unique_names names : bool :=
 match names with
 | [] => true
 | x::rest => if existsb (String.eqb x) rest then false else unique_names rest
 end.
Theorem unique_names_sound : forall names,
 unique_names names = true -> NoDup names.
Proof.
 induction names as [|x rest IH]; intro H; [constructor|].
 cbn in H. destruct (existsb (String.eqb x) rest) eqn:E; try discriminate.
 constructor; [|apply IH; exact H]. intro Member.
 assert (existsb (String.eqb x) rest = true) as Impossible.
 { apply existsb_exists. exists x; split; [exact Member|apply String.eqb_refl]. }
 congruence.
Qed.
Definition decode_record fuel d : option entry :=
 match d with
 | Cons (Atom false name) (Cons inputs (Cons src (Cons dst Nil))) =>
   match decode_scope inputs, decode_expr fuel KLambda src, decode_expr fuel Scheme dst with
   | Some names,Some a,Some b =>
     if unique_names names then Some (Entry name names a b) else None
   | _,_,_ => None end
 | _ => None end.
Fixpoint kexpr_eq_dec (a b : kexpr) : {a=b}+{a<>b}.
Proof. decide equality; try apply Nat.eq_dec; try apply Z.eq_dec. Defined.
Definition agrees names a b : bool :=
 match resolve names a, resolve names b with
 | Some x,Some y => if Normalize.Normalize.arithmetic_eq_dec (Normalize.Normalize.normalize x) (Normalize.Normalize.normalize y) then true else false
 | _,_ => false end.
Theorem agrees_sound : forall names a b,
 agrees names a b = true -> forall env, meaning env a = meaning env b.
Proof.
 intros names a b H; unfold agrees in H.
 destruct (resolve names a) as [x|] eqn:A; try discriminate.
 destruct (resolve names b) as [y|] eqn:B; try discriminate.
 destruct (Normalize.Normalize.arithmetic_eq_dec (Normalize.Normalize.normalize x) (Normalize.Normalize.normalize y)); try discriminate.
 intros env.
 rewrite <- (resolve_named_meaning _ _ _ env A), <- (resolve_named_meaning _ _ _ env B).
 apply Normalize.Normalize.normal_equal_sound; assumption.
Qed.
Definition entry_sound e := forall env, meaning env (source e) = meaning env (target e).
Definition check_record fuel raw :=
 match decode_record fuel raw with
 | Some e => if agrees (scope e) (source e) (target e) then Some e else None
 | None => None end.
Theorem check_record_sound : forall fuel raw e,
 check_record fuel raw = Some e -> entry_sound e.
Proof.
 intros fuel raw e H; unfold check_record in H.
 destruct (decode_record fuel raw) as [v|]; try discriminate.
 destruct (agrees (scope v) (source v) (target v)) eqn:E; try discriminate.
 inversion H; subst. unfold entry_sound. eapply agrees_sound; exact E.
Qed.
Fixpoint check_records fuel raw : option (list entry) :=
 match raw with
 | Nil => Some []
 | Cons head tail =>
   match check_record fuel head, check_records fuel tail with
   | Some e,Some es => Some (e::es) | _,_ => None end
 | _ => None end.
Fixpoint list_data (ds : list datum) := match ds with [] => Nil | d::rest => Cons d (list_data rest) end.
Theorem check_records_exact : forall fuel raw es,
 check_records fuel raw = Some es ->
 exists ds, raw = list_data ds /\ Forall2 (fun d e => check_record fuel d = Some e) ds es.
Proof.
 intros fuel raw; induction raw; intros es H; try discriminate.
 - inversion H; subst. exists []; split; constructor.
 - cbn in H. destruct (check_record fuel raw1) as [e|] eqn:E; try discriminate.
   destruct (check_records fuel raw2) as [rest|] eqn:R; try discriminate.
   inversion H; subst. destruct (IHraw2 _ eq_refl) as [ds [Eq Rel]].
   exists (raw1::ds); split; [simpl; congruence|constructor; assumption].
Qed.
Theorem check_records_sound : forall fuel raw es,
 check_records fuel raw = Some es -> Forall entry_sound es.
Proof.
 intros fuel raw; induction raw; intros es H; try discriminate.
 - inversion H; constructor.
 - cbn in H. destruct (check_record fuel raw1) as [e|] eqn:E; try discriminate.
   destruct (check_records fuel raw2) as [rest|] eqn:R; try discriminate.
   inversion H; subst. constructor.
   + eapply check_record_sound; exact E.
   + apply IHraw2; reflexivity.
Qed.
Definition capture_records raw : option datum :=
 match raw with
 | Cons (Atom false profile) (Cons records Nil) =>
   if String.eqb profile "buri-native-1" then Some records else None
 | _ => None end.
Definition check_capture fuel bits : option (datum * list entry) :=
 match decode_text bits with
 | Some raw => match capture_records raw with
   | Some records => match check_records fuel records with
                    | Some es => Some (raw,es) | None => None end
   | None => None end
 | None => None end.
Theorem check_capture_sound : forall fuel bits raw es,
 check_capture fuel bits = Some (raw,es) ->
 capture raw = bits /\ Forall entry_sound es.
Proof.
 intros fuel bits raw es H. unfold check_capture in H.
 destruct (decode_text bits) as [d|] eqn:E; try discriminate.
 destruct (capture_records d) as [records|] eqn:P; try discriminate.
 destruct (check_records fuel records) as [entries|] eqn:C; try discriminate.
 inversion H; subst; split.
 - apply capture_exact; exact E.
 - eapply check_records_sound; exact C.
Qed.
Lemma capture_records_shape : forall raw records,
 capture_records raw = Some records ->
 raw = Cons (Atom false "buri-native-1") (Cons records Nil).
Proof.
 intros raw records H; destruct raw as [|tag text|head tail]; try discriminate.
 destruct head as [|tag text|]; try discriminate. destruct tag; try discriminate.
 destruct tail as [|tag text2|head2 tail2]; try discriminate.
 destruct tail2; try discriminate. cbn in H.
 destruct (String.eqb text "buri-native-1") eqn:E; try discriminate.
 apply String.eqb_eq in E; subst. inversion H; reflexivity.
Qed.
Theorem check_capture_complete_record_coverage : forall fuel bits raw es,
 check_capture fuel bits = Some (raw,es) ->
 exists ds, raw = Cons (Atom false "buri-native-1") (Cons (list_data ds) Nil) /\
 Forall2 (fun d e => check_record fuel d = Some e) ds es.
Proof.
 intros fuel bits raw es H. unfold check_capture in H.
 destruct (decode_text bits) as [d|] eqn:E; try discriminate.
 destruct (capture_records d) as [records|] eqn:P; try discriminate.
 destruct (check_records fuel records) as [entries|] eqn:C; try discriminate.
 inversion H; subst. destruct (check_records_exact _ _ _ C) as [ds [Eq Rel]].
 exists ds; split; auto. apply capture_records_shape in P. rewrite Eq in P. exact P.
Qed.
Definition count_ok fuel bits count : bool :=
 match check_capture fuel bits with Some (_, es) => Nat.eqb (List.length es) count | None => false end.
Theorem checked_count_sound : forall fuel bits count,
 count_ok fuel bits count = true -> exists raw es,
 check_capture fuel bits = Some (raw,es) /\ List.length es = count /\
 capture raw = bits /\ Forall entry_sound es.
Proof.
 intros fuel bits count H; unfold count_ok in H.
 destruct (check_capture fuel bits) as [[raw es]|] eqn:E; try discriminate.
 apply Nat.eqb_eq in H. exists raw, es; split; [reflexivity|]; split; [exact H|].
 eapply check_capture_sound; exact E.
Qed.
Theorem checked_count_coverage : forall fuel bits count,
 count_ok fuel bits count = true -> exists raw es ds,
 check_capture fuel bits = Some (raw,es) /\ List.length es = count /\
 raw = Cons (Atom false "buri-native-1") (Cons (list_data ds) Nil) /\
 Forall2 (fun d e => check_record fuel d = Some e) ds es.
Proof.
 intros fuel bits count H.
 destruct (checked_count_sound _ _ _ H) as [raw [es [Accepted [Count _]]]].
 destruct (check_capture_complete_record_coverage _ _ _ _ Accepted) as [ds [Shape All]].
 exists raw, es, ds; auto.
Qed.
End NativeValidation.
