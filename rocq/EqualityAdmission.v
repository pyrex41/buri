(* Rejecting typed admission for inert, axiom-free certificate data. The
   reader never evaluates source, names, rules, macros, or native procedures. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Equality Native NativeRuntime EqualityCoreCorrect.
Import ListNotations.
Module EqualityAdmission.
Import Native.Native.
Module C := EqualityCoreCorrect.EqualityCoreCorrect.
Open Scope string_scope.
Definition natural z := if Z.leb 0 z then Some (Z.to_nat z) else None.
Fixpoint read_term fuel raw := match fuel with
 | O=>None
 | S n=>match elements raw with
   | Some (Symbol tag::args)=>
     if String.eqb tag "var" then match args with [Integer z]=>option_map Equality.Var (natural z)|_=>None end
     else if String.eqb tag "const" then match args with [Integer z]=>option_map Equality.Const (natural z)|_=>None end
     else if String.eqb tag "app" then match args with [a;b]=>match read_term n a,read_term n b with
       | Some a,Some b=>Some (Equality.App a b)|_,_=>None end|_=>None end
     else None
   | _=>None end end.
Fixpoint read_certificate fuel raw := match fuel with
 | O=>None
 | S n=>match elements raw with
   | Some (Symbol tag::args)=>
     if String.eqb tag "refl" then match args with [a]=>option_map Refl (read_term n a)|_=>None end
     else if String.eqb tag "sym" then match args with [p]=>option_map Sym (read_certificate n p)|_=>None end
     else if String.eqb tag "trans" then match args with [p;q]=>match read_certificate n p,read_certificate n q with
       | Some p,Some q=>Some (Trans p q)|_,_=>None end|_=>None end
     else if String.eqb tag "cong" then match args with [p;q]=>match read_certificate n p,read_certificate n q with
       | Some p,Some q=>Some (Cong p q)|_,_=>None end|_=>None end
     else None
   | _=>None end end.
Lemma elements_canonical : forall v xs, elements v=Some xs -> v=L xs.
Proof.
 induction v; intros xs H; cbn [elements] in H; try discriminate.
 - inversion H;reflexivity.
 - destruct (elements v2) eqn:E; try discriminate. inversion H;subst.
   cbn [L fold_right]; rewrite (IHv2 _ eq_refl); reflexivity.
Qed.
Lemma natural_canonical : forall z n, natural z=Some n -> z=Z.of_nat n.
Proof.
 intros z n; unfold natural; destruct (Z.leb 0 z) eqn:E; try discriminate.
 intro H; inversion H;subst; apply Z.leb_le in E; rewrite Z2Nat.id by assumption; reflexivity.
Qed.
Theorem read_term_canonical : forall fuel raw t, read_term fuel raw=Some t -> raw=C.term t.
Proof.
 induction fuel as [|fuel IH]; intros raw t H; [discriminate|].
 cbn [read_term] in H. destruct (elements raw) as [xs|] eqn:E; [|discriminate].
 apply elements_canonical in E; subst raw.
 destruct xs as [|tag args]; [discriminate|]. destruct tag; try discriminate.
 destruct (String.eqb s "var") eqn:V.
 - apply String.eqb_eq in V; subst s.
   destruct args as [|a [|b args]]; try discriminate; destruct a; try discriminate.
   destruct (natural z) eqn:N; try discriminate. inversion H;subst t.
   cbn [C.term]. rewrite (natural_canonical _ _ N); reflexivity.
 - destruct (String.eqb s "const") eqn:K.
   + apply String.eqb_eq in K; subst s.
     destruct args as [|a [|b args]]; try discriminate; destruct a; try discriminate.
     destruct (natural z) eqn:N; try discriminate. inversion H;subst t.
     cbn [C.term]. rewrite (natural_canonical _ _ N); reflexivity.
   + destruct (String.eqb s "app") eqn:A; [|discriminate].
     apply String.eqb_eq in A; subst s.
     destruct args as [|a [|b [|extra args]]]; try discriminate.
     destruct (read_term fuel a) eqn:RA; try discriminate.
     destruct (read_term fuel b) eqn:RB; try discriminate.
     inversion H;subst t. rewrite (IH _ _ RA),(IH _ _ RB); reflexivity.
Qed.
Theorem read_certificate_canonical : forall fuel raw p,
 read_certificate fuel raw=Some p -> raw=C.certificate p.
Proof.
 induction fuel as [|fuel IH]; intros raw p H; [discriminate|].
 cbn [read_certificate] in H. destruct (elements raw) as [xs|] eqn:E; [|discriminate].
 apply elements_canonical in E; subst raw.
 destruct xs as [|tag args]; [discriminate|]. destruct tag; try discriminate.
 destruct (String.eqb s "refl") eqn:R.
 - apply String.eqb_eq in R; subst s; destruct args as [|a [|b args]]; try discriminate.
   destruct (read_term fuel a) eqn:A; try discriminate. inversion H;subst p.
   rewrite (read_term_canonical _ _ _ A); reflexivity.
 - destruct (String.eqb s "sym") eqn:S.
   + apply String.eqb_eq in S; subst s; destruct args as [|a [|b args]]; try discriminate.
     destruct (read_certificate fuel a) eqn:A; try discriminate. inversion H;subst p.
     rewrite (IH _ _ A); reflexivity.
   + destruct (String.eqb s "trans") eqn:T.
     * apply String.eqb_eq in T; subst s; destruct args as [|a [|b [|extra args]]]; try discriminate.
       destruct (read_certificate fuel a) eqn:A; try discriminate.
       destruct (read_certificate fuel b) eqn:B; try discriminate. inversion H;subst p.
       rewrite (IH _ _ A),(IH _ _ B); reflexivity.
     * destruct (String.eqb s "cong") eqn:G; [|discriminate].
       apply String.eqb_eq in G; subst s; destruct args as [|a [|b [|extra args]]]; try discriminate.
       destruct (read_certificate fuel a) eqn:A; try discriminate.
       destruct (read_certificate fuel b) eqn:B; try discriminate. inversion H;subst p.
       rewrite (IH _ _ A),(IH _ _ B); reflexivity.
Qed.
Fixpoint term_depth t := match t with Equality.App a b=>S (Nat.max (term_depth a) (term_depth b))|_=>1 end.
Fixpoint certificate_depth p := match p with
 | Refl t=>S (term_depth t) | Sym p=>S (certificate_depth p)
 | Trans p q | Cong p q=>S (Nat.max (certificate_depth p) (certificate_depth q))
 | Instance _ _=>1 end.
Fixpoint axiom_free p := match p with
 | Refl _=>true | Sym p=>axiom_free p | Trans p q | Cong p q=>axiom_free p && axiom_free q
 | Instance _ _=>false end.
Lemma natural_roundtrip : forall n, natural (Z.of_nat n)=Some n.
Proof.
 intro; unfold natural; assert (Z.leb 0 (Z.of_nat n)=true) as H by (apply Z.leb_le;lia).
 rewrite H,Nat2Z.id; reflexivity.
Qed.
Theorem term_admission_complete : forall t fuel, term_depth t<=fuel -> read_term fuel (C.term t)=Some t.
Proof.
 induction t; intros [|fuel] B; cbn [term_depth] in B; try lia;
 cbn [C.term read_term elements L fold_right String.eqb Ascii.eqb Bool.eqb andb].
 - rewrite natural_roundtrip; reflexivity.
 - rewrite natural_roundtrip; reflexivity.
 - rewrite IHt1,IHt2 by lia; reflexivity.
Qed.
Theorem certificate_admission_complete : forall p fuel,
 axiom_free p=true -> certificate_depth p<=fuel -> read_certificate fuel (C.certificate p)=Some p.
Proof.
 induction p; intros [|fuel] A B; cbn [certificate_depth] in B; try lia;
 cbn [axiom_free] in A; try discriminate;
 cbn [C.certificate read_certificate elements L fold_right String.eqb Ascii.eqb Bool.eqb andb].
 - rewrite term_admission_complete by lia; reflexivity.
 - rewrite IHp by (assumption||lia); reflexivity.
 - apply Bool.andb_true_iff in A; destruct A. rewrite IHp1,IHp2 by (assumption||lia);reflexivity.
 - apply Bool.andb_true_iff in A; destruct A. rewrite IHp1,IHp2 by (assumption||lia);reflexivity.
Qed.
Theorem admitted_native_checker_sound : forall (D:Type) (constants:nat->D) (application:D->D->D)
 fuel raw p steps a b,
 read_certificate fuel raw=Some p ->
 NativeRuntime.invoke steps C.program "kl:buri.eq2-derive" [raw]=Returned (C.result_value (Some (a,b))) ->
 forall rho, @denote D constants application rho a=@denote D constants application rho b.
Proof.
 intros D constants application fuel raw p steps a b A E.
 apply read_certificate_canonical in A; subst raw.
 eapply C.actual_checker_sound; exact E.
Qed.
Fixpoint value_size v : nat := match v with Pair a b=>S (value_size a+value_size b)|_=>1 end.
Lemma term_depth_size : forall t, term_depth t<=value_size (C.term t).
Proof. induction t; cbn [term_depth C.term L fold_right value_size]; lia. Qed.
Lemma certificate_depth_size : forall p, certificate_depth p<=value_size (C.certificate p).
Proof.
 induction p; cbn [certificate_depth C.certificate L fold_right value_size]; try lia.
 pose proof (term_depth_size t); lia.
Qed.
Theorem read_certificate_axiom_free : forall fuel raw p,
 read_certificate fuel raw=Some p -> axiom_free p=true.
Proof.
 induction fuel as [|fuel IH]; intros raw p H; [discriminate|].
 cbn [read_certificate] in H. destruct (elements raw) as [xs|]; [|discriminate].
 destruct xs as [|tag args]; [discriminate|]. destruct tag; try discriminate.
 destruct (String.eqb s "refl").
 - destruct args as [|a [|b args]]; try discriminate.
   destruct (read_term fuel a); inversion H;reflexivity.
 - destruct (String.eqb s "sym").
   + destruct args as [|a [|b args]]; try discriminate.
     destruct (read_certificate fuel a) eqn:A; try discriminate; inversion H;subst.
     apply (IH _ _ A).
   + destruct (String.eqb s "trans").
     * destruct args as [|a [|b [|extra args]]]; try discriminate.
       destruct (read_certificate fuel a) eqn:A; try discriminate.
       destruct (read_certificate fuel b) eqn:B; try discriminate; inversion H;subst.
       cbn [axiom_free]; rewrite (IH _ _ A),(IH _ _ B);reflexivity.
     * destruct (String.eqb s "cong"); [|discriminate].
       destruct args as [|a [|b [|extra args]]]; try discriminate.
       destruct (read_certificate fuel a) eqn:A; try discriminate.
       destruct (read_certificate fuel b) eqn:B; try discriminate; inversion H;subst.
       cbn [axiom_free]; rewrite (IH _ _ A),(IH _ _ B);reflexivity.
Qed.
Definition admit raw := read_certificate (value_size raw) raw.
Theorem admission_decision_complete : forall raw fuel p,
 read_certificate fuel raw=Some p -> admit raw=Some p.
Proof.
 intros raw fuel p H; pose proof (read_certificate_axiom_free _ _ _ H) as A.
 apply read_certificate_canonical in H; subst raw; unfold admit.
 apply certificate_admission_complete; [exact A|apply certificate_depth_size].
Qed.
Inductive verdict := AcceptedEquation (a b:Equality.term) | OutsideCertificateProfile | InvalidDerivation.
Definition check_raw raw := match admit raw with
 | None=>OutsideCertificateProfile
 | Some p=>match check [] p with Some (a,b)=>AcceptedEquation a b|None=>InvalidDerivation end end.
Theorem raw_acceptance_sound : forall (D:Type) (constants:nat->D) (application:D->D->D) raw a b,
 check_raw raw=AcceptedEquation a b ->
 forall rho, @denote D constants application rho a=@denote D constants application rho b.
Proof.
 intros D constants application raw a b H; unfold check_raw in H.
 destruct (admit raw); [|discriminate]. destruct (check [] c) as [[x y]|] eqn:E; [|discriminate].
 inversion H;subst; eapply (@check_sound_under_rules D constants application []);
 [intros x y I;inversion I|exact E].
Qed.
Theorem admitted_native_agreement : forall raw p,
 admit raw=Some p -> exists steps,
 NativeRuntime.invoke steps C.program "kl:buri.eq2-derive" [raw]=Returned (C.result_value (check [] p)).
Proof.
 intros raw p H; unfold admit in H; apply read_certificate_canonical in H;subst raw;apply C.checker_machine.
Qed.
End EqualityAdmission.
