(* E2E-17, Shen-Scheme wrappers: body proofs of the ACTUAL pinned definitions
   of kl:_scm.assert-boolean and kl:= (tizoc/shen-scheme 8d261518,
   src/primitives.scm blob 92b8875a, raise-error from src/chez-prelude.scm blob
   18d1ce9a). The exact bytes are packaged in PrimitiveSources.v, read by the
   independent PortReader, decoded here and admitted by computed equality with
   the reviewed expected AST. The theorems quantify over EVERY host operation
   table satisfying the individually named Chez contracts in
   [chez_equality_ops] / [chez_assert_ops]; those host operations remain
   owned by E2E-21/E2E-24 (docs/PRIMITIVES.md). The vector branch of kl:=
   (vector=?, a do loop) is captured but not decoded: it is unreachable on the
   first-order data domain proved here and remains open for the heap model. *)
From Coq Require Import String List ZArith Bool Ascii Lia.
From Buri Require Import Native ObserverEffects PortReader PrimitiveSources Observation KLSyntax KLValue KLSemantics.
From Buri Require CLLowering.
Import ListNotations.
Module SchemeWrappers.
Import Native.Native ObserverEffects.ObserverEffects.
Module R := PortReader.PortReader.
Open Scope string_scope.

(* ---------- Decoding of the admitted Scheme subset ---------- *)
Fixpoint digits_val (s : string) (acc : Z) : option Z := match s with
 | EmptyString => Some acc
 | String c r => if R.digit c then digits_val r (acc * 10 + Z.of_nat (nat_of_ascii c - 48))%Z else None end.
Definition zparse (s : string) : option Z := match s with
 | String c r => if Ascii.eqb c "-" then option_map Z.opp (digits_val r 0) else digits_val s 0
 | EmptyString => None end.
Fixpoint datum (d : CLLowering.sv) : option value := match d with
 | CLLowering.VNil => Some Nil
 | CLLowering.VSym s => Some (if String.eqb s "#t" then Boolean true else if String.eqb s "#f" then Boolean false else Symbol s)
 | CLLowering.VStr s => Some (Text s)
 | CLLowering.VNum s => option_map Integer (zparse s)
 | CLLowering.VCons a b => match datum a, datum b with Some x, Some y => Some (Pair x y) | _, _ => None end
 | CLLowering.VObj _ => None end.
(* Heads that are Scheme syntax outside the admitted subset: never a call. *)
Definition unsupported_head h := existsb (String.eqb h)
 ["define"; "define-syntax"; "do"; "lambda"; "set!"; "case"; "guard"; "let*"; "letrec"; "begin"; "when"; "unless"].
Fixpoint expr_of (fuel : nat) (d : CLLowering.sv) {struct fuel} : option expr := match fuel with
 | O => None
 | S n =>
   let many := fix many xs := match xs with
     | [] => Some [] | x :: xs => match expr_of n x, many xs with Some e, Some es => Some (e :: es) | _, _ => None end end in
   let conj := fix conj (unit : bool) (mk : expr -> expr -> expr) es := match es with
     | [] => Lit (Boolean unit) | [e] => e | e :: es => mk e (conj unit mk es) end in
   let clauses := fix clauses cs := match cs with
     | [] => None
     | c :: cs => match R.to_list c with
       | Some [CLLowering.VSym "else"; b] => match cs with [] => expr_of n b | _ => None end
       | Some [t; b] => match expr_of n t, expr_of n b, clauses cs with
         | Some t, Some b, Some r => Some (If t b r) | _, _, _ => None end
       | _ => None end end in
   match d with
   | CLLowering.VSym s => Some (if String.eqb s "#t" then Lit (Boolean true)
       else if String.eqb s "#f" then Lit (Boolean false) else Var s)
   | CLLowering.VStr s => Some (Lit (Text s))
   | CLLowering.VNum s => option_map (fun z => Lit (Integer z)) (zparse s)
   | CLLowering.VCons (CLLowering.VSym h) args => match R.to_list args with
     | None => None
     | Some xs =>
       if String.eqb h "quote" then match xs with [x] => option_map Lit (datum x) | _ => None end
       else if String.eqb h "if" then match xs with
         | [c; a; b] => match expr_of n c, expr_of n a, expr_of n b with
           | Some c, Some a, Some b => Some (If c a b) | _, _, _ => None end
         | _ => None end
       else if String.eqb h "cond" then clauses xs
       else if String.eqb h "and" then option_map (conj true And) (many xs)
       else if String.eqb h "or" then option_map (conj false Or) (many xs)
       else if String.eqb h "let" then match xs with
         | [bs; body] => match R.to_list bs with
           | Some [b] => match R.to_list b with
             | Some [CLLowering.VSym x; a] => match expr_of n a, expr_of n body with
               | Some a, Some body => Some (Let x a body) | _, _ => None end
             | _ => None end
           | _ => None end
         | _ => None end
       (* The admitted syntax-rules macro (checked below) expands to error. *)
       else if String.eqb h "raise-error" then option_map (Call "error") (many xs)
       else if unsupported_head h then None
       else option_map (Call h) (many xs) end
   | _ => None end end.
Definition definition_of (d : CLLowering.sv) : option (string * definition) :=
 match R.to_list d with
 | Some [CLLowering.VSym "define"; header; body] => match R.to_list header with
   | Some (CLLowering.VSym f :: ps) =>
     let ps' := map (fun p => match p with CLLowering.VSym x => Some x | _ => None end) ps in
     if forallb (fun o => match o with Some _ => true | None => false end) ps'
     then match expr_of 40 body with
       | Some e => Some (f, Def (map (fun o => match o with Some x => x | None => "" end) ps') e)
       | None => None end
     else None
   | _ => None end
 | _ => None end.

(* The reviewed expected text of the raise-error macro, as read data. *)
Definition SL := fold_right CLLowering.VCons CLLowering.VNil.
Definition Sy := CLLowering.VSym.
Definition expected_raise_error := SL [Sy "define-syntax"; Sy "raise-error";
 SL [Sy "syntax-rules"; CLLowering.VNil;
    SL [SL [Sy "_"; Sy "location"; Sy "message"; Sy "obj"; Sy "..."];
       SL [Sy "error"; Sy "location"; Sy "message"; Sy "obj"; Sy "..."]]]].

Definition assert_boolean_def := Def ["value"]
 (If (Call "boolean?" [Var "value"]) (Var "value")
  (Call "error" [Lit (Symbol "_scm.assert-boolean");
                 Lit (Text "expected a boolean in if/and/or expression, got"); Var "value"])).
Definition eq_body :=
 If (Call "eq?" [Var "a"; Var "b"]) (Lit (Boolean true))
 (If (Call "number?" [Var "a"]) (And (Call "number?" [Var "b"]) (Call "=" [Var "a"; Var "b"]))
 (If (Call "pair?" [Var "a"])
   (And (Call "pair?" [Var "b"])
     (And (Call "kl:=" [Call "car" [Var "a"]; Call "car" [Var "b"]])
          (Call "kl:=" [Call "cdr" [Var "a"]; Call "cdr" [Var "b"]])))
 (If (Call "string?" [Var "a"]) (And (Call "string?" [Var "b"]) (Call "string=?" [Var "a"; Var "b"]))
 (If (Call "vector?" [Var "a"]) (And (Call "vector?" [Var "b"]) (Call "vector=?" [Var "a"; Var "b"]))
   (Lit (Boolean false)))))).
Definition eq_def := Def ["a"; "b"] eq_body.
Definition program : list (string * definition) :=
 [("kl:_scm.assert-boolean", assert_boolean_def); ("kl:=", eq_def)].

(* Admission: the captured bytes read, the macro is the reviewed text, the two
   admitted definitions decode to exactly the reviewed program, and vector=?
   (a do loop) is rejected by the decoder rather than guessed. *)
Definition admission_of (src : string) : option (list (string * definition)) * bool :=
 match R.read false src with
 | Some [macro; ab; veq; eqd] =>
   (match definition_of ab, definition_of eqd with
    | Some x, Some y => if CLLowering.sv_eqb macro expected_raise_error then Some [x; y] else None
    | _, _ => None end,
    match definition_of veq with None => true | Some _ => false end)
 | _ => (None, false) end.
Definition admission := admission_of scheme_source.
Theorem scheme_wrappers_admitted : admission = (Some program, true).
Proof. vm_compute. reflexivity. Qed.

(* ---------- Evaluation lemmas for pure host answers ---------- *)
Definition P := lookup program.
Definition yields (op : string -> list value -> computation) f vs r := forall st, op f vs st = Out (Returned r) st [].
Lemma out_eta : forall o : outcome, Out (answer o) (records o) ([] ++ trace o) = o.
Proof. intros []; reflexivity. Qed.
Lemma var_step : forall m p op rho x v st, rho x = Some v ->
 eval_with (S m) p op rho (Var x) st = Out (Returned v) st [].
Proof. intros; cbn; rewrite H; reflexivity. Qed.
Lemma lit_step : forall m p op rho v st, eval_with (S m) p op rho (Lit v) st = Out (Returned v) st [].
Proof. reflexivity. Qed.
Lemma if_pure : forall m p op rho c a b st v, eval_with m p op rho c st = Out (Returned v) st [] ->
 eval_with (S m) p op rho (If c a b) st = eval_with m p op rho (match v with Boolean false => b | _ => a end) st.
Proof. intros; cbn [eval_with]; unfold bind; rewrite H; apply out_eta. Qed.
Lemma and_pure : forall m p op rho a b st v, eval_with m p op rho a st = Out (Returned v) st [] ->
 eval_with (S m) p op rho (And a b) st = match v with Boolean false => Out (Returned v) st [] | _ => eval_with m p op rho b st end.
Proof. intros; cbn [eval_with]; unfold bind; rewrite H; destruct v as [| | | | | | [|] | | |]; try apply out_eta; reflexivity. Qed.
Lemma call1 : forall m p op rho f e v st, p f = None -> eval_with m p op rho e st = Out (Returned v) st [] ->
 eval_with (S m) p op rho (Call f [e]) st = op f [v] st.
Proof. intros; cbn [eval_with]; unfold bind; rewrite H0; cbn; rewrite H; apply out_eta. Qed.
Lemma call2 : forall m p op rho f e1 e2 v1 v2 st, p f = None ->
 eval_with m p op rho e1 st = Out (Returned v1) st [] -> eval_with m p op rho e2 st = Out (Returned v2) st [] ->
 eval_with (S m) p op rho (Call f [e1; e2]) st = op f [v1; v2] st.
Proof. intros; cbn [eval_with]; unfold bind; rewrite H0; cbn; rewrite H1; cbn; rewrite H.
 repeat rewrite out_eta; reflexivity. Qed.
Lemma call3 : forall m p op rho f e1 e2 e3 v1 v2 v3 st, p f = None ->
 eval_with m p op rho e1 st = Out (Returned v1) st [] -> eval_with m p op rho e2 st = Out (Returned v2) st [] ->
 eval_with m p op rho e3 st = Out (Returned v3) st [] ->
 eval_with (S m) p op rho (Call f [e1; e2; e3]) st = op f [v1; v2; v3] st.
Proof. intros; cbn [eval_with]; unfold bind; rewrite H0; cbn; rewrite H1; cbn; rewrite H2; cbn; rewrite H.
 destruct (op f [v1; v2; v3] st); reflexivity. Qed.
Lemma call1_def : forall m p op rho f e v st d, p f = Some d -> List.length (params d) = 1 ->
 eval_with m p op rho e st = Out (Returned v) st [] ->
 eval_with (S m) p op rho (Call f [e]) st = eval_with m p op (arguments (params d) [v]) (body d) st.
Proof. intros; cbn [eval_with]; unfold bind; rewrite H1; cbn; rewrite H, H0; cbn.
 destruct (eval_with m p op (arguments (params d) [v]) (body d) st); reflexivity. Qed.
Lemma call2_def : forall m p op rho f e1 e2 v1 v2 st d, p f = Some d -> List.length (params d) = 2 ->
 eval_with m p op rho e1 st = Out (Returned v1) st [] -> eval_with m p op rho e2 st = Out (Returned v2) st [] ->
 eval_with (S m) p op rho (Call f [e1; e2]) st = eval_with m p op (arguments (params d) [v1; v2]) (body d) st.
Proof. intros; cbn [eval_with]; unfold bind; rewrite H1; cbn; rewrite H2; cbn; rewrite H, H0; cbn.
 repeat rewrite out_eta; reflexivity. Qed.

(* ---------- assert-boolean ---------- *)
Definition is_bool v := match v with Boolean _ => true | _ => false end.
Definition assert_message := [Symbol "_scm.assert-boolean"; Text "expected a boolean in if/and/or expression, got"].
Record chez_assert_ops (op : string -> list value -> computation) : Prop := {
 chez_boolean_p : forall v, yields op "boolean?" [v] (Boolean (is_bool v));
 chez_error_raises : forall args st, match answer (op "error" args st) with Returned _ => False | _ => True end }.
Definition rho1 v := arguments ["value"] [v].
Theorem assert_boolean_body : forall op, chez_assert_ops op -> forall n v st, n >= 3 ->
 eval_with n P op (rho1 v) (body assert_boolean_def) st =
 if is_bool v then Out (Returned v) st [] else op "error" (app assert_message [v]) st.
Proof.
 intros op C n v st Hn. destruct n as [|[|[|m]]]; try lia. unfold assert_boolean_def; cbn [body].
 rewrite (if_pure _ _ _ _ _ _ _ _ (Boolean (is_bool v))).
 - destruct v; cbn [is_bool]; try (apply var_step; reflexivity).
   all: apply call3; [reflexivity|apply lit_step|apply lit_step|apply var_step; reflexivity].
 - rewrite (call1 _ _ _ _ _ _ v) by (reflexivity || (apply var_step; reflexivity)). apply (chez_boolean_p op C).
Qed.
(* Shen-Scheme compiles a non-Boolean-yielding test to
   (if (kl:_scm.assert-boolean T) A B). With the captured wrapper this is the
   KLambda if rule: true selects A, false selects B, and any other value
   raises before either branch runs (XNotBoolean). *)
Theorem guarded_if : forall op, chez_assert_ops op -> forall m rho t a b st w, m >= 4 ->
 eval_with m P op rho t st = Out (Returned w) st [] ->
 let o := eval_with (S (S m)) P op rho (If (Call "kl:_scm.assert-boolean" [t]) a b) st in
 match w with
 | Boolean true => o = eval_with (S m) P op rho a st
 | Boolean false => o = eval_with (S m) P op rho b st
 | _ => o = op "error" (app assert_message [w]) st /\ match answer o with Returned _ => False | _ => True end end.
Proof.
 intros op C m rho t a b st w Hm Ht o. unfold o.
 assert (Hc : eval_with (S m) P op rho (Call "kl:_scm.assert-boolean" [t]) st =
   if is_bool w then Out (Returned w) st [] else op "error" (app assert_message [w]) st).
 { rewrite (call1_def _ _ _ _ _ _ w _ assert_boolean_def) by (reflexivity || exact Ht).
   apply assert_boolean_body; [exact C | lia]. }
 destruct (is_bool w) eqn:B.
 - rewrite (if_pure _ _ _ _ _ _ _ _ w) by exact Hc. destruct w as [| | | | | |[|]| | |]; try discriminate; reflexivity.
 - assert (Hif : eval_with (S (S m)) P op rho (If (Call "kl:_scm.assert-boolean" [t]) a b) st =
     bind (eval_with (S m) P op rho (Call "kl:_scm.assert-boolean" [t]))
          (fun v => eval_with (S m) P op rho (match v with Boolean false => b | _ => a end)) st) by reflexivity.
   rewrite Hif. unfold bind. rewrite Hc.
   pose proof (chez_error_raises op C (app assert_message [w]) st) as E.
   destruct w as [| | | | | |[|]| | |]; try discriminate;
   destruct (op "error" (app assert_message _) st) as [[] ? ?]; cbn in *; try contradiction; auto.
Qed.

(* ---------- kl:= on first-order data ---------- *)
(* The data fragment reached by symbols, strings, exact integers, Booleans,
   the empty list and pairs (no closures, vectors, inexact numbers). *)
Fixpoint data v := match v with
 | Nil | Symbol _ | Text _ | Integer _ | Boolean _ => true
 | Pair a b => data a && data b | _ => false end.
Definition atomic_identity v := match v with Nil | Symbol _ | Boolean _ => true | _ => false end.
Definition is_pair v := match v with Pair _ _ => true | _ => false end.
Definition is_text v := match v with Text _ => true | _ => false end.
(* Each Chez operation reached by kl:= on data, named separately. eq? may
   answer differently in different states (object identity): only soundness
   and completeness on interned atoms are assumed. *)
Record chez_equality_ops (op : string -> list value -> computation) : Prop := {
 chez_eq : forall a b st, data a = true -> data b = true -> exists r,
   op "eq?" [a; b] st = Out (Returned (Boolean r)) st [] /\
   (r = true -> same a b = true) /\ (atomic_identity a = true -> same a b = true -> r = true);
 chez_number_p : forall a, data a = true -> yields op "number?" [a] (Boolean (numeric a));
 chez_num_eq : forall x y, yields op "=" [Integer x; Integer y] (Boolean (Z.eqb x y));
 chez_pair_p : forall a, data a = true -> yields op "pair?" [a] (Boolean (is_pair a));
 chez_car : forall a b, yields op "car" [Pair a b] a;
 chez_cdr : forall a b, yields op "cdr" [Pair a b] b;
 chez_string_p : forall a, data a = true -> yields op "string?" [a] (Boolean (is_text a));
 chez_string_eq : forall s t, yields op "string=?" [Text s; Text t] (Boolean (String.eqb s t));
 chez_vector_p : forall a, data a = true -> yields op "vector?" [a] (Boolean false) }.
Fixpoint bound v := match v with Pair a b => 8 + Nat.max (bound a) (bound b) | _ => 8 end.
Definition rho2 a b := arguments ["a"; "b"] [a; b].
Section Equality.
Variable op : string -> list value -> computation.
Hypothesis C : chez_equality_ops op.
Lemma c2 : forall m f a b st, P f = None ->
 eval_with (S (S m)) P op (rho2 a b) (Call f [Var "a"; Var "b"]) st = op f [a; b] st.
Proof. intros; apply call2; auto; apply var_step; reflexivity. Qed.
Lemma c1a : forall m f a b st, P f = None -> eval_with (S (S m)) P op (rho2 a b) (Call f [Var "a"]) st = op f [a] st.
Proof. intros; apply call1; auto; apply var_step; reflexivity. Qed.
Lemma c1b : forall m f a b st, P f = None -> eval_with (S (S m)) P op (rho2 a b) (Call f [Var "b"]) st = op f [b] st.
Proof. intros; apply call1; auto; apply var_step; reflexivity. Qed.
Lemma recurse_car : forall m a1 a2 b1 b2 st,
 eval_with (S (S (S m))) P op (rho2 (Pair a1 a2) (Pair b1 b2)) (Call "kl:=" [Call "car" [Var "a"]; Call "car" [Var "b"]]) st =
 eval_with (S (S m)) P op (rho2 a1 b1) eq_body st.
Proof.
 intros. rewrite (call2_def _ _ _ _ _ _ _ a1 b1 _ eq_def); try reflexivity.
 - rewrite c1a by reflexivity; apply (chez_car op C).
 - rewrite c1b by reflexivity; apply (chez_car op C).
Qed.
Lemma recurse_cdr : forall m a1 a2 b1 b2 st,
 eval_with (S (S (S m))) P op (rho2 (Pair a1 a2) (Pair b1 b2)) (Call "kl:=" [Call "cdr" [Var "a"]; Call "cdr" [Var "b"]]) st =
 eval_with (S (S m)) P op (rho2 a2 b2) eq_body st.
Proof.
 intros. rewrite (call2_def _ _ _ _ _ _ _ a2 b2 _ eq_def); try reflexivity.
 - rewrite c1a by reflexivity; apply (chez_cdr op C).
 - rewrite c1b by reflexivity; apply (chez_cdr op C).
Qed.
(* For every pair of first-order data values and every fuel above the
   structural bound, the captured kl:= body returns Boolean (same a b), with
   the state unchanged and no events: stock kl:= is structural equality on
   data, given only the named Chez operation contracts. *)
Theorem kl_eq_data : forall a b st n, data a = true -> data b = true ->
 n >= bound a -> eval_with n P op (rho2 a b) eq_body st = Out (Returned (Boolean (same a b))) st [].
Proof.
 induction a as [|s0|s0|z0|f0 d0|t0|b0|a1 IH1 a2 IH2|c0|h0]; intros b st k Da Db Hn; try discriminate Da;
 (assert (exists m, k = S (S (S (S (S (S (S (S m)))))))) as [m ->] by (exists (k - 8); cbn [bound] in Hn; lia));
 unfold eq_body; destruct (chez_eq op C _ b st Da Db) as [r [Er [Sound Comp]]];
 (rewrite (if_pure _ _ _ _ _ _ _ _ (Boolean r)) by (rewrite c2 by reflexivity; exact Er));
 (destruct r; [rewrite (Sound eq_refl); reflexivity|]);
 (rewrite (if_pure _ _ _ _ _ _ _ _ (Boolean (numeric _))) by (rewrite c1a by reflexivity; apply (chez_number_p op C); exact Da));
 cbn [numeric].
 1,2,3,5: (rewrite (if_pure _ _ _ _ _ _ _ _ (Boolean false)) by (rewrite c1a by reflexivity; apply (chez_pair_p op C); exact Da));
   (rewrite (if_pure _ _ _ _ _ _ _ _ (Boolean (is_text _))) by (rewrite c1a by reflexivity; apply (chez_string_p op C); exact Da)); cbn [is_text].
 1,2,4: (rewrite (if_pure _ _ _ _ _ _ _ _ (Boolean false)) by (rewrite c1a by reflexivity; apply (chez_vector_p op C); exact Da));
   (destruct (same _ b) eqn:E; [specialize (Comp eq_refl eq_refl); discriminate|reflexivity]).
 - (* Text *)
   rewrite (and_pure _ _ _ _ _ _ _ (Boolean (is_text b))) by (rewrite c1b by reflexivity; apply (chez_string_p op C); exact Db).
   destruct b; cbn [is_text same]; try reflexivity.
   rewrite c2 by reflexivity; apply (chez_string_eq op C).
 - (* Integer *)
   rewrite (and_pure _ _ _ _ _ _ _ (Boolean (numeric b))) by (rewrite c1b by reflexivity; apply (chez_number_p op C); exact Db).
   destruct b; cbn [numeric same] in *; try reflexivity; try discriminate Db.
   rewrite c2 by reflexivity; apply (chez_num_eq op C).
 - (* Pair *)
   cbn [data] in Da; apply andb_true_iff in Da as [D1 D2].
   rewrite (if_pure _ _ _ _ _ _ _ _ (Boolean true)) by (rewrite c1a by reflexivity; apply (chez_pair_p op C); cbn; rewrite D1, D2; reflexivity).
   rewrite (and_pure _ _ _ _ _ _ _ (Boolean (is_pair b))) by (rewrite c1b by reflexivity; apply (chez_pair_p op C); exact Db).
   destruct b as [| | | | | | |b1 b2| |]; cbn [is_pair same]; try reflexivity.
   cbn [data] in Db; apply andb_true_iff in Db as [E1 E2]. cbn [bound] in Hn.
   rewrite (and_pure _ _ _ _ _ _ _ (Boolean (same a1 b1))).
   + destruct (same a1 b1); cbn [andb]; [|reflexivity].
     rewrite recurse_cdr. apply IH2; auto; lia.
   + rewrite recurse_car. apply IH1; auto; lia.
Qed.
End Equality.

(* ---------- Connection to the formal rule slot KLSemantics.rule_equal ---------- *)
(* Representation of KLambda first-order data by Chez data: exact integers,
   ASCII-named symbols and strings, Booleans as #t/#f, () and pairs. *)
Inductive rep_s : KLValue.KLValue.value -> value -> Prop :=
 | rs_int z : rep_s (KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt z)) (Integer z)
 | rs_sym s : rep_s (KLValue.KLValue.VSym (KLSyntax.KLSyntax.of_string s)) (Symbol s)
 | rs_str s : rep_s (KLValue.KLValue.VStr (KLSyntax.KLSyntax.of_string s)) (Text s)
 | rs_bool b : rep_s (KLValue.KLValue.VBool b) (Boolean b)
 | rs_nil : rep_s KLValue.KLValue.VNil Nil
 | rs_cons a a' d d' : rep_s a a' -> rep_s d d' -> rep_s (KLValue.KLValue.VCons a d) (Pair a' d').
Lemma of_string_inj : forall s t, KLSyntax.KLSyntax.of_string s = KLSyntax.KLSyntax.of_string t -> s = t.
Proof.
 induction s as [|c s IH]; destruct t as [|d t]; cbn; intro H; try discriminate; auto.
 injection H as H1 H2. apply (f_equal N.to_nat) in H1. rewrite !Nnat.Nat2N.id in H1.
 rewrite <- (ascii_nat_embedding c), <- (ascii_nat_embedding d), H1. f_equal. apply IH; exact H2.
Qed.
Lemma text_of : forall s t, KLSyntax.KLSyntax.text_eqb (KLSyntax.KLSyntax.of_string s) (KLSyntax.KLSyntax.of_string t) = String.eqb s t.
Proof.
 intros s t. destruct (String.eqb s t) eqn:E.
 - apply String.eqb_eq in E; subst; apply KLSyntax.KLSyntax.text_eqb_refl.
 - apply KLSyntax.KLSyntax.text_eqb_neq. intro H. apply of_string_inj in H; subst. rewrite String.eqb_refl in E; discriminate.
Qed.
Lemma rep_data : forall a a', rep_s a a' -> data a' = true.
Proof. intros a a' H; induction H; cbn; auto; rewrite IHrep_s1, IHrep_s2; reflexivity. Qed.
Lemma eq_depth_cons : forall Pr h d a1 a2 b1 b2,
 KLValue.KLValue.eq_depth Pr h (Datatypes.S d) (KLValue.KLValue.VCons a1 a2) (KLValue.KLValue.VCons b1 b2) =
 match KLValue.KLValue.eq_depth Pr h (Datatypes.S d) a1 b1 with
 | Some true => KLValue.KLValue.eq_depth Pr h (Datatypes.S d) a2 b2 | r => r end.
Proof. reflexivity. Qed.
Lemma eq_depth_rep : forall Pr h d a a', rep_s a a' -> forall b b', rep_s b b' ->
 KLValue.KLValue.eq_depth Pr h (Datatypes.S d) a b = Some (same a' b').
Proof.
 intros Pr h d a a' Ha. induction Ha as [z|s|s|bo| |a a' d0 d0' Ha1 IHHa1 Ha2 IHHa2]; intros y y' Hb; destruct Hb as [z2|s2|s2|bo2| |b1 b1' b2 b2' Hb1 Hb2]; try reflexivity.
 - cbn. rewrite text_of. reflexivity.
 - cbn. rewrite text_of. reflexivity.
 - rewrite eq_depth_cons, (IHHa1 _ _ Hb1). cbn [same]. destruct (same a' b1'); [apply IHHa2; exact Hb2|reflexivity].
Qed.
(* The captured stock kl:= refines the KLambda = rule on represented data:
   rule_equal answers VBool r exactly when the Chez wrapper answers #t/#f = r. *)
Theorem stock_equality_refines_rule : forall op, chez_equality_ops op ->
 forall Pr s a a' b b' st, rep_s a a' -> rep_s b b' ->
 exists r, KLSemantics.KLSemantics.rule_equal Pr [a; b] s = KLSemantics.KLSemantics.ret (KLValue.KLValue.VBool r) s /\
   forall n, n >= bound a' -> eval_with n P op (rho2 a' b') eq_body st = Out (Returned (Boolean r)) st [].
Proof.
 intros op C Pr s a a' b b' st Ha Hb. exists (same a' b'). split.
 - unfold KLSemantics.KLSemantics.rule_equal, KLValue.KLValue.kl_eq. rewrite (eq_depth_rep Pr _ _ _ _ Ha _ _ Hb). reflexivity.
 - intros n Hn. apply kl_eq_data; auto; eapply rep_data; eauto.
Qed.
(* The sealed lane and the EQ-1 Native program bind kl:= to the replacement
   (lambda (x y) (equal? x y)), whose Native meaning is Native.primitive
   "equal?". On first-order data the stock wrapper computes the same answer,
   so on that domain the replacement does not change the observed equality. *)
Theorem stock_matches_replacement : forall op, chez_equality_ops op -> forall a b st n,
 data a = true -> data b = true -> n >= bound a ->
 Some (answer (eval_with n P op (rho2 a b) eq_body st)) = option_map Returned (primitive "equal?" [a; b]).
Proof. intros. rewrite kl_eq_data; auto. Qed.
(* Outside that domain they differ: with Chez's numeric = (which identifies
   1 and 1.0), the stock wrapper reports equality where equal? (Native same)
   does not. The compiled literal path (eqv?) agrees with equal? here, so the
   ports' two equality lowerings disagree on mixed exactness; the native
   regression in tests/primitives.shen observes this on Shen-Scheme. *)
Theorem stock_mixed_exactness : forall op t,
 (forall st, op "eq?" [Integer 1; Inexact t] st = Out (Returned (Boolean false)) st []) ->
 yields op "number?" [Integer 1] (Boolean true) -> yields op "number?" [Inexact t] (Boolean true) ->
 yields op "=" [Integer 1; Inexact t] (Boolean true) ->
 forall st, eval_with 9 P op (rho2 (Integer 1) (Inexact t)) eq_body st = Out (Returned (Boolean true)) st [] /\
   same (Integer 1) (Inexact t) = false.
Proof.
 intros op t Heq N1 N2 E st. split; [|reflexivity]. unfold eq_body.
 rewrite (if_pure _ _ _ _ _ _ _ _ (Boolean false)) by (rewrite (call2 _ _ _ _ _ _ _ (Integer 1) (Inexact t)) by (reflexivity || (apply var_step; reflexivity)); apply Heq).
 rewrite (if_pure _ _ _ _ _ _ _ _ (Boolean true)) by (rewrite (call1 _ _ _ _ _ _ (Integer 1)) by (reflexivity || (apply var_step; reflexivity)); apply N1).
 rewrite (and_pure _ _ _ _ _ _ _ (Boolean true)) by (rewrite (call1 _ _ _ _ _ _ (Inexact t)) by (reflexivity || (apply var_step; reflexivity)); apply N2).
 rewrite (call2 _ _ _ _ _ _ _ (Integer 1) (Inexact t)) by (reflexivity || (apply var_step; reflexivity)); apply E.
Qed.
(* Anti-vacuity: one concrete operation table satisfies every named Chez
   contract above (it identifies only (), symbols and Booleans under eq?, as
   R6RS permits). It is not a model of Chez. *)
Definition model_op (f : string) (vs : list value) : computation := fun st =>
 match f, vs with
 | "eq?", [a; b] => Out (Returned (Boolean (atomic_identity a && same a b))) st []
 | "number?", [a] => Out (Returned (Boolean (numeric a))) st []
 | "=", [Integer x; Integer y] => Out (Returned (Boolean (Z.eqb x y))) st []
 | "pair?", [a] => Out (Returned (Boolean (is_pair a))) st []
 | "car", [Pair a _] => Out (Returned a) st []
 | "cdr", [Pair _ b] => Out (Returned b) st []
 | "string?", [a] => Out (Returned (Boolean (is_text a))) st []
 | "string=?", [Text s; Text t] => Out (Returned (Boolean (String.eqb s t))) st []
 | "vector?", [_] => Out (Returned (Boolean false)) st []
 | "boolean?", [a] => Out (Returned (Boolean (is_bool a))) st []
 | "error", (owner :: message :: _) => Out (Raised owner message) st []
 | _, _ => Out Unsupported st [] end.
Theorem model_ops_satisfiable : chez_equality_ops model_op /\ chez_assert_ops model_op.
Proof.
 split; constructor; intros; try (intro; reflexivity).
 - exists (atomic_identity a && same a b)%bool. split; [reflexivity|split].
   + intro E; apply andb_true_iff in E; tauto.
   + intros A E; rewrite A, E; reflexivity.
 - match goal with |- context[model_op "error" ?a ?s] => destruct a as [|o [|m r]] end; exact I.
Qed.
End SchemeWrappers.
