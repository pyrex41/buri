(* E2E-17, Wave-D primitives lane: body proofs of Shen-Scheme kl:intern.

   Stock: tizoc/shen-scheme 8d261518 src/primitives.scm (blob 92b8875a)
   bytes 350..640, identical at the v0.52 tag fa071737. Patched: the same
   file with ports/patches/shen-scheme-primitives.diff applied (blob
   526a89b2), bytes 350..482. Both excerpts are packaged by
   scripts/package-prims2.py into Prims2Sources.v, read by the independent
   PortReader, decoded by SchemeWrappers.definition_of and admitted here by
   computed equality with the reviewed AST.

   Every theorem quantifies over EVERY Chez operation table satisfying the
   individually named contracts in [chez_intern_ops] (owned by E2E-21 and
   E2E-24). Nothing here is a theorem about Chez itself.

   - The stock body is given its exact denotation, which on a digit-led name
     of length > 1 returns whatever string->number answers when that is a
     number. With Chez's answer for "12" (the integer 12, sampled on the
     v0.52 binary) the result represents no KLambda symbol, while
     rule_intern gives VSym "12": OB-SCHEME-INTERN-NUMERIC stays refuted.
   - The patched body returns, for EVERY string, #t for "true", #f for
     "false", and otherwise the symbol of that name, and it refines
     KLSemantics.rule_intern through SchemeWrappers.rep_s. *)
From Coq Require Import String List ZArith Bool Ascii Lia.
From Buri Require Import Native ObserverEffects PortReader Prims2Sources KLSyntax KLValue KLSemantics SchemeWrappers.
Import ListNotations.
Module SchemeIntern.
Import Native.Native ObserverEffects.ObserverEffects.
Module R := PortReader.PortReader.
Module W := SchemeWrappers.SchemeWrappers.
Open Scope string_scope.

(* ---------- The reviewed ASTs and admission ---------- *)
Definition nm := Var "name".
Definition bool_tests (rest : expr) :=
 If (Call "equal?" [nm; Lit (Text "true")]) (Lit (Boolean true))
 (If (Call "equal?" [nm; Lit (Text "false")]) (Lit (Boolean false)) rest).
Definition numeric_branch :=
 And (Call ">" [Call "string-length" [nm]; Lit (Integer 1)])
     (And (Call "char-numeric?" [Call "string-ref" [nm; Lit (Integer 0)]])
          (Call "string->number" [nm])).
Definition stock_body := bool_tests (Or numeric_branch (Call "string->symbol" [nm])).
Definition patched_body := bool_tests (Call "string->symbol" [nm]).
Definition admission_of (src : string) : option (string * definition) :=
 match R.read false src with Some [d] => W.definition_of d | _ => None end.
Theorem intern_admitted :
 admission_of stock_intern_source = Some ("kl:intern", Def ["name"] stock_body) /\
 admission_of patched_intern_source = Some ("kl:intern", Def ["name"] patched_body).
Proof. split; vm_compute; reflexivity. Qed.

(* ---------- Named Chez contracts ---------- *)
Definition first_digit (s : string) := match s with String c _ => R.digit c | EmptyString => false end.
Record chez_intern_ops (op : string -> list value -> computation) : Prop := {
 intern_equal_text : forall s t, W.yields op "equal?" [Text s; Text t] (Boolean (String.eqb s t));
 intern_string_symbol : forall s, W.yields op "string->symbol" [Text s] (Symbol s);
 intern_string_length : forall s, W.yields op "string-length" [Text s] (Integer (Z.of_nat (String.length s)));
 intern_gt : forall x y, W.yields op ">" [Integer x; Integer y] (Boolean (Z.gtb x y));
 intern_string_ref : forall c s, W.yields op "string-ref" [Text (String c s); Integer 0] (Character c);
 intern_char_numeric : forall c, W.yields op "char-numeric?" [Character c] (Boolean (R.digit c));
 intern_string_number : forall s, exists r, W.yields op "string->number" [Text s] r /\
   (r = Boolean false \/ numeric r = true) }.

(* ---------- Evaluation steps ---------- *)
Definition Pn : program := fun _ => None.
Definition rho (s : string) := arguments ["name"] [Text s].
Lemma or_pure : forall m p op rho a b st v, eval_with m p op rho a st = Out (Returned v) st [] ->
 eval_with (S m) p op rho (Or a b) st = match v with Boolean false => eval_with m p op rho b st | _ => Out (Returned v) st [] end.
Proof. intros; cbn [eval_with]; unfold bind; rewrite H; destruct v as [| | | | | | [|] | | |]; try apply W.out_eta; reflexivity. Qed.
Section Steps.
Variable op : string -> list value -> computation.
Hypothesis C : chez_intern_ops op.
Lemma name_step : forall m s st, eval_with (S m) Pn op (rho s) nm st = Out (Returned (Text s)) st [].
Proof. intros; apply W.var_step; reflexivity. Qed.
Lemma eq_step : forall m s t st,
 eval_with (S (S m)) Pn op (rho s) (Call "equal?" [nm; Lit (Text t)]) st = Out (Returned (Boolean (String.eqb s t))) st [].
Proof. intros. rewrite (W.call2 _ _ _ _ _ _ _ (Text s) (Text t)); [apply (intern_equal_text op C)|reflexivity|apply name_step|apply W.lit_step]. Qed.
Lemma sym_step : forall m s st,
 eval_with (S (S m)) Pn op (rho s) (Call "string->symbol" [nm]) st = Out (Returned (Symbol s)) st [].
Proof. intros. rewrite (W.call1 _ _ _ _ _ _ (Text s)); [apply (intern_string_symbol op C)|reflexivity|apply name_step]. Qed.
Lemma tests_step : forall m s st rest,
 eval_with (S (S (S (S m)))) Pn op (rho s) (bool_tests rest) st =
 if String.eqb s "true" then Out (Returned (Boolean true)) st []
 else if String.eqb s "false" then Out (Returned (Boolean false)) st []
 else eval_with (S (S m)) Pn op (rho s) rest st.
Proof.
 intros. unfold bool_tests.
 rewrite (W.if_pure _ _ _ _ _ _ _ _ (Boolean (String.eqb s "true"))) by apply eq_step.
 destruct (String.eqb s "true"); [apply W.lit_step|].
 rewrite (W.if_pure _ _ _ _ _ _ _ _ (Boolean (String.eqb s "false"))) by apply eq_step.
 destruct (String.eqb s "false"); [apply W.lit_step|reflexivity].
Qed.
End Steps.

(* ---------- The patched body ---------- *)
Definition patched_answer s :=
 if String.eqb s "true" then Boolean true else if String.eqb s "false" then Boolean false else Symbol s.
(* For every string and every fuel >= 6: the patched body returns #t, #f or
   the symbol of that name, with the state unchanged, no events and no raise. *)
Theorem patched_intern_body : forall op, chez_intern_ops op -> forall s st n, n >= 6 ->
 eval_with n Pn op (rho s) patched_body st = Out (Returned (patched_answer s)) st [].
Proof.
 intros op C s st n Hn. assert (exists m, n = S (S (S (S (S (S m)))))) as [m ->] by (exists (n - 6); lia).
 unfold patched_body, patched_answer. rewrite tests_step by exact C.
 destruct (String.eqb s "true"); [reflexivity|]. destruct (String.eqb s "false"); [reflexivity|].
 apply sym_step; exact C.
Qed.
(* In particular the patched kl:intern returns a symbol for every string
   other than "true" and "false", whatever its first character. *)
Theorem patched_intern_symbol : forall op, chez_intern_ops op -> forall s st n, n >= 6 ->
 s <> "true" -> s <> "false" ->
 eval_with n Pn op (rho s) patched_body st = Out (Returned (Symbol s)) st [].
Proof.
 intros op C s st n Hn T F. rewrite patched_intern_body by assumption. unfold patched_answer.
 apply String.eqb_neq in T, F. rewrite T, F. reflexivity.
Qed.
(* The patched body refines the KLambda rule: for every ASCII string s,
   rule_intern returns k with the store unchanged, and the patched wrapper
   returns a Chez value representing k. *)
Theorem patched_intern_refines_rule : forall op, chez_intern_ops op -> forall s ks st n, n >= 6 ->
 exists k v, KLSemantics.KLSemantics.rule_intern [KLValue.KLValue.VStr (KLSyntax.KLSyntax.of_string s)] ks = KLSemantics.KLSemantics.ret k ks /\
   W.rep_s k v /\ eval_with n Pn op (rho s) patched_body st = Out (Returned v) st [].
Proof.
 intros op C s ks st n Hn. rewrite patched_intern_body by assumption.
 unfold KLSemantics.KLSemantics.rule_intern, KLSemantics.KLSemantics.kw, patched_answer. rewrite !W.text_of.
 destruct (String.eqb s "true"); [|destruct (String.eqb s "false")].
 - eexists; eexists; split; [reflexivity|split; [apply W.rs_bool|reflexivity]].
 - eexists; eexists; split; [reflexivity|split; [apply W.rs_bool|reflexivity]].
 - eexists; eexists; split; [reflexivity|split; [apply W.rs_sym|reflexivity]].
Qed.

(* ---------- The stock body ---------- *)
Definition long_digit_led s := (Z.gtb (Z.of_nat (String.length s)) 1 && first_digit s)%bool.
(* Exact denotation of the stock body: for every string there is a Chez
   string->number answer r (#f or a number) such that the result is #t, #f,
   r when the name is digit-led of length > 1 and r is a number, and the
   symbol otherwise. *)
Theorem stock_intern_body : forall op, chez_intern_ops op -> forall s st n, n >= 8 ->
 exists r, W.yields op "string->number" [Text s] r /\ (r = Boolean false \/ numeric r = true) /\
 eval_with n Pn op (rho s) stock_body st = Out (Returned
   (if String.eqb s "true" then Boolean true else if String.eqb s "false" then Boolean false
    else if long_digit_led s then match r with Boolean false => Symbol s | _ => r end else Symbol s)) st [].
Proof.
 intros op C s st n Hn. destruct (intern_string_number op C s) as [r [Er Kr]]. exists r. split; [exact Er|split; [exact Kr|]].
 assert (exists m, n = S (S (S (S (S (S (S (S m)))))))) as [m ->] by (exists (n - 8); lia).
 unfold stock_body. rewrite tests_step by exact C.
 destruct (String.eqb s "true"); [reflexivity|]. destruct (String.eqb s "false"); [reflexivity|].
 assert (Hgt : eval_with (S (S (S m))) Pn op (rho s) (Call ">" [Call "string-length" [nm]; Lit (Integer 1)]) st =
   Out (Returned (Boolean (Z.gtb (Z.of_nat (String.length s)) 1))) st []).
 { rewrite (W.call2 _ _ _ _ _ _ _ (Integer (Z.of_nat (String.length s))) (Integer 1)); [apply (intern_gt op C)|reflexivity| |apply W.lit_step].
   rewrite (W.call1 _ _ _ _ _ _ (Text s)); [apply (intern_string_length op C)|reflexivity|apply name_step]. }
 unfold long_digit_led, numeric_branch.
 destruct (Z.gtb (Z.of_nat (String.length s)) 1) eqn:G; cbn [andb].
 - destruct s as [|c s']; [cbn in G; discriminate|].
   assert (Hdig : eval_with (S (S (S m))) Pn op (rho (String c s')) (Call "char-numeric?" [Call "string-ref" [nm; Lit (Integer 0)]]) st =
     Out (Returned (Boolean (R.digit c))) st []).
   { rewrite (W.call1 _ _ _ _ _ _ (Character c)); [apply (intern_char_numeric op C)|reflexivity|].
     rewrite (W.call2 _ _ _ _ _ _ _ (Text (String c s')) (Integer 0)); [apply (intern_string_ref op C)|reflexivity|apply name_step|apply W.lit_step]. }
   rewrite (or_pure _ _ _ _ _ _ _
     (if R.digit c then r else Boolean false)).
   + cbn [first_digit]. destruct (R.digit c); [|apply sym_step; exact C].
     destruct Kr as [-> | Nr]; [apply sym_step; exact C|].
     destruct r as [| | | | | | [|] | | |]; cbn in Nr; try discriminate; reflexivity.
   + rewrite (W.and_pure _ _ _ _ _ _ _ (Boolean true)) by exact Hgt.
     rewrite (W.and_pure _ _ _ _ _ _ _ (Boolean (R.digit c))) by exact Hdig.
     destruct (R.digit c); [|reflexivity].
     rewrite (W.call1 _ _ _ _ _ _ (Text (String c s'))); [apply Er|reflexivity|apply name_step].
 - rewrite (or_pure _ _ _ _ _ _ _ (Boolean false)); [apply sym_step; exact C|].
   rewrite (W.and_pure _ _ _ _ _ _ _ (Boolean false)) by exact Hgt. reflexivity.
Qed.

Lemma rep_number_not_symbol : forall k v, W.rep_s k v -> numeric v = true -> forall x, k <> KLValue.KLValue.VSym x.
Proof. intros k v H N x E; destruct H; cbn in N; try discriminate; inversion E. Qed.
(* The stock body diverges from rule_intern on every digit-led name of
   length > 1 that the host string->number reads as a number: the wrapper
   returns that number, which represents no KLambda symbol, while
   rule_intern returns the symbol of the name. *)
Theorem stock_intern_digit_led : forall op, chez_intern_ops op -> forall s r ks st n, n >= 8 ->
 long_digit_led s = true -> W.yields op "string->number" [Text s] r -> numeric r = true ->
 eval_with n Pn op (rho s) stock_body st = Out (Returned r) st [] /\
 KLSemantics.KLSemantics.rule_intern [KLValue.KLValue.VStr (KLSyntax.KLSyntax.of_string s)] ks =
   KLSemantics.KLSemantics.ret (KLValue.KLValue.VSym (KLSyntax.KLSyntax.of_string s)) ks /\
 forall k, W.rep_s k r -> k <> KLValue.KLValue.VSym (KLSyntax.KLSyntax.of_string s).
Proof.
 intros op C s r ks st n Hn L Er Nr.
 assert (Ht : String.eqb s "true" = false /\ String.eqb s "false" = false).
 { unfold long_digit_led in L. apply andb_true_iff in L as [_ D].
   destruct s as [|c s']; [discriminate|]. cbn [first_digit] in D.
   split; apply String.eqb_neq; intro E; injection E as E1 _; subst; vm_compute in D; discriminate. }
 destruct Ht as [T F]. split; [|split].
 - destruct (stock_intern_body op C s st n Hn) as [r' [Er' [_ Ev]]]. rewrite Ev, T, F, L.
   assert (r' = r) as ->.
   { pose proof (Er' st) as A. pose proof (Er st) as B. rewrite A in B. injection B; auto. }
   destruct r as [| | | | | | [|] | | |]; cbn in Nr; try discriminate; reflexivity.
 - unfold KLSemantics.KLSemantics.rule_intern, KLSemantics.KLSemantics.kw. rewrite !W.text_of, T, F. reflexivity.
 - intros k Hk; apply (rep_number_not_symbol k r Hk Nr).
Qed.
(* The sampled v0.52 instance: if string->number reads "12" as the integer
   12, stock kl:intern returns 12 where rule_intern returns VSym "12". *)
Theorem stock_intern_twelve : forall op, chez_intern_ops op ->
 W.yields op "string->number" [Text "12"] (Integer 12) -> forall ks st n, n >= 8 ->
 eval_with n Pn op (rho "12") stock_body st = Out (Returned (Integer 12)) st [] /\
 KLSemantics.KLSemantics.rule_intern [KLValue.KLValue.VStr (KLSyntax.KLSyntax.of_string "12")] ks =
   KLSemantics.KLSemantics.ret (KLValue.KLValue.VSym (KLSyntax.KLSyntax.of_string "12")) ks /\
 forall k, W.rep_s k (Integer 12) -> k <> KLValue.KLValue.VSym (KLSyntax.KLSyntax.of_string "12").
Proof. intros op C E ks st n Hn. apply stock_intern_digit_led; auto. Qed.
(* Where the two bodies agree: on every name that is not digit-led of
   length > 1, stock and patched return the same value. *)
Theorem stock_patched_agree : forall op, chez_intern_ops op -> forall s st n, n >= 8 ->
 long_digit_led s = false ->
 eval_with n Pn op (rho s) stock_body st = eval_with n Pn op (rho s) patched_body st.
Proof.
 intros op C s st n Hn L. destruct (stock_intern_body op C s st n Hn) as [r [_ [_ Ev]]].
 rewrite Ev, patched_intern_body by (auto; lia). rewrite L. reflexivity.
Qed.

(* ---------- Anti-vacuity ---------- *)
(* One concrete table satisfies every contract, with string->number reading
   "12" as 12 and every other string as #f. It is not a model of Chez. *)
Definition model_op (f : string) (vs : list value) : computation := fun st =>
 match f, vs with
 | "equal?", [Text s; Text t] => Out (Returned (Boolean (String.eqb s t))) st []
 | "string->symbol", [Text s] => Out (Returned (Symbol s)) st []
 | "string-length", [Text s] => Out (Returned (Integer (Z.of_nat (String.length s)))) st []
 | ">", [Integer x; Integer y] => Out (Returned (Boolean (Z.gtb x y))) st []
 | "string-ref", [Text (String c _); Integer 0] => Out (Returned (Character c)) st []
 | "char-numeric?", [Character c] => Out (Returned (Boolean (R.digit c))) st []
 | "string->number", [Text s] => Out (Returned (if String.eqb s "12" then Integer 12 else Boolean false)) st []
 | _, _ => Out Unsupported st [] end.
Theorem model_intern_ops : chez_intern_ops model_op /\ W.yields model_op "string->number" [Text "12"] (Integer 12).
Proof.
 split; [constructor; intros; try (intro; reflexivity)|intro; reflexivity].
 exists (if String.eqb s "12" then Integer 12 else Boolean false). split; [intro; reflexivity|].
 destruct (String.eqb s "12"); [right|left]; reflexivity.
Qed.
End SchemeIntern.
