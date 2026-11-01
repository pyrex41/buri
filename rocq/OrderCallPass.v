(* Execution of the actual captured Shen-Scheme argument-ordering pass,
   linked with the actual captured Shen kernel list helpers (occurrences,
   reverse, not). gensym is an ARBITRARY stateful generator: every theorem
   below holds for every generator, including the real counter-based one.
   Only kl:=, kl:_scm.assert-boolean and Scheme list primitives remain
   primitive contracts (from the pinned src/primitives.scm). *)
From Coq Require Import List String ZArith Bool Arith Lia.
From Buri Require Import Native ObserverEffects EffectContract EffectBigStep
  OrderCallInput KernelListInput OrderCallCorrect.
Import ListNotations.
Module OrderCallPass.
Import Native.Native ObserverEffects.ObserverEffects EffectContract.EffectContract EffectBigStep.EffectBigStep.
Module O := OrderCallCorrect.OrderCallCorrect.
Open Scope string_scope.

(* The pass calls kernel functions by their kernel names; the capture defines
   the same bodies under buri.kernel.* names (see ports/kernel-list.shen). *)
Definition link name :=
 if String.eqb name "kl:occurrences" then "kl:buri.kernel.occurrences"
 else if String.eqb name "kl:reverse" then "kl:buri.kernel.reverse"
 else if String.eqb name "kl:not" then "kl:buri.kernel.not" else name.
Definition linked := (order_call_program ++ kernel_list_program)%list.
Definition P : program := fun name => lookup linked (link name).
Definition symbol_is s v := match v with Symbol t => String.eqb s t | _ => false end.
(* kl:= is only modelled with a symbol on the left (its use in occurrences on
   symbol names): Shen-Scheme's kl:= is eq? there, i.e. same interned symbol.
   assert-boolean is the identity on booleans; other inputs are unsupported. *)
Definition op (gen:computation) name args : computation := fun st =>
 match name, args with
 | "kl:gensym", [Symbol "arg"] => gen st
 | "kl:=", [Symbol s; v] => Out (Returned (Boolean (symbol_is s v))) st []
 | "kl:_scm.assert-boolean", [Boolean b] => Out (Returned (Boolean b)) st []
 | _, _ => Out (external name args) st [] end.

Section Pass.
Variable gen : computation.
Definition returns f vs v := forall st, evapp P (op gen) f vs st (Out (Returned v) st []).

Definition simple x := match x with
 | Pair h t => (symbol_is "quote" h && match t with Pair _ Nil => true | _ => false end) ||
               (symbol_is "lambda" h && match t with Pair _ _ => true | _ => false end)
 | _ => true end.

Lemma returns_def : forall f vs d v, P f = Some d -> List.length (params d) = List.length vs ->
 yields P (op gen) (arguments (params d) vs) (body d) v -> returns f vs v.
Proof. intros f vs d v D A Y st. apply (evapp_def P (op gen) f vs d st _ D A). apply Y. Qed.

Lemma returns_prim : forall f vs v, P f = None -> (forall st, op gen f vs st = Out (Returned v) st []) ->
 returns f vs v.
Proof. intros f vs v D O st. apply (evapp_op P (op gen) f vs st _ D). split; [apply returned_completed|apply O]. Qed.
Lemma yields_call_returns : forall rho f es vs v, Forall2 (yields P (op gen) rho) es vs ->
 returns f vs v -> yields P (op gen) rho (Call f es) v.
Proof. intros rho f es vs v F R. exact (yields_returns P (op gen) rho f es vs v F R). Qed.

Ltac decisions := repeat match goal with Q : _ = true |- _ => rewrite Q | Q : _ = false |- _ => rewrite Q end.
Ltac sel := cbv beta iota zeta fix delta [L fold_right negb andb orb symbol_is]; decisions;
 cbn [String.eqb Ascii.eqb Bool.eqb]; cbv beta iota zeta fix delta [L fold_right negb andb orb symbol_is].
Ltac Y := match goal with
 | |- yields _ _ _ (Lit _) _ => apply yields_lit
 | |- yields _ _ _ (Var _) _ => apply yields_var; reflexivity
 | |- yields _ _ _ (If _ _ _) _ => eapply yields_if; [Y|sel; Y]
 | |- yields _ _ _ (And _ _) _ => eapply yields_and; [Y|sel; Y]
 | |- yields _ _ _ (Or _ _) _ => eapply yields_or; [Y|sel; Y]
 | |- yields _ _ _ (Let _ _ _) _ => eapply yields_let; [Y|Y]
 | |- yields _ _ _ (Call _ _) _ => eapply yields_call_returns; [Yargs|R]
 end
with R := first
 [ solve [match goal with H : returns _ _ _ |- _ => apply H | H : forall _, returns _ _ _ |- _ => apply H
          | H : forall _ _, returns _ _ _ |- _ => apply H end]
 | eapply returns_prim; [reflexivity|intro; reflexivity]
 | eapply returns_def; [reflexivity|reflexivity|cbn [Native.body Native.params]; Y] ]
with Yargs := match goal with
 | |- Forall2 _ [] _ => constructor
 | |- Forall2 _ (_::_) _ => econstructor; [Y|Yargs]
 end.
Ltac body := eapply returns_def; [reflexivity|reflexivity|cbn [Native.body Native.params]].

Lemma not_returns : forall b, returns "kl:not" [Boolean b] (Boolean (negb b)).
Proof. intros [|]; body; Y. Qed.

Lemma simple_returns : forall x, returns "kl:_scm.simple-scheme-expression?" [x] (Boolean (simple x)).
Proof.
 intros x. assert (N := not_returns).
 destruct x as [| s| | | | | |h t| |]; try (body; Y).
 destruct h as [|s| | | | | | | |]; try (body; Y).
 destruct (String.eqb "quote" s) eqn:Q; destruct (String.eqb "lambda" s) eqn:La;
 destruct t as [| | | | | | |a [| | | | | | | | |]| |]; cbn [simple symbol_is andb orb]; rewrite ?Q, ?La;
 body; Y.
Qed.
Definition has_comp xs := existsb (fun x => negb (simple x)) xs.
Lemma has_comp_returns : forall xs, returns "kl:_scm.has-computation?" [L xs] (Boolean (has_comp xs)).
Proof.
 assert (N := not_returns). assert (S := simple_returns).
 induction xs as [|x xs IH]; [body; Y|].
 cbn [has_comp existsb]. fold (has_comp xs).
 destruct (simple x) eqn:Sx; destruct (has_comp xs) eqn:Hx; cbn [negb orb]; body; Y.
Qed.

Lemma occurrences_returns : forall name v,
 returns "kl:occurrences" [Symbol name; v] (Integer (Z.of_nat (O.occurrences name v))).
Proof.
 intros name v; induction v as [| t | | | | | |a IHa b IHb| |]; try (cbn [O.occurrences]; body; Y).
 - cbn [O.occurrences]. destruct (String.eqb name t) eqn:E; body; Y.
 - cbn [O.occurrences]. rewrite Nat2Z.inj_add. body; Y.
Qed.

Lemma reverse_help_returns : forall xs acc,
 returns "kl:buri.kernel.reverse-help" [L xs; L acc] (L (rev_append xs acc)).
Proof.
 induction xs as [|x xs IH]; intro acc; [body; Y|].
 cbn [rev_append]. specialize (IH (x::acc)). body; Y.
Qed.
Lemma reverse_returns : forall r, returns "kl:reverse" [L r] (L (rev r)).
Proof.
 intro r. assert (H := reverse_help_returns r []). rewrite rev_append_rev, app_nil_r in H.
 body; Y.
Qed.

(* merge-nested-lets on exactly the three shapes order-call-inputs feeds it:
   a call whose head is not let/let*, a let* form, or a one-binding let. *)
Definition merge_spec b1 inner :=
 let v := L [Symbol "let"; L [b1]; inner] in
 match inner with
 | Pair h t =>
   if symbol_is "let*" h then match t with Pair bs (Pair b Nil) => L [Symbol "let*"; Pair b1 bs; b] | _ => v end
   else if symbol_is "let" h then match t with
     | Pair (Pair b2 Nil) (Pair b Nil) => L [Symbol "let*"; L [b1; b2]; b] | _ => v end
   else v
 | _ => v end.
Lemma merge_call : forall b1 f args, String.eqb "let*" f = false -> String.eqb "let" f = false ->
 returns "kl:_scm.merge-nested-lets" [L [Symbol "let"; L [b1]; Pair (Symbol f) args]]
  (merge_spec b1 (Pair (Symbol f) args)).
Proof. intros b1 f args Q1 Q2. unfold merge_spec; cbn [symbol_is]; rewrite Q1, Q2. body; Y. Qed.
Lemma merge_star : forall b1 bs b,
 returns "kl:_scm.merge-nested-lets" [L [Symbol "let"; L [b1]; L [Symbol "let*"; bs; b]]]
  (merge_spec b1 (L [Symbol "let*"; bs; b])).
Proof. intros. unfold merge_spec. body; Y. Qed.
Lemma merge_let : forall b1 b2 b,
 returns "kl:_scm.merge-nested-lets" [L [Symbol "let"; L [b1]; L [Symbol "let"; L [b2]; b]]]
  (merge_spec b1 (L [Symbol "let"; L [b2]; b])).
Proof. intros. unfold merge_spec. body; Y. Qed.

(* ---------- fresh-call-variable: the actual loop with any generator ---------- *)
Definition guard := Call "eqv?" [Lit (Integer 0); Call "kl:occurrences" [Var "W5974"; Var "V5973"]].
Definition fresh_body := Let "W5974" (Call "kl:gensym" [Lit (Symbol "arg")])
 (If guard (Var "W5974") (Call "kl:_scm.fresh-call-variable" [Var "V5973"])).
Lemma fresh_def : P "kl:_scm.fresh-call-variable" = Some (Def ["V5973"] fresh_body).
Proof. reflexivity. Qed.
Lemma guard_symbol : forall u name,
 yields P (op gen) (Native.bind (arguments ["V5973"] [u]) "W5974" (Symbol name)) guard
  (Boolean (Z.eqb 0 (Z.of_nat (O.occurrences name u)))).
Proof. intros. assert (OC := occurrences_returns). unfold guard. Y. Qed.
Lemma guard_other : forall u w st, (forall name, w <> Symbol name) ->
 ev P (op gen) (Native.bind (arguments ["V5973"] [u]) "W5974" w) guard st (Out Unsupported st []).
Proof.
 intros u w st N. unfold guard.
 apply (ev_call_focus P (op gen) _ "eqv?" [Lit (Integer 0)] _ [] [Integer 0] [] st _);
  [constructor; [apply yields_lit|constructor]|constructor|].
 right. split; [|intros v; discriminate].
 apply (ev_call_yields P (op gen) _ _ _ [w; u]); [constructor; [apply yields_var; reflexivity|];
  constructor; [apply yields_var; reflexivity|constructor]|].
 eapply evapp_def; [reflexivity|reflexivity|]. cbn [Native.body Native.params].
 apply ev_if. right. split; [|intros v; discriminate].
 apply (ev_call_yields P (op gen) _ _ _ [w; u]); [constructor; [apply yields_var; reflexivity|];
  constructor; [apply yields_var; reflexivity|constructor]|].
 apply evapp_op; [reflexivity|]. split; [unfold completed; discriminate|].
 destruct w; try (exfalso; eapply N; reflexivity); reflexivity.
Qed.

Lemma answer_after : forall c st es e o, Out (Returned c) st es = after e o ->
 exists st' es', o = Out (Returned c) st' es'.
Proof. intros c st es e [r s t] E; unfold after in E; cbn in E; inversion E; subst; eauto. Qed.

Theorem fresh_fixed : forall n u st c st' es,
 apply n P (op gen) "kl:_scm.fresh-call-variable" [u] st = Out (Returned c) st' es ->
 exists name, c = Symbol name /\ O.occurrences name u = 0.
Proof.
 intro n; induction n as [n IH] using lt_wf_ind; intros u st c st' es H.
 unfold apply in H; rewrite fresh_def in H; cbn [Native.params Native.body List.length Nat.eqb] in H.
 destruct n as [|n1]; [discriminate H|].
 unfold fresh_body in H. cbn [eval_with] in H.
 destruct (bind_inv _ _ _ _ H (returned_completed c st' es)) as [[v [s1 [e1 [G [C1 E]]]]]|[G S]];
  [|exfalso; apply (S c); reflexivity].
 cbv beta in C1, E.
 destruct (answer_after _ _ _ _ _ E) as [s2 [e2 O]].
 destruct n1 as [|n2]; [discriminate O|]. cbn [eval_with] in O.
 destruct (bind_inv _ _ _ _ O (returned_completed c s2 e2)) as [[b [s3 [e3 [B [C2 E2]]]]]|[B S]];
  [|exfalso; apply (S c); reflexivity].
 cbv beta in C2, E2.
 destruct v as [| name | | | | | | | |];
  try (match type of B with eval_with _ _ _ (Native.bind _ _ ?w) _ _ = _ =>
        assert (NS : forall nm, w <> Symbol nm) by (intros nm Q; discriminate Q);
        pose proof (conv_fixed _ n2 s1 _ _ (eval_monotone _ _ _ _) B (returned_completed _ _ _)
         (guard_other u w s1 NS)) as X; discriminate X end).
 pose proof (yields_at P (op gen) n2 _ _ _ s1 _ (guard_symbol u name) B (returned_completed _ _ _)) as X.
 inversion X; subst b s3 e3. clear X.
 destruct (Z.of_nat (O.occurrences name u)) as [|q|q] eqn:Z; cbv beta iota delta [Z.eqb] in E2.
 1:{ destruct (answer_after _ _ _ _ _ E2) as [s4 [e4 V]].
   pose proof (yields_at P (op gen) n2 _ (Var "W5974") (Symbol name) s1 _
     (yields_var P (op gen) _ _ _ eq_refl) V (returned_completed _ _ _)) as V'.
   inversion V'; subst. exists name. split; [reflexivity|].
   lia. }
 all: destruct (answer_after _ _ _ _ _ E2) as [s4 [e4 V]];
   destruct n2 as [|n3]; [discriminate V|]; rewrite call_step in V; cbn [many] in V;
   destruct (bind_inv _ _ _ _ V (returned_completed c s4 e4)) as [[w [s5 [e5 [W [C3 E3]]]]]|[W S]];
    [|exfalso; apply (S c); reflexivity];
   pose proof (yields_at P (op gen) n3 _ (Var "V5973") u s1 _
     (yields_var P (op gen) _ _ _ eq_refl) W (returned_completed _ _ _)) as W';
   inversion W'; subst w s5 e5; cbv beta in E3; rewrite after_nil in E3;
   (eapply (IH n3); [lia|exact (eq_sym E3)]).
Qed.

Theorem fresh_success : forall u st c st' es,
 evapp P (op gen) "kl:_scm.fresh-call-variable" [u] st (Out (Returned c) st' es) ->
 exists name, c = Symbol name /\ O.occurrences name u = 0.
Proof. intros u st c st' es [_ [n H]]. exact (fresh_fixed n u st c st' es H). Qed.

(* ---------- order-call-inputs: every successful run, any generator ---------- *)
Definition keep x xs := simple x || negb (has_comp xs).
(* The exact decision structure of the captured loop: keep an argument when it
   is simple or no later argument computes; otherwise bind it to a name whose
   occurrence count in the used set is zero, then merge the binding. *)
Inductive Ord : list value -> list value -> value -> value -> Prop :=
| ord_done : forall r u, Ord [] r u (L (rev r))
| ord_keep : forall x xs r u o, keep x xs = true -> Ord xs (x::r) u o -> Ord (x::xs) r u o
| ord_lift : forall x xs r u name o, keep x xs = false -> O.occurrences name u = 0 ->
   Ord xs (Symbol name::r) (Pair (Symbol name) u) o ->
   Ord (x::xs) r u (merge_spec (L [Symbol name; x]) o).

Definition shaped f o := (exists args, o = Pair (Symbol f) args) \/
 (exists bs b, o = L [Symbol "let*"; bs; b]) \/ (exists b2 b, o = L [Symbol "let"; L [b2]; b]).
Definition bottom f (r xs : list value) := (exists r0, r = (r0 ++ [Symbol f])%list) \/ (r = [] /\ exists t, xs = Symbol f :: t).

Definition inputs_body :=
 If (Call "null?" [Var "V5977"]) (Call "kl:reverse" [Var "V5978"])
 (If (And (Call "pair?" [Var "V5977"])
   (Or (Call "kl:_scm.assert-boolean" [Call "kl:_scm.simple-scheme-expression?" [Call "car" [Var "V5977"]]])
    (Or (Call "kl:not" [Call "kl:_scm.has-computation?" [Call "cdr" [Var "V5977"]]]) (Lit (Boolean false)))))
  (Let "_scm.arg5981" (Call "cdr" [Var "V5977"])
   (Call "kl:_scm.order-call-inputs" [Var "_scm.arg5981"; Call "cons" [Call "car" [Var "V5977"]; Var "V5978"]; Var "V5979"]))
  (If (Call "pair?" [Var "V5977"])
   (Let "W5980" (Call "kl:_scm.fresh-call-variable" [Var "V5979"])
    (Call "kl:_scm.merge-nested-lets"
     [Call "cons" [Lit (Symbol "let");
       Let "_scm.arg5984" (Call "list" [Call "list" [Var "W5980"; Call "car" [Var "V5977"]]])
        (Call "list" [Var "_scm.arg5984";
          Let "_scm.arg5982" (Call "cdr" [Var "V5977"])
           (Let "_scm.arg5983" (Call "cons" [Var "W5980"; Var "V5978"])
            (Call "kl:_scm.order-call-inputs" [Var "_scm.arg5982"; Var "_scm.arg5983";
              Call "cons" [Var "W5980"; Var "V5979"]]))])]]))
   (Call "kl:shen.f-error" [Lit (Symbol "_scm.order-call-inputs")]))).
Lemma inputs_def : P "kl:_scm.order-call-inputs" = Some (Def ["V5977"; "V5978"; "V5979"] inputs_body).
Proof. reflexivity. Qed.

Lemma merge_shaped : forall f b1 o, String.eqb "let*" f = false -> String.eqb "let" f = false ->
 shaped f o -> returns "kl:_scm.merge-nested-lets" [L [Symbol "let"; L [b1]; o]] (merge_spec b1 o) /\
 shaped f (merge_spec b1 o).
Proof.
 intros f b1 o Q1 Q2 [[args E]|[[bs [b E]]|[b2 [b E]]]]; subst o.
 - split; [apply merge_call; assumption|]. right; right. exists b1, (Pair (Symbol f) args).
   unfold merge_spec; cbn [symbol_is]; rewrite Q1, Q2; reflexivity.
 - split; [apply merge_star|]. right; left. exists (Pair b1 bs), b. reflexivity.
 - split; [apply merge_let|]. right; left. exists (L [b1; b2]), b. reflexivity.
Qed.

Lemma returned_not_stopped : forall c st es, stops (Out (Returned c) st es) -> False.
Proof. intros c st es S; apply (S c); reflexivity. Qed.
Lemma after_returned : forall e o c st es, after e o = Out (Returned c) st es -> stops o -> False.
Proof. intros e [r s t] c st es E S; unfold after in E; cbn in E; inversion E; subst; apply (S c); reflexivity. Qed.

Ltac app_value H :=
  match type of H with evapp _ _ _ _ _ _ =>
    let C := fresh in let O := fresh in destruct H as [C [? O]]; unfold apply in O; cbn in O; subst end.

Ltac selH H := cbv beta iota zeta fix delta [L fold_right negb andb orb symbol_is] in H;
 repeat match goal with Q : _ = true |- _ => rewrite Q in H | Q : _ = false |- _ => rewrite Q in H end;
 cbv beta iota zeta fix delta [L fold_right negb andb orb symbol_is] in H.
Ltac cond H := match type of H with ev _ _ ?rho (If ?c _ _) _ _ =>
  let C := fresh "C" in eassert (C : yields P (op gen) rho c _) by Y;
  rewrite (ev_if_yields _ _ _ _ _ _ _ _ _ C) in H; selH H; clear C end.
Ltac letp H := match type of H with ev _ _ ?rho (Let _ ?a _) _ _ =>
  let C := fresh "C" in eassert (C : yields P (op gen) rho a _) by Y;
  rewrite (ev_let_yields _ _ _ _ _ _ _ _ _ C) in H; clear C end.
Ltac callp H := match type of H with ev _ _ ?rho (Call _ ?es) _ _ =>
  let A := fresh "A" in eassert (A : Forall2 (yields P (op gen) rho) es _) by Yargs;
  rewrite (ev_call_yields _ _ _ _ _ _ _ _ A) in H; clear A end.
Ltac focus H pre := match type of H with ev _ _ ?rho (Call _ _) _ _ =>
  let A := fresh "A" in eassert (A : Forall2 (yields P (op gen) rho) pre _) by Yargs;
  apply (ev_call_focus _ _ rho _ pre _ [] _ [] _ _ A (Forall2_nil _)) in H; clear A end.

Theorem inputs_success : forall f, String.eqb "let*" f = false -> String.eqb "let" f = false ->
 forall xs r u st c st' es, bottom f r xs ->
 evapp P (op gen) "kl:_scm.order-call-inputs" [L xs; L r; u] st (Out (Returned c) st' es) ->
 Ord xs r u c /\ shaped f c.
Proof.
 intros f Q1 Q2 xs. assert (RV := reverse_returns). assert (SR := simple_returns).
 assert (NR := not_returns). assert (HC := has_comp_returns). assert (FR := fresh_success).
 induction xs as [|x xs IH]; intros r u st c st' es Bot H;
  match type of H with evapp _ _ _ ?vs ?st ?out => rewrite (evapp_def P (op gen) _ vs _ st out inputs_def eq_refl) in H end;
  cbn [Native.body Native.params] in H; unfold inputs_body in H; cond H.
 - match type of H with ev _ _ ?rho ?e _ _ =>
     eassert (C2 : yields P (op gen) rho e _) by Y end.
   pose proof (yields_ev _ _ _ _ _ _ _ C2 H) as X. inversion X; subst c. clear X.
   split; [constructor|].
   destruct Bot as [[r0 E]|[_ [t E]]]; [|discriminate E]. subst r.
   left. rewrite rev_app_distr. exists (L (rev r0)). reflexivity.
 - destruct (simple x) eqn:Sx; destruct (has_comp xs) eqn:Hx; cond H.
   (* three keep cases *)
   1,2,4:
     letp H; callp H;
     (destruct (IH (x::r) u st c st' es) as [O Sh];
      [destruct Bot as [[r0 E]|[E [t T]]];
        [left; exists (x::r0); subst r; reflexivity|left; exists []; subst r; inversion T; reflexivity]
      |exact H|]);
     (split; [apply ord_keep; [unfold keep; rewrite Sx, Hx; reflexivity|exact O]|exact Sh]).
   (* lift: simple x = false, has_comp xs = true *)
   destruct Bot as [[r0 E]|[E [t T]]]; [|inversion T; subst x; discriminate Sx].
   cond H. apply ev_let in H.
   destruct H as [[v [s1 [e1 [o2 [F [M E1]]]]]]|[F S]]; [|exfalso; exact (returned_not_stopped _ _ _ S)].
   callp F. destruct (FR _ _ _ _ _ F) as [name [V Occ]]. subst v.
   focus M (@nil expr).
   destruct M as [[v' [s2 [e2 [o3 [CONS [MRG E2]]]]]]|[CONS S]];
    [|exfalso; exact (after_returned _ _ _ _ _ (eq_sym E1) S)].
   focus CONS [Lit (Symbol "let")].
   destruct CONS as [[v'' [s3 [e3 [o4 [LE [APP E3]]]]]]|[LE S]];
    [|exfalso; exact (returned_not_stopped _ _ _ S)].
   rewrite evapp_op in APP by reflexivity. destruct APP as [_ APP].
   cbn in APP. subst o4. unfold after in E3; cbn in E3. inversion E3; subst v' s2 e2. clear E3.
   letp LE. focus LE [Var "_scm.arg5984"].
   destruct LE as [[w [s4 [e4 [o5 [LE2 [APP2 E4]]]]]]|[LE2 S]];
    [|exfalso; exact (returned_not_stopped _ _ _ S)].
   rewrite evapp_op in APP2 by reflexivity. destruct APP2 as [_ APP2].
   cbn in APP2. subst o5. unfold after in E4; cbn in E4. inversion E4; subst v'' s3 e3. clear E4.
   letp LE2. letp LE2. callp LE2.
   destruct (IH (Symbol name :: r) (Pair (Symbol name) u) s1 w s4 e4) as [O Sh];
    [left; exists (Symbol name :: r0); subst r; reflexivity|exact LE2|].
   destruct (merge_shaped f (L [Symbol name; x]) w Q1 Q2 Sh) as [MR MS].
   pose proof (evapp_det _ _ _ _ _ _ _ MRG (MR s4)) as X. subst o3.
   subst o2. unfold after in E1; cbn in E1. inversion E1; subst; clear E1.
   split; [|exact MS].
   apply ord_lift; [unfold keep; rewrite Sx, Hx; reflexivity|exact Occ|exact O].
Qed.

Theorem order_call_success : forall f args st c st' es,
 String.eqb "let*" f = false -> String.eqb "let" f = false ->
 evapp P (op gen) "kl:_scm.order-call" [L (Symbol f :: args)] st (Out (Returned c) st' es) ->
 Ord (Symbol f :: args) [] (L (Symbol f :: args)) c /\ shaped f c.
Proof.
 intros f args st c st' es Q1 Q2 H.
 assert (D : P "kl:_scm.order-call" = Some (Def ["V5985"] (Call "kl:_scm.order-call-inputs" [Var "V5985"; Lit Nil; Var "V5985"]))) by reflexivity.
 rewrite (evapp_def P (op gen) _ [L (Symbol f :: args)] _ st _ D eq_refl) in H. cbn [Native.body Native.params] in H.
 callp H.
 apply (inputs_success f Q1 Q2 (Symbol f :: args) [] (L (Symbol f :: args)) st c st' es); [|exact H].
 right. split; [reflexivity|exists args; reflexivity].
Qed.
End Pass.
End OrderCallPass.
