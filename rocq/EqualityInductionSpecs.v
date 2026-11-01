(* Captured EQ-1 helper code (base.shen, equations.shen, spec/arithmetic.shen)
   computes the reference functions of EqualityInductionModel: every value the
   actual Native evaluator returns for these definitions is the reference
   value. Partial correctness, by induction on oracle fuel. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native NativeHelpers EqualityInductionOracle EqualityInductionModel
 EqualityInductionBaseInput EqualityInductionEquationsInput EqualityInductionTheoryInput EqualityInductionKernelInput.
Import ListNotations Native.Native.
Module EqualityInductionSpecs.
Module O := EqualityInductionOracle.EqualityInductionOracle.
Import EqualityInductionModel.EqualityInductionModel.
Open Scope string_scope.
Definition runtime_names := ["kl:=";"kl:_scm.assert-boolean";"kl:symbol?";"kl:str"].
Definition runtime := (filter (fun d => existsb (String.eqb (fst d)) runtime_names) NativeHelpers.helpers ++
 [("kl:not",Def ["x"] (If (Var "x") (Lit (Boolean false)) (Lit (Boolean true))))])%list.
Definition program := (eq1_kernel_program ++ eq1_equations_program ++ eq1_base_program ++ eq1_theory_program ++ runtime)%list.
Definition names := Eval vm_compute in map fst program.
Definition defined s := existsb (String.eqb s) names.
Lemma defined_lookup : forall s, defined s = match lookup program s with Some _ => true | None => false end.
Proof. intro s. unfold defined. rewrite <- O.defined_names. reflexivity. Qed.
Definition ask := O.oracle program defined.
Lemma ask_unfold : forall k s vs d, lookup program s = Some d ->
 ask (S k) s vs = if Nat.eqb (List.length (params d)) (List.length vs)
   then O.step defined (ask k) (arguments (params d) vs) (body d) else None.
Proof. intros; apply O.oracle_unfold; assumption. Qed.
Definition def_of name := match lookup program name with Some d => d | None => Def [] (Lit Nil) end.

(* Directed symbolic execution of one captured body. Calls into the program
   stay opaque [ask] hypotheses, discharged by specification lemmas [spec].
   Tests split on their outcome, not on the tested value; a value's shape is
   learnt only from a positive outcome, so failed tests do not multiply. *)
Ltac vvar y := is_var y; lazymatch type of y with value => idtac end.
Ltac decide_bool t := let r := eval vm_compute in t in match r with
 | true => let D := fresh "D" in assert (D : t = true) by (vm_compute; reflexivity); rewrite D in *; clear D
 | false => let D := fresh "D" in assert (D : t = false) by (vm_compute; reflexivity); rewrite D in *; clear D
 | _ => let E := fresh "S" in destruct t eqn:E
 end.
Ltac positive c := match c with
 | false => fail 1 | None => fail 1 | Boolean false => fail 1 | Symbol "missing" => fail 1 | _ => idtac end.
(* [injection] normalises its equations (it would unfold String.eqb). *)
Lemma some_inj : forall (a b : value), Some a = Some b -> a = b.
Proof. intros a b H; congruence. Qed.
Lemma bool_inj : forall a b, Boolean a = Boolean b -> a = b.
Proof. intros a b H; congruence. Qed.
Ltac tidy := repeat match goal with
 | E : (match _ with _ => _ end) = _ |- _ => progress cbn beta iota in E
 | E : ?a = ?b |- _ => constr_eq a b; clear E
 | E : _ = _ |- _ => discriminate E
 | E : Some _ = Some _ |- _ => injection E as E
 | E : Boolean _ = Boolean _ |- _ => injection E as E
 end.
(* A stuck test outcome [E]: learn the shape of the tested variable. *)
Ltac learn E := lazymatch type of E with
 | (match ?y with _ => _ end) = ?c => vvar y; positive c; destruct y; tidy
 end.
Ltac split_term t := lazymatch t with
 | match ?y with _ => _ end => first [is_var y; lazymatch type of t with expr => fail | _ => idtac end;
     let E := fresh "E" in destruct t eqn:E; try learn E
   | vvar y; destruct y
   | split_term y]
 | same ?a ?b => decide_bool (same a b)
 | String.eqb ?a ?b => decide_bool (String.eqb a b)
 | _ => lazymatch type of t with expr => fail | _ => let E := fresh "E" in destruct t eqn:E end
 end.
Ltac split_scrut t := first [vvar t; destruct t | split_term t].
Lemma bind_hit : forall rho s v, bind rho s v s = Some v.
Proof. intros; unfold bind; rewrite String.eqb_refl; reflexivity. Qed.
Lemma bind_miss : forall rho s v t, t <> s -> bind rho s v t = rho t.
Proof. intros; unfold bind; apply String.eqb_neq in H; rewrite H; reflexivity. Qed.
(* Environment lookups compare literal names only; bound values stay folded. *)
Ltac lookup_env H := cbn [arguments] in H;
 repeat first [rewrite bind_hit in H | rewrite bind_miss in H by discriminate];
 cbv beta in H.
Ltac finish H := lazymatch type of H with
 | Some _ = Some _ => injection H as H; finish H
 | None = Some _ => discriminate H
 | ?a = ?b => first [is_var b; subst b | is_var a; subst a | discriminate H | idtac]
 end.
Ltac run spec H :=
 lazymatch type of H with
 | O.step _ _ _ (Lit _) = Some _ => apply O.inv_lit in H; finish H
 | O.step _ _ _ (Var _) = Some _ => apply O.inv_var in H; lookup_env H; finish H
 | O.step _ _ _ (If _ _ _) = Some _ => let x := fresh "x" in let C := fresh "C" in
     apply O.inv_if in H; destruct H as (x & C & H); run spec C; branch spec H
 | O.step _ _ _ (Let _ _ _) = Some _ => let x := fresh "x" in let C := fresh "C" in
     apply O.inv_let in H; destruct H as (x & C & H); run spec C; run spec H
 | O.step _ _ _ (And _ _) = Some _ => let x := fresh "x" in let C := fresh "C" in
     apply O.inv_and in H; destruct H as (x & C & H); run spec C; branch spec H
 | O.step _ _ _ (Or _ _) = Some _ => let x := fresh "x" in let C := fresh "C" in
     apply O.inv_or in H; destruct H as (x & C & H); run spec C; branch spec H
 | O.step _ _ _ (Call _ _) = Some _ => let vs := fresh "vs" in let F := fresh "F" in
     apply O.inv_call in H; destruct H as (vs & F & H); args spec F; call spec H
 | O.step _ _ _ (match _ with _ => _ end) = Some _ => branch spec H
 | _ => branch spec H
 end
with args spec F := lazymatch type of F with
 | Forall2 _ nil _ => apply O.forall2_nil in F; subst
 | Forall2 _ (_::_) _ => let w := fresh "w" in let ws := fresh "ws" in
     let E := fresh "E" in let C := fresh "C" in
     apply O.forall2_cons in F; destruct F as (w & ws & E & C & F); subst; run spec C; args spec F
 end
with call spec H := lazymatch type of H with
 | (if defined ?s then _ else _) = Some _ =>
     let r := eval vm_compute in (defined s) in let D := fresh "D" in
     assert (D : defined s = r) by (vm_compute; reflexivity); rewrite D in H; clear D;
     cbn [external primitive] in H; call spec H
 | (if true then _ else _) = Some _ => cbn beta iota in H; call spec H
 | (if false then _ else _) = Some _ => cbn beta iota in H; call spec H
 | ask _ _ _ = Some _ => spec H
 | _ => branch spec H
 end
with branch spec H := cbn beta iota in H; lazymatch type of H with
 | O.step _ _ _ (match ?t with _ => _ end) = Some _ => split_scrut t; branch spec H
 | O.step _ _ _ _ = Some _ => run spec H
 | (match ?t with _ => _ end) = Some _ => split_scrut t; branch spec H
 | match ?t with _ => _ end => split_scrut t; branch spec H
 | ?a = ?b => finish H
 | _ => idtac
 end.
(* Close a leaf: learn remaining shapes from recorded test outcomes. *)
Ltac leaf := repeat match goal with
 | E : (match ?y with _ => _ end) = _ |- _ => vvar y; destruct y; tidy
 end.
Ltac rewrite_known := repeat match goal with
 | S : ?t = ?c |- context [?t] => lazymatch t with
   | same _ _ => rewrite S | String.eqb _ _ => rewrite S
   | _ => lazymatch c with true => rewrite S | false => rewrite S end end
 end.
(* Some reductions expose a name comparison as a raw match; fold it back. *)
Ltac refold := repeat match goal with
 | |- context [String.eqb ?a ?b] => match goal with
   | E : (match _ with _ => _ end) = ?c |- _ =>
     first [change (String.eqb a b = c) in E | change (c = String.eqb a b) in E]; rewrite E
   end
 end.
Ltac close := leaf; tidy; repeat match goal with E : ?a = ?b |- _ => is_var b; subst b end;
 cbn -[same String.eqb ask signature_value rules_value theory_value constructors_value]; rewrite_known; refold.
Ltac solve_leaf := close; cbn -[same String.eqb ask signature_value rules_value theory_value constructors_value]; try reflexivity;
 try (repeat (match goal with |- context [match ?y with _ => _ end] => vvar y; destruct y end); cbn -[signature_value rules_value theory_value constructors_value]; rewrite_known; reflexivity).
Ltac enter H := lazymatch type of H with ask (S ?k) ?s ?vs = _ =>
 let d := eval vm_compute in (def_of s) in
 let Lk := fresh "Lk" in
 assert (Lk : lookup program s = Some d) by (vm_compute; reflexivity);
 rewrite (ask_unfold k s vs d Lk) in H; clear Lk;
 cbn [Nat.eqb List.length params body arguments] in H end.
Ltac spec_proof hook := let H := fresh "H" in
 intro H; enter H; run hook H; solve_leaf.

(* Runtime contracts and base.shen. *)
Lemma ask_eq : forall k a b v, ask k "kl:=" [a;b] = Some v -> v = Boolean (same a b).
Proof. intros [|k] a b v; [discriminate|]. spec_proof ltac:(fun H => idtac). Qed.
Lemma ask_assert : forall k w u, ask k "kl:_scm.assert-boolean" [w] = Some u ->
 exists b, w = Boolean b /\ u = Boolean b.
Proof.
 intros [|k] w u H; [discriminate|]. enter H. run ltac:(fun H => idtac) H.
 all: leaf; eexists; split; reflexivity.
Qed.
Lemma ask_symbol : forall k w u, ask k "kl:symbol?" [w] = Some u -> u = Boolean (is_sym w).
Proof. intros [|k] w u; [discriminate|]. spec_proof ltac:(fun H => idtac). Qed.
Lemma ask_not : forall k w u, ask k "kl:not" [w] = Some u ->
 u = Boolean (match w with Boolean false => true | _ => false end).
Proof. intros [|k] w u; [discriminate|]. spec_proof ltac:(fun H => idtac). Qed.
Ltac use_assert H := let b := fresh "b" in let E1 := fresh "E" in let E2 := fresh "E" in
 apply ask_assert in H; destruct H as (b & E1 & E2); finish E2; finish E1.
Ltac known0 H := lazymatch type of H with
 | ask _ "kl:=" _ = _ => apply ask_eq in H; finish H
 | ask _ "kl:_scm.assert-boolean" _ = _ => use_assert H
 | ask _ "kl:symbol?" _ = _ => apply ask_symbol in H; finish H
 | ask _ "kl:not" _ = _ => apply ask_not in H; finish H
 end.
Lemma ask_member : forall k x ys v, ask k "kl:buri.member?" [x;ys] = Some v -> v = Boolean (r_mem x ys).
Proof. induction k as [|k IH]; intros x ys v; [discriminate|]. spec_proof ltac:(fun H => first [known0 H | apply IH in H; finish H]). Qed.
Ltac known1 H := first [known0 H | lazymatch type of H with
 | ask _ "kl:buri.member?" _ = _ => apply ask_member in H; finish H end].
Lemma ask_unique : forall k ys v, ask k "kl:buri.unique?" [ys] = Some v -> v = Boolean (r_uniq ys).
Proof. induction k as [|k IH]; intros ys v; [discriminate|]. spec_proof ltac:(fun H => first [known1 H | apply IH in H; finish H]). Qed.
Lemma ask_append : forall k xs ys v, ask k "kl:buri.append" [xs;ys] = Some v -> v = r_app xs ys.
Proof. induction k as [|k IH]; intros xs ys v; [discriminate|]. spec_proof ltac:(fun H => first [known1 H | apply IH in H; finish H]). Qed.
Lemma ask_revh : forall k xs a v, ask k "kl:buri.rev-h" [xs;a] = Some v -> v = r_revh xs a.
Proof. induction k as [|k IH]; intros xs a v; [discriminate|]. spec_proof ltac:(fun H => first [known1 H | apply IH in H; finish H]). Qed.
Lemma ask_rev : forall k xs v, ask k "kl:buri.rev" [xs] = Some v -> v = r_revh xs Nil.
Proof.
 intros [|k] xs v; [discriminate|].
 spec_proof ltac:(fun H => apply ask_revh in H; finish H).
Qed.
Lemma ask_get : forall k key xs v, ask k "kl:buri.get" [key;xs] = Some v -> v = r_get key xs.
Proof. induction k as [|k IH]; intros key xs v; [discriminate|]. spec_proof ltac:(fun H => first [known1 H | apply IH in H; finish H]). Qed.
Lemma ask_keys : forall k xs v, ask k "kl:buri.keys" [xs] = Some v -> v = r_keys xs.
Proof. induction k as [|k IH]; intros xs v; [discriminate|]. spec_proof ltac:(fun H => first [known1 H | apply IH in H; finish H]). Qed.
Lemma ask_remove : forall k key xs v, ask k "kl:buri.remove" [key;xs] = Some v -> v = r_remove key xs.
Proof. induction k as [|k IH]; intros key xs v; [discriminate|]. spec_proof ltac:(fun H => first [known1 H | apply IH in H; finish H]). Qed.
Lemma ask_allsym : forall k xs v, ask k "kl:buri.all-symbols?" [xs] = Some v -> v = Boolean (r_allsym xs).
Proof. induction k as [|k IH]; intros xs v; [discriminate|]. spec_proof ltac:(fun H => first [known1 H | apply IH in H; finish H]). Qed.
Lemma ask_nat : forall k n v, ask k "kl:buri.nat?" [n] = Some v ->
 v = Boolean false \/ (v = Boolean true /\ exists z, n = Integer z /\ (0 <= z)%Z).
Proof.
 intros [|k] n v H; [discriminate|]. enter H. run ltac:(fun H => first [known1 H | idtac]) H.
 all: close; try (left; reflexivity).
 all: try (destruct b; [|left; reflexivity]).
 all: right; split; [reflexivity|]; eexists; split; [reflexivity|]; apply Z.geb_le; assumption.
Qed.
Ltac known2 H := first [known1 H | lazymatch type of H with
 | ask _ "kl:buri.unique?" _ = _ => apply ask_unique in H; finish H
 | ask _ "kl:buri.append" _ = _ => apply ask_append in H; finish H
 | ask _ "kl:buri.rev" _ = _ => apply ask_rev in H; finish H
 | ask _ "kl:buri.get" _ = _ => apply ask_get in H; finish H
 | ask _ "kl:buri.keys" _ = _ => apply ask_keys in H; finish H
 | ask _ "kl:buri.remove" _ = _ => apply ask_remove in H; finish H
 | ask _ "kl:buri.all-symbols?" _ = _ => apply ask_allsym in H; finish H
 end].

(* Literal theory data and equations.shen. *)
Lemma ask_signature : forall k v, ask k "kl:buri.signature" [] = Some v -> v = signature_value.
Proof. intros [|k] v H; [discriminate|]. enter H. vm_compute in H. injection H as <-. reflexivity. Qed.
Lemma ask_constructors : forall k v, ask k "kl:buri.constructors" [] = Some v -> v = constructors_value.
Proof. intros [|k] v H; [discriminate|]. enter H. vm_compute in H. injection H as <-. reflexivity. Qed.
Lemma ask_rules : forall k v, ask k "kl:buri.rules" [] = Some v -> v = rules_value.
Proof. intros [|k] v H; [discriminate|]. enter H. vm_compute in H. injection H as <-. reflexivity. Qed.
Lemma ask_theory : forall k v, ask k "kl:buri.theory" [] = Some v -> v = theory_value.
Proof.
 intros [|k] v; [discriminate|]. spec_proof ltac:(fun H => first [apply ask_signature in H; finish H
   | apply ask_constructors in H; finish H | apply ask_rules in H; finish H]).
Qed.
Lemma ask_sig : forall k f ss v, ask k "kl:buri.sig" [f;ss] = Some v -> v = r_sig f ss.
Proof. induction k as [|k IH]; intros f ss v; [discriminate|]. spec_proof ltac:(fun H => first [known2 H | apply IH in H; finish H]). Qed.
Ltac known3 H := first [known2 H | lazymatch type of H with
 | ask _ "kl:buri.signature" _ = _ => apply ask_signature in H; finish H
 | ask _ "kl:buri.rules" _ = _ => apply ask_rules in H; finish H
 | ask _ "kl:buri.theory" _ = _ => apply ask_theory in H; finish H
 | ask _ "kl:buri.sig" _ = _ => apply ask_sig in H; finish H
 end].
Lemma ask_sorting : forall k,
 (forall t C v, ask k "kl:buri.sort" [t;C] = Some v -> v = r_sort t C) /\
 (forall g xs C v, ask k "kl:buri.sort-app" [g;xs;C] = Some v -> v =
   match sig_parts g with Some (sorts,r) => if r_args xs sorts C then found r else missing | None => missing end) /\
 (forall xs ss C v, ask k "kl:buri.args?" [xs;ss;C] = Some v -> v = Boolean (r_args xs ss C)).
Proof.
 induction k as [|k (IHs & IHp & IHa)]; [repeat split; intros; discriminate|].
 split; [|split].
 - intros t C v. spec_proof ltac:(fun H => first [known3 H | apply IHs in H; finish H | apply IHp in H; finish H | apply IHa in H; finish H]).
 - intros g xs C v. spec_proof ltac:(fun H => first [known3 H | apply IHs in H; finish H | apply IHp in H; finish H | apply IHa in H; finish H]).
 - intros xs ss C v. spec_proof ltac:(fun H => first [known3 H | apply IHs in H; finish H | apply IHp in H; finish H | apply IHa in H; finish H]).
Qed.
Lemma ask_sort : forall k t C v, ask k "kl:buri.sort" [t;C] = Some v -> v = r_sort t C.
Proof. intro k; exact (proj1 (ask_sorting k)). Qed.
End EqualityInductionSpecs.
