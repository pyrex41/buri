(* BURI/EQ-1 reference model. Total functions over raw Native values that
   mirror the Shen kernel and helper definitions (the captured code is proved
   to agree with them in EqualityInductionCorrect), the standard model of the
   BURI/ARITH-1 theory, and the semantic facts used for soundness: sorting,
   substitution, positional replacement and structural induction over expr. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Arithmetic Native.
Import ListNotations Native.Native.
Module EqualityInductionModel.
Open Scope string_scope.

Definition sym s := Symbol s.
Definition found v := L [Symbol "found";v].
Definition missing := Symbol "missing".
Definition is_sym v := match v with Symbol _ => true | _ => false end.
(* [v X] in the kernel: a pair headed by the symbol v with one more element. *)
Definition var_of t := match t with
 | Pair (Symbol s) (Pair x Nil) => if String.eqb "v" s then Some x else None
 | _ => None end.
Definition tagged tag v := match v with
 | Pair (Symbol s) (Pair x Nil) => if String.eqb tag s then Some x else None
 | _ => None end.

(* base.shen *)
Fixpoint r_mem x ys := match ys with Pair y r => same x y || r_mem x r | _ => false end.
Fixpoint r_uniq ys := match ys with Pair y r => negb (r_mem y r) && r_uniq r | _ => true end.
Fixpoint r_app xs ys := match xs with Pair x r => Pair x (r_app r ys) | _ => ys end.
Fixpoint r_revh xs a := match xs with Pair x r => r_revh r (Pair x a) | _ => a end.
Fixpoint r_get k xs := match xs with
 | Pair (Pair j (Pair v Nil)) r => if same k j then found v else r_get k r
 | _ => missing end.
Fixpoint r_keys xs := match xs with Pair (Pair k (Pair _ Nil)) r => Pair k (r_keys r) | _ => Nil end.
Fixpoint r_remove k xs := match xs with
 | Pair (Pair j (Pair v Nil)) r => if same k j then r else Pair (Pair j (Pair v Nil)) (r_remove k r)
 | _ => Nil end.
Fixpoint r_allsym xs := match xs with Nil => true | Pair x r => is_sym x && r_allsym r | _ => false end.
Fixpoint r_fresh xs ys := match xs with Pair x r => negb (r_mem x ys) && r_fresh r ys | _ => true end.

(* spec/arithmetic.shen, as literal data. *)
Definition sorts_value := L [sym "nat";sym "expr";sym "stack";sym "code";sym "outcome"].
Definition signature_value := L [
 L [sym "zero";Nil;sym "nat"]; L [sym "succ";L [sym "nat"];sym "nat"];
 L [sym "lit";L [sym "nat"];sym "expr"]; L [sym "add";L [sym "expr";sym "expr"];sym "expr"];
 L [sym "mul";L [sym "expr";sym "expr"];sym "expr"];
 L [sym "nil";Nil;sym "stack"]; L [sym "cons";L [sym "nat";sym "stack"];sym "stack"];
 L [sym "halt";Nil;sym "code"]; L [sym "push";L [sym "nat";sym "code"];sym "code"];
 L [sym "plus";L [sym "code"];sym "code"]; L [sym "times";L [sym "code"];sym "code"];
 L [sym "ok";L [sym "stack"];sym "outcome"]; L [sym "fault";Nil;sym "outcome"];
 L [sym "nadd";L [sym "nat";sym "nat"];sym "nat"]; L [sym "nmul";L [sym "nat";sym "nat"];sym "nat"];
 L [sym "eval";L [sym "expr"];sym "nat"]; L [sym "compile";L [sym "expr";sym "code"];sym "code"];
 L [sym "run";L [sym "code";sym "stack"];sym "outcome"]].
Definition constructors_value := L (map sym ["zero";"succ";"lit";"add";"mul";"nil";"cons";"halt";"push";"plus";"times";"ok";"fault"]).
Definition v x := L [sym "v";sym x].
Definition ap f xs := L (sym f::xs).
Definition rule_value name vars lhs rhs := L [sym name;L (map (fun p => L [sym (fst p);sym (snd p)]) vars);lhs;rhs].
Definition rules_value := L [
 rule_value "nadd-zero" [("y","nat")] (ap "nadd" [ap "zero" [];v "y"]) (v "y");
 rule_value "nadd-succ" [("x","nat");("y","nat")] (ap "nadd" [ap "succ" [v "x"];v "y"]) (ap "succ" [ap "nadd" [v "x";v "y"]]);
 rule_value "nmul-zero" [("y","nat")] (ap "nmul" [ap "zero" [];v "y"]) (ap "zero" []);
 rule_value "nmul-succ" [("x","nat");("y","nat")] (ap "nmul" [ap "succ" [v "x"];v "y"]) (ap "nadd" [v "y";ap "nmul" [v "x";v "y"]]);
 rule_value "eval-lit" [("n","nat")] (ap "eval" [ap "lit" [v "n"]]) (v "n");
 rule_value "eval-add" [("a","expr");("b","expr")] (ap "eval" [ap "add" [v "a";v "b"]]) (ap "nadd" [ap "eval" [v "a"];ap "eval" [v "b"]]);
 rule_value "eval-mul" [("a","expr");("b","expr")] (ap "eval" [ap "mul" [v "a";v "b"]]) (ap "nmul" [ap "eval" [v "a"];ap "eval" [v "b"]]);
 rule_value "compile-lit" [("n","nat");("k","code")] (ap "compile" [ap "lit" [v "n"];v "k"]) (ap "push" [v "n";v "k"]);
 rule_value "compile-add" [("a","expr");("b","expr");("k","code")] (ap "compile" [ap "add" [v "a";v "b"];v "k"]) (ap "compile" [v "a";ap "compile" [v "b";ap "plus" [v "k"]]]);
 rule_value "compile-mul" [("a","expr");("b","expr");("k","code")] (ap "compile" [ap "mul" [v "a";v "b"];v "k"]) (ap "compile" [v "a";ap "compile" [v "b";ap "times" [v "k"]]]);
 rule_value "run-halt" [("s","stack")] (ap "run" [ap "halt" [];v "s"]) (ap "ok" [v "s"]);
 rule_value "run-push" [("n","nat");("k","code");("s","stack")] (ap "run" [ap "push" [v "n";v "k"];v "s"]) (ap "run" [v "k";ap "cons" [v "n";v "s"]]);
 rule_value "run-plus" [("k","code");("x","nat");("y","nat");("s","stack")] (ap "run" [ap "plus" [v "k"];ap "cons" [v "y";ap "cons" [v "x";v "s"]]]) (ap "run" [v "k";ap "cons" [ap "nadd" [v "x";v "y"];v "s"]]);
 rule_value "run-times" [("k","code");("x","nat");("y","nat");("s","stack")] (ap "run" [ap "times" [v "k"];ap "cons" [v "y";ap "cons" [v "x";v "s"]]]) (ap "run" [v "k";ap "cons" [ap "nmul" [v "x";v "y"];v "s"]]);
 rule_value "plus-empty" [("k","code")] (ap "run" [ap "plus" [v "k"];ap "nil" []]) (ap "fault" []);
 rule_value "plus-short" [("k","code");("x","nat")] (ap "run" [ap "plus" [v "k"];ap "cons" [v "x";ap "nil" []]]) (ap "fault" []);
 rule_value "times-empty" [("k","code")] (ap "run" [ap "times" [v "k"];ap "nil" []]) (ap "fault" []);
 rule_value "times-short" [("k","code");("x","nat")] (ap "run" [ap "times" [v "k"];ap "cons" [v "x";ap "nil" []]]) (ap "fault" [])].
Definition theory_value := L [sym "buri-arith-1";signature_value;constructors_value;rules_value].

(* equations.shen *)
Fixpoint r_sig f ss := match ss with
 | Pair (Pair g (Pair a (Pair r Nil))) rest => if same f g then L [sym "signature";a;r] else r_sig f rest
 | _ => missing end.
Definition sig_parts v := match v with
 | Pair (Symbol s) (Pair a (Pair r Nil)) => if String.eqb "signature" s then Some (a,r) else None
 | _ => None end.
Fixpoint r_sort (t C : value) {struct t} : value := match var_of t with
 | Some x => r_get x C
 | None => match t with
   | Pair f args => match sig_parts (r_sig f signature_value) with
     | Some (sorts,r) => if r_args args sorts C then found r else missing
     | None => missing end
   | _ => missing end end
with r_args (xs ss C : value) {struct xs} : bool := match xs,ss with
 | Nil,Nil => true
 | Pair a xs,Pair s ss => same (r_sort a C) (found s) && r_args xs ss C
 | _,_ => false end.
Lemma r_sort_app : forall f args C, var_of (Pair f args) = None ->
 r_sort (Pair f args) C = match sig_parts (r_sig f signature_value) with
 | Some (sorts,r) => if r_args args sorts C then found r else missing | None => missing end.
Proof. intros f args C N. cbn [r_sort]. rewrite N. reflexivity. Qed.
Fixpoint r_ctxh C := match C with
 | Nil => true
 | Pair (Pair x (Pair s Nil)) r => is_sym x && r_mem s sorts_value && r_ctxh r
 | _ => false end.
Definition r_ctx C := r_ctxh C && r_uniq (r_keys C).
Definition subst_var x b := match tagged "found" b with Some t => t | None => L [sym "v";x] end.
(* Malformed inputs make the Shen code fail; the reference keeps them inert. *)
Fixpoint r_subst (t sub : value) {struct t} : value := match var_of t with
 | Some x => subst_var x (r_get x sub)
 | None => match t with
   | Pair f args => Pair f (r_substs args sub)
   | other => other end end
with r_substs (a sub : value) {struct a} : value := match a with
 | Pair u r => Pair (r_subst u sub) (r_substs r sub) | Nil => Nil | other => other end.
Lemma r_subst_app : forall f args sub, var_of (Pair f args) = None ->
 r_subst (Pair f args) sub = Pair f (r_substs args sub).
Proof.
 intros f args sub N. cbn [r_subst]. rewrite N. reflexivity.
Qed.
Fixpoint r_substitution vars sub C := match vars,sub with
 | Nil,Nil => true
 | Pair (Pair x (Pair s Nil)) vs,Pair (Pair x' (Pair t Nil)) ss =>
   if same x x' then same (r_sort t C) (found s) && r_substitution vs ss C else false
 | _,_ => false end.
Fixpoint r_rule n rs := match rs with
 | Pair (Pair m (Pair vs (Pair l (Pair r Nil)))) rest => if same n m then L [sym "rule";vs;l;r] else r_rule n rest
 | _ => missing end.

(* kernel.shen *)
Definition mismatch := Symbol "mismatch".
Definition rejected why := L [sym "rejected";sym why].
Fixpoint r_zip xs ys := match xs,ys with
 | Nil,Nil => L [sym "zipped";Nil]
 | Pair x xs,Pair y ys => match tagged "zipped" (r_zip xs ys) with
   | Some zs => L [sym "zipped";Pair (L [x;y]) zs] | None => mismatch end
 | _,_ => mismatch end.
Fixpoint r_vars ns := match ns with Pair n r => Pair (L [sym "v";n]) (r_vars r) | _ => Nil end.
Definition one x t := L [L [x;t]].
Fixpoint r_ihyps bs x g l r := match bs with
 | Pair (Pair a (Pair (Symbol e) Nil)) rest =>
   if String.eqb "expr" e
   then Pair (L [a;g;r_subst l (one x (L [sym "v";a]));r_subst r (one x (L [sym "v";a]))]) (r_ihyps rest x g l r)
   else r_ihyps rest x g l r
 | Pair _ rest => r_ihyps rest x g l r
 | _ => Nil end.
Definition r_resolve ref hs ls := match ref with
 | Pair (Symbol t) (Pair n Nil) =>
   if String.eqb "definition" t then r_rule n rules_value
   else if String.eqb "hypothesis" t then r_rule n hs
   else if String.eqb "lemma" t then r_rule n ls else missing
 | _ => missing end.
Definition r_inst rl sub C := match rl with
 | Pair (Symbol t) (Pair vs (Pair l (Pair r Nil))) =>
   if String.eqb "rule" t then
     if r_substitution vs sub C then L [sym "equation";r_subst l sub;r_subst r sub]
     else rejected "invalid-substitution"
   else rejected "unknown-rule"
 | _ => rejected "unknown-rule" end.
Definition r_head x ts := match tagged "replaced" x with
 | Some t => L [sym "replaced-args";Pair t ts] | None => mismatch end.
Definition r_tail t x := match tagged "replaced-args" x with
 | Some ts => L [sym "replaced-args";Pair t ts] | None => mismatch end.
Definition r_rapp f x := match tagged "replaced-args" x with
 | Some ts => L [sym "replaced";Pair f ts] | None => mismatch end.
Fixpoint r_replace t path a b {struct path} := match path with
 | Nil => if same t a then L [sym "replaced";b] else mismatch
 | Pair i is => match var_of t with
   | Some _ => mismatch
   | None => match t,i with
     | Pair f args,Integer z => if Z.leb 0 z then r_rapp f ((fix rarg args z := match args with
       | Pair x xs => if Z.eqb 0 z then r_head (r_replace x is a b) xs else r_tail x (rarg xs (z-1)%Z)
       | _ => mismatch end) args z) else mismatch
     | _,_ => mismatch end end
 | _ => mismatch end.
Fixpoint r_rarg args z is a b := match args with
 | Pair x xs => if Z.eqb 0 z then r_head (r_replace x is a b) xs else r_tail x (r_rarg xs (z-1)%Z is a b)
 | _ => mismatch end.
Lemma r_replace_step : forall t i is a b, r_replace t (Pair i is) a b = match var_of t with
 | Some _ => mismatch
 | None => match t,i with
   | Pair f args,Integer z => if Z.leb 0 z then r_rapp f (r_rarg args z is a b) else mismatch
   | _,_ => mismatch end end.
Proof.
 intros. cbn [r_replace]. destruct (var_of t); [reflexivity|]. destruct t; try reflexivity.
 destruct i; try reflexivity. destruct (Z.leb 0 z); [|reflexivity]. f_equal.
 revert z; induction t2; intro w; try reflexivity. cbn. rewrite IHt2_2. reflexivity.
Qed.
Definition is_missing v := match v with Symbol s => String.eqb s "missing" | _ => false end.
Definition r_goal C l r := r_ctx C && negb (is_missing (r_sort l C)) && same (r_sort l C) (r_sort r C).

(* The standard model of BURI/ARITH-1. *)
Inductive datum := DNat (n : nat) | DExpr (e : Arithmetic.expr) | DStack (s : Arithmetic.stack)
 | DCode (c : Arithmetic.code) | DOut (o : Arithmetic.outcome).
Definition sname d := match d with
 | DNat _ => "nat" | DExpr _ => "expr" | DStack _ => "stack" | DCode _ => "code" | DOut _ => "outcome" end.
Definition apply_fn f ds :=
 if String.eqb f "zero" then match ds with [] => Some (DNat O) | _ => None end else
 if String.eqb f "succ" then match ds with [DNat n] => Some (DNat (S n)) | _ => None end else
 if String.eqb f "lit" then match ds with [DNat n] => Some (DExpr (Arithmetic.Lit n)) | _ => None end else
 if String.eqb f "add" then match ds with [DExpr a;DExpr b] => Some (DExpr (Arithmetic.Add a b)) | _ => None end else
 if String.eqb f "mul" then match ds with [DExpr a;DExpr b] => Some (DExpr (Arithmetic.Mul a b)) | _ => None end else
 if String.eqb f "nil" then match ds with [] => Some (DStack []) | _ => None end else
 if String.eqb f "cons" then match ds with [DNat n;DStack s] => Some (DStack (n::s)) | _ => None end else
 if String.eqb f "halt" then match ds with [] => Some (DCode Halt) | _ => None end else
 if String.eqb f "push" then match ds with [DNat n;DCode k] => Some (DCode (Push n k)) | _ => None end else
 if String.eqb f "plus" then match ds with [DCode k] => Some (DCode (Plus k)) | _ => None end else
 if String.eqb f "times" then match ds with [DCode k] => Some (DCode (Times k)) | _ => None end else
 if String.eqb f "ok" then match ds with [DStack s] => Some (DOut (Ok s)) | _ => None end else
 if String.eqb f "fault" then match ds with [] => Some (DOut Fault) | _ => None end else
 if String.eqb f "nadd" then match ds with [DNat x;DNat y] => Some (DNat (nadd x y)) | _ => None end else
 if String.eqb f "nmul" then match ds with [DNat x;DNat y] => Some (DNat (nmul x y)) | _ => None end else
 if String.eqb f "eval" then match ds with [DExpr e] => Some (DNat (Arithmetic.eval e)) | _ => None end else
 if String.eqb f "compile" then match ds with [DExpr e;DCode k] => Some (DCode (Arithmetic.compile e k)) | _ => None end else
 if String.eqb f "run" then match ds with [DCode k;DStack s] => Some (DOut (Arithmetic.run k s)) | _ => None end else
 None.
Definition environment := string -> option datum.
Fixpoint denote (rho : environment) t := match var_of t with
 | Some (Symbol x) => rho x
 | Some _ => None
 | None => match t with
   | Pair (Symbol f) args => match (fix dl a := match a with
     | Nil => Some []
     | Pair u r => match denote rho u,dl r with Some d,Some ds => Some (d::ds) | _,_ => None end
     | _ => None end) args with Some ds => apply_fn f ds | None => None end
   | _ => None end end.
Fixpoint denotes rho a := match a with
 | Nil => Some []
 | Pair u r => match denote rho u,denotes rho r with Some d,Some ds => Some (d::ds) | _,_ => None end
 | _ => None end.
Lemma denote_app : forall rho f args, var_of (Pair (Symbol f) args) = None ->
 denote rho (Pair (Symbol f) args) = match denotes rho args with Some ds => apply_fn f ds | None => None end.
Proof.
 intros rho f args N. cbn [denote]. rewrite N.
 replace ((fix dl a := match a with
   | Nil => Some []
   | Pair u r => match denote rho u,dl r with Some d,Some ds => Some (d::ds) | _,_ => None end
   | _ => None end) args) with (denotes rho args); [reflexivity|].
 clear N; induction args; try reflexivity. cbn. rewrite IHargs2. reflexivity.
Qed.
Lemma denote_atom : forall rho t, match t with Pair _ _ => False | _ => True end -> denote rho t = None.
Proof. intros rho [] H; try contradiction; reflexivity. Qed.
(* A well-typed environment for a raw context: every bound key is a symbol
   whose value has the recorded sort. *)
Definition env_ok (rho : environment) C := forall k s, r_get k C = found s ->
 exists x d, k = Symbol x /\ rho x = Some d /\ s = Symbol (sname d).
Definition valid C l r := forall rho, env_ok rho C -> denote rho l <> None /\ denote rho l = denote rho r.

(* Facts about the runtime equality [same]. *)
Lemma same_refl : forall a, same a a = true.
Proof.
 induction a; cbn; try apply String.eqb_refl; try apply Z.eqb_refl; try apply Bool.eqb_reflx.
 - reflexivity.
 - rewrite IHa1, IHa2; reflexivity.
 - apply Ascii.eqb_refl.
 - apply PeanoNat.Nat.eqb_refl.
Qed.
Lemma same_symbol : forall a s, same a (Symbol s) = true -> a = Symbol s.
Proof. intros a s H; destruct a; cbn in H; try discriminate. apply String.eqb_eq in H; subst; reflexivity. Qed.
Lemma same_symbol_l : forall a s, same (Symbol s) a = true -> a = Symbol s.
Proof. intros a s H; destruct a; cbn in H; try discriminate. apply String.eqb_eq in H; subst; reflexivity. Qed.
Lemma same_nil : forall a, same a Nil = true -> a = Nil.
Proof. intros [] H; cbn in H; try discriminate; reflexivity. Qed.
Lemma same_pair : forall a b c, same a (Pair b c) = true ->
 exists x y, a = Pair x y /\ same x b = true /\ same y c = true.
Proof. intros a0 b c H; destruct a0; cbn in H; try discriminate. apply andb_true_iff in H as [H1 H2]; eauto. Qed.
Lemma same_pair_l : forall a b c, same (Pair b c) a = true ->
 exists x y, a = Pair x y /\ same b x = true /\ same c y = true.
Proof. intros a0 b c H; destruct a0; cbn in H; try discriminate. apply andb_true_iff in H as [H1 H2]; eauto. Qed.
Lemma same_found : forall a s, same a (found s) = true -> exists t, a = found t /\ same t s = true.
Proof.
 intros a s H. apply same_pair in H as (x & y & -> & X & Y). apply same_symbol in X; subst.
 apply same_pair in Y as (u & w & -> & U & W). apply same_nil in W; subst. exists u; split; [reflexivity|exact U].
Qed.
Lemma is_sym_same : forall a b, same a b = true -> is_sym a = is_sym b.
Proof. intros a0 [] H; destruct a0; cbn in H; try discriminate; reflexivity. Qed.
Lemma var_of_same : forall a b, same a b = true -> match var_of a,var_of b with
 | Some x,Some y => same x y = true | None,None => True | _,_ => False end.
Proof.
 intros a b H. destruct a; destruct b; cbn -[String.eqb] in H; try discriminate; cbn -[String.eqb]; try exact I.
 apply andb_true_iff in H as [H1 H2].
 destruct a1; destruct b1; cbn in H1; try discriminate; cbn -[String.eqb]; try exact I.
 apply String.eqb_eq in H1; subst.
 destruct a2; destruct b2; cbn -[String.eqb] in H2; try discriminate; cbn -[String.eqb]; try exact I.
 apply andb_true_iff in H2 as [H2 H3].
 destruct a2_2; destruct b2_2; cbn -[String.eqb] in H3; try discriminate; cbn -[String.eqb]; try exact I.
 destruct (String.eqb "v" s0); [exact H2|exact I].
Qed.
Lemma same_denote : forall a b rho, same a b = true ->
 denote rho a = denote rho b /\ denotes rho a = denotes rho b.
Proof.
 induction a; intros b0 rho H; destruct b0 as [| | | | | | |b1 b2| |]; cbn in H; try discriminate; try (split; reflexivity).
 apply andb_true_iff in H as [H1 H2].
 destruct (IHa1 _ rho H1) as [D1 _]; destruct (IHa2 _ rho H2) as [D2 L2].
 split; [|cbn [denotes]; rewrite D1, L2; reflexivity].
 assert (V := var_of_same (Pair a1 a2) (Pair b1 b2) (andb_true_intro (conj H1 H2))).
 destruct (var_of (Pair a1 a2)) as [x|] eqn:A; destruct (var_of (Pair b1 b2)) as [y|] eqn:B; try contradiction.
 - cbn [denote]. rewrite A, B. destruct x; destruct y; cbn in V; try discriminate; try reflexivity.
   apply String.eqb_eq in V; subst; reflexivity.
 - destruct a1; destruct b1; cbn in H1; try discriminate; try reflexivity.
   apply String.eqb_eq in H1; subst. rewrite !denote_app by assumption. rewrite L2. reflexivity.
Qed.

(* Typing: a sorted term denotes a value of its sort. *)
Fixpoint typed (ds : list datum) sorts := match ds,sorts with
 | [],Nil => True
 | d::ds,Pair s ss => s = Symbol (sname d) /\ typed ds ss
 | _,_ => False end.
Lemma signature_sound : forall f sorts r, sig_parts (r_sig f signature_value) = Some (sorts,r) ->
 exists g, f = Symbol g /\ forall ds, typed ds sorts -> exists d, apply_fn g ds = Some d /\ r = Symbol (sname d).
Proof.
 intros f sorts r H. unfold signature_value, sym in H. cbn [L fold_right r_sig] in H.
 repeat match type of H with
 | context [same f (Symbol ?g)] => let E := fresh in destruct (same f (Symbol g)) eqn:E;
     [apply same_symbol in E; subst f; cbn in H; injection H as <- <-; exists g; split; [reflexivity|]|]
 end.
 all: try (cbn in H; discriminate H).
 all: intros ds T;
 repeat match goal with
   | T : False |- _ => contradiction
   | T : True |- _ => clear T
   | T : _ /\ _ |- _ => destruct T
   | T : Symbol _ = Symbol (sname ?d) |- _ => destruct d; cbn in T; try discriminate T; clear T
   | T : typed ?ds _ |- _ => is_var ds; destruct ds; cbn in T
   | T : typed _ _ |- _ => progress cbn in T
 end; eexists; split; reflexivity.
Qed.
Lemma sort_sound : forall t C rho, env_ok rho C ->
 (forall s, r_sort t C = found s -> exists d, denote rho t = Some d /\ s = Symbol (sname d)) /\
 (forall sorts, r_args t sorts C = true -> exists ds, denotes rho t = Some ds /\ typed ds sorts).
Proof.
 intros t C rho OK; induction t; split; intros s0 H; try discriminate;
 try (destruct s0; cbn in H; try discriminate; exists []; split; [reflexivity|exact I]).
 - destruct (var_of (Pair t1 t2)) as [x|] eqn:V.
   + cbn [r_sort] in H; rewrite V in H. destruct (OK _ _ H) as (y & d & -> & R & S).
     exists d; split; [|exact S]. cbn [denote]; rewrite V; exact R.
   + rewrite r_sort_app in H by exact V.
     destruct (sig_parts _) as [[sorts r]|] eqn:G; [|discriminate].
     destruct (r_args t2 sorts C) eqn:A; [|discriminate].
     injection H as H; subst r. destruct (signature_sound _ _ _ G) as (g & -> & T).
     destruct (proj2 IHt2 _ A) as (ds & D & Y). destruct (T _ Y) as (d & F & S).
     exists d; split; [|exact S]. rewrite denote_app by exact V. rewrite D; exact F.
 - destruct s0; cbn in H; try discriminate. apply andb_true_iff in H as [H1 H2].
   apply same_found in H1 as (t & E & S). destruct (proj1 IHt1 _ E) as (d & D & ->).
   apply same_symbol_l in S. destruct (proj2 IHt2 _ H2) as (ds & Ds & Y).
   exists (d::ds); split; [cbn [denotes]; rewrite D, Ds; reflexivity|split; assumption].
Qed.
Lemma sort_denotes : forall t C rho s, env_ok rho C -> r_sort t C = found s ->
 exists d, denote rho t = Some d /\ s = Symbol (sname d).
Proof. intros; eapply sort_sound; eauto. Qed.

(* Substitution: denotation in the extended environment. *)
Definition keys_sym sub := forall k t, r_get k sub = found t -> exists x, k = Symbol x.
Definition extend (rho : environment) sub : environment := fun x =>
 match tagged "found" (r_get (Symbol x) sub) with Some t => denote rho t | None => rho x end.
Lemma tagged_found : forall v t, tagged "found" v = Some t -> v = found t.
Proof.
 intros a0 t H; destruct a0 as [| | | | | | |v1 v2| |]; cbn -[String.eqb] in H; try discriminate. destruct v1; try discriminate.
 destruct v2; try discriminate. destruct v2_2; try discriminate.
 destruct (String.eqb "found" s) eqn:E; [|discriminate]. apply String.eqb_eq in E; subst.
 injection H as ->; reflexivity.
Qed.
Lemma subst_sound : forall sub rho, keys_sym sub -> forall t,
 denote rho (r_subst t sub) = denote (extend rho sub) t /\
 denotes rho (r_substs t sub) = denotes (extend rho sub) t.
Proof.
 intros sub rho K t; induction t; split; try reflexivity.
 - destruct (var_of (Pair t1 t2)) as [x|] eqn:V.
   + cbn [r_subst]; rewrite V. cbn [denote]; rewrite V. unfold subst_var.
     destruct (tagged "found" (r_get x sub)) as [u|] eqn:T.
     * apply tagged_found in T. destruct (K _ _ T) as [y ->].
       unfold extend. rewrite T. reflexivity.
     * cbn. destruct x; try reflexivity. unfold extend. rewrite T. reflexivity.
   + rewrite r_subst_app by exact V.
     assert (V' : var_of (Pair t1 (r_substs t2 sub)) = None).
     { destruct t1; try reflexivity. destruct t2; try reflexivity. destruct t2_2; try discriminate V; try reflexivity.
       cbn -[String.eqb] in V |- *. destruct (String.eqb "v" s); [discriminate|reflexivity]. }
     destruct t1; try (rewrite !denote_atom; reflexivity);
     try (cbn [denote]; rewrite V, V'; reflexivity).
     rewrite !denote_app by assumption. rewrite (proj2 IHt2). reflexivity.
 - cbn [r_substs denotes]. rewrite (proj1 IHt1), (proj2 IHt2). reflexivity.
Qed.

(* Positional replacement under a true equation preserves denotation. *)
Lemma tagged_shape : forall tag v t, tagged tag v = Some t -> v = L [Symbol tag;t].
Proof.
 intros tag a0 t H; destruct a0 as [| | | | | | |v1 v2| |]; cbn -[String.eqb] in H; try discriminate. destruct v1; try discriminate.
 destruct v2; try discriminate. destruct v2_2; try discriminate.
 destruct (String.eqb tag s) eqn:E; [|discriminate]. apply String.eqb_eq in E; subst.
 injection H as ->; reflexivity.
Qed.
Lemma tagged_L : forall tag t, tagged tag (L [Symbol tag;t]) = Some t.
Proof. intros; cbn. rewrite String.eqb_refl. reflexivity. Qed.
(* Replacement keeps the list spine. *)
Fixpoint spine a b := match a,b with
 | Pair _ x,Pair _ y => spine x y
 | Pair _ _,_ | _,Pair _ _ => False
 | x,y => x = y end.
Lemma spine_refl : forall a, spine a a.
Proof. induction a; cbn; auto. Qed.
Lemma spine_var : forall f a b, spine a b -> var_of (Pair f a) = None -> var_of (Pair f b) = None.
Proof.
 intros f a b S V. destruct f; try reflexivity.
 destruct a as [| | | | | | |x xs| |]; destruct b as [| | | | | | |y ys| |]; cbn in S; try contradiction;
 try (subst; exact V); try reflexivity.
 destruct ys; try reflexivity. destruct xs; cbn in S; try contradiction; try discriminate S.
 cbn -[String.eqb] in V |- *. destruct (String.eqb "v" s); [discriminate|reflexivity].
Qed.
Lemma replace_sound : forall path rho a b, denote rho a = denote rho b ->
 forall t t', r_replace t path a b = L [Symbol "replaced";t'] -> denote rho t = denote rho t'.
Proof.
 intros path rho a b E; induction path; intros t t' H; try discriminate.
 - cbn in H. destruct (same t a) eqn:S; [|discriminate]. injection H as <-.
   rewrite (proj1 (same_denote _ _ rho S)); exact E.
 - rewrite r_replace_step in H. destruct (var_of t) eqn:V; [discriminate|].
   destruct t as [| | | | | | |f args| |]; try discriminate. destruct path1; try discriminate.
   destruct (Z.leb 0 z); [|discriminate].
   assert (R : forall xs w ts, r_rarg xs w path2 a b = L [Symbol "replaced-args";ts] ->
     spine xs ts /\ denotes rho xs = denotes rho ts).
   { intro xs; induction xs as [| | | | | | |x _ xs' IHx| |]; intros w ts Q; try discriminate.
     cbn [r_rarg] in Q. destruct (Z.eqb 0 w).
     - unfold r_head in Q. destruct (tagged "replaced" (r_replace x path2 a b)) eqn:T; [|discriminate].
       apply tagged_shape in T. cbn in Q. injection Q as <-. split; [cbn; apply spine_refl|].
       cbn [denotes]. rewrite (IHpath2 _ _ T). reflexivity.
     - unfold r_tail in Q. destruct (tagged "replaced-args" (r_rarg xs' (w-1) path2 a b)) eqn:T; [|discriminate].
       apply tagged_shape in T. cbn in Q. injection Q as <-. destruct (IHx _ _ T) as [Sp D].
       split; [exact Sp|]. cbn [denotes]. rewrite D. reflexivity. }
   unfold r_rapp in H. destruct (tagged "replaced-args" (r_rarg args z path2 a b)) eqn:T; [|discriminate].
   apply tagged_shape in T. cbn in H. injection H as <-. destruct (R _ _ _ T) as [Sp D].
   assert (V' : var_of (Pair f v0) = None).
   { exact (spine_var _ _ _ Sp V). }
   destruct f; try (rewrite !denote_atom; reflexivity); try (cbn [denote]; rewrite V, V'; reflexivity).
   rewrite !denote_app by assumption. rewrite D. reflexivity.
Qed.

(* Denotation depends only on the variables a sorted term may mention. *)
Definition agree C (rho1 rho2 : environment) :=
 forall k s z, r_get k C = found s -> k = Symbol z -> rho1 z = rho2 z.
Lemma denote_agree : forall t C rho1 rho2, agree C rho1 rho2 ->
 (forall s, r_sort t C = found s -> denote rho1 t = denote rho2 t) /\
 (forall sorts, r_args t sorts C = true -> denotes rho1 t = denotes rho2 t).
Proof.
 intros t C rho1 rho2 A; induction t; split; intros s0 H; try discriminate; try reflexivity.
 - destruct (var_of (Pair t1 t2)) as [x|] eqn:V.
   + cbn [r_sort] in H; rewrite V in H. cbn [denote]; rewrite V.
     destruct x; try reflexivity. exact (A _ _ _ H eq_refl).
   + rewrite r_sort_app in H by exact V.
     destruct (sig_parts _) as [[sorts r]|] eqn:G; [|discriminate].
     destruct (r_args t2 sorts C) eqn:R; [|discriminate].
     destruct (signature_sound _ _ _ G) as (g & -> & _).
     rewrite !denote_app by exact V. rewrite (proj2 IHt2 _ R). reflexivity.
 - destruct s0; cbn in H; try discriminate. apply andb_true_iff in H as [H1 H2].
   apply same_found in H1 as (t & E & _). cbn [denotes].
   rewrite (proj1 IHt1 _ E), (proj2 IHt2 _ H2). reflexivity.
Qed.

(* Rules and their truth. A rule holds at [rho] when every well-typed
   assignment of its own variables, agreeing with [rho] elsewhere, makes its
   two sides denote the same value. *)
Definition holds (rho : environment) vars l r := forall rho', env_ok rho' vars ->
 (forall x, r_get (Symbol x) vars = missing -> rho' x = rho x) -> denote rho' l = denote rho' r.
Definition rules_true (rho : environment) rs := forall n vars l r,
 r_rule n rs = L [sym "rule";vars;l;r] -> keys_sym vars /\ holds rho vars l r.
Lemma r_get_cases : forall k xs, r_get k xs = missing \/ exists v, r_get k xs = found v.
Proof.
 intros k xs; induction xs; try (left; reflexivity).
 destruct xs1; try (left; reflexivity). destruct xs1_2; try (left; reflexivity).
 destruct xs1_2_2; try (left; reflexivity). cbn [r_get].
 destruct (same k xs1_1); [right; eexists; reflexivity|exact IHxs2].
Qed.
Lemma substitution_env : forall vars sub C rho, r_substitution vars sub C = true ->
 keys_sym vars -> env_ok rho C ->
 env_ok (extend rho sub) vars /\ keys_sym sub /\
 (forall x, r_get (Symbol x) vars = missing -> extend rho sub x = rho x).
Proof.
 induction vars as [| | | | | | |e _ vs IH| |]; intros sub C rho H K OK; cbn in H; try discriminate.
 - destruct sub; try discriminate.
   split; [intros k s G; discriminate G|]. split; [intros k t G; discriminate G|].
   intros x _. reflexivity.
 - destruct e as [| | | | | | |x e| |]; try discriminate. destruct e as [| | | | | | |s e| |]; try discriminate.
   destruct e; try discriminate.
   destruct sub as [| | | | | | |f ss| |]; try discriminate.
   destruct f as [| | | | | | |x' f| |]; try discriminate. destruct f as [| | | | | | |t f| |]; try discriminate.
   destruct f; try discriminate.
   destruct (same x x') eqn:X; [|discriminate]. apply andb_true_iff in H as [S H].
   assert (Kx : exists y, x = Symbol y).
   { apply (K x s). cbn [r_get]. rewrite same_refl. reflexivity. }
   destruct Kx as [y ->]. apply same_symbol_l in X; subst x'.
   assert (Kv : keys_sym vs).
   { intros k u G. destruct (same k (Symbol y)) eqn:E.
     - apply same_symbol in E; subst; eauto.
     - apply (K k u). cbn [r_get]. rewrite E. exact G. }
   destruct (IH _ _ _ H Kv OK) as (E & Ks & Ag).
   apply same_found in S as (s' & T & S').
   destruct (sort_denotes _ _ _ _ OK T) as (d & D & ->). apply same_symbol_l in S'.
   split; [|split].
   + intros k u G. cbn [r_get] in G. destruct (same k (Symbol y)) eqn:Q.
     * apply same_symbol in Q; subst k. injection G as <-. exists y, d. split; [reflexivity|].
       split; [|exact S']. unfold extend. cbn [r_get]. rewrite same_refl. exact D.
     * destruct (E _ _ G) as (z & d' & -> & D' & U). exists z, d'. split; [reflexivity|]. split; [|exact U].
       unfold extend in D' |- *. cbn [r_get]. rewrite Q. exact D'.
   + intros k u G. cbn [r_get] in G. destruct (same k (Symbol y)) eqn:Q.
     * apply same_symbol in Q; subst; eauto.
     * exact (Ks _ _ G).
   + intros z G. cbn [r_get] in G |- *. destruct (same (Symbol z) (Symbol y)) eqn:Q; [discriminate|].
     unfold extend in Ag |- *. cbn [r_get]. rewrite Q. apply Ag. exact G.
Qed.
Definition table_true rho hs ls := rules_true rho rules_value /\ rules_true rho hs /\ rules_true rho ls.
Lemma instance_sound : forall rho ref hs ls sub C a b, table_true rho hs ls -> env_ok rho C ->
 r_inst (r_resolve ref hs ls) sub C = L [sym "equation";a;b] -> denote rho a = denote rho b.
Proof.
 intros rho ref hs ls sub C a b (Td & Th & Tl) OK H.
 assert (G : forall rs, rules_true rho rs -> forall n, r_inst (r_rule n rs) sub C = L [sym "equation";a;b] ->
   denote rho a = denote rho b).
 { intros rs T n I. unfold r_inst in I. destruct (r_rule n rs) as [| | | | | | |v1 v2| |] eqn:R; try discriminate.
   destruct v1; try discriminate. destruct v2 as [| | | | | | |vars v2| |]; try discriminate.
   destruct v2 as [| | | | | | |l v2| |]; try discriminate. destruct v2 as [| | | | | | |r v2| |]; try discriminate.
   destruct v2; try discriminate. destruct (String.eqb "rule" s) eqn:Q; [|discriminate].
   apply String.eqb_eq in Q; subst s.
   destruct (r_substitution vars sub C) eqn:S; [|discriminate]. cbn in I. injection I as <- <-.
   destruct (T _ _ _ _ R) as [K Hd].
   destruct (substitution_env _ _ _ _ S K OK) as (E & Ks & Ag).
   rewrite (proj1 (subst_sound _ rho Ks l)), (proj1 (subst_sound _ rho Ks r)).
   apply Hd; [exact E|exact Ag]. }
 unfold r_resolve in H. destruct ref; try discriminate. destruct ref1; try discriminate.
 destruct ref2; try discriminate. destruct ref2_2; try discriminate.
 destruct (String.eqb "definition" s); [exact (G _ Td _ H)|].
 destruct (String.eqb "hypothesis" s); [exact (G _ Th _ H)|].
 destruct (String.eqb "lemma" s); [exact (G _ Tl _ H)|discriminate].
Qed.

(* Rule tables: lookup returns a member of the table. *)
Fixpoint entry_in e rs := match rs with Pair x rest => x = e \/ entry_in e rest | _ => False end.
Lemma rule_member : forall rs n vars l r, r_rule n rs = L [sym "rule";vars;l;r] ->
 exists m, entry_in (L [m;vars;l;r]) rs.
Proof.
 induction rs as [| | | | | | |e _ rest IH| |]; intros n0 vars l r H; try discriminate.
 cbn [r_rule] in H. destruct e as [| | | | | | |m e| |]; try discriminate.
 destruct e as [| | | | | | |vs e| |]; try discriminate. destruct e as [| | | | | | |l' e| |]; try discriminate.
 destruct e as [| | | | | | |r' e| |]; try discriminate. destruct e; try discriminate.
 destruct (same n0 m).
 - cbn in H. injection H as -> -> ->. exists m. left. reflexivity.
 - destruct (IH _ _ _ _ H) as [m' I]. exists m'. right. exact I.
Qed.
Lemma keys_sym_of : forall vars, r_allsym (r_keys vars) = true -> keys_sym vars.
Proof.
 induction vars as [| | | | | | |e _ rest IH| |]; intros A k t G; try discriminate.
 destruct e as [| | | | | | |x e| |]; try discriminate. destruct e as [| | | | | | |s e| |]; try discriminate.
 destruct e; try discriminate. cbn [r_get] in G. cbn [r_keys r_allsym] in A.
 apply andb_true_iff in A as [S A]. destruct (same k x) eqn:Q.
 - destruct x; try discriminate. apply same_symbol in Q. eauto.
 - exact (IH A _ _ G).
Qed.
Ltac grab E ps := lazymatch ps with
 | (?x,?s) :: ?rest =>
   let z := fresh "z" in let d := fresh "d" in let Hz := fresh "Hz" in let Hd := fresh "Hd" in let Hs := fresh "Hs" in
   destruct (E (Symbol x) (Symbol s) eq_refl) as (z & d & Hz & Hd & Hs); injection Hz as <-;
   destruct d; cbn in Hs; try discriminate Hs; clear Hs; grab E rest
 | [] => idtac
 end.
Lemma rules_value_true : forall rho, rules_true rho rules_value.
Proof.
 intros rho n vars l r H. apply rule_member in H as [m I].
 unfold rules_value in I. cbn [L fold_right entry_in] in I.
 repeat match type of I with
 | _ \/ _ => destruct I as [I|I]
 | False => contradiction
 end;
 match type of I with rule_value ?name ?ps ?l0 ?r0 = _ =>
   unfold rule_value in I; cbn [L fold_right map fst snd] in I; injection I as _ Ev El Er; subst vars l r;
   split; [apply keys_sym_of; reflexivity|];
   intros rho' E _; grab E ps; unfold v, ap, sym; cbn [L fold_right];
   repeat (rewrite denote_app by reflexivity; cbn [denotes]);
   cbn [denote var_of String.eqb Ascii.eqb Bool.eqb];
   repeat match goal with Hd : rho' ?x = Some _ |- _ => rewrite Hd; clear Hd end;
   reflexivity
 end.
Qed.

(* Structural induction over expr. A branch binds fresh, distinct names to
   the constructor's arguments; hypotheses hold for the expr arguments. *)
Fixpoint pfind (z : string) (ps : list (string * datum)) := match ps with
 | [] => None | (a,d)::ps => if String.eqb z a then Some d else pfind z ps end.
Definition bs_of (ps : list (string * datum)) := L (map (fun p => L [Symbol (fst p);Symbol (sname (snd p))]) ps).
Definition names_of (ps : list (string * datum)) := L (map (fun p => Symbol (fst p)) ps).
Lemma get_bs : forall ps z, r_get (Symbol z) (bs_of ps) =
 match pfind z ps with Some d => found (Symbol (sname d)) | None => missing end.
Proof.
 induction ps as [|[a d] ps IH]; intro z; [reflexivity|]. cbn [bs_of map L fold_right r_get pfind fst snd].
 cbn [same]. destruct (String.eqb z a); [reflexivity|]. apply IH.
Qed.
Lemma get_bs_nonsym : forall ps k, is_sym k = false -> r_get k (bs_of ps) = missing.
Proof.
 induction ps as [|[a d] ps IH]; intros k N; [reflexivity|]. cbn [bs_of map L fold_right r_get fst snd].
 destruct k; try discriminate; apply IH; exact N.
Qed.
Lemma get_app : forall ps G k, r_get k (r_app (bs_of ps) G) =
 match tagged "found" (r_get k (bs_of ps)) with Some s => found s | None => r_get k G end.
Proof.
 induction ps as [|[a d] ps IH]; intros G k; [reflexivity|]. cbn [bs_of map L fold_right r_app r_get fst snd].
 destruct (same k (Symbol a)); [reflexivity|]. apply IH.
Qed.
Lemma ctx_keys : forall C, r_ctxh C = true -> keys_sym C.
Proof.
 induction C as [|s1|s2|z1|n1 d1|t1|b1|e _ rest IH|c1|h1]; intros H k t G; try discriminate.
 destruct e as [| | | | | | |x e| |]; try discriminate. destruct e as [| | | | | | |s e| |]; try discriminate.
 destruct e; try discriminate. cbn [r_ctxh] in H. cbn [r_get] in G.
 apply andb_true_iff in H as [H R]. apply andb_true_iff in H as [S _].
 destruct (same k x) eqn:Q.
 - destruct x; try discriminate. apply same_symbol in Q. eauto.
 - exact (IH R _ _ G).
Qed.
Lemma mem_keys : forall C k, r_mem k (r_keys C) = false -> r_get k C = missing.
Proof.
 induction C as [|s1|s2|z1|n1 d1|t1|b1|e _ rest IH|c1|h1]; intros k M; try reflexivity.
 destruct e as [| | | | | | |x e| |]; try reflexivity. destruct e as [| | | | | | |s e| |]; try reflexivity.
 destruct e; try reflexivity. cbn [r_keys r_mem] in M. apply orb_false_iff in M as [Q M].
 cbn [r_get]. rewrite Q. exact (IH _ M).
Qed.
Lemma ctxh_remove : forall C X, r_ctxh C = true -> r_ctxh (r_remove X C) = true.
Proof.
 induction C as [|s1|s2|z1|n1 d1|t1|b1|e _ rest IH|c1|h1]; intros X H; try discriminate; try reflexivity.
 destruct e as [| | | | | | |x e| |]; try discriminate. destruct e as [| | | | | | |s e| |]; try discriminate.
 destruct e; try discriminate. cbn [r_remove]. cbn [r_ctxh] in H.
 apply andb_true_iff in H as [H R]. destruct (same X x); [exact R|].
 cbn [r_ctxh]. rewrite H. apply IH. exact R.
Qed.
Lemma remove_get : forall C x z, r_ctxh C = true -> r_uniq (r_keys C) = true ->
 r_get (Symbol z) (r_remove (Symbol x) C) = if String.eqb z x then missing else r_get (Symbol z) C.
Proof.
 induction C as [|s1|s2|z1|n1 d1|t1|b1|e _ rest IH|c1|h1]; intros x z H U; try discriminate;
 try (destruct (String.eqb z x); reflexivity).
 destruct e as [| | | | | | |k e| |]; try discriminate. destruct e as [| | | | | | |s e| |]; try discriminate.
 destruct e; try discriminate. cbn [r_ctxh] in H. apply andb_true_iff in H as [H R].
 apply andb_true_iff in H as [K _]. destruct k; try discriminate.
 cbn [r_keys r_uniq] in U. apply andb_true_iff in U as [M U].
 cbn [r_remove r_get same]. destruct (String.eqb x s0) eqn:XS.
 - apply String.eqb_eq in XS; subst s0. destruct (String.eqb z x) eqn:ZX.
   + apply String.eqb_eq in ZX; subst z. apply mem_keys. destruct (r_mem (Symbol x) (r_keys rest)); [discriminate|reflexivity].
   + reflexivity.
 - cbn [r_get same]. rewrite (IH _ _ R U).
   destruct (String.eqb z x) eqn:ZX; [|reflexivity].
   apply String.eqb_eq in ZX; subst z. rewrite XS. reflexivity.
Qed.
Lemma remove_found : forall C X k s, r_ctxh C = true -> r_get k (r_remove X C) = found s ->
 exists z, k = Symbol z.
Proof. intros C X k s H G. exact (ctx_keys _ (ctxh_remove _ X H) _ _ G). Qed.
Lemma ihyps_member : forall ps X G l r h, entry_in h (r_ihyps (bs_of ps) X G l r) ->
 exists a e, In (a,DExpr e) ps /\ h = L [Symbol a;G;r_subst l (one X (L [sym "v";Symbol a]));r_subst r (one X (L [sym "v";Symbol a]))].
Proof.
 induction ps as [|[a d] ps IH]; intros X G l r h I; [contradiction|].
 cbn [bs_of map L fold_right r_ihyps fst snd] in I. destruct d; cbn [sname String.eqb Ascii.eqb Bool.eqb] in I;
 try (destruct (IH _ _ _ _ _ I) as (a' & e' & In' & ->); exists a', e'; split; [right; exact In'|reflexivity]).
 destruct I as [<-|I].
 - exists a, e. split; [left; reflexivity|reflexivity].
 - destruct (IH _ _ _ _ _ I) as (a' & e' & In' & ->). exists a', e'. split; [right; exact In'|reflexivity].
Qed.
Lemma pfind_in : forall ps a d, NoDup (map fst ps) -> In (a,d) ps -> pfind a ps = Some d.
Proof.
 induction ps as [|[b e] ps IH]; intros a d N I; [contradiction|]. cbn [map fst] in N. inversion N; subst.
 cbn [pfind]. destruct I as [E|I].
 - injection E as -> ->. rewrite String.eqb_refl. reflexivity.
 - destruct (String.eqb a b) eqn:Q.
   + apply String.eqb_eq in Q; subst. exfalso; apply H1. apply (in_map fst) in I. exact I.
   + apply IH; assumption.
Qed.
Lemma pfind_none : forall ps z, ~ In z (map fst ps) -> pfind z ps = None.
Proof.
 induction ps as [|[b e] ps IH]; intros z N; [reflexivity|]. cbn [pfind].
 destruct (String.eqb z b) eqn:Q.
 - apply String.eqb_eq in Q; subst. exfalso; apply N; left; reflexivity.
 - apply IH. intro I; apply N; right; exact I.
Qed.
Lemma denote_v : forall rho a, denote rho (Pair (Symbol "v") (Pair (Symbol a) Nil)) = rho a.
Proof. reflexivity. Qed.
Lemma vars_denote : forall ps rho, NoDup (map fst ps) ->
 (forall a d, In (a,d) ps -> rho a = Some d) ->
 denotes rho (r_vars (names_of ps)) = Some (map snd ps).
Proof.
 induction ps as [|[a d] ps IH]; intros rho N E; [reflexivity|].
 cbn [names_of map L fold_right r_vars denotes fst snd sym]. inversion N; subst.
 rewrite denote_v, (E a d (or_introl eq_refl)).
 unfold names_of, L in IH. rewrite IH; [reflexivity|assumption|].
 intros a' d' I. apply E. right. exact I.
Qed.
Lemma one_get : forall x z t, r_get (Symbol z) (one (Symbol x) t) =
 if String.eqb z x then found t else missing.
Proof. intros; cbn; destruct (String.eqb z x); reflexivity. Qed.
Lemma one_keys : forall x t, keys_sym (one (Symbol x) t).
Proof.
 intros x t k u G. cbn [one L fold_right r_get] in G. destruct (same k (Symbol x)) eqn:Q; [|discriminate].
 apply same_symbol in Q; eauto.
Qed.
Definition expr_claim C x l r e := forall rho, env_ok rho C -> rho x = Some (DExpr e) -> denote rho l = denote rho r.
Lemma branch_sound : forall C x l r ctor ps e,
 r_ctx C = true -> r_get (Symbol x) C = found (sym "expr") ->
 (exists s, r_sort l C = found s) -> (exists s, r_sort r C = found s) ->
 NoDup (map fst ps) -> (forall a, In a (map fst ps) -> r_get (Symbol a) C = missing) ->
 apply_fn ctor (map snd ps) = Some (DExpr e) ->
 (forall a e', In (a,DExpr e') ps -> expr_claim C x l r e') ->
 (forall rhob, env_ok rhob (r_app (bs_of ps) (r_remove (Symbol x) C)) ->
   rules_true rhob (r_ihyps (bs_of ps) (Symbol x) (r_remove (Symbol x) C) l r) ->
   denote rhob (r_subst l (one (Symbol x) (Pair (Symbol ctor) (r_vars (names_of ps))))) =
   denote rhob (r_subst r (one (Symbol x) (Pair (Symbol ctor) (r_vars (names_of ps)))))) ->
 expr_claim C x l r e.
Proof.
 intros C x l r ctor ps e Ctx Gx [sl Sl] [sr Sr] N Fr Ap IHs Br rho OK Rx.
 apply andb_true_iff in Ctx as [Ch U].
 set (G := r_remove (Symbol x) C).
 set (rhob := fun z => match pfind z ps with Some d => Some d | None => rho z end).
 assert (Notx : ~ In x (map fst ps)).
 { intro I. rewrite (Fr _ I) in Gx. discriminate. }
 assert (Okb : env_ok rhob (r_app (bs_of ps) G)).
 { intros k s H. rewrite get_app in H. destruct (is_sym k) eqn:Sk.
   - destruct k; try discriminate. rewrite get_bs in H. unfold rhob. destruct (pfind s0 ps) as [d|] eqn:P.
     + cbn in H. injection H as <-. exists s0, d. split; [reflexivity|].
       split; [cbn; rewrite P; reflexivity|reflexivity].
     + cbn in H. unfold G in H. rewrite (remove_get _ _ _ Ch U) in H.
       destruct (String.eqb s0 x); [discriminate|]. destruct (OK _ _ H) as (z & d & Ez & D & Sd).
       injection Ez as Ez; subst z. exists s0, d. split; [reflexivity|].
       split; [cbn; rewrite P; exact D|exact Sd].
   - rewrite (get_bs_nonsym _ _ Sk) in H. cbn in H. destruct (remove_found _ _ _ _ Ch H) as [z ->]; discriminate. }
 assert (Ih : rules_true rhob (r_ihyps (bs_of ps) (Symbol x) G l r)).
 { intros n vars l' r' H. apply rule_member in H as [m I]. apply ihyps_member in I as (a & e' & Ia & E).
   injection E as _ -> -> ->. split; [exact (ctx_keys _ (ctxh_remove _ _ Ch))|].
   intros rho' Ok' Ag.
   rewrite (proj1 (subst_sound (one (Symbol x) (Pair (sym "v") (Pair (Symbol a) Nil))) rho' (one_keys _ _) l)).
   rewrite (proj1 (subst_sound (one (Symbol x) (Pair (sym "v") (Pair (Symbol a) Nil))) rho' (one_keys _ _) r)).
   assert (Ina : In a (map fst ps)) by (apply (in_map fst) in Ia; exact Ia).
   assert (Ra : rho' a = Some (DExpr e')).
   { rewrite Ag. unfold rhob. rewrite (pfind_in _ _ _ N Ia). reflexivity.
     unfold G. rewrite (remove_get _ _ _ Ch U). destruct (String.eqb a x) eqn:Q.
     - apply String.eqb_eq in Q; subst. contradiction.
     - apply Fr; exact Ina. }
   apply (IHs a e' Ia).
   - intros k s H. destruct (ctx_keys _ Ch _ _ H) as [z ->]. destruct (String.eqb z x) eqn:Q.
     + apply String.eqb_eq in Q; subst z. rewrite Gx in H. injection H as <-.
       exists x, (DExpr e'). split; [reflexivity|]. split; [|reflexivity].
       unfold extend; cbv beta; rewrite one_get, String.eqb_refl. exact Ra.
     + assert (Hg : r_get (Symbol z) G = found s) by (unfold G; rewrite (remove_get _ _ _ Ch U), Q; exact H).
       destruct (Ok' _ _ Hg) as (z' & d & Ez & D & Sd). injection Ez as Ez; subst z'.
       exists z, d. split; [reflexivity|]. split; [|exact Sd].
       unfold extend; cbv beta; rewrite one_get, Q. exact D.
   - unfold extend; cbv beta; rewrite one_get, String.eqb_refl. exact Ra. }
 specialize (Br rhob Okb Ih).
 rewrite (proj1 (subst_sound (one (Symbol x) (Pair (Symbol ctor) (r_vars (names_of ps)))) rhob (one_keys _ _) l)) in Br.
 rewrite (proj1 (subst_sound (one (Symbol x) (Pair (Symbol ctor) (r_vars (names_of ps)))) rhob (one_keys _ _) r)) in Br.
 assert (Ag : agree C (extend rhob (one (Symbol x) (Pair (Symbol ctor) (r_vars (names_of ps))))) rho).
 { intros k s z H ->. unfold extend; cbv beta; rewrite one_get. destruct (String.eqb z x) eqn:Q.
   - apply String.eqb_eq in Q; subst z. cbn [tagged found L fold_right String.eqb Ascii.eqb Bool.eqb]. rewrite Rx.
     assert (Vc : var_of (Pair (Symbol ctor) (r_vars (names_of ps))) = None).
     { destruct ps as [|[a d] [|q qs]]; cbn -[String.eqb]; try reflexivity.
       destruct (String.eqb "v" ctor) eqn:Q; [|reflexivity]. apply String.eqb_eq in Q; subst. cbn in Ap. discriminate Ap. }
     rewrite denote_app by exact Vc. rewrite (vars_denote _ _ N). exact Ap.
     intros a d I. unfold rhob. rewrite (pfind_in _ _ _ N I). reflexivity.
   - cbn [tagged]. unfold rhob. rewrite pfind_none; [reflexivity|]. intro I. rewrite (Fr _ I) in H. discriminate. }
 rewrite (proj1 (denote_agree _ _ _ _ Ag) _ Sl), (proj1 (denote_agree _ _ _ _ Ag) _ Sr) in Br. exact Br.
Qed.

(* What a checked induction case establishes (see kernel check-case-bound). *)
Definition case_ok C X l r ctor sorts := exists names bs,
 r_allsym names = true /\ r_uniq names = true /\ r_fresh names (r_keys C) = true /\
 r_zip names sorts = L [sym "zipped";bs] /\
 forall rhob, env_ok rhob (r_app bs (r_remove X C)) -> rules_true rhob (r_ihyps bs X (r_remove X C) l r) ->
   denote rhob (r_subst l (one X (Pair ctor (r_vars names)))) = denote rhob (r_subst r (one X (Pair ctor (r_vars names)))).
Lemma case_names1 : forall C X l r ctor s, case_ok C X l r ctor (L [s]) ->
 exists a bs, bs = L [L [Symbol a;s]] /\ r_mem (Symbol a) (r_keys C) = false /\
 forall rhob, env_ok rhob (r_app bs (r_remove X C)) -> rules_true rhob (r_ihyps bs X (r_remove X C) l r) ->
   denote rhob (r_subst l (one X (Pair ctor (r_vars (L [Symbol a]))))) = denote rhob (r_subst r (one X (Pair ctor (r_vars (L [Symbol a]))))).
Proof.
 intros C X l r ctor s (names & bs & A & _ & F & Z & B).
 destruct names as [| | | | | | |n ns| |]; try discriminate. destruct ns; try discriminate.
 cbn in Z. injection Z as <-. destruct n; try discriminate. cbn [r_fresh] in F.
 exists s0, (L [L [Symbol s0;s]]). split; [reflexivity|]. split; [|exact B].
 destruct (r_mem (Symbol s0) (r_keys C)); [discriminate|reflexivity].
Qed.
Lemma case_names2 : forall C X l r ctor s t, case_ok C X l r ctor (L [s;t]) ->
 exists a b bs, bs = L [L [Symbol a;s];L [Symbol b;t]] /\ String.eqb a b = false /\
 r_mem (Symbol a) (r_keys C) = false /\ r_mem (Symbol b) (r_keys C) = false /\
 forall rhob, env_ok rhob (r_app bs (r_remove X C)) -> rules_true rhob (r_ihyps bs X (r_remove X C) l r) ->
   denote rhob (r_subst l (one X (Pair ctor (r_vars (L [Symbol a;Symbol b]))))) =
   denote rhob (r_subst r (one X (Pair ctor (r_vars (L [Symbol a;Symbol b]))))).
Proof.
 intros C X l r ctor s t (names & bs & A & U & F & Z & B).
 destruct names as [| | | | | | |n ns| |]; try discriminate.
 destruct ns as [| | | | | | |m ms| |]; try discriminate. destruct ms; try discriminate.
 cbn in Z. injection Z as <-. destruct n; try discriminate. destruct m; try discriminate.
 cbn [r_fresh] in F. cbn [r_uniq r_mem same] in U.
 exists s0, s1, (L [L [Symbol s0;s];L [Symbol s1;t]]). split; [reflexivity|].
 destruct (String.eqb s0 s1); [discriminate|]. split; [reflexivity|].
 destruct (r_mem (Symbol s0) (r_keys C)); [discriminate|].
 destruct (r_mem (Symbol s1) (r_keys C)); [discriminate|]. split; [reflexivity|]. split; [reflexivity|exact B].
Qed.
Theorem induction_sound : forall C X l r,
 r_ctx C = true -> r_get X C = found (sym "expr") ->
 (exists s, r_sort l C = found s) -> (exists s, r_sort r C = found s) ->
 case_ok C X l r (sym "lit") (L [sym "nat"]) ->
 case_ok C X l r (sym "add") (L [sym "expr";sym "expr"]) ->
 case_ok C X l r (sym "mul") (L [sym "expr";sym "expr"]) ->
 forall rho, env_ok rho C -> denote rho l = denote rho r.
Proof.
 intros C X l r Ctx Gx Sl Sr Clit Cadd Cmul.
 assert (Ch : r_ctxh C = true) by (apply andb_true_iff in Ctx; tauto).
 destruct (ctx_keys _ Ch _ _ Gx) as [x ->].
 assert (Claim : forall e, expr_claim C x l r e).
 { induction e as [n|e1 IH1 e2 IH2|e1 IH1 e2 IH2].
   - destruct (case_names1 _ _ _ _ _ _ Clit) as (a & bs & -> & Fa & B).
     apply (branch_sound C x l r "lit" [(a,DNat n)] (Arithmetic.Lit n)); auto.
     + repeat constructor; intro I; inversion I.
     + intros a' [<-|[]]. apply mem_keys; exact Fa.
     + intros a' e' [I|[]]; discriminate I.
   - destruct (case_names2 _ _ _ _ _ _ _ Cadd) as (a & b & bs & -> & Nab & Fa & Fb & B).
     apply (branch_sound C x l r "add" [(a,DExpr e1);(b,DExpr e2)] (Arithmetic.Add e1 e2)); auto.
     + constructor; [|constructor; [intro I; inversion I|constructor]].
       intros [I|[]]. cbn in I. subst. rewrite String.eqb_refl in Nab. discriminate.
     + intros a' [<-|[<-|[]]]; apply mem_keys; assumption.
     + intros a' e' [I|[I|[]]]; injection I as <- <-; assumption.
   - destruct (case_names2 _ _ _ _ _ _ _ Cmul) as (a & b & bs & -> & Nab & Fa & Fb & B).
     apply (branch_sound C x l r "mul" [(a,DExpr e1);(b,DExpr e2)] (Arithmetic.Mul e1 e2)); auto.
     + constructor; [|constructor; [intro I; inversion I|constructor]].
       intros [I|[]]. cbn in I. subst. rewrite String.eqb_refl in Nab. discriminate.
     + intros a' [<-|[<-|[]]]; apply mem_keys; assumption.
     + intros a' e' [I|[I|[]]]; injection I as <- <-; assumption. }
 intros rho OK. destruct (OK _ _ Gx) as (z & d & Ez & D & S). injection Ez as <-.
 destruct d; try discriminate S. exact (Claim e rho OK D).
Qed.
End EqualityInductionModel.
