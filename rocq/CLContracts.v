(* E2E-16/E2E-17: CLLowering.primitive_contracts discharged from the captured
   Shen-CL 4844072d primitives.lsp bodies.

   CLLowering proves the captured IF lowering in a relational CL model whose
   primitive relation is a parameter. CLWrappers proves the captured wrapper
   bodies, partly in that relational model and partly in a functional CL
   evaluator [ceval]. This module builds the bridge: a relational world
   [captured_prim] in which
   - the Boolean wrappers (cons?, string?, number?, shen-cl.equal?, the four
     comparisons) run their captured bodies in CLLowering's relational [ev]
     (CLWrappers.wrapped);
   - the pure helpers shen-cl.absequal and shen-cl.numeric-equal run their
     captured bodies in [ceval], and a call means the value at which the
     fuel-indexed result stabilises ([eventually]);
   - the Shen kernel functions not, empty? and fail (kernel code compiled by
     Shen-CL, no primitives.lsp body) are a relation [kern] with the named
     contracts [cl_kernel_ops] (owned by E2E-16);
   - every other head is a host operation, given by a host table [h] with the
     individually named contracts [cl_host_ops] (owned by E2E-21 and E2E-24).
   [captured_contracts] proves every field of the narrowed
   CLLowering.primitive_contracts for that world, for every state type, every
   relation for unmodeled forms, every host table satisfying [cl_host_ops]
   and every kernel relation satisfying [cl_kernel_ops]. The final
   corollaries are the captured optimise/emit-if theorems with only those
   named host and kernel contracts left as hypotheses.

   Modeling boundary (documented in docs/CL-PORT.md): host operations named
   in [cl_host_ops] are pure functions of their arguments, and a raised
   host condition is a function of the arguments (fresh condition identity is
   quotiented); VObj values are host objects that are not numbers, symbols,
   strings or conses; VNum spellings never denote NaN. *)
From Coq Require Import String List Bool Ascii Arith ZArith Lia.
From Buri Require Import CLLowering.
From Buri Require KLSyntax KLValue KLSemantics CLWrappers CLLoweringCapture.
Import ListNotations.
Open Scope string_scope.

Module CLContracts.
Module W := CLWrappers.CLWrappers.

Definition is_obj (v : sv) := match v with VObj _ => true | _ => false end.

(* ---------- 1. Named host-operation contracts (E2E-21 / E2E-24) ---------- *)
(* Each field names one SBCL operation at the argument shapes the captured
   helper bodies and the optimizer's output reach. *)
Record cl_host_ops (h : string -> list sv -> W.cres) : Prop := {
 host_eq : forall a b, exists r, h "EQ" [a; b] = W.CRet (W.hb r) /\ (r = true -> a = b) /\
   ((symbolic a || symbolic b)%bool = true -> a = b -> r = true);
 host_typep_fixnum : forall a, exists r, h "TYPEP" [a; VSym "FIXNUM"] = W.CRet (W.hb r) /\
   (r = true -> is_num a = true /\ h "INTEGERP" [a] = W.CRet W.T);
 host_integerp : forall a, exists r, h "INTEGERP" [a] = W.CRet (W.hb r) /\ (r = true -> is_num a = true);
 host_numberp : forall a, h "NUMBERP" [a] = W.CRet (W.hb (is_num a));
 host_consp : forall a, h "CONSP" [a] = W.CRet (W.hb (is_cons a));
 host_stringp : forall a, h "STRINGP" [a] = W.CRet (W.hb (is_str a));
 host_arrayp : forall a, exists r, h "ARRAYP" [a] = W.CRet (W.hb r) /\ (is_str a = true -> r = true) /\
   (r = true -> (is_str a || is_obj a)%bool = true);
 host_symbolp : forall a, h "SYMBOLP" [a] = W.CRet (W.hb (symbolic a));
 host_string_eq : forall x y, h "STRING=" [VStr x; VStr y] = W.CRet (W.hb (String.eqb x y));
 host_not : forall a, h "NOT" [a] = W.CRet (W.hb (is_nil a));
 host_null : forall a, h "NULL" [a] = W.CRet (W.hb (is_nil a));
 host_equal_string : forall x a, h "EQUAL" [VStr x; a] = W.CRet (W.hb (sv_eqb (VStr x) a)) /\
   h "EQUAL" [a; VStr x] = W.CRet (W.hb (sv_eqb a (VStr x)));
 host_equal_object : forall n b, is_obj b = false -> h "EQUAL" [VObj n; b] = W.CRet VNil;
 host_eql_integer : forall a b, h "INTEGERP" [a] = W.CRet W.T -> h "INTEGERP" [b] = W.CRet W.T ->
   h "EQL" [a; b] = h "=" [a; b];
 host_num_eq_sym : forall a b, is_num a = true -> is_num b = true -> h "=" [a; b] = h "=" [b; a];
 host_num_eq_refl : forall n, h "=" [VNum n; VNum n] = W.CRet W.T }.

Section Functional.
Variable h : string -> list sv -> W.cres.
Hypothesis H : cl_host_ops h.

Lemma eq_exact : forall a b, (symbolic a || symbolic b)%bool = true -> h "EQ" [a; b] = W.CRet (W.hb (sv_eqb a b)).
Proof.
 intros a b S. destruct (host_eq h H a b) as [r [E [Snd Cmp]]]. rewrite E. f_equal. f_equal.
 destruct r.
 - rewrite (Snd eq_refl). symmetry. apply sv_eqb_eq. reflexivity.
 - destruct (sv_eqb a b) eqn:Q; [|reflexivity]. apply sv_eqb_eq in Q. apply Cmp; auto.
Qed.


(* ----- Evaluation steps of the captured bodies under known host answers ----- *)
Lemma call1 : forall m env g x a r, W.plain g = true -> W.assoc g W.program = None ->
 String.eqb x "T" = false -> lookup x env = Some a -> h g [a] = r ->
 W.ceval (S (S m)) h env (W.SL [W.Sy g; W.Sy x]) = r.
Proof. intros. eapply W.ce_host1; eauto. apply W.ce_var; auto. Qed.
Lemma call2 : forall m env g x y a b r, W.plain g = true -> W.assoc g W.program = None ->
 String.eqb x "T" = false -> lookup x env = Some a -> String.eqb y "T" = false -> lookup y env = Some b ->
 h g [a; b] = r -> W.ceval (S (S m)) h env (W.SL [W.Sy g; W.Sy x; W.Sy y]) = r.
Proof. intros. eapply W.ce_host2; eauto; apply W.ce_var; auto. Qed.
Lemma call2q : forall m env g x d a r, W.plain g = true -> W.assoc g W.program = None ->
 String.eqb x "T" = false -> lookup x env = Some a -> h g [a; d] = r ->
 W.ceval (S (S m)) h env (W.SL [W.Sy g; W.Sy x; W.Q d]) = r.
Proof. intros. eapply W.ce_host2; eauto; [apply W.ce_var; auto | apply W.ce_quote]. Qed.
Lemma call11 : forall m env g g2 x a v r, W.plain g = true -> W.assoc g W.program = None ->
 W.plain g2 = true -> W.assoc g2 W.program = None ->
 String.eqb x "T" = false -> lookup x env = Some a -> h g2 [a] = W.CRet v -> h g [v] = r ->
 W.ceval (S (S (S m))) h env (W.SL [W.Sy g; W.SL [W.Sy g2; W.Sy x]]) = r.
Proof. intros. eapply W.ce_host1; eauto. eapply call1; eauto. Qed.
Lemma ce_t : forall m env, W.ceval (S m) h env (W.Sy "T") = W.CRet (W.hb true).
Proof. reflexivity. Qed.
Lemma cond_bool : forall m env t b cs (c : bool), W.ceval m h env t = W.CRet (W.hb c) ->
 W.ceval (S m) h env (W.SL (W.Sy "COND" :: W.SL [t; b] :: cs)) =
 if c then W.ceval m h env b else W.ceval (S m) h env (W.SL (W.Sy "COND" :: cs)).
Proof. intros. destruct c; [apply W.ce_cond_hit with (v := W.T); auto | apply W.ce_cond_miss; auto]. Qed.
Lemma and2_bool : forall m env x y (c : bool), W.ceval m h env x = W.CRet (W.hb c) ->
 W.ceval (S m) h env (W.SL [W.Sy "AND"; x; y]) = if c then W.ceval m h env y else W.CRet VNil.
Proof. intros. rewrite (W.ce_and2 h m env x y (W.hb c)) by assumption. destruct c; reflexivity. Qed.
Lemma and3_bool : forall m env x y z (c : bool), W.ceval m h env x = W.CRet (W.hb c) ->
 W.ceval (S m) h env (W.SL [W.Sy "AND"; x; y; z]) = if c then W.ceval (S m) h env (W.SL [W.Sy "AND"; y; z]) else W.CRet VNil.
Proof. intros. rewrite (W.ce_and3 h m env x y z (W.hb c)) by assumption. destruct c; reflexivity. Qed.
Lemma if_bool : forall m env c a b (k : bool), W.ceval m h env c = W.CRet (W.hb k) ->
 W.ceval (S m) h env (W.SL [W.Sy "IF"; c; a; b]) = if k then W.ceval m h env a else W.ceval m h env b.
Proof. intros. rewrite (W.ce_if h m env c a b (W.hb k)) by assumption. destruct k; reflexivity. Qed.

Lemma and2_hb : forall m env x y (c d : bool), W.ceval m h env x = W.CRet (W.hb c) -> W.ceval m h env y = W.CRet (W.hb d) ->
 W.ceval (S m) h env (W.SL [W.Sy "AND"; x; y]) = W.CRet (W.hb (c && d)).
Proof. intros. rewrite (and2_bool m env x y c) by assumption. destruct c; [assumption|reflexivity]. Qed.

Ltac tcall := first
 [ apply ce_t
 | eapply and2_hb; [tcall|tcall]
 | eapply call2q; [reflexivity|reflexivity|reflexivity|reflexivity|eassumption]
 | eapply call2; [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|eassumption]
 | eapply call11; [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|eassumption|apply (host_not h H)]
 | eapply call1; [reflexivity|reflexivity|reflexivity|reflexivity|eassumption] ].
Ltac red_if := cbv beta iota delta [is_num is_str is_cons symbolic is_nil is_obj sv_eqb orb andb negb W.hb W.T].
Ltac clean := repeat match goal with
 | B : true = true -> _ |- _ => specialize (B eq_refl)
 | B : false = true -> _ |- _ => clear B
 | B : _ /\ _ |- _ => destruct B
 | B : ?x = ?x |- _ => clear B
 | B : _ = _ |- _ => discriminate B
 | B : VNum _ = VNum _ |- _ => injection B as B; subst
 | B : VSym _ = VSym _ |- _ => injection B as B; subst
 | B : VStr _ = VStr _ |- _ => injection B as B; subst
 | B : VObj _ = VObj _ |- _ => injection B as B; subst
 | B : String.eqb _ _ = true |- _ => apply String.eqb_eq in B; subst
 | B : String.eqb ?x ?x = false |- _ => rewrite String.eqb_refl in B; discriminate B
 | B : (if ?c then _ else _) = _ |- _ => is_var c; destruct c
 end.
Ltac walk := repeat first
 [ progress (erewrite cond_bool by tcall); red_if
 | progress (erewrite and3_bool by tcall); red_if
 | progress (erewrite and2_bool by tcall); red_if
 | progress (erewrite if_bool by tcall); red_if
 | match goal with |- context [if ?c then _ else _] =>
     first [is_var c; destruct c | destruct c eqn:?]; clean; red_if end ].
Ltac fin_host := first
 [ eassumption
 | apply (host_equal_object h H); reflexivity
 | rewrite (proj1 (host_equal_string h H _ _)); reflexivity
 | rewrite (proj2 (host_equal_string h H _ _)); reflexivity
 | rewrite (host_string_eq h H); red_if; rewrite ?String.eqb_refl;
   repeat match goal with B : String.eqb _ _ = false |- _ => rewrite B end; reflexivity
 | apply (host_num_eq_refl h H)
 | rewrite (host_eql_integer h H) by assumption; first [apply (host_num_eq_refl h H) | reflexivity
     | apply (host_num_eq_sym h H); reflexivity]
 | apply (host_num_eq_sym h H); reflexivity ].
Ltac fin := first
 [ reflexivity
 | rewrite String.eqb_refl; reflexivity
 | eapply call2; [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|]; fin_host ].

(* Facts about one value, with the existential host answers named. *)
Ltac facts a := let N := fresh "N" in let C := fresh "C" in let Sg := fresh "Sg" in let Sb := fresh "Sb" in
 let F := fresh "F" in let I := fresh "I" in let Ar := fresh "Ar" in
 pose proof (host_numberp h H a) as N; pose proof (host_consp h H a) as C;
 pose proof (host_stringp h H a) as Sg; pose proof (host_symbolp h H a) as Sb;
 destruct (host_typep_fixnum h H a) as [?q [F ?Fq]];
 destruct (host_integerp h H a) as [?i [I ?Iq]];
 destruct (host_arrayp h H a) as [?ar [Ar [?Ara ?Arb]]].
Ltac eqfacts a b := destruct (host_eq h H a b) as [?r [?E [?Es ?Ec]]].
Ltac fuel n := let k := fresh "k" in
 assert (exists k, n = S (S (S (S (S (S (S (S (S (S k)))))))))) as [k ->] by (exists (n - 10); lia).

Lemma abs_symbolic_right : forall a d n, symbolic d = true -> 10 <= n ->
 W.ceval n h (W.env2 a d) W.absequal_body = W.CRet (W.hb (sv_eqb a d)).
Proof.
 intros a d n Sd Hn. fuel n. unfold W.absequal_body.
 facts a. facts d. pose proof (eq_exact a d ltac:(rewrite Sd, orb_true_r; reflexivity)) as E.
 destruct d; try discriminate Sd; destruct a; red_if; clean; walk; fin.
Qed.
Lemma abs_symbolic_left : forall a d n, symbolic d = true -> 10 <= n ->
 W.ceval n h (W.env2 d a) W.absequal_body = W.CRet (W.hb (sv_eqb d a)).
Proof.
 intros a d n Sd Hn. fuel n. unfold W.absequal_body.
 facts a. facts d. pose proof (eq_exact d a ltac:(rewrite Sd; reflexivity)) as E.
 destruct d; try discriminate Sd; destruct a; red_if; clean; walk; fin.
Qed.
Lemma abs_string_right : forall a x n, 10 <= n ->
 W.ceval n h (W.env2 a (VStr x)) W.absequal_body = W.CRet (W.hb (sv_eqb a (VStr x))).
Proof.
 intros a x n Hn. fuel n. unfold W.absequal_body.
 facts a. facts (VStr x). eqfacts a (VStr x).
 destruct a; red_if; clean; walk; fin.
Qed.
Lemma abs_string_left : forall a x n, 10 <= n ->
 W.ceval n h (W.env2 (VStr x) a) W.absequal_body = W.CRet (W.hb (sv_eqb (VStr x) a)).
Proof.
 intros a x n Hn. fuel n. unfold W.absequal_body.
 facts a. facts (VStr x). eqfacts (VStr x) a.
 destruct a; red_if; clean; walk; fin.
Qed.

(* absequal and numeric-equal against a numeric literal: both reach the same
   host comparison, so they give the same result for every value. *)
Definition num_spec (a b : sv) : W.cres :=
 if is_num a then (if sv_eqb a b then W.CRet W.T else h "=" [a; b]) else W.CRet VNil.
Lemma abs_numeric_right : forall a m n, 10 <= n ->
 W.ceval n h (W.env2 a (VNum m)) W.absequal_body = num_spec a (VNum m).
Proof.
 intros a m n Hn. fuel n. unfold W.absequal_body, num_spec.
 facts a. facts (VNum m). eqfacts a (VNum m).
 destruct a; red_if; clean; walk; fin.
Qed.
Lemma abs_numeric_left : forall a m n, 10 <= n ->
 W.ceval n h (W.env2 (VNum m) a) W.absequal_body = num_spec a (VNum m).
Proof.
 intros a m n Hn. fuel n. unfold W.absequal_body, num_spec.
 facts a. facts (VNum m). eqfacts (VNum m) a.
 destruct a; red_if; clean; walk; fin.
Qed.
Lemma numeric_equal_value : forall a m n, 10 <= n ->
 W.ceval n h (W.env2 a (VNum m)) W.numeric_equal_body = num_spec a (VNum m).
Proof.
 intros a m n Hn. fuel n. unfold W.numeric_equal_body, num_spec.
 facts a. facts (VNum m).
 destruct a; red_if; clean; walk; fin.
Qed.
End Functional.

(* ---------- 2. Named Shen kernel-function contracts (E2E-16) ---------- *)
(* not, empty? and fail have no primitives.lsp body: they are kernel KLambda
   compiled by Shen-CL itself, so their behaviour belongs to the compiled
   kernel (E2E-15/E2E-16), not to a host operation. *)
Record cl_kernel_ops (St : Type) (kern : string -> list sv -> St -> out St -> Prop) : Prop := {
 kernel_not : forall v s o, kern "not" [v] s o <-> o = shen_not_result St v s;
 kernel_empty : forall v s o, kern "empty?" [v] s o <-> o = Ok (shen_bool (is_nil v)) s;
 kernel_fail : forall s o, kern "fail" [] s o <-> o = Ok (VSym "shen.fail!") s }.

(* ---------- 3. The relational world that runs the captured bodies ---------- *)
Section World.
Variable St : Type.
Variable h : string -> list sv -> W.cres.
Variable kern : string -> list sv -> St -> out St -> Prop.
Variable other : binding -> sv -> St -> out St -> Prop.

(* A pure host or helper result as a relational outcome; exhausted fuel and
   unsupported forms have no outcome (they are not values). *)
Definition of_cres (r : W.cres) (s : St) (o : out St) : Prop :=
 match r with W.CRet v => o = Ok v s | W.CRaise x => o = Raise x s | _ => False end.
Definition eventually (P : nat -> Prop) : Prop := exists N, forall n, N <= n -> P n.
Definition helpers := ["shen-cl.absequal"; "shen-cl.numeric-equal"].
Definition kernel_fns := ["not"; "empty?"; "fail"].
(* A helper call: the captured body, evaluated by ceval with the host table,
   at the result on which the fuel-indexed evaluation stabilises. *)
Definition run_helper (f : string) (vs : list sv) (s : St) (o : out St) : Prop :=
 match W.assoc f W.program with
 | Some (ps, [body]) => List.length ps = List.length vs /\
     exists r, eventually (fun n => W.ceval n h (combine ps vs) body = r) /\ of_cres r s o
 | _ => False end.
Definition host_rel (f : string) (vs : list sv) (s : St) (o : out St) : Prop :=
 if mem f helpers then run_helper f vs s o
 else if mem f kernel_fns then kern f vs s o
 else of_cres (h f vs) s o.
(* The Boolean wrappers run their captured bodies relationally over host_rel. *)
Definition captured_prim : string -> list sv -> St -> out St -> Prop := W.wrapped St host_rel other.

Lemma prim_host : forall f vs s o, W.is_wrapper f = false -> (captured_prim f vs s o <-> host_rel f vs s o).
Proof.
 intros f vs s o Hw. unfold captured_prim, W.wrapped. rewrite Hw.
 destruct (W.assoc f W.program) as [[ps [|b [|]]]|]; tauto.
Qed.
Lemma helper_value : forall f ps body vs R, W.assoc f W.program = Some (ps, [body]) ->
 List.length ps = List.length vs -> (forall n, 10 <= n -> W.ceval n h (combine ps vs) body = R) ->
 forall s o, run_helper f vs s o <-> of_cres R s o.
Proof.
 intros f ps body vs R A L E s o. unfold run_helper. rewrite A. split.
 - intros [_ [r [[N HN] Ho]]]. replace r with R in Ho; [exact Ho|].
   transitivity (W.ceval (Nat.max N 10) h (combine ps vs) body); [symmetry; apply E | apply HN]; lia.
 - intros Ho. split; [exact L|]. exists R. split; [exists 10; exact E | exact Ho].
Qed.
Lemma prim_absequal : forall a b R, (forall n, 10 <= n -> W.ceval n h (W.env2 a b) W.absequal_body = R) ->
 forall s o, captured_prim "shen-cl.absequal" [a; b] s o <-> of_cres R s o.
Proof.
 intros a b R E s o. rewrite prim_host by reflexivity.
 change (run_helper "shen-cl.absequal" [a; b] s o <-> of_cres R s o).
 apply (helper_value _ ["X"; "Y"] W.absequal_body); [reflexivity|reflexivity|exact E].
Qed.
Lemma prim_numeric : forall a b R, (forall n, 10 <= n -> W.ceval n h (W.env2 a b) W.numeric_equal_body = R) ->
 forall s o, captured_prim "shen-cl.numeric-equal" [a; b] s o <-> of_cres R s o.
Proof.
 intros a b R E s o. rewrite prim_host by reflexivity.
 change (run_helper "shen-cl.numeric-equal" [a; b] s o <-> of_cres R s o).
 apply (helper_value _ ["X"; "Y"] W.numeric_equal_body); [reflexivity|reflexivity|exact E].
Qed.
Lemma prim_of_host : forall f vs, W.is_wrapper f = false -> mem f helpers = false -> mem f kernel_fns = false ->
 forall s o, captured_prim f vs s o <-> of_cres (h f vs) s o.
Proof. intros f vs W1 W2 W3 s o. rewrite prim_host by exact W1. unfold host_rel. rewrite W2, W3. tauto. Qed.
Lemma prim_kernel : forall f vs, W.is_wrapper f = false -> mem f helpers = false -> mem f kernel_fns = true ->
 forall s o, captured_prim f vs s o <-> kern f vs s o.
Proof. intros f vs W1 W2 W3 s o. rewrite prim_host by exact W1. unfold host_rel. rewrite W2, W3. tauto. Qed.

Lemma refine_chain : forall f xs g ys g' ys', args_refine St captured_prim f xs g ys ->
 (forall s o, captured_prim g ys s o <-> captured_prim g' ys' s o) -> args_refine St captured_prim f xs g' ys'.
Proof.
 intros f xs g ys g' ys' R E s t. rewrite (R s t).
 split; intros [o [Ho Ht]]; exists o; split; auto; apply E; auto.
Qed.
Lemma same_value : forall f xs g ys R1 R2,
 (forall s o, captured_prim f xs s o <-> of_cres R1 s o) -> (forall s o, captured_prim g ys s o <-> of_cres R2 s o) ->
 R1 = R2 -> forall s o, captured_prim f xs s o <-> captured_prim g ys s o.
Proof. intros f xs g ys R1 R2 A B -> s o. rewrite A, B. tauto. Qed.
Lemma refine_det : forall f xs g ys (o1 o2 : St -> out St),
 (forall s o, captured_prim f xs s o <-> o = o1 s) -> (forall s o, captured_prim g ys s o <-> o = o2 s) ->
 (forall s, shen_test St (o1 s) = cl_test St (o2 s)) -> args_refine St captured_prim f xs g ys.
Proof.
 intros f xs g ys o1 o2 A B E s t. split; intros [o [Ho Ht]].
 - apply A in Ho. subst. exists (o2 s). split; [apply B; reflexivity | symmetry; apply E].
 - apply B in Ho. subst. exists (o1 s). split; [apply A; reflexivity | apply E].
Qed.

Hypothesis HH : cl_host_ops h.
Hypothesis HK : cl_kernel_ops St kern.

Ltac host_val f := apply prim_of_host; reflexivity.
Lemma eq_value : forall a b, (symbolic a || symbolic b)%bool = true ->
 forall s o, captured_prim "EQ" [a; b] s o <-> of_cres (W.CRet (W.hb (sv_eqb a b))) s o.
Proof. intros a b S s o. rewrite prim_of_host by reflexivity. rewrite (eq_exact h HH a b S). tauto. Qed.

(* The narrowed record holds in the world that runs the captured bodies. *)
Theorem captured_contracts : primitive_contracts St captured_prim.
Proof.
 constructor.
 - intro v. apply W.cons_wrapper.
 - intro v. apply W.string_wrapper.
 - intro v. apply W.number_wrapper.
 - intro v. apply (refine_det _ _ _ _ (fun s => Ok (shen_bool (is_nil v)) s) (fun s => Ok (W.hb (is_nil v)) s)).
   + intros s o. rewrite prim_kernel by reflexivity. apply (kernel_empty St kern HK).
   + intros s o. rewrite prim_of_host by reflexivity. rewrite (host_null h HH). reflexivity.
   + intros s. destruct (is_nil v); reflexivity.
 - intros v w. apply (proj1 (W.comparison_wrappers St host_rel other v w)).
 - intros v w. apply (proj1 (proj2 (W.comparison_wrappers St host_rel other v w))).
 - intros v w. apply (proj1 (proj2 (proj2 (W.comparison_wrappers St host_rel other v w)))).
 - intros v w. apply (proj2 (proj2 (proj2 (W.comparison_wrappers St host_rel other v w)))).
 - intros v w. apply W.equal_wrapper.
 - intros v s o. rewrite prim_kernel by reflexivity. apply (kernel_not St kern HK).
 - intros v s o. rewrite prim_of_host by reflexivity. rewrite (host_not h HH).
   unfold cl_not_result. destruct v; reflexivity.
 - intros v. eapply refine_chain; [apply W.equal_wrapper|].
   apply (same_value _ _ _ _ (W.CRet (W.hb (sv_eqb v VNil))) (W.CRet (W.hb (is_nil v)))).
   + apply prim_absequal. intros; apply (abs_symbolic_right h HH); auto.
   + intros s o. rewrite prim_of_host by reflexivity. rewrite (host_null h HH). tauto.
   + destruct v; reflexivity.
 - intros v. eapply refine_chain; [apply W.equal_wrapper|].
   apply (same_value _ _ _ _ (W.CRet (W.hb (sv_eqb VNil v))) (W.CRet (W.hb (is_nil v)))).
   + apply prim_absequal. intros; apply (abs_symbolic_left h HH); auto.
   + intros s o. rewrite prim_of_host by reflexivity. rewrite (host_null h HH). tauto.
   + destruct v; reflexivity.
 - intros s a s1 Hf v.
   rewrite prim_kernel in Hf by reflexivity. apply (kernel_fail St kern HK) in Hf. injection Hf as -> ->.
   split; (eapply refine_chain; [apply W.equal_wrapper|]).
   + apply (same_value _ _ _ _ (W.CRet (W.hb (sv_eqb (VSym "shen.fail!") v))) (W.CRet (W.hb (sv_eqb (VSym "shen.fail!") v)))); auto.
     * apply prim_absequal. intros; apply (abs_symbolic_left h HH); auto.
     * apply eq_value. reflexivity.
   + apply (same_value _ _ _ _ (W.CRet (W.hb (sv_eqb v (VSym "shen.fail!")))) (W.CRet (W.hb (sv_eqb v (VSym "shen.fail!"))))); auto.
     * apply prim_absequal. intros; apply (abs_symbolic_right h HH); auto.
     * apply eq_value. rewrite orb_true_r. reflexivity.
 - intros x v. split; (eapply refine_chain; [apply W.equal_wrapper|]).
   + apply (same_value _ _ _ _ (W.CRet (W.hb (sv_eqb (VStr x) v))) (W.CRet (W.hb (sv_eqb (VStr x) v)))); auto.
     * apply prim_absequal. intros; apply (abs_string_left h HH); auto.
     * intros s o. rewrite prim_of_host by reflexivity. rewrite (proj1 (host_equal_string h HH x v)). tauto.
   + apply (same_value _ _ _ _ (W.CRet (W.hb (sv_eqb v (VStr x)))) (W.CRet (W.hb (sv_eqb v (VStr x))))); auto.
     * apply prim_absequal. intros; apply (abs_string_right h HH); auto.
     * intros s o. rewrite prim_of_host by reflexivity. rewrite (proj2 (host_equal_string h HH x v)). tauto.
 - intros n v. split; (eapply refine_chain; [apply W.equal_wrapper|]).
   + apply (same_value _ _ _ _ (num_spec h v (VNum n)) (num_spec h v (VNum n))); auto.
     * apply prim_absequal. intros; apply (abs_numeric_right h HH); auto.
     * apply prim_numeric. intros; apply (numeric_equal_value h HH); auto.
   + apply (same_value _ _ _ _ (num_spec h v (VNum n)) (num_spec h v (VNum n))); auto.
     * apply prim_absequal. intros; apply (abs_numeric_left h HH); auto.
     * apply prim_numeric. intros; apply (numeric_equal_value h HH); auto.
 - intros d v Sd. split; (eapply refine_chain; [apply W.equal_wrapper|]).
   + apply (same_value _ _ _ _ (W.CRet (W.hb (sv_eqb v d))) (W.CRet (W.hb (sv_eqb v d)))); auto.
     * apply prim_absequal. intros; apply (abs_symbolic_right h HH); auto.
     * apply eq_value. rewrite Sd, orb_true_r. reflexivity.
   + apply (same_value _ _ _ _ (W.CRet (W.hb (sv_eqb d v))) (W.CRet (W.hb (sv_eqb v d)))).
     * apply prim_absequal. intros; apply (abs_symbolic_left h HH); auto.
     * apply eq_value. rewrite Sd, orb_true_r. reflexivity.
     * rewrite sv_eqb_sym. reflexivity.
Qed.
End World.

(* ---------- 4. Why the all-arity record was a false requirement ---------- *)
(* In any world running the captured wrapper body, a wrong-arity call of
   cons? has no successful or raising outcome of its own, while the host
   CONSP at that arity raises: the all-arity field cannot hold. SBCL raises
   for both, with distinct fresh program-error conditions naming different
   functions, so it fails natively as well. The optimizer never emits it. *)
Theorem all_arity_unjustified : forall St hp other vs (s : St) x, List.length vs <> 1 ->
 hp "CONSP" vs s (Raise x s) -> ~ pred_refines St (W.wrapped St hp other) "cons?" "CONSP".
Proof.
 intros St hp other vs s x L R P. destruct (proj2 (P vs s (TR x s))) as [o [Ho _]].
 - exists (Raise x s). split; [exact R | reflexivity].
 - destruct Ho as [Hl _]. apply L. simpl in Hl. lia.
Qed.
Theorem captured_all_arity_false : forall St h kern other a b x (s : St), h "CONSP" [a; b] = W.CRaise x ->
 ~ pred_refines St (captured_prim St h kern other) "cons?" "CONSP".
Proof.
 intros St h kern other a b x s E. apply (all_arity_unjustified St (host_rel St h kern) other [a; b] s x).
 - discriminate.
 - unfold host_rel. simpl. rewrite E. reflexivity.
Qed.

(* ---------- 5. The captured lowering with every non-host field discharged ---------- *)
(* The wrapper and helper bodies are the admitted decoding of the pinned
   primitives.lsp bytes (W.cl_wrappers_admitted); the lowering is the
   admitted stored capture of compiler.shen. Remaining hypotheses: exactly
   the named host contracts cl_host_ops (E2E-21/E2E-24) and the named kernel
   contracts cl_kernel_ops (E2E-16), plus qsafe from the theorem itself. *)
Theorem discharged_optimise_sound : forall St h kern other ce n v r,
 cl_host_ops h -> cl_kernel_ops St kern ->
 run n (lowering_defs CLLoweringCapture.captured_lowering) ce OPT [v] = LOk r -> qsafe v = true ->
 W.admission = Some W.program /\ OptEquiv St (captured_prim St h kern other) other v r.
Proof.
 intros. split; [exact W.cl_wrappers_admitted|].
 eapply CLLoweringCapture.captured_optimise_sound; eauto. apply captured_contracts; assumption.
Qed.
Theorem discharged_emit_if_refines : forall St h kern other ce n t th el sc r,
 cl_host_ops h -> cl_kernel_ops St kern ->
 run n (lowering_defs CLLoweringCapture.captured_lowering) ce EMIT_IF [t; th; el; sc] = LOk r ->
 W.admission = Some W.program /\
 ((t = VSym "true" /\ ce th sc = LOk r) \/ (t = VSym "false" /\ ce el sc = LOk r) \/
  (exists c a b, ce t sc = LOk c /\ ce th sc = LOk a /\ ce el sc = LOk b /\
    (qsafe c = true -> forall e s o, ev St (captured_prim St h kern other) other e r s o <->
                                     shen_if St (captured_prim St h kern other) other e c a b s o))).
Proof.
 intros. split; [exact W.cl_wrappers_admitted|].
 eapply CLLoweringCapture.captured_emit_if_refines; eauto. apply captured_contracts; assumption.
Qed.

(* ---------- 6. The named contracts are jointly satisfiable ---------- *)
(* A concrete host table and kernel relation (anti-vacuity). Its EQ
   identifies only symbols and NIL, as the CL standard permits; it is not a
   model of SBCL. *)
Definition model_host (f : string) (vs : list sv) : W.cres :=
 match f, vs with
 | "EQ", [a; b] => W.CRet (W.hb ((symbolic a || symbolic b) && sv_eqb a b))
 | "TYPEP", [a; VSym "FIXNUM"] => W.CRet (W.hb (is_num a))
 | "INTEGERP", [a] => W.CRet (W.hb (is_num a))
 | "NUMBERP", [a] => W.CRet (W.hb (is_num a))
 | "CONSP", [a] => W.CRet (W.hb (is_cons a))
 | "STRINGP", [a] => W.CRet (W.hb (is_str a))
 | "ARRAYP", [a] => W.CRet (W.hb (is_str a || is_obj a))
 | "SYMBOLP", [a] => W.CRet (W.hb (symbolic a))
 | "STRING=", [VStr x; VStr y] => W.CRet (W.hb (String.eqb x y))
 | "NOT", [a] => W.CRet (W.hb (is_nil a))
 | "NULL", [a] => W.CRet (W.hb (is_nil a))
 | "EQUAL", [a; b] => W.CRet (W.hb (negb (is_obj a) && sv_eqb a b))
 | "EQL", [a; b] => W.CRet (W.hb (sv_eqb a b))
 | "=", [a; b] => W.CRet (W.hb (sv_eqb a b))
 | _, _ => W.CUnsup end.
Theorem model_host_ops : cl_host_ops model_host.
Proof.
 constructor.
 - intros a b. exists ((symbolic a || symbolic b) && sv_eqb a b)%bool. split; [reflexivity|split].
   + intro E. apply andb_true_iff in E as [_ E]. apply sv_eqb_eq; exact E.
   + intros S ->. rewrite S. apply sv_eqb_eq. reflexivity.
 - intros a. exists (is_num a). split; [reflexivity|]. intros E. split; [exact E|]. cbn. rewrite E. reflexivity.
 - intros a. exists (is_num a). split; [reflexivity | auto].
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - intros a. exists (is_str a || is_obj a)%bool. split; [reflexivity|split; auto].
   intros E. rewrite E. reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - intros x a. split; [reflexivity|]. destruct a; reflexivity.
 - intros n b E. cbn. reflexivity.
 - reflexivity.
 - intros a b _ _. cbn. rewrite sv_eqb_sym. reflexivity.
 - intros n. cbn. rewrite String.eqb_refl. reflexivity.
Qed.
Definition model_kernel (St : Type) (f : string) (vs : list sv) (s : St) (o : out St) : Prop :=
 match f, vs with
 | "not", [v] => o = shen_not_result St v s
 | "empty?", [v] => o = Ok (shen_bool (is_nil v)) s
 | "fail", [] => o = Ok (VSym "shen.fail!") s
 | _, _ => False end.
Theorem model_kernel_ops : forall St, cl_kernel_ops St (model_kernel St).
Proof. intros St. constructor; intros; reflexivity. Qed.
Theorem model_world_contracts : forall St other,
 primitive_contracts St (captured_prim St model_host (model_kernel St) other).
Proof. intros. apply captured_contracts; [apply model_host_ops | apply model_kernel_ops]. Qed.

(* ---------- 7. shen-cl.increment and shen-cl.decrement ---------- *)
(* optimise-static-application rewrites [add 1 X], [add X 1] to
   (shen-cl.increment X) and [subtract X 1] to (shen-cl.decrement X). The
   captured bodies are (if (typep x 'fixnum) (1+ (the fixnum x)) (1+ x)) and
   the 1- analogue; ceval evaluates (THE type x) as x, which SBCL also does
   when the declaration holds, as TYPEP has just checked. *)
Record cl_step_ops (h : string -> list sv -> W.cres) : Prop := {
 step_typep_int : forall z, exists r, h "TYPEP" [W.zs z; VSym "FIXNUM"] = W.CRet (W.hb r);
 step_incr : forall z, h "1+" [W.zs z] = W.CRet (W.zs (z + 1)%Z);
 step_decr : forall z, h "1-" [W.zs z] = W.CRet (W.zs (z - 1)%Z) }.

Section Step.
Variable h : string -> list sv -> W.cres.
Hypothesis A : cl_step_ops h.
Lemma ce_the : forall m env t x, W.ceval (S m) h env (W.SL [W.Sy "THE"; t; x]) = W.ceval m h env x.
Proof. reflexivity. Qed.
Lemma step_value : forall g (o : Z -> Z), W.plain g = true -> W.assoc g W.program = None ->
 (forall z, h g [W.zs z] = W.CRet (W.zs (o z))) ->
 forall z n, 10 <= n -> W.ceval n h [("X", W.zs z)] (W.step_body g) = W.CRet (W.zs (o z)).
Proof.
 intros g o P G Ho z n Hn.
 assert (exists k, n = S (S (S (S (S (S (S (S (S (S k)))))))))) as [k ->] by (exists (n - 10); lia).
 unfold W.step_body. destruct (step_typep_int h A z) as [r E].
 rewrite (if_bool h _ _ _ _ _ r) by (eapply call2q; [reflexivity|reflexivity|reflexivity|reflexivity|exact E]).
 destruct r.
 - eapply W.ce_host1; [exact P|exact G| |apply Ho]. rewrite ce_the. apply W.ce_var; reflexivity.
 - eapply call1; [exact P|exact G|reflexivity|reflexivity|apply Ho].
Qed.
Theorem increment_int : forall z n, 10 <= n ->
 W.ceval n h [("X", W.zs z)] (W.step_body "1+") = W.CRet (W.zs (z + 1)%Z).
Proof. intros z n Hn. apply (step_value "1+" (fun z => z + 1)%Z); auto. apply (step_incr h A). Qed.
Theorem decrement_int : forall z n, 10 <= n ->
 W.ceval n h [("X", W.zs z)] (W.step_body "1-") = W.CRet (W.zs (z - 1)%Z).
Proof. intros z n Hn. apply (step_value "1-" (fun z => z - 1)%Z); auto. apply (step_decr h A). Qed.
(* The KLambda rules the rewritten calls stand for give the same integers. *)
Theorem step_refines_rules : forall Pr st z n, 10 <= n ->
 KLSemantics.KLSemantics.rule_arith Pr KLSyntax.KLSyntax.PAdd Z.add
   [KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt z); KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt 1)] st
   = KLSemantics.KLSemantics.ret (KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt (z + 1))) st /\
 KLSemantics.KLSemantics.rule_arith Pr KLSyntax.KLSyntax.PAdd Z.add
   [KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt 1); KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt z)] st
   = KLSemantics.KLSemantics.ret (KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt (z + 1))) st /\
 KLSemantics.KLSemantics.rule_arith Pr KLSyntax.KLSyntax.PSub Z.sub
   [KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt z); KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt 1)] st
   = KLSemantics.KLSemantics.ret (KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt (z - 1))) st /\
 W.ceval n h [("X", W.zs z)] (W.step_body "1+") = W.CRet (W.zs (z + 1)%Z) /\
 W.ceval n h [("X", W.zs z)] (W.step_body "1-") = W.CRet (W.zs (z - 1)%Z).
Proof.
 intros Pr st z n Hn. split; [reflexivity|]. split.
 - rewrite (Z.add_comm z 1). reflexivity.
 - split; [reflexivity|]. split; [apply increment_int | apply decrement_int]; exact Hn.
Qed.
End Step.
Definition model_step (f : string) (vs : list sv) : W.cres :=
 match f, vs with
 | "TYPEP", [VNum _; VSym "FIXNUM"] => W.CRet W.T
 | "1+", [VNum s] => match W.zinv s with Some z => W.CRet (W.zs (z + 1)%Z) | None => W.CUnsup end
 | "1-", [VNum s] => match W.zinv s with Some z => W.CRet (W.zs (z - 1)%Z) | None => W.CUnsup end
 | _, _ => W.CUnsup end.
Theorem model_step_ops : cl_step_ops model_step.
Proof.
 constructor; intros z.
 - exists true. reflexivity.
 - cbn. rewrite W.zinv_zs. reflexivity.
 - cbn. rewrite W.zinv_zs. reflexivity.
Qed.

End CLContracts.
