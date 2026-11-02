(* E2E-07: the captured shen/klambda.shen evaluator refines the Wave-A TLambda
   semantics (KLSemantics/KLMetatheory) on the KL-PURE-1 construct subset
   literals, variables, lambda, one-argument application, let, if, saturated
   primitives (+ - * < = cons hd tl cons? number? string?), raise and trap.
   The thing proved is the captured Native program of KLambdaEvaluatorCapture;
   this module only states the translation into TLambda syntax/values and the
   machine-side composition. [global], [freeze], [thaw] and function values
   are covered by KLambdaEvaluatorExtended; a run that reaches
   kl:shen.f-error has no Native value and is outside every theorem. *)
From Coq Require Import List String ZArith NArith Bool Lia Ascii.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLMetatheory Native
 KLambdaEvaluatorCapture KLambdaEvaluatorEquations KLambdaEvaluatorPrimitives.
Import ListNotations.
Module KLambdaEvaluatorRefinement.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics.
Module C := KLambdaEvaluatorCapture.KLambdaEvaluatorCapture.
Module Pr := KLambdaEvaluatorPrimitives.KLambdaEvaluatorPrimitives.
Module Q := KLambdaEvaluatorEquations.KLambdaEvaluatorEquations.
Import C.
Open Scope string_scope.

(* ---------- text ---------- *)
Lemma text_eqb_of_string : forall s t, text_eqb (of_string s) (of_string t) = String.eqb s t.
Proof.
 induction s as [|c s IH]; destruct t as [|d t]; try reflexivity. cbn [of_string] in *.
 change (text_eqb (N.of_nat (nat_of_ascii c) :: of_string s) (N.of_nat (nat_of_ascii d) :: of_string t) =
   String.eqb (String c s) (String d t)).
 cbn [text_eqb]. rewrite IH. cbn [String.eqb]. destruct (Ascii.eqb c d) eqn:E.
 - apply Ascii.eqb_eq in E; subst; rewrite N.eqb_refl; reflexivity.
 - replace (N.eqb (N.of_nat (nat_of_ascii c)) (N.of_nat (nat_of_ascii d))) with false; [reflexivity|].
   symmetry; apply N.eqb_neq; intro Q; apply Nat2N.inj in Q.
   assert (c = d) by (rewrite <- (ascii_nat_embedding c), <- (ascii_nat_embedding d), Q; reflexivity).
   subst; rewrite Ascii.eqb_refl in E; discriminate.
Qed.

(* ---------- translation into TLambda ---------- *)
(* Global function names are kept apart from primitive names. *)
Definition fname (f : string) : name := of_string ("user:" ++ f).
Fixpoint lit (d : rv) : expr := match d with
 | RInt z => ENum (NInt z) | RBool b => EBool b | RStr s => EStr (of_string s)
 | RSym s => ESym (of_string s) | RNil => ENil
 | RPair a b => ECall (of_string "cons") [lit a; lit b]
 | _ => ENil end.  (* never admitted: buri.literal? rejects non-data *)
(* trap: the handler expression is evaluated after the exception, in the trap's
   own lexical environment, and applied to the exception's message text. *)
Definition handler (h : expr) : expr :=
 EApp (ELam (of_string "h") (ELam (of_string "trap")
   (EApp (EVar (of_string "h")) [ECall (of_string "error-to-string") [EVar (of_string "trap")]]))) [h].
Fixpoint tr (e : term) : expr := match e with
 | TLit d => lit d
 | TVar x => EVar (of_string x)
 | TGlobal x => ECall (fname x) []
 | TLambda x b => ELam (of_string x) (tr b)
 | TApply f a => EApp (tr f) [tr a]
 | TLet x a b => ELet (of_string x) (tr a) (tr b)
 | TIf c a b => EIf (tr c) (tr a) (tr b)
 | TPrim op args => ECall (of_string op) (map tr args)
 | TRaise e => ECall (of_string "simple-error") [tr e]
 | TTrap e h => ETrap (tr e) (handler (tr h))
 | TFreeze e => EFreeze (tr e)
 | TThaw e => EApp (tr e) [] end.
(* The representation relation is this function: klambda.shen values to
   KLValue values (environments to lexical environments, pointwise). *)
Fixpoint tr_rv (v : rv) : value := match v with
 | RInt z => VNum (NInt z) | RBool b => VBool b | RStr s => VStr (of_string s)
 | RSym s => VSym (of_string s) | RNil => VNil
 | RPair a d => VCons (tr_rv a) (tr_rv d)
 | RClosure x e env => VLam (of_string x) (tr e) (map (fun p => (of_string (fst p), tr_rv (snd p))) env)
 | RFunction f args => VPartial (fname f) (map tr_rv args)
 | RThunk e env => VFrozen (tr e) (map (fun p => (of_string (fst p), tr_rv (snd p))) env) end.
Definition tr_env (env : list (string * rv)) : lenv := map (fun p => (of_string (fst p), tr_rv (snd p))) env.

Lemma lookup_tr : forall x env, lookup (of_string x) (tr_env env) = option_map tr_rv (assoc x env).
Proof.
 intros x env; induction env as [|[y v] env IH]; [reflexivity|]. cbn [tr_env map lookup assoc fst snd].
 rewrite text_eqb_of_string. destruct (String.eqb x y); [reflexivity|exact IH].
Qed.

(* ---------- the proved profile ---------- *)
Definition prim_of (op : string) : option prim := match op with
 | "+" => Some PAdd | "-" => Some PSub | "*" => Some PMul | "<" => Some PLt | "=" => Some PEqual
 | "cons" => Some PCons | "hd" => Some PHd | "tl" => Some PTl | "cons?" => Some PConsP
 | "number?" => Some PNumberP | "string?" => Some PStringP | _ => None end.
Definition prim_ok (op : string) (n : nat) : Prop :=
 match prim_of op with Some p => prim_arity p = n | None => False end.
Fixpoint sub (e : term) : Prop := match e with
 | TLit d => Pr.data d
 | TVar _ => True
 | TLambda _ b => sub b
 | TApply f a => sub f /\ sub a
 | TLet _ a b => sub a /\ sub b
 | TIf c a b => sub c /\ sub a /\ sub b
 | TPrim op args => prim_ok op (List.length args) /\ fold_right (fun a acc => sub a /\ acc) True args
 | TRaise e => sub e
 | TTrap e h => sub e /\ sub h
 | TGlobal _ | TFreeze _ | TThaw _ => False end.
Fixpoint ok (v : rv) : Prop := match v with
 | RPair a d => ok a /\ ok d
 | RClosure _ e env => sub e /\ fold_right (fun p acc => ok (snd p) /\ acc) True env
 | RFunction _ _ | RThunk _ _ => False
 | _ => True end.
Definition okenv (env : list (string * rv)) := Forall (fun p => ok (snd p)) env.
Lemma okenv_fold : forall env, fold_right (fun p acc => ok (snd p) /\ acc) True env <-> okenv env.
Proof. unfold okenv; induction env as [|p env IH]; cbn; [split; auto|]. rewrite Forall_cons_iff, <- IH. reflexivity. Qed.
Lemma sub_fold : forall es, fold_right (fun a acc => sub a /\ acc) True es <-> Forall sub es.
Proof. induction es as [|e es IH]; cbn; [split; auto|]. rewrite Forall_cons_iff, <- IH. reflexivity. Qed.
Lemma data_ok : forall d, Pr.data d -> ok d.
Proof. induction d; cbn; intuition. Qed.
Lemma assoc_ok : forall x env v, okenv env -> assoc x env = Some v -> ok v.
Proof.
 unfold okenv; induction env as [|[y w] env IH]; cbn; intros v O E; [discriminate|].
 inversion O; subst. destruct (String.eqb x y); [injection E as <-; assumption|eauto].
Qed.

(* Pinned profile slots: no modeled stack bound, and the system-error message
   of each exception class the evaluator can raise is its klambda.shen text. *)
Definition pure (P : profile) : Prop :=
 stack_limit P = None /\
 sys_message P XNotBoolean = of_string "nonboolean-condition" /\
 sys_message P XNotCallable = of_string "not-callable" /\
 (forall y, sys_message P (XUnboundVar y) = of_string "unbound-variable") /\
 sys_message P (XPrim PSimpleError) = of_string "error-message-not-string" /\
 (forall p, p <> PSimpleError -> sys_message P (XPrim p) = of_string "primitive-domain-or-arity").
Definition prim_table : list (string * prim) :=
 [("+", PAdd); ("-", PSub); ("*", PMul); ("<", PLt); ("=", PEqual); ("cons", PCons);
  ("hd", PHd); ("tl", PTl); ("cons?", PConsP); ("number?", PNumberP); ("string?", PStringP);
  ("simple-error", PSimpleError); ("error-to-string", PErrorToString)].
(* The store binds the primitive names (the [primitive Op Args] form does not
   consult the function namespace; here the namespace holds the primitives). *)
Definition prims (s : store) : Prop :=
 forall op p, In (op, p) prim_table -> lookup (of_string op) (gfuns s) = Some (FPrim p).

(* The premises are satisfiable: a concrete profile and store. *)
Definition pure_profile : profile := Profile
 (fun _ _ _ => None) (fun _ _ _ => false) (fun _ _ => NInt 0) (fun _ => []) (fun _ => None)
 (fun x => match x with
   | XNotBoolean => of_string "nonboolean-condition" | XNotCallable => of_string "not-callable"
   | XUnboundVar _ => of_string "unbound-variable"
   | XPrim PSimpleError => of_string "error-message-not-string"
   | XPrim _ => of_string "primitive-domain-or-arity" | _ => [] end)
 VNil (fun _ _ => None) None None.
Definition prim_store : store := Store [] [] (map (fun p => (of_string (fst p), FPrim (snd p))) prim_table).
Theorem pure_profile_ok : pure pure_profile.
Proof.
 unfold pure; cbn; repeat split; try reflexivity.
 intros p N; destruct p; try reflexivity; contradiction.
Qed.
Theorem prim_store_ok : prims prim_store.
Proof. intros op p I; cbn in I; repeat (destruct I as [I|I]; [injection I as <- <-; reflexivity|]); contradiction. Qed.

(* ---------- verdict correspondence ---------- *)
(* klambda.shen error messages and the TLambda exception classes they stand
   for (many-to-one; a user [raise] of the same text is XUser). *)
Definition exn_class (m : string) (x : exn) : Prop :=
 x = XUser (of_string m) \/
 (m = "unbound-variable" /\ exists y, x = XUnboundVar y) \/
 (m = "nonboolean-condition" /\ x = XNotBoolean) \/
 (m = "not-callable" /\ x = XNotCallable) \/
 (m = "error-message-not-string" /\ x = XPrim PSimpleError) \/
 (m = "primitive-domain-or-arity" /\ exists p, x = XPrim p /\ p <> PSimpleError).
Definition error_text (P : profile) (x : exn) : text :=
 match x with XUser t => t | _ => sys_message P x end.
Lemma class_text : forall P m x, pure P -> exn_class m x -> error_text P x = of_string m.
Proof.
 intros P m x (S0 & S1 & S2 & S3 & S4 & S5) C.
 destruct C as [->|[[-> [y ->]]|[[-> ->]|[[-> ->]|[[-> ->]|[-> [p [-> N]]]]]]]]; cbn; auto.
Qed.

Inductive taus (P : profile) : config -> config -> Prop :=
 | t_refl c : taus P c c
 | t_step c c' c'' : next P c = MTau c' -> taus P c' c'' -> taus P c c''.
Lemma taus_trans : forall P a b c, taus P a b -> taus P b c -> taus P a c.
Proof. intros P a b c H; induction H; intros; [assumption|econstructor; eauto]. Qed.

Definition reaches (P : profile) (c : config) (w : verdict) (k : list frame) (s : store) : Prop :=
 match w with
 | WRet v => taus P c (Cfg (Ret (tr_rv v)) k s)
 | WRaise m => exists x, exn_class m x /\ taus P c (Cfg (Throw x) k s)
 | WBudget | WUnsupported => True end.

(* ---------- machine-side composition, one lemma per construct ---------- *)
(* Every machine lemma takes the profile and store premises, used or not. *)
Set Default Proof Using "All".
Section Machine.
Variables (P : profile) (s : store).
Hypotheses (HP : pure P) (Hs : prims s).
Lemma Hst : stack_limit P = None. Proof. exact (proj1 HP). Qed.
Lemma Lp : forall op p, In (op, p) prim_table -> lookup (of_string op) (gfuns s) = Some (FPrim p).
Proof. exact Hs. Qed.
Ltac nx := cbn -[of_string kw lookup tr_env kl_eq]; unfold push, continue_with; rewrite ?Hst; cbn -[of_string kw lookup tr_env kl_eq].
Ltac tau := eapply t_step; [nx; reflexivity|].
(* A saturated call of a primitive-table name is that primitive's rule. *)
Lemma call_prim : forall op p args k, In (op, p) prim_table -> List.length args = prim_arity p ->
 call_named P (of_string op) args k s = prim_move P p args [] k s.
Proof.
 intros op p args k I L. unfold call_named. rewrite (Lp op p I). cbn beta iota.
 rewrite L, Nat.ltb_irrefl. cbn beta iota. rewrite <- L, firstn_all, skipn_all. reflexivity.
Qed.

Lemma reaches_step : forall c c' w k, next P c = MTau c' -> reaches P c' w k s -> reaches P c w k s.
Proof.
 intros c c' [v|m| |] k N R; cbn in *; auto.
 - econstructor; eauto.
 - destruct R as (x & C & T); exists x; split; [exact C|econstructor; eauto].
Qed.
Lemma reaches_taus : forall c c' w k, taus P c c' -> reaches P c' w k s -> reaches P c w k s.
Proof. intros c c' w k T; induction T; intro R; [exact R|eapply reaches_step; eauto]. Qed.
(* A value delivered to a frame, then the rest of the computation. *)
Lemma reaches_ret : forall c v (f : frame) (k1 k : list frame) c' w, reaches P c (WRet v) (f :: k1) s ->
 next P (Cfg (Ret (tr_rv v)) (f :: k1) s) = MTau c' -> reaches P c' w k s -> reaches P c w k s.
Proof. intros c v f k1 k c' w T N R. eapply reaches_taus; [exact T|]. eapply reaches_step; eauto. Qed.
(* A failure crosses any non-trap frame unchanged. *)
Definition notret (w : verdict) := match w with WRet _ => False | _ => True end.
Lemma reaches_fail : forall c w (f : frame) (k : list frame), notret w -> (forall h rho, f <> KTrap h rho) ->
 reaches P c w (f :: k) s -> reaches P c w k s.
Proof.
 intros c [v|m| |] f k NR NT R; cbn in *; try contradiction; auto.
 destruct R as (x & C & T); exists x; split; [exact C|].
 eapply taus_trans; [exact T|]. econstructor; [|constructor].
 destruct f; cbn; try reflexivity. exfalso; eapply NT; reflexivity.
Qed.

Lemma m_lit : forall d rho k, Pr.data d -> taus P (Cfg (Eval rho (lit d)) k s) (Cfg (Ret (tr_rv d)) k s).
Proof.
 induction d; intros rho k D; cbn in D; try contradiction; try (tau; constructor).
 destruct D as [Da Dd]. cbn [lit tr_rv]. tau.
 eapply taus_trans; [apply IHd1; exact Da|]. tau.
 eapply taus_trans; [apply IHd2; exact Dd|].
 eapply t_step; [|constructor]. nx.
 rewrite (call_prim "cons" PCons) by (cbn; tauto || reflexivity). reflexivity.
Qed.
Lemma m_var : forall x env k,
 reaches P (Cfg (Eval (tr_env env) (EVar (of_string x))) k s)
   (match assoc x env with Some v => WRet v | None => WRaise "unbound-variable" end) k s.
Proof.
 intros x env k. eapply reaches_step; [nx; rewrite lookup_tr; reflexivity|].
 destruct (assoc x env) as [v|]; cbn.
 - constructor.
 - exists (XUnboundVar (of_string x)); split; [right; left; eauto|constructor].
Qed.

(* Per-construct composition, for this profile and store. *)
Definition ev (e : term) (env : list (string * rv)) (w : verdict) : Prop :=
 forall k, reaches P (Cfg (Eval (tr_env env) (tr e)) k s) w k s.
Definition ap (f a : rv) (w : verdict) : Prop := forall k, match w with
 | WRet _ | WRaise _ => exists c, apply_value P (tr_rv f) [tr_rv a] k s = MTau c /\ reaches P c w k s
 | _ => True end.
Definition argsr (es : list term) (env : list (string * rv)) (a : args_verdict) : Prop :=
 match a with
 | AVals vs => forall k f done e1 es', es = e1 :: es' ->
   exists c, taus P (Cfg (Eval (tr_env env) (tr e1)) (KCallArgs f done (map tr es') (tr_env env) :: k) s) c /\
     next P c = call_named P f (rev done ++ map tr_rv vs) k s
 | AFail (WRaise m) => forall k f done e1 es', es = e1 :: es' ->
   exists x, exn_class m x /\
     taus P (Cfg (Eval (tr_env env) (tr e1)) (KCallArgs f done (map tr es') (tr_env env) :: k) s) (Cfg (Throw x) k s)
 | AFail (WRet _) => False
 | AFail _ => True end.
Ltac nf := intros ? ? E; discriminate E.
Lemma raise_here : forall m x k, exn_class m x -> reaches P (Cfg (Throw x) k s) (WRaise m) k s.
Proof. intros; exists x; split; [assumption|constructor]. Qed.

Lemma m_lambda : forall x b env, ev (TLambda x b) env (WRet (RClosure x b env)).
Proof. intros x b env k. cbn [tr reaches]. tau. constructor. Qed.
Lemma m_let_ret : forall x a b env v w, ev a env (WRet v) -> ev b ((x, v) :: env) w -> ev (TLet x a b) env w.
Proof.
 intros x a b env v w Ga Gb k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Ga|nx; reflexivity|apply Gb].
Qed.
Lemma m_let_fail : forall x a b env w, notret w -> ev a env w -> ev (TLet x a b) env w.
Proof.
 intros x a b env w N Ga k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_fail; [exact N| |apply Ga]; nf.
Qed.
Lemma m_if_bool : forall c a b env bv w, ev c env (WRet (RBool bv)) -> ev (if bv then a else b) env w ->
 ev (TIf c a b) env w.
Proof.
 intros c a b env bv w Gc Gb k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Gc|nx; reflexivity|]. destruct bv; apply Gb.
Qed.
Lemma m_if_nonbool : forall c a b env v, (forall bv, v <> RBool bv) -> ev c env (WRet v) ->
 ev (TIf c a b) env (WRaise "nonboolean-condition").
Proof.
 intros c a b env v NB Gc k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 destruct v; try (exfalso; eapply NB; reflexivity);
 (eapply reaches_ret; [apply Gc|nx; reflexivity|apply raise_here; right; right; left; split; reflexivity]).
Qed.
Lemma m_if_fail : forall c a b env w, notret w -> ev c env w -> ev (TIf c a b) env w.
Proof.
 intros c a b env w N Gc k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_fail; [exact N| |apply Gc]; nf.
Qed.
Lemma m_app_ret : forall f a env fv av w, ev f env (WRet fv) -> ev a env (WRet av) -> ap fv av w ->
 ev (TApply f a) env w.
Proof.
 intros f a env fv av w Gf Ga Ap k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Gf|nx; reflexivity|].
 specialize (Ap k). destruct w; try exact I; destruct Ap as (c & E & Rc);
 (eapply reaches_ret; [apply Ga|cbn [next ctl kont mem ret_move rev List.app]; exact E|exact Rc]).
Qed.
Lemma m_app_fail1 : forall f a env w, notret w -> ev f env w -> ev (TApply f a) env w.
Proof.
 intros f a env w N Gf k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_fail; [exact N| |apply Gf]; nf.
Qed.
Lemma m_app_fail2 : forall f a env fv w, notret w -> ev f env (WRet fv) -> ev a env w -> ev (TApply f a) env w.
Proof.
 intros f a env fv w N Gf Ga k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Gf|nx; reflexivity|]. eapply reaches_fail; [exact N| |apply Ga]; nf.
Qed.
Lemma ap_closure : forall x e env a w, ev e ((x, a) :: env) w -> ap (RClosure x e env) a w.
Proof.
 intros x e env a w Ge k. destruct w; try exact I;
 (exists (Cfg (Eval (tr_env ((x, a) :: env)) (tr e)) k s); split; [reflexivity|apply Ge]).
Qed.
Lemma ap_noncallable : forall f a, (forall x e env, f <> RClosure x e env) ->
 (forall g args, f <> RFunction g args) -> (forall e env, f <> RThunk e env) ->
 ap f a (WRaise "not-callable").
Proof.
 intros f a NC NF NT k. destruct f; try (exfalso; eapply NC; reflexivity);
 try (exfalso; eapply NF; reflexivity); try (exfalso; eapply NT; reflexivity);
 (exists (Cfg (Throw XNotCallable) k s); split; [reflexivity|apply raise_here; right; right; right; left; split; reflexivity]).
Qed.
Lemma m_raise_str : forall e env t, ev e env (WRet (RStr t)) -> ev (TRaise e) env (WRaise t).
Proof.
 intros e env t Ge k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Ge| |apply raise_here; left; reflexivity].
 nx. rewrite (call_prim "simple-error" PSimpleError) by (cbn; first [tauto|reflexivity]). reflexivity.
Qed.
Lemma m_raise_nonstr : forall e env v, (forall t, v <> RStr t) -> ev e env (WRet v) ->
 ev (TRaise e) env (WRaise "error-message-not-string").
Proof.
 intros e env v NS Ge k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Ge| |apply raise_here; right; right; right; right; left; split; reflexivity].
 nx. rewrite (call_prim "simple-error" PSimpleError) by (cbn; first [tauto|reflexivity]).
 destruct v; try (exfalso; eapply NS; reflexivity); reflexivity.
Qed.
Lemma m_raise_fail : forall e env w, notret w -> ev e env w -> ev (TRaise e) env w.
Proof.
 intros e env w N Ge k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_fail; [exact N| |apply Ge]; nf.
Qed.
Lemma m_trap_ret : forall e h env v, ev e env (WRet v) -> ev (TTrap e h) env (WRet v).
Proof.
 intros e h env v Ge k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Ge|nx; reflexivity|constructor].
Qed.
Lemma m_trap_other : forall e h env w, (w = WBudget \/ w = WUnsupported) -> ev (TTrap e h) env w.
Proof. intros e h env w [->| ->] k; exact I. Qed.
Ltac steps := repeat (eapply reaches_step; [nx; first [
 (cbn [lookup]; rewrite ?text_eqb_of_string; cbn -[tr_env of_string kl_eq]; reflexivity) |
 rewrite (call_prim "error-to-string" PErrorToString) by (cbn; first [tauto|reflexivity]); reflexivity | reflexivity]|]).
(* The exception at a trap frame: evaluate the handler expression in the
   trap's environment, then apply it to the exception's message text. *)
Lemma m_trap_raise_ret : forall e h env m hv w, ev e env (WRaise m) -> ev h env (WRet hv) ->
 ap hv (RStr m) w -> ev (TTrap e h) env w.
Proof.
 intros e h env m hv w Ge Gh Ap k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 specialize (Ap k). destruct w; try exact I; destruct Ap as (c & E & Rc);
 destruct (Ge (KTrap (handler (tr h)) (tr_env env) :: k)) as (x & C & T);
 pose proof (class_text P m x HP C) as Tx; destruct x; cbn in Tx;
 (eapply reaches_taus; [exact T|]); unfold handler; steps;
 (eapply reaches_ret; [apply Gh|nx; reflexivity|]); steps;
 (eapply reaches_step; [|exact Rc]); cbn [next ctl kont mem ret_move rev List.app];
 cbn [tr_rv] in E; rewrite <- Tx in E; exact E.
Qed.
Lemma m_trap_raise_fail : forall e h env m w, notret w -> ev e env (WRaise m) -> ev h env w ->
 ev (TTrap e h) env w.
Proof.
 intros e h env m w N Ge Gh k. cbn [tr]. eapply reaches_step; [nx; reflexivity|].
 destruct (Ge (KTrap (handler (tr h)) (tr_env env) :: k)) as (x & C & T).
 eapply reaches_taus; [exact T|].
 eapply reaches_step; [nx; reflexivity|]. unfold handler.
 eapply reaches_step; [nx; reflexivity|]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_step; [nx; reflexivity|].
 eapply reaches_fail; [exact N| |eapply reaches_fail; [exact N| |apply Gh]; nf]; nf.
Qed.

(* Arguments of a saturated primitive call, left to right. *)
Lemma args_ret : forall e1 es env v vs, ev e1 env (WRet v) ->
 match es with [] => vs = [] | _ => argsr es env (AVals vs) end -> argsr (e1 :: es) env (AVals (v :: vs)).
Proof.
 intros e1 es env v vs G1 Gs k f done e es' E; injection E as <- <-.
 destruct es as [|e2 es2].
 - subst vs. exists (Cfg (Ret (tr_rv v)) (KCallArgs f done [] (tr_env env) :: k) s). split; [apply G1|].
   cbn [next ctl kont mem ret_move map rev]. reflexivity.
 - destruct (Gs k f (tr_rv v :: done) e2 es2 eq_refl) as (c & T & N).
   exists c; split.
   + eapply taus_trans; [apply G1|]. eapply t_step; [cbn [next ctl kont mem ret_move map]; reflexivity|exact T].
   + rewrite N. cbn [rev map]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma args_fail1 : forall e1 es env m, ev e1 env (WRaise m) -> argsr (e1 :: es) env (AFail (WRaise m)).
Proof.
 intros e1 es env m G1 k f done e es' E; injection E as <- <-.
 destruct (G1 (KCallArgs f done (map tr es) (tr_env env) :: k)) as (x & C & T).
 exists x; split; [exact C|]. eapply taus_trans; [exact T|]. eapply t_step; [reflexivity|constructor].
Qed.
Lemma args_fail2 : forall e1 e2 es env v m, ev e1 env (WRet v) -> argsr (e2 :: es) env (AFail (WRaise m)) ->
 argsr (e1 :: e2 :: es) env (AFail (WRaise m)).
Proof.
 intros e1 e2 es env v m G1 Gs k f done e es' E; injection E as <- <-.
 destruct (Gs k f (tr_rv v :: done) e2 es eq_refl) as (x & C & T). exists x; split; [exact C|].
 eapply taus_trans; [apply G1|]. eapply t_step; [cbn [next ctl kont mem ret_move map]; reflexivity|exact T].
Qed.
Lemma m_prim_vals : forall op es env vs w, es <> [] -> argsr es env (AVals vs) ->
 (forall k, exists c, call_named P (of_string op) (map tr_rv vs) k s = MTau c /\ reaches P c w k s) ->
 ev (TPrim op es) env w.
Proof.
 intros op [|e1 es] env vs w NE G Pr k; [contradiction|]. cbn [tr map].
 eapply reaches_step; [nx; reflexivity|].
 destruct (G k (of_string op) [] e1 es eq_refl) as (c & T & N). destruct (Pr k) as (c' & E & R).
 eapply reaches_taus; [exact T|]. eapply reaches_step; [|exact R]. rewrite N. exact E.
Qed.
Lemma m_prim_fail : forall op es env m, es <> [] -> argsr es env (AFail (WRaise m)) -> ev (TPrim op es) env (WRaise m).
Proof.
 intros op [|e1 es] env m NE G k; [contradiction|]. cbn [tr map].
 eapply reaches_step; [nx; reflexivity|].
 destruct (G k (of_string op) [] e1 es eq_refl) as (x & C & T). exists x; split; assumption.
Qed.

(* Saturated primitive rules against the captured clause results. *)
Lemma dom_class : forall p, p <> PSimpleError -> exn_class "primitive-domain-or-arity" (XPrim p).
Proof. intros p N; right; right; right; right; right; split; [reflexivity|eauto]. Qed.
Lemma kl_prim : forall op p vs k, In op ["+"; "-"; "*"; "<"; "cons"; "hd"; "tl"; "cons?"; "number?"; "string?"] ->
 prim_of op = Some p -> List.length vs = prim_arity p ->
 exists c, call_named P (of_string op) (map tr_rv vs) k s = MTau c /\ reaches P c (Pr.prim_spec op vs) k s.
Proof.
 intros op p vs k I O L.
 cbn [In] in I; repeat (destruct I as [<-|I]; [|]); try contradiction;
 injection O as <-; rewrite (call_prim _ _ (map tr_rv vs)) by (cbn; tauto || (rewrite map_length; exact L));
 cbn in L; destruct vs as [|a [|b [|]]]; try discriminate L;
 destruct a; try destruct b; cbn -[of_string];
 (eexists; split; [reflexivity|]);
 first [constructor | apply raise_here; apply dom_class; discriminate].
Qed.
Lemma eq_depth_cons : forall h n a1 a2 b1 b2, eq_depth P h (S n) (VCons a1 a2) (VCons b1 b2) =
 match eq_depth P h (S n) a1 b1 with Some true => eq_depth P h (S n) a2 b2 | r => r end.
Proof. reflexivity. Qed.
Lemma kl_eq_data : forall a b h, Pr.data a -> Pr.data b ->
 kl_eq P h (tr_rv a) (tr_rv b) = Some (Native.Native.same (enc a) (enc b)).
Proof.
 intros a b h. unfold kl_eq. generalize (List.length h) as n. intro n.
 revert b; induction a as [z|bb|st|sy| |a1 IHa1 a2 IHa2|x e env|f args|e env]; intros b0 Da Db; destruct b0 as [z0|bb0|st0|sy0| |b1 b2|x0 e0 env0|f0 args0|e0 env0]; cbn in Da, Db; try contradiction; first [cbn [tr_rv]; rewrite eq_depth_cons; cbn -[of_string eq_depth] | cbn -[of_string]];
 try reflexivity.
 - rewrite andb_true_r. reflexivity.
 - rewrite andb_true_r. reflexivity.
 - rewrite text_eqb_of_string, andb_true_r. reflexivity.
 - rewrite text_eqb_of_string, andb_true_r. reflexivity.
 - destruct Da as [Da1 Da2], Db as [Db1 Db2].
   rewrite (IHa1 b1 Da1 Db1), (IHa2 b2 Da2 Db2).
   destruct (Native.Native.same (enc a1) (enc b1)); cbn; rewrite ?andb_true_r; reflexivity.
Qed.
(* KLambda equality of translated values is the evaluator's eqv, for every
   value: closures, [function ...] and thunks are the function values of
   kl_eq, and pairs compare left to right. *)
Lemma kl_eq_tr : forall a b h, kl_eq P h (tr_rv a) (tr_rv b) = Pr.eqv a b.
Proof.
 intros a b h. unfold kl_eq. generalize (List.length h) as n. intro n.
 revert b; induction a as [z|bb|st|sy| |a1 IHa1 a2 IHa2|x e env|f args|e env]; intro b0;
 destruct b0 as [z0|bb0|st0|sy0| |b1 b2|x0 e0 env0|f0 args0|e0 env0];
 first [cbn [tr_rv]; rewrite eq_depth_cons; cbn -[of_string eq_depth tr_rv tr] | cbn -[of_string tr]];
 try reflexivity; rewrite ?text_eqb_of_string, ?andb_true_r; try reflexivity.
 rewrite IHa1. destruct (Pr.eqv a1 b1) as [[|]|]; [apply IHa2|reflexivity|reflexivity].
Qed.
Lemma kl_prim_equal_tr : forall a b k,
 match Pr.eqv a b with
 | Some x => exists c, call_named P (of_string "=") (map tr_rv [a; b]) k s = MTau c /\
     reaches P c (WRet (RBool x)) k s
 | None => next P (Cfg (Ret (tr_rv b)) (KCallArgs (of_string "=") [tr_rv a] [] (tr_env []) :: k) s) =
     MTau (Cfg (Wrong (kw "equality-undefined")) k s) end.
Proof.
 intros a b k. pose proof (call_prim "=" PEqual (map tr_rv [a; b]) k) as C.
 cbn [map] in C |- *. cbn [rev List.app next ctl kont mem ret_move].
 rewrite C by (cbn; first [tauto|reflexivity]). clear C.
 pose proof (kl_eq_tr a b (heap s)) as KE.
 unfold prim_move; cbn [prim_rule]. unfold rule_equal. rewrite KE.
 destruct (Pr.eqv a b) as [x|]; [eexists; split; [reflexivity|constructor]|reflexivity].
Qed.
Lemma kl_prim_equal : forall a b k, Pr.data a -> Pr.data b ->
 exists c, call_named P (of_string "=") (map tr_rv [a; b]) k s = MTau c /\
   reaches P c (WRet (RBool (Native.Native.same (enc a) (enc b)))) k s.
Proof.
 intros a b k Da Db. rewrite (call_prim "=" PEqual) by (cbn; first [tauto|reflexivity]).
 unfold prim_move; cbn [prim_rule map]. unfold rule_equal. rewrite (kl_eq_data a b (heap s) Da Db).
 eexists; split; [reflexivity|constructor].
Qed.
End Machine.

(* ---------- the refinement induction (over oracle fuel) ---------- *)
Definition Gd e env w := forall P s, pure P -> prims s -> ev P s e env w.
Definition Ga f a w := forall P s, pure P -> prims s -> ap P s f a w.
Definition Gargs es env a := forall P s, pure P -> prims s -> argsr P s es env a.
Definition ok_verdict (w : verdict) := match w with WRet v => ok v | _ => True end.
Definition ok_args (a : args_verdict) := match a with AVals vs => Forall ok vs | AFail w => notret w end.
Definition len_args (es : list term) (a : args_verdict) :=
 match a with AVals vs => List.length vs = List.length es | AFail _ => es <> [] end.
Definition Seval k := forall D e env z r, sub e -> okenv env ->
 ask k "kl:buri.eval" [D; enc_term e; enc_env env; Native.Native.Integer z] = Some r ->
 exists w, r = enc_verdict w /\ ok_verdict w /\ Gd e env w.
Definition Sapply k := forall D f a z r, ok f -> ok a ->
 ask k "kl:buri.apply-value" [D; enc f; enc a; Native.Native.Integer z] = Some r ->
 exists w, r = enc_verdict w /\ ok_verdict w /\ Ga f a w.
Definition Sargs k := forall D es env z r, Forall sub es -> okenv env ->
 ask k "kl:buri.eval-args" [D; Native.Native.L (map enc_term es); enc_env env; Native.Native.Integer z] = Some r ->
 exists a, r = enc_args a /\ ok_args a /\ len_args es a /\ Gargs es env a.

Lemma prim_cases : forall op p, prim_of op = Some p ->
 (In op ["+"; "-"; "*"; "<"; "cons"] /\ prim_arity p = 2) \/
 (In op ["hd"; "tl"; "cons?"; "number?"; "string?"] /\ prim_arity p = 1) \/ (op = "=" /\ p = PEqual).
Proof.
 intros op p E. unfold prim_of in E.
 repeat match type of E with context [match ?o with _ => _ end] => is_var o; destruct o end;
 try discriminate E; injection E as <-; cbn; auto 20.
Qed.
Lemma prim_table_in : forall op p, prim_of op = Some p -> In (op, p) prim_table.
Proof.
 intros op p E. unfold prim_of in E.
 repeat match type of E with context [match ?o with _ => _ end] => is_var o; destruct o end;
 try discriminate E; injection E as <-; cbn; auto 20.
Qed.
Lemma prim_spec_ok : forall op vs, Forall ok vs ->
 In op ["+"; "-"; "*"; "<"; "cons"; "hd"; "tl"; "cons?"; "number?"; "string?"] -> ok_verdict (Pr.prim_spec op vs).
Proof.
 intros op vs O Hin. cbn [In] in Hin.
 repeat (destruct Hin as [<-|Hin]; [|]); try contradiction;
 destruct vs as [|a [|b [|c vs]]]; cbn; try exact I;
 repeat match goal with Hf : Forall _ (_ :: _) |- _ => inversion Hf; subst; clear Hf end;
 try (destruct a; cbn; try exact I; cbn in *; tauto);
 destruct a, b; cbn in *; tauto.
Qed.
Ltac ret H := match type of H with Some ?X = Some ?r => assert (EQ : r = X) by congruence; clear H; subst r end;
 eexists; split; [reflexivity|].
Ltac gate_case H := unfold gate in H; destruct (Z.eqb _ 0);
 [ret H; repeat split; intros ? ? ? ? ?; exact I|].

Lemma step_all : forall j, (forall i, i <= j -> Seval i /\ Sapply i /\ Sargs i) ->
 Seval (S j) /\ Sapply (S j) /\ Sargs (S j).
Proof.
 intros j IH. assert (IE : forall i, i <= j -> Seval i) by (intros i L; apply (IH i L)).
 assert (IA : forall i, i <= j -> Sapply i) by (intros i L; apply (IH i L)).
 assert (IG : forall i, i <= j -> Sargs i) by (intros i L; apply (IH i L)).
 split; [|split].
 - (* buri.eval *)
   intros D e env z r Se Oe H. destruct e as [d|x|x|x b|f a|x a b|c a b|op args|e|e h|e|e]; cbn [sub] in Se;
     try contradiction.
   + rewrite Q.eval_lit in H. gate_case H. ret H. split; [apply data_ok; exact Se|].
     intros P s HP Hs k. apply (m_lit P s HP Hs d _ k Se).
   + rewrite Q.eval_var in H. gate_case H.
     destruct (ask j "kl:buri.get" _) as [g|] eqn:G; [|discriminate]. apply ask_get in G; subst g.
     destruct j as [|j]; [discriminate|].
     destruct (assoc x env) as [v|] eqn:A; cbn beta iota in H;
       [rewrite Q.lookup_found in H|rewrite Q.lookup_missing in H]; ret H.
     * split; [eapply assoc_ok; eassumption|]. intros P s HP Hs k.
       pose proof (m_var P s HP Hs x env k) as M; rewrite A in M; exact M.
     * split; [exact I|]. intros P s HP Hs k.
       pose proof (m_var P s HP Hs x env k) as M; rewrite A in M; exact M.
   + rewrite Q.eval_lambda in H. gate_case H. ret H. split; [split; [exact Se|apply okenv_fold; exact Oe]|].
     intros P s HP Hs; apply (m_lambda P s HP Hs); assumption.
   + destruct Se as [Sf Sa]. rewrite Q.eval_apply in H. gate_case H.
     destruct (ask j "kl:buri.eval" [D; enc_term f; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ _ Sf Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite Q.function_verdict in H.
     destruct w1 as [fv|m| |]; try (ret H; split; [exact I|];
       intros P s HP Hs; apply (m_app_fail1 P s HP Hs); [exact I|apply G1; assumption]).
     destruct (ask j "kl:buri.eval" [D; enc_term a; enc_env env; _]) as [v2|] eqn:E2; [|discriminate].
     destruct (IE j (le_S _ _ (le_n j)) _ _ _ _ _ Sa Oe E2) as (w2 & -> & O2 & G2).
     destruct j as [|j]; [discriminate|]. rewrite Q.argument_verdict in H.
     destruct w2 as [av|m| |]; try (ret H; split; [exact I|];
       intros P s HP Hs; eapply (m_app_fail2 P s HP Hs); [exact I|apply G1; assumption|apply G2; assumption]).
     destruct (IA j (le_S _ _ (le_S _ _ (le_n j))) _ _ _ _ _ O1 O2 H) as (w & -> & O & GA).
     eexists; split; [reflexivity|split; [exact O|]].
     intros P s HP Hs. eapply (m_app_ret P s HP Hs); [apply G1|apply G2|apply GA]; assumption.
   + destruct Se as [Sa Sb]. rewrite Q.eval_let in H. gate_case H.
     destruct (ask j "kl:buri.eval" [D; enc_term a; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ _ Sa Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite Q.let_verdict in H.
     destruct w1 as [v|m| |]; try (ret H; split; [exact I|];
       intros P s HP Hs; apply (m_let_fail P s HP Hs); [exact I|apply G1; assumption]).
     assert (O' : okenv ((x, v) :: env)) by (constructor; assumption).
     destruct (IE j (le_S _ _ (le_n j)) _ _ _ _ _ Sb O' H) as (w & -> & O & G2).
     eexists; split; [reflexivity|split; [exact O|]].
     intros P s HP Hs. eapply (m_let_ret P s HP Hs); [apply G1|apply G2]; assumption.
   + destruct Se as (Sc & Sa & Sb). rewrite Q.eval_if in H. gate_case H.
     destruct (ask j "kl:buri.eval" [D; enc_term c; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ _ Sc Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. apply Q.if_verdict in H.
     destruct w1 as [v|m| |]; try (subst r; eexists; split; [reflexivity|]; split; [exact I|];
       intros P s HP Hs; apply (m_if_fail P s HP Hs); [exact I|apply G1; assumption]).
     destruct v as [z0| [|] |st|sy| |a1 a2|x0 e0 env0|f0 g0|e0 env0];
       try (subst r; eexists; split; [reflexivity|]; split; [exact I|];
         intros P s HP Hs; eapply (m_if_nonbool P s HP Hs); [|apply G1; assumption]; intros bv E; discriminate E).
     * destruct (IE j (le_S _ _ (le_n j)) _ _ _ _ _ Sa Oe H) as (w & -> & O & G2).
       eexists; split; [reflexivity|split; [exact O|]].
       intros P s HP Hs. eapply (m_if_bool P s HP Hs c a b env true); [apply G1|apply G2]; assumption.
     * destruct (IE j (le_S _ _ (le_n j)) _ _ _ _ _ Sb Oe H) as (w & -> & O & G2).
       eexists; split; [reflexivity|split; [exact O|]].
       intros P s HP Hs. eapply (m_if_bool P s HP Hs c a b env false); [apply G1|apply G2]; assumption.
   + destruct Se as [Ar Sargs0]. apply sub_fold in Sargs0.
     unfold prim_ok in Ar. destruct (prim_of op) as [p|] eqn:Op; [|contradiction].
     rewrite Q.eval_prim in H. gate_case H.
     destruct (ask j "kl:buri.eval-args" _) as [v1|] eqn:E1; [|discriminate].
     destruct (IG j (le_n j) _ _ _ _ _ Sargs0 Oe E1) as (a1 & -> & O1 & L1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite Q.primitive_args in H.
     assert (NE : args <> []) by (intro Z; subst args; destruct p; discriminate Ar).
     destruct a1 as [vs|w1].
     * cbn in L1. pose proof (prim_table_in op p Op) as In0.
       destruct (prim_cases op p Op) as [[I2 A2]|[[I1 A1]|[-> ->]]].
       -- destruct vs as [|v1 [|v2 [|]]]; cbn in L1; try (rewrite <- Ar, A2 in L1; discriminate L1).
          cbn [map] in H. apply Pr.ask_prim2 in H; [|exact I2]. subst r.
          eexists; split; [reflexivity|split; [apply prim_spec_ok; [exact O1|cbn in I2 |- *; tauto]|]].
          intros P s HP Hs. eapply (m_prim_vals P s HP Hs); [exact NE|apply G1; assumption|].
          intro k. apply (kl_prim P s HP Hs op p [v1; v2] k); [cbn in I2 |- *; tauto|exact Op|rewrite A2; reflexivity].
       -- destruct vs as [|v1 [|]]; cbn in L1; try (rewrite <- Ar, A1 in L1; discriminate L1).
          cbn [map] in H. apply Pr.ask_prim1 in H; [|exact I1]. subst r.
          eexists; split; [reflexivity|split; [apply prim_spec_ok; [exact O1|cbn in I1 |- *; tauto]|]].
          intros P s HP Hs. eapply (m_prim_vals P s HP Hs); [exact NE|apply G1; assumption|].
          intro k. apply (kl_prim P s HP Hs op p [v1] k); [cbn in I1 |- *; tauto|exact Op|rewrite A1; reflexivity].
       -- destruct vs as [|v1 [|v2 [|]]]; cbn in L1; try (rewrite <- Ar in L1; discriminate L1).
          cbn [map] in H. apply Pr.ask_prim_equal in H. subst r. unfold Pr.eq_spec.
          pose proof (fun P s HP Hs k => kl_prim_equal_tr P s HP Hs v1 v2 k) as KE.
          destruct (Pr.eqv v1 v2) as [x|].
          ++ eexists; split; [reflexivity|split; [exact I|]].
             intros P s HP Hs. eapply (m_prim_vals P s HP Hs); [exact NE|apply G1; assumption|].
             intro k. apply (KE P s HP Hs k).
          ++ exists WUnsupported; repeat split; intros ? ? ? ? ?; exact I.
     * ret H. split; [destruct w1; cbn in O1 |- *; tauto|].
       intros P s HP Hs. destruct w1 as [v|m| |]; cbn in O1; try contradiction; try (intros k; exact I).
       apply (m_prim_fail P s HP Hs); [exact NE|apply G1; assumption].
   + rewrite Q.eval_raise in H. gate_case H.
     destruct (ask j "kl:buri.eval" [D; enc_term e; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ _ Se Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite Q.raise_verdict in H.
     destruct w1 as [v|m| |]; try (ret H; split; [exact I|];
       intros P s HP Hs; apply (m_raise_fail P s HP Hs); [exact I|apply G1; assumption]).
     destruct v as [z0|b0|t|sy| |a1 a2|x0 e0 env0|f0 g0|e0 env0]; ret H; split; try exact I; intros P s HP Hs;
       first [eapply (m_raise_str P s HP Hs); apply G1; assumption
             |eapply (m_raise_nonstr P s HP Hs); [|apply G1; assumption]; intros t' E; discriminate E].
   + destruct Se as [Se Sh]. rewrite Q.eval_trap in H. gate_case H.
     destruct (ask j "kl:buri.eval" [D; enc_term e; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ _ Se Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite Q.trap_verdict in H.
     destruct w1 as [v|m| |].
     * ret H. split; [exact O1|]. intros P s HP Hs. apply (m_trap_ret P s HP Hs); apply G1; assumption.
     * destruct (ask j "kl:buri.eval" [D; enc_term h; enc_env env; _]) as [v2|] eqn:E2; [|discriminate].
       destruct (IE j (le_S _ _ (le_n j)) _ _ _ _ _ Sh Oe E2) as (w2 & -> & O2 & G2).
       destruct j as [|j]; [discriminate|]. rewrite Q.handler_verdict in H.
       destruct w2 as [hv|m2| |]; try (ret H; split; [exact I|];
         intros P s HP Hs; eapply (m_trap_raise_fail P s HP Hs); [exact I|apply G1; assumption|apply G2; assumption]).
       destruct (IA j (le_S _ _ (le_S _ _ (le_n j))) D hv (RStr m) _ _ O2 I H) as (w & -> & O & GA).
       eexists; split; [reflexivity|split; [exact O|]].
       intros P s HP Hs. eapply (m_trap_raise_ret P s HP Hs); [apply G1|apply G2|apply GA]; assumption.
     * ret H. split; [exact I|]. intros P s HP Hs; apply (m_trap_other P s HP Hs); auto.
     * ret H. split; [exact I|]. intros P s HP Hs; apply (m_trap_other P s HP Hs); auto.
 - (* buri.apply-value on a closure or a non-callable value *)
   intros D f a z r Of Oa H.
   rewrite Q.apply_value_eq in H; [|intros g args E; subst f; exact Of|intros e0 env0 E; subst f; exact Of].
   gate_case H. destruct f as [z0|b0|st|sy| |a1 a2|x e env|g args|e env]; cbn in Of; try contradiction;
     try (ret H; split; [exact I|]; intros P s HP Hs; apply (ap_noncallable P s HP Hs); intros; discriminate).
   destruct Of as [Se Oe]. apply okenv_fold in Oe.
   assert (O' : okenv ((x, a) :: env)) by (constructor; assumption).
   destruct (IE j (le_n j) _ _ _ _ _ Se O' H) as (w & -> & O & G).
   eexists; split; [reflexivity|split; [exact O|]].
   intros P s HP Hs. apply (ap_closure P s HP Hs). apply G; assumption.
 - (* buri.eval-args *)
   intros D es env z r Ss Oe H. destruct es as [|e es].
   + rewrite Q.args_nil in H. injection H as <-. exists (AVals []); repeat split; [constructor|].
     intros P s HP Hs k f done e1 es' E; discriminate E.
   + inversion Ss as [|e0 es0 Se Ss']; subst. rewrite Q.args_cons in H.
     destruct (ask j "kl:buri.eval" [D; enc_term e; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ _ Se Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite Q.args_first in H.
     destruct w1 as [v|m| |];
       try (match type of H with Some (enc_verdict ?W) = Some ?r => assert (EQ : r = enc_verdict W) by congruence;
         clear H; subst r; exists (AFail W) end; split; [reflexivity|]; split; [exact I|];
         split; [discriminate|]; intros P s HP Hs; first [apply (args_fail1 P s HP Hs); apply G1; assumption|exact I]).
     destruct (ask j "kl:buri.eval-args" _) as [v2|] eqn:E2; [|discriminate].
     destruct (IG j (le_S _ _ (le_n j)) _ _ _ _ _ Ss' Oe E2) as (a2 & -> & O2 & L2 & G2).
     destruct j as [|j]; [discriminate|]. rewrite Q.args_rest in H. injection H as <-.
     destruct a2 as [vs|w2].
     * exists (AVals (v :: vs)); split; [reflexivity|]; split; [constructor; assumption|].
       split; [cbn in L2 |- *; rewrite L2; reflexivity|].
       intros P s HP Hs. apply (args_ret P s HP Hs); [apply G1; assumption|].
       destruct es as [|e2 es2]; [destruct vs; [reflexivity|discriminate L2]|apply G2; assumption].
     * exists (AFail w2); split; [reflexivity|]; split; [exact O2|]; split; [discriminate|].
       intros P s HP Hs. destruct w2 as [x|m| |]; cbn in O2; try contradiction; try exact I.
       destruct es as [|e2 es2]; [contradiction|]. eapply (args_fail2 P s HP Hs); [apply G1; assumption|apply G2; assumption].
Qed.

Lemma all_fuel : forall n i, i <= n -> Seval i /\ Sapply i /\ Sargs i.
Proof.
 induction n as [|n IH]; intros i L.
 - inversion L; subst. repeat split; intros; discriminate.
 - inversion L as [|n' L']; subst; [apply step_all; exact IH|apply IH; exact L'].
Qed.

(* ---------- the E2E-07 refinement theorems ---------- *)
(* A closed run: no environment events, no IO (KL-PURE-1 has none). *)
Definition env_none (_ : unit) (_ : request) : response * unit := (RClosed, tt).
Definition quiet (_ : unit) : option env_event := None.
Definition still (w : unit) : unit := w.
Definition krun (P : profile) := KLMetatheory.KLMetatheory.run unit env_none quiet still P.
Lemma taus_star : forall P c c', taus P c c' ->
 star (KLMetatheory.KLMetatheory.rstep unit env_none quiet still P) (c, tt) [] (c', tt).
Proof.
 intros P c c' T; induction T as [c|c c1 c2 N T IH]; [constructor|].
 change (@nil event) with (trace_of Tau ++ [])%list. eapply star_step; [|exact IH].
 apply KLMetatheory.KLMetatheory.cs_tau; [reflexivity|exact N].
Qed.
Lemma taus_run : forall P c c' o, taus P c c' -> next P c' = MFinal o -> exists m, krun P m c tt = VDone [] o.
Proof.
 intros P c c' o T F. apply KLMetatheory.KLMetatheory.run_complete.
 econstructor; [apply taus_star; exact T|exact F].
Qed.

(* E2E-07, KL-PURE-1 subset. For every program term in the proved construct
   subset, every definition table D, every budget z and every fuel n of the
   actual Native evaluator running the captured klambda.shen program: if the
   captured buri.eval returns r, then r is the encoding of an evaluator
   verdict w, and under every pinned profile and primitive store the KLambda
   machine run from the translated program agrees: [returned v] is a normal
   result tr_rv v, [raised m] is an exception of the stated class for m, both
   found by KLMetatheory.run with enough fuel; [unknown evaluation-budget] and
   [unsupported closure-equality] make no behavior claim (in particular no
   divergence claim). *)
Theorem klambda_refines : forall n D e z r, sub e ->
 Native.Native.run n program "kl:buri.eval" [D; enc_term e; enc_env []; Native.Native.Integer z] = Native.Native.Returned r ->
 exists w, r = enc_verdict w /\ ok_verdict w /\
 forall P s, pure P -> prims s -> match w with
 | WRet v => exists m, krun P m (Cfg (Eval [] (tr e)) [] s) tt = VDone [] (Normal (tr_rv v))
 | WRaise msg => exists x m, exn_class msg x /\ krun P m (Cfg (Eval [] (tr e)) [] s) tt = VDone [] (Error x)
 | WBudget | WUnsupported => True end.
Proof.
 intros n D e z r Se H. apply native_run_ask in H.
 destruct (all_fuel (S n) (S n) (le_n _)) as [SE _].
 destruct (SE D e [] z r Se (Forall_nil _) H) as (w & -> & O & G).
 exists w; split; [reflexivity|split; [exact O|]]. intros P s HP Hs.
 pose proof (G P s HP Hs []) as R. destruct w as [v|m| |]; cbn in R; try exact I.
 - eapply taus_run; [exact R|reflexivity].
 - destruct R as (x & C & T). destruct (taus_run P _ _ (Error x) T eq_refl) as [k K]. eauto.
Qed.

(* A decided verdict is a terminating KLambda behavior, which therefore cannot
   also diverge (closed determinism, KLMetatheory). Exhaustion stays silent. *)
Definition kbehaves (P : profile) (c : config) (b : behavior value exn) :=
 behaves (KLMetatheory.KLMetatheory.rstep unit env_none quiet still P)
   (KLMetatheory.KLMetatheory.cfinal unit P) (c, tt) b.
Lemma env_none_deterministic :
 KLMetatheory.KLMetatheory.oracle_deterministic unit (KLMetatheory.KLMetatheory.graph unit env_none).
Proof.
 intros w q r1 w1 r2 w2 A B. unfold KLMetatheory.KLMetatheory.graph in *.
 rewrite A in B; injection B as -> ->; split; reflexivity.
Qed.
Theorem klambda_decided_terminates : forall n D e z r, sub e ->
 Native.Native.run n program "kl:buri.eval" [D; enc_term e; enc_env []; Native.Native.Integer z] = Native.Native.Returned r ->
 exists w, r = enc_verdict w /\ forall P s, pure P -> prims s -> match w with
 | WRet v => kbehaves P (Cfg (Eval [] (tr e)) [] s) (Terminates [] (Normal (tr_rv v))) /\
     forall t, ~ kbehaves P (Cfg (Eval [] (tr e)) [] s) (Diverges t)
 | WRaise msg => exists x, exn_class msg x /\ kbehaves P (Cfg (Eval [] (tr e)) [] s) (Terminates [] (Error x)) /\
     forall t, ~ kbehaves P (Cfg (Eval [] (tr e)) [] s) (Diverges t)
 | WBudget | WUnsupported => True end.
Proof.
 intros n D e z r Se H. apply native_run_ask in H.
 destruct (all_fuel (S n) (S n) (le_n _)) as [SE _].
 destruct (SE D e [] z r Se (Forall_nil _) H) as (w & -> & _ & G).
 exists w; split; [reflexivity|]. intros P s HP Hs.
 pose proof (G P s HP Hs []) as R. destruct w as [v|m| |]; cbn in R; try exact I.
 - assert (B : kbehaves P (Cfg (Eval [] (tr e)) [] s) (Terminates [] (Normal (tr_rv v))))
     by (econstructor; [apply taus_star; exact R|reflexivity]).
   split; [exact B|]. intros t.
   exact (KLMetatheory.KLMetatheory.closed_terminates_excludes_divergence unit _ quiet still P
     env_none_deterministic _ tt [] _ t B).
 - destruct R as (x & C & T). exists x; split; [exact C|].
   assert (B : kbehaves P (Cfg (Eval [] (tr e)) [] s) (Terminates [] (Error x)))
     by (econstructor; [apply taus_star; exact T|reflexivity]).
   split; [exact B|]. intros t.
   exact (KLMetatheory.KLMetatheory.closed_terminates_excludes_divergence unit _ quiet still P
     env_none_deterministic _ tt [] _ t B).
Qed.

(* The same, for the captured buri.eval at any oracle fuel and in any
   lexical environment of related values (the compositional form). *)
Theorem klambda_refines_open : forall k D e env z r, sub e -> okenv env ->
 ask k "kl:buri.eval" [D; enc_term e; enc_env env; Native.Native.Integer z] = Some r ->
 exists w, r = enc_verdict w /\ ok_verdict w /\
 forall P s kont, pure P -> prims s -> reaches P (Cfg (Eval (tr_env env) (tr e)) kont s) w kont s.
Proof.
 intros k D e env z r Se Oe H. destruct (all_fuel k k (le_n _)) as [SE _].
 destruct (SE D e env z r Se Oe H) as (w & -> & O & G).
 exists w; split; [reflexivity|split; [exact O|]]. intros P s kont HP Hs. apply (G P s HP Hs kont).
Qed.

(* buri.evaluate: its captured body is a Chez guard whose handler is the
   literal [unknown host-error] and whose body admits the program and calls
   buri.eval with the empty environment. Native has no guard, so the guard is a
   stated contract (when the body returns a value, guard returns it); the
   theorem below is about the body, and [unknown host-error] has no KLambda
   counterpart: it can only come from the handler. *)
Definition guard_handler := Native.Native.Call "Z6107" [Native.Native.Call "else" [Native.Native.Call "list"
 [Native.Native.Lit (Native.Native.Symbol "unknown"); Native.Native.Lit (Native.Native.Symbol "host-error")]]].
Definition rejected := Native.Native.L [Native.Native.Symbol "rejected"; Native.Native.Symbol "unsupported-or-malformed-program"].
Theorem evaluate_shape : exists admit,
 Native.Native.params d_evaluate = ["V6104"; "V6105"; "V6106"] /\
 Native.Native.body d_evaluate = Native.Native.Call "guard" [guard_handler;
   Native.Native.If admit
     (Native.Native.Call "kl:buri.eval" [Native.Native.Var "V6104"; Native.Native.Var "V6105";
        Native.Native.Lit Native.Native.Nil; Native.Native.Var "V6106"])
     (Native.Native.Call "list" [Native.Native.Lit (Native.Native.Symbol "rejected");
        Native.Native.Lit (Native.Native.Symbol "unsupported-or-malformed-program")])].
Proof. eexists; split; vm_compute; reflexivity. Qed.
Theorem evaluate_body_refines : forall k admit D e z r, sub e ->
 O.step defined (ask k) (Native.Native.arguments ["V6104"; "V6105"; "V6106"] [D; enc_term e; Native.Native.Integer z])
   (Native.Native.If admit
     (Native.Native.Call "kl:buri.eval" [Native.Native.Var "V6104"; Native.Native.Var "V6105";
        Native.Native.Lit Native.Native.Nil; Native.Native.Var "V6106"])
     (Native.Native.Call "list" [Native.Native.Lit (Native.Native.Symbol "rejected");
        Native.Native.Lit (Native.Native.Symbol "unsupported-or-malformed-program")])) = Some r ->
 r = rejected \/ exists w, r = enc_verdict w /\ ok_verdict w /\
   forall P s kont, pure P -> prims s -> reaches P (Cfg (Eval [] (tr e)) kont s) w kont s.
Proof.
 intros k admit D e z r Se H. apply O.inv_if in H. destruct H as (x & _ & H).
 destruct x as [| | | | | | [|] | | |]; cbn in H;
   try (right; eapply (klambda_refines_open k D e [] z r Se (Forall_nil _)); exact H).
 left. injection H as <-. reflexivity.
Qed.
End KLambdaEvaluatorRefinement.
