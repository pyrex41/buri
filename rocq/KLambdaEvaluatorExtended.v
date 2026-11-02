(* E2E-07, extended subset: the captured shen/klambda.shen evaluator refines the
   Wave-A KLambda semantics (KLSemantics/KLMetatheory) on every BURI/KL-PURE-1
   construct: literals, variables, [global X], lambda, one-argument
   application of closures, [function ...] values (currying through
   buri.apply-global) and thunks, let, if, saturated primitives
   (+ - * < = cons hd tl cons? number? string?), raise, trap, freeze and thaw.
   The definition table is the evaluator's own list (KLambdaEvaluatorGlobal);
   the KLambda store holds its translation in the global function namespace
   (defs). Equality of two function values is undefined in the agreed profile:
   the evaluator answers [unsupported closure-equality] exactly when the
   KLambda machine goes wrong at that call (reaches2 WUnsupported).
   KLambdaEvaluatorRefinement keeps the earlier, definition-table-free
   theorems for the pure subset. *)
From Coq Require Import List String ZArith NArith Bool Lia Ascii.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLMetatheory Native
 KLambdaEvaluatorCapture KLambdaEvaluatorEquations KLambdaEvaluatorPrimitives
 KLambdaEvaluatorRefinement KLambdaEvaluatorGlobal.
Import ListNotations.
Module KLambdaEvaluatorExtended.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics.
Module C := KLambdaEvaluatorCapture.KLambdaEvaluatorCapture.
Module Pr := KLambdaEvaluatorPrimitives.KLambdaEvaluatorPrimitives.
Module Q := KLambdaEvaluatorEquations.KLambdaEvaluatorEquations.
Module R := KLambdaEvaluatorRefinement.KLambdaEvaluatorRefinement.
Module G := KLambdaEvaluatorGlobal.KLambdaEvaluatorGlobal.
Import C.
Open Scope string_scope.

(* ---------- the extended subset and value invariant ---------- *)
Fixpoint sub2 (e : term) : Prop := match e with
 | TLit d => Pr.data d
 | TVar _ | TGlobal _ => True
 | TLambda _ b => sub2 b
 | TApply f a => sub2 f /\ sub2 a
 | TLet _ a b => sub2 a /\ sub2 b
 | TIf c a b => sub2 c /\ sub2 a /\ sub2 b
 | TPrim op args => R.prim_ok op (List.length args) /\ fold_right (fun a acc => sub2 a /\ acc) True args
 | TRaise e => sub2 e
 | TTrap e h => sub2 e /\ sub2 h
 | TFreeze e | TThaw e => sub2 e end.
(* Well-formed definitions: positive arity (buri.definitions? rejects []) and
   bodies in the subset. Repeated names are harmless: both sides take the
   first binding. *)
Definition ds_ok (ds : list G.defn) : Prop :=
 Forall (fun d => match d with (_, ps, b) => ps <> [] /\ sub2 b end) ds.
Lemma find_def_ok : forall ds x ps b, ds_ok ds -> G.find_def x ds = Some (ps, b) -> ps <> [] /\ sub2 b.
Proof.
 induction ds as [|[[n ps0] b0] ds IH]; intros x ps b O F; [discriminate|].
 inversion O as [|? ? H0 O']; subst. cbn in F. destruct (String.eqb x n); [injection F as <- <-; exact H0|eauto].
Qed.
Section Values.
Variable ds : list G.defn.
Fixpoint ok2 (v : rv) : Prop := match v with
 | RPair a d => ok2 a /\ ok2 d
 | RClosure _ e env | RThunk e env => sub2 e /\ fold_right (fun p acc => ok2 (snd p) /\ acc) True env
 | RFunction f args => (exists ps b, G.find_def f ds = Some (ps, b) /\ List.length args < List.length ps) /\
     fold_right (fun a acc => ok2 a /\ acc) True args
 | _ => True end.
Definition okenv2 (env : list (string * rv)) := Forall (fun p => ok2 (snd p)) env.
Lemma okenv2_fold : forall env, fold_right (fun p acc => ok2 (snd p) /\ acc) True env <-> okenv2 env.
Proof. unfold okenv2; induction env as [|p env IH]; cbn; [split; auto|]. rewrite Forall_cons_iff, <- IH. reflexivity. Qed.
Lemma oklist_fold : forall vs, fold_right (fun a acc => ok2 a /\ acc) True vs <-> Forall ok2 vs.
Proof. induction vs as [|v vs IH]; cbn; [split; auto|]. rewrite Forall_cons_iff, <- IH. reflexivity. Qed.
Lemma data_ok2 : forall d, Pr.data d -> ok2 d.
Proof. induction d; cbn; intuition. Qed.
Lemma assoc_ok2 : forall x env v, okenv2 env -> assoc x env = Some v -> ok2 v.
Proof.
 unfold okenv2; induction env as [|[y w] env IH]; cbn; intros v O E; [discriminate|].
 inversion O; subst. destruct (String.eqb x y); [injection E as <-; assumption|eauto].
Qed.
Lemma combine_ok2 : forall ps vs, Forall ok2 vs -> okenv2 (combine ps vs).
Proof.
 unfold okenv2; induction ps as [|p ps IH]; intros [|v vs] O; cbn; try constructor;
 inversion O; subst; [assumption|apply IH; assumption].
Qed.
End Values.
Lemma sub2_fold : forall es, fold_right (fun a acc => sub2 a /\ acc) True es <-> Forall sub2 es.
Proof. induction es as [|e es IH]; cbn; [split; auto|]. rewrite Forall_cons_iff, <- IH. reflexivity. Qed.

(* ---------- profile, exception classes, store ---------- *)
(* The extended profile pins two more system messages. *)
Definition pure2 (P : profile) : Prop := R.pure P /\ sys_message P XArity = of_string "arity" /\
 (forall y, sys_message P (XUndefinedFun y) = of_string "unbound-function").
Definition exn2 (m : string) (x : exn) : Prop := R.exn_class m x \/ (m = "arity" /\ x = XArity) \/
 (m = "unbound-function" /\ exists y, x = XUndefinedFun y).
Lemma class_text2 : forall P m x, pure2 P -> exn2 m x -> R.error_text P x = of_string m.
Proof.
 intros P m x (HP & A & U) [Cl|[[-> ->]|[-> [y ->]]]]; [exact (R.class_text P m x HP Cl)|exact A|apply U].
Qed.
(* The global function namespace holds the translated definition table under
   the user: names (first binding wins, as in buri.definition). *)
Definition tr_fundef (o : option (list string * term)) : option fundef := match o with
 | Some (ps, b) => Some (FUser (map of_string ps) (R.tr b)) | None => None end.
Definition defs (s : store) (ds : list G.defn) : Prop :=
 forall x, lookup (R.fname x) (gfuns s) = tr_fundef (G.find_def x ds).

(* The premises are satisfiable, for every definition table. *)
Definition pure2_profile : profile := Profile
 (fun _ _ _ => None) (fun _ _ _ => false) (fun _ _ => NInt 0) (fun _ => []) (fun _ => None)
 (fun x => match x with
   | XNotBoolean => of_string "nonboolean-condition" | XNotCallable => of_string "not-callable"
   | XUnboundVar _ => of_string "unbound-variable"
   | XPrim PSimpleError => of_string "error-message-not-string"
   | XPrim _ => of_string "primitive-domain-or-arity"
   | XArity => of_string "arity" | XUndefinedFun _ => of_string "unbound-function" | _ => [] end)
 VNil (fun _ _ => None) None None.
Theorem pure2_profile_ok : pure2 pure2_profile.
Proof.
 split; [|split; [reflexivity|intro; reflexivity]].
 unfold R.pure; cbn; repeat split; try reflexivity. intros p N; destruct p; try reflexivity; contradiction.
Qed.
Definition user_entry (d : G.defn) : name * fundef := match d with
 (n, ps, b) => (R.fname n, FUser (map of_string ps) (R.tr b)) end.
Definition defs_store (ds : list G.defn) : store :=
 Store [] [] (map user_entry ds ++ map (fun p => (of_string (fst p), FPrim (snd p))) R.prim_table).
Lemma fname_eqb : forall x y, text_eqb (R.fname x) (R.fname y) = String.eqb x y.
Proof. intros x y. unfold R.fname. rewrite R.text_eqb_of_string. reflexivity. Qed.
Lemma fname_prim : forall x op p, In (op, p) R.prim_table -> text_eqb (of_string op) (R.fname x) = false.
Proof.
 intros x op p I. unfold R.fname. rewrite R.text_eqb_of_string.
 cbn in I; repeat (destruct I as [I|I]; [injection I as <- <-; reflexivity|]); contradiction.
Qed.
Lemma lookup_app : forall {A} x (l1 l2 : list (name * A)),
 lookup x (l1 ++ l2) = match lookup x l1 with Some v => Some v | None => lookup x l2 end.
Proof. intros A x l1 l2; induction l1 as [|[y v] l1 IH]; cbn; [reflexivity|]. destruct (text_eqb x y); auto. Qed.
Theorem defs_store_ok : forall ds, R.prims (defs_store ds) /\ defs (defs_store ds) ds.
Proof.
 intro ds. split.
 - intros op p I. cbn [gfuns defs_store]. rewrite lookup_app.
   replace (lookup (of_string op) (map user_entry ds)) with (@None fundef).
   + pose proof R.prim_store_ok as PS. exact (PS op p I).
   + induction ds as [|[[n ps] b] ds IH]; [reflexivity|]. cbn [map user_entry lookup].
     rewrite (fname_prim n op p I). exact IH.
 - intro x. cbn [gfuns defs_store]. rewrite lookup_app. induction ds as [|[[n ps] b] ds IH].
   + cbn [map lookup G.find_def tr_fundef List.app].
     assert (N : forall l : list (string * prim), Forall (fun q => In q R.prim_table) l ->
       lookup (R.fname x) (map (fun p => (of_string (fst p), FPrim (snd p))) l) = None).
     { induction l as [|[op p] l IHl]; intro F; [reflexivity|]. inversion F as [|? ? I F']; subst.
       cbn [map lookup fst snd]. pose proof (fname_prim x op p I) as E.
       destruct (text_eqb (R.fname x) (of_string op)) eqn:E'; [|apply IHl; exact F'].
       apply text_eqb_eq in E'. rewrite E', text_eqb_refl in E. discriminate. }
     apply N. apply Forall_forall; intros q Iq; exact Iq.
   + cbn [map user_entry lookup G.find_def]. rewrite fname_eqb. destruct (String.eqb x n); [reflexivity|exact IH].
Qed.

(* ---------- verdict correspondence ---------- *)
(* [unsupported closure-equality] corresponds to the KLambda machine going
   wrong (rule_equal: equality of two function values is undefined). *)
Definition reaches2 (P : profile) (s : store) (c : config) (w : verdict) (k : list frame) : Prop :=
 match w with
 | WRet v => R.taus P c (Cfg (Ret (R.tr_rv v)) k s)
 | WRaise m => exists x, exn2 m x /\ R.taus P c (Cfg (Throw x) k s)
 | WUnsupported => exists k' s', R.taus P c (Cfg (Wrong (kw "equality-undefined")) k' s')
 | WBudget => True end.
Definition notret := R.notret.

Lemma tr_env_combine : forall ps vs, R.tr_env (combine ps vs) = combine (map of_string ps) (map R.tr_rv vs).
Proof. induction ps as [|p ps IH]; intros [|v vs]; cbn; try reflexivity. f_equal; apply IH. Qed.

Set Default Proof Using "All".
Section Machine.
Variables (P : profile) (s : store) (ds : list G.defn).
Hypotheses (HP : pure2 P) (Hs : R.prims s) (Hd : defs s ds).
Lemma Hst : stack_limit P = None. Proof. exact (proj1 (proj1 HP)). Qed.
Ltac nx := cbn -[of_string kw lookup R.tr_env kl_eq]; unfold push, continue_with; rewrite ?Hst; cbn -[of_string kw lookup R.tr_env kl_eq].
Ltac tau := eapply R.t_step; [nx; reflexivity|].
Definition call_prim := R.call_prim P s (proj1 HP) Hs.

Lemma reaches_step : forall c c' w k, next P c = MTau c' -> reaches2 P s c' w k -> reaches2 P s c w k.
Proof.
 intros c c' [v|m| |] k N Rc; cbn in *; auto.
 - econstructor; eauto.
 - destruct Rc as (x & Cl & T); exists x; split; [exact Cl|econstructor; eauto].
 - destruct Rc as (k' & s' & T); exists k', s'; econstructor; eauto.
Qed.
Lemma reaches_taus : forall c c' w k, R.taus P c c' -> reaches2 P s c' w k -> reaches2 P s c w k.
Proof. intros c c' w k T; induction T; intro Rc; [exact Rc|eapply reaches_step; eauto]. Qed.
Lemma reaches_ret : forall c v (f : frame) (k1 k : list frame) c' w, reaches2 P s c (WRet v) (f :: k1) ->
 next P (Cfg (Ret (R.tr_rv v)) (f :: k1) s) = MTau c' -> reaches2 P s c' w k -> reaches2 P s c w k.
Proof. intros c v f k1 k c' w T N Rc. eapply reaches_taus; [exact T|]. eapply reaches_step; eauto. Qed.
Lemma reaches_fail : forall c w (f : frame) (k : list frame), notret w -> (forall h rho, f <> KTrap h rho) ->
 reaches2 P s c w (f :: k) -> reaches2 P s c w k.
Proof.
 intros c [v|m| |] f k NR NT Rc; cbn in *; try contradiction; auto.
 destruct Rc as (x & Cl & T); exists x; split; [exact Cl|].
 eapply R.taus_trans; [exact T|]. econstructor; [|constructor].
 destruct f; cbn; try reflexivity. exfalso; eapply NT; reflexivity.
Qed.
Lemma reaches_any : forall c w k k', (w = WBudget \/ w = WUnsupported) -> reaches2 P s c w k -> reaches2 P s c w k'.
Proof. intros c w k k' [->| ->] Rc; exact Rc. Qed.
Lemma raise_here : forall m x k, exn2 m x -> reaches2 P s (Cfg (Throw x) k s) (WRaise m) k.
Proof. intros; exists x; split; [assumption|constructor]. Qed.

Definition ev (e : term) (env : list (string * rv)) (w : verdict) : Prop :=
 forall k, reaches2 P s (Cfg (Eval (R.tr_env env) (R.tr e)) k s) w k.
Definition ap (f a : rv) (w : verdict) : Prop := forall k, match w with
 | WBudget => True
 | _ => exists c, apply_value P (R.tr_rv f) [R.tr_rv a] k s = MTau c /\ reaches2 P s c w k end.
Definition th (f : rv) (w : verdict) : Prop := forall k, match w with
 | WBudget => True
 | _ => exists c, apply_value P (R.tr_rv f) [] k s = MTau c /\ reaches2 P s c w k end.
Definition argsr (es : list term) (env : list (string * rv)) (a : args_verdict) : Prop :=
 match a with
 | AVals vs => forall k f done e1 es', es = e1 :: es' ->
   exists c, R.taus P (Cfg (Eval (R.tr_env env) (R.tr e1)) (KCallArgs f done (map R.tr es') (R.tr_env env) :: k) s) c /\
     next P c = call_named P f (rev done ++ map R.tr_rv vs) k s
 | AFail w => notret w /\ forall k f done e1 es', es = e1 :: es' ->
   reaches2 P s (Cfg (Eval (R.tr_env env) (R.tr e1)) (KCallArgs f done (map R.tr es') (R.tr_env env) :: k) s) w k end.
Ltac nf := intros ? ? E; discriminate E.

Lemma m_lit : forall d env, Pr.data d -> ev (TLit d) env (WRet d).
Proof. intros d env D k. exact (R.m_lit P s (proj1 HP) Hs d _ k D). Qed.
Lemma m_var : forall x env,
 ev (TVar x) env (match assoc x env with Some v => WRet v | None => WRaise "unbound-variable" end).
Proof.
 intros x env k. cbn [R.tr]. eapply reaches_step; [nx; rewrite R.lookup_tr; reflexivity|].
 destruct (assoc x env) as [v|]; cbn.
 - constructor.
 - exists (XUnboundVar (of_string x)); split; [left; right; left; eauto|constructor].
Qed.
Lemma m_lambda : forall x b env, ev (TLambda x b) env (WRet (RClosure x b env)).
Proof. intros x b env k. cbn [R.tr reaches2]. tau. constructor. Qed.
Lemma m_freeze : forall e env, ev (TFreeze e) env (WRet (RThunk e env)).
Proof. intros e env k. cbn [R.tr reaches2]. tau. constructor. Qed.
Lemma m_let_ret : forall x a b env v w, ev a env (WRet v) -> ev b ((x, v) :: env) w -> ev (TLet x a b) env w.
Proof.
 intros x a b env v w Ga Gb k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Ga|nx; reflexivity|apply Gb].
Qed.
Lemma m_let_fail : forall x a b env w, notret w -> ev a env w -> ev (TLet x a b) env w.
Proof.
 intros x a b env w N Ga k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_fail; [exact N| |apply Ga]; nf.
Qed.
Lemma m_if_bool : forall c a b env bv w, ev c env (WRet (RBool bv)) -> ev (if bv then a else b) env w ->
 ev (TIf c a b) env w.
Proof.
 intros c a b env bv w Gc Gb k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Gc|nx; reflexivity|]. destruct bv; apply Gb.
Qed.
Lemma m_if_nonbool : forall c a b env v, (forall bv, v <> RBool bv) -> ev c env (WRet v) ->
 ev (TIf c a b) env (WRaise "nonboolean-condition").
Proof.
 intros c a b env v NB Gc k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 destruct v; try (exfalso; eapply NB; reflexivity);
 (eapply reaches_ret; [apply Gc|nx; reflexivity|apply raise_here; left; right; right; left; split; reflexivity]).
Qed.
Lemma m_if_fail : forall c a b env w, notret w -> ev c env w -> ev (TIf c a b) env w.
Proof.
 intros c a b env w N Gc k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_fail; [exact N| |apply Gc]; nf.
Qed.
Lemma m_app_ret : forall f a env fv av w, ev f env (WRet fv) -> ev a env (WRet av) -> ap fv av w ->
 ev (TApply f a) env w.
Proof.
 intros f a env fv av w Gf Ga Ap k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Gf|nx; reflexivity|].
 specialize (Ap k). destruct w; try exact I; destruct Ap as (c & E & Rc);
 (eapply reaches_ret; [apply Ga|cbn [next ctl kont mem ret_move rev List.app]; exact E|exact Rc]).
Qed.
Lemma m_app_fail1 : forall f a env w, notret w -> ev f env w -> ev (TApply f a) env w.
Proof.
 intros f a env w N Gf k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_fail; [exact N| |apply Gf]; nf.
Qed.
Lemma m_app_fail2 : forall f a env fv w, notret w -> ev f env (WRet fv) -> ev a env w -> ev (TApply f a) env w.
Proof.
 intros f a env fv w N Gf Ga k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Gf|nx; reflexivity|]. eapply reaches_fail; [exact N| |apply Ga]; nf.
Qed.
Lemma m_thaw_ret : forall e env v w, ev e env (WRet v) -> th v w -> ev (TThaw e) env w.
Proof.
 intros e env v w Ge Th k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 specialize (Th k). destruct w; try exact I; destruct Th as (c & E & Rc);
 (eapply reaches_ret; [apply Ge|cbn [next ctl kont mem ret_move]; exact E|exact Rc]).
Qed.
Lemma m_thaw_fail : forall e env w, notret w -> ev e env w -> ev (TThaw e) env w.
Proof.
 intros e env w N Ge k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_fail; [exact N| |apply Ge]; nf.
Qed.

(* Application and thawing of each value shape. *)
Lemma ap_closure : forall x e env a w, ev e ((x, a) :: env) w -> ap (RClosure x e env) a w.
Proof.
 intros x e env a w Ge k. destruct w; try exact I;
 (exists (Cfg (Eval (R.tr_env ((x, a) :: env)) (R.tr e)) k s); split; [reflexivity|apply Ge]).
Qed.
Lemma ap_noncallable : forall f a, (forall x e env, f <> RClosure x e env) ->
 (forall g args, f <> RFunction g args) -> (forall e env, f <> RThunk e env) ->
 ap f a (WRaise "not-callable").
Proof.
 intros f a NC NF NT k. destruct f; try (exfalso; eapply NC; reflexivity);
 try (exfalso; eapply NF; reflexivity); try (exfalso; eapply NT; reflexivity);
 (exists (Cfg (Throw XNotCallable) k s); split; [reflexivity|apply raise_here; left; right; right; right; left; split; reflexivity]).
Qed.
Lemma ap_thunk : forall e env a, ap (RThunk e env) a (WRaise "arity").
Proof.
 intros e env a k. exists (Cfg (Throw XArity) k s); split; [reflexivity|].
 apply raise_here; right; left; split; reflexivity.
Qed.
Lemma call_user : forall f ps b args k, G.find_def f ds = Some (ps, b) ->
 call_named P (R.fname f) (map R.tr_rv args) k s =
 if Nat.ltb (List.length args) (List.length ps) then MTau (Cfg (Ret (R.tr_rv (RFunction f args))) k s)
 else MTau (continue_with P (skipn (List.length ps) (map R.tr_rv args)) k
   (Eval (combine (map of_string ps) (firstn (List.length ps) (map R.tr_rv args))) (R.tr b)) s).
Proof.
 intros f ps b args k F. unfold call_named. rewrite (Hd f), F. cbn [tr_fundef].
 rewrite !map_length. reflexivity.
Qed.
Lemma ap_partial : forall f args a ps b, G.find_def f ds = Some (ps, b) ->
 List.length (args ++ [a]) < List.length ps -> ap (RFunction f args) a (WRet (RFunction f (args ++ [a]))).
Proof.
 intros f args a ps b F L k. cbn [R.tr_rv apply_value].
 replace (map R.tr_rv args ++ [R.tr_rv a])%list with (map R.tr_rv (args ++ [a])) by (rewrite map_app; reflexivity).
 rewrite (call_user f ps b _ k F). apply Nat.ltb_lt in L. rewrite L.
 eexists; split; [reflexivity|constructor].
Qed.
Lemma ap_call : forall f args a ps b w, G.find_def f ds = Some (ps, b) ->
 List.length (args ++ [a]) = List.length ps -> ev b (combine ps (args ++ [a])) w ->
 ap (RFunction f args) a w.
Proof.
 intros f args a ps b w F L Gb k. cbn [R.tr_rv apply_value].
 replace (map R.tr_rv args ++ [R.tr_rv a])%list with (map R.tr_rv (args ++ [a])) by (rewrite map_app; reflexivity).
 rewrite (call_user f ps b _ k F). rewrite <- L, Nat.ltb_irrefl.
 rewrite <- (map_length R.tr_rv (args ++ [a])), skipn_all, firstn_all.
 cbn [continue_with]. rewrite <- tr_env_combine.
 destruct w; try exact I; (eexists; split; [reflexivity|apply Gb]).
Qed.
Lemma th_frozen : forall e env w, ev e env w -> th (RThunk e env) w.
Proof.
 intros e env w Ge k. destruct w; try exact I;
 (exists (Cfg (Eval (R.tr_env env) (R.tr e)) k s); split; [reflexivity|apply Ge]).
Qed.
Lemma th_closure : forall x e env, th (RClosure x e env) (WRaise "arity").
Proof.
 intros x e env k. exists (Cfg (Throw XArity) k s); split; [reflexivity|].
 apply raise_here; right; left; split; reflexivity.
Qed.
Lemma th_partial : forall f args ps b, G.find_def f ds = Some (ps, b) ->
 List.length args < List.length ps -> th (RFunction f args) (WRet (RFunction f args)).
Proof.
 intros f args ps b F L k. cbn [R.tr_rv apply_value]. rewrite app_nil_r.
 rewrite (call_user f ps b _ k F). apply Nat.ltb_lt in L. rewrite L.
 eexists; split; [reflexivity|constructor].
Qed.
Lemma th_noncallable : forall f, (forall x e env, f <> RClosure x e env) ->
 (forall g args, f <> RFunction g args) -> (forall e env, f <> RThunk e env) ->
 th f (WRaise "not-callable").
Proof.
 intros f NC NF NT k. destruct f; try (exfalso; eapply NC; reflexivity);
 try (exfalso; eapply NF; reflexivity); try (exfalso; eapply NT; reflexivity);
 (exists (Cfg (Throw XNotCallable) k s); split; [reflexivity|apply raise_here; left; right; right; right; left; split; reflexivity]).
Qed.
(* [global X]: a defined name is its (unapplied) partial application. *)
Lemma m_global_found : forall x env ps b, G.find_def x ds = Some (ps, b) -> ps <> [] ->
 ev (TGlobal x) env (WRet (RFunction x [])).
Proof.
 intros x env ps b F NE k. cbn [R.tr]. eapply R.t_step; [|constructor].
 cbn [next ctl kont mem eval_move]. pose proof (call_user x ps b [] k F) as Cu. cbn [map] in Cu. rewrite Cu.
 destruct ps; [contradiction|reflexivity].
Qed.
Lemma m_global_missing : forall x env, G.find_def x ds = None -> ev (TGlobal x) env (WRaise "unbound-function").
Proof.
 intros x env F k. cbn [R.tr]. eapply reaches_step.
 - cbn [next ctl kont mem eval_move]. unfold call_named. rewrite (Hd x), F. reflexivity.
 - apply raise_here; right; right; split; [reflexivity|eauto].
Qed.

Lemma m_raise_str : forall e env t, ev e env (WRet (RStr t)) -> ev (TRaise e) env (WRaise t).
Proof.
 intros e env t Ge k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Ge| |apply raise_here; left; left; reflexivity].
 nx. rewrite (call_prim "simple-error" PSimpleError) by (cbn; first [tauto|reflexivity]). reflexivity.
Qed.
Lemma m_raise_nonstr : forall e env v, (forall t, v <> RStr t) -> ev e env (WRet v) ->
 ev (TRaise e) env (WRaise "error-message-not-string").
Proof.
 intros e env v NS Ge k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Ge| |apply raise_here; left; right; right; right; right; left; split; reflexivity].
 nx. rewrite (call_prim "simple-error" PSimpleError) by (cbn; first [tauto|reflexivity]).
 destruct v; try (exfalso; eapply NS; reflexivity); reflexivity.
Qed.
Lemma m_raise_fail : forall e env w, notret w -> ev e env w -> ev (TRaise e) env w.
Proof.
 intros e env w N Ge k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_fail; [exact N| |apply Ge]; nf.
Qed.
Lemma m_trap_ret : forall e h env v, ev e env (WRet v) -> ev (TTrap e h) env (WRet v).
Proof.
 intros e h env v Ge k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_ret; [apply Ge|nx; reflexivity|constructor].
Qed.
Lemma m_trap_other : forall e h env w, (w = WBudget \/ w = WUnsupported) -> ev e env w -> ev (TTrap e h) env w.
Proof.
 intros e h env w O Ge k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 eapply reaches_any; [exact O|apply Ge].
Qed.
Ltac steps := repeat (eapply reaches_step; [nx; first [
 (cbn [lookup]; rewrite ?R.text_eqb_of_string; cbn -[R.tr_env of_string kl_eq]; reflexivity) |
 rewrite (call_prim "error-to-string" PErrorToString) by (cbn; first [tauto|reflexivity]); reflexivity | reflexivity]|]).
Lemma m_trap_raise_ret : forall e h env m hv w, ev e env (WRaise m) -> ev h env (WRet hv) ->
 ap hv (RStr m) w -> ev (TTrap e h) env w.
Proof.
 intros e h env m hv w Ge Gh Ap k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 specialize (Ap k). destruct w; try exact I; destruct Ap as (c & E & Rc);
 destruct (Ge (KTrap (R.handler (R.tr h)) (R.tr_env env) :: k)) as (x & Cl & T);
 pose proof (class_text2 P m x HP Cl) as Tx; destruct x; cbn in Tx;
 (eapply reaches_taus; [exact T|]); unfold R.handler; steps;
 (eapply reaches_ret; [apply Gh|nx; reflexivity|]); steps;
 (eapply reaches_step; [|exact Rc]); cbn [next ctl kont mem ret_move rev List.app];
 cbn [R.tr_rv] in E; rewrite <- Tx in E; exact E.
Qed.
Lemma m_trap_raise_fail : forall e h env m w, notret w -> ev e env (WRaise m) -> ev h env w ->
 ev (TTrap e h) env w.
Proof.
 intros e h env m w N Ge Gh k. cbn [R.tr]. eapply reaches_step; [nx; reflexivity|].
 destruct (Ge (KTrap (R.handler (R.tr h)) (R.tr_env env) :: k)) as (x & Cl & T).
 eapply reaches_taus; [exact T|].
 eapply reaches_step; [nx; reflexivity|]. unfold R.handler.
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
 - subst vs. exists (Cfg (Ret (R.tr_rv v)) (KCallArgs f done [] (R.tr_env env) :: k) s). split; [apply G1|].
   cbn [next ctl kont mem ret_move map rev]. reflexivity.
 - destruct (Gs k f (R.tr_rv v :: done) e2 es2 eq_refl) as (c & T & N).
   exists c; split.
   + eapply R.taus_trans; [apply G1|]. eapply R.t_step; [cbn [next ctl kont mem ret_move map]; reflexivity|exact T].
   + rewrite N. cbn [rev map]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma args_fail1 : forall e1 es env w, notret w -> ev e1 env w -> argsr (e1 :: es) env (AFail w).
Proof.
 intros e1 es env w N G1. split; [exact N|]. intros k f done e es' E; injection E as <- <-.
 eapply reaches_fail; [exact N| |apply G1]; nf.
Qed.
Lemma args_fail2 : forall e1 e2 es env v w, ev e1 env (WRet v) -> argsr (e2 :: es) env (AFail w) ->
 argsr (e1 :: e2 :: es) env (AFail w).
Proof.
 intros e1 e2 es env v w G1 [N Gs]. split; [exact N|]. intros k f done e es' E; injection E as <- <-.
 eapply reaches_taus; [apply (G1 (KCallArgs f done (map R.tr (e2 :: es)) (R.tr_env env) :: k))|].
 eapply reaches_step; [cbn [next ctl kont mem ret_move map]; reflexivity|].
 exact (Gs k f (R.tr_rv v :: done) e2 es eq_refl).
Qed.
Lemma m_prim_vals : forall op es env vs w, es <> [] -> argsr es env (AVals vs) ->
 (forall k, exists c, call_named P (of_string op) (map R.tr_rv vs) k s = MTau c /\ reaches2 P s c w k) ->
 ev (TPrim op es) env w.
Proof.
 intros op [|e1 es] env vs w NE Ga Pm k; [contradiction|]. cbn [R.tr map].
 eapply reaches_step; [nx; reflexivity|].
 destruct (Ga k (of_string op) [] e1 es eq_refl) as (c & T & N). destruct (Pm k) as (c' & E & Rc).
 eapply reaches_taus; [exact T|]. eapply reaches_step; [|exact Rc]. rewrite N. exact E.
Qed.
Lemma m_prim_fail : forall op es env w, es <> [] -> argsr es env (AFail w) -> ev (TPrim op es) env w.
Proof.
 intros op [|e1 es] env w NE [N Ga] k; [contradiction|]. cbn [R.tr map].
 eapply reaches_step; [nx; reflexivity|]. exact (Ga k (of_string op) [] e1 es eq_refl).
Qed.
Lemma kl_prim2 : forall op p vs k, In op ["+"; "-"; "*"; "<"; "cons"; "hd"; "tl"; "cons?"; "number?"; "string?"] ->
 R.prim_of op = Some p -> List.length vs = prim_arity p ->
 exists c, call_named P (of_string op) (map R.tr_rv vs) k s = MTau c /\ reaches2 P s c (Pr.prim_spec op vs) k.
Proof.
 intros op p vs k I O L. destruct (R.kl_prim P s (proj1 HP) Hs op p vs k I O L) as (c & E & Rc).
 exists c; split; [exact E|]. unfold R.reaches in Rc.
 destruct (Pr.prim_spec op vs) as [v|m| |] eqn:Sp;
 [exact Rc|destruct Rc as (x & Cl & T); exists x; split; [left; exact Cl|exact T]|exact Rc|];
 exfalso; clear -Sp I; cbn [In] in I; repeat (destruct I as [<-|I]; [|]); try contradiction;
 destruct vs as [|a [|b [|c vs]]]; try destruct a; try destruct b; discriminate Sp.
Qed.
Lemma kl_prim_equal2 : forall a b k,
 exists c, call_named P (of_string "=") (map R.tr_rv [a; b]) k s = MTau c /\ reaches2 P s c (Pr.eq_spec a b) k.
Proof.
 intros a b k. rewrite (call_prim "=" PEqual) by (cbn; first [tauto|reflexivity]).
 unfold prim_move; cbn [prim_rule map]. unfold rule_equal. rewrite (R.kl_eq_tr P s (proj1 HP) Hs a b (heap s)).
 unfold Pr.eq_spec. destruct (Pr.eqv a b) as [x|]; (eexists; split; [reflexivity|]).
 - constructor.
 - exists k, s; constructor.
Qed.
End Machine.

(* ---------- the refinement induction (over oracle fuel) ---------- *)
Section Induction.
Variable ds : list G.defn.
Hypothesis Hds : ds_ok ds.
Let D := G.enc_defs ds.
Definition Gd e env w := forall P s, pure2 P -> R.prims s -> defs s ds -> ev P s e env w.
Definition Ga f a w := forall P s, pure2 P -> R.prims s -> defs s ds -> ap P s f a w.
Definition Gargs es env a := forall P s, pure2 P -> R.prims s -> defs s ds -> argsr P s es env a.
Definition okv (w : verdict) := match w with WRet v => ok2 ds v | _ => True end.
Definition oka (a : args_verdict) := match a with AVals vs => Forall (ok2 ds) vs | AFail w => notret w end.
Definition Seval k := forall e env z r, sub2 e -> okenv2 ds env ->
 ask k "kl:buri.eval" [D; enc_term e; enc_env env; Native.Native.Integer z] = Some r ->
 exists w, r = enc_verdict w /\ okv w /\ Gd e env w.
Definition Sapply k := forall f a z r, ok2 ds f -> ok2 ds a ->
 ask k "kl:buri.apply-value" [D; enc f; enc a; Native.Native.Integer z] = Some r ->
 exists w, r = enc_verdict w /\ okv w /\ Ga f a w.
Definition Sargs k := forall es env z r, Forall sub2 es -> okenv2 ds env ->
 ask k "kl:buri.eval-args" [D; Native.Native.L (map enc_term es); enc_env env; Native.Native.Integer z] = Some r ->
 exists a, r = enc_args a /\ oka a /\ R.len_args es a /\ Gargs es env a.

Lemma prim_spec_ok2 : forall op vs, Forall (ok2 ds) vs ->
 In op ["+"; "-"; "*"; "<"; "cons"; "hd"; "tl"; "cons?"; "number?"; "string?"] -> okv (Pr.prim_spec op vs).
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
 [ret H; repeat split; intros ? ? ? ? ? ?; exact I|].
Ltac fails G1 := split; [exact I|]; intros P s HP Hs Hd0.
Lemma defn_found : forall f, (exists ps b, G.find_def f ds = Some (ps, b)) ->
 forall j v, ask j "kl:buri.definition" [Native.Native.Symbol f; D] = Some v ->
 exists ps b, G.find_def f ds = Some (ps, b) /\ v = G.enc_found (Some (ps, b)).
Proof.
 intros f (ps & b & F) j v E. apply G.ask_definition in E. rewrite F in E. eauto.
Qed.

Lemma step_all : forall j, (forall i, i <= j -> Seval i /\ Sapply i /\ Sargs i) ->
 Seval (S j) /\ Sapply (S j) /\ Sargs (S j).
Proof.
 intros j IH. assert (IE : forall i, i <= j -> Seval i) by (intros i L; apply (IH i L)).
 assert (IA : forall i, i <= j -> Sapply i) by (intros i L; apply (IH i L)).
 assert (IG : forall i, i <= j -> Sargs i) by (intros i L; apply (IH i L)).
 split; [|split].
 - (* buri.eval *)
   intros e env z r Se Oe H. destruct e as [d|x|x|x b|f a|x a b|c a b|op args|e|e h|e|e]; cbn [sub2] in Se.
   + rewrite Q.eval_lit in H. gate_case H. ret H. split; [apply data_ok2; exact Se|].
     intros P s HP Hs Hd0. apply (m_lit P s ds HP Hs Hd0 d env Se).
   + rewrite Q.eval_var in H. gate_case H.
     destruct (ask j "kl:buri.get" _) as [g|] eqn:Gt; [|discriminate]. apply ask_get in Gt; subst g.
     destruct j as [|j]; [discriminate|].
     destruct (assoc x env) as [v|] eqn:A; cbn beta iota in H;
       [rewrite Q.lookup_found in H|rewrite Q.lookup_missing in H]; ret H.
     * split; [eapply assoc_ok2; eassumption|]. intros P s HP Hs Hd0 k.
       pose proof (m_var P s ds HP Hs Hd0 x env k) as M; rewrite A in M; exact M.
     * split; [exact I|]. intros P s HP Hs Hd0 k.
       pose proof (m_var P s ds HP Hs Hd0 x env k) as M; rewrite A in M; exact M.
   + (* [global X] *)
     apply G.eval_global in H. destruct H as [[_ ->]|(v & Df & Rv)].
     * exists WBudget; repeat split; intros ? ? ? ? ? ?; exact I.
     * apply G.ask_definition in Df. specialize (Rv _ Df). unfold G.gate_value in Rv.
       destruct (Z.eqb z 0); [subst r; exists WBudget; repeat split; intros ? ? ? ? ? ?; exact I|].
       destruct (G.find_def x ds) as [[ps b]|] eqn:F; subst r; eexists; split; try reflexivity.
       -- destruct (find_def_ok ds x ps b Hds F) as [NE _]. split.
          ++ cbn. split; [exists ps, b; split; [exact F|destruct ps; [contradiction|cbn; lia]]|exact I].
          ++ intros P s HP Hs Hd0. exact (m_global_found P s ds HP Hs Hd0 x env ps b F NE).
       -- split; [exact I|]. intros P s HP Hs Hd0. exact (m_global_missing P s ds HP Hs Hd0 x env F).
   + rewrite Q.eval_lambda in H. gate_case H. ret H. split; [split; [exact Se|apply okenv2_fold; exact Oe]|].
     intros P s HP Hs Hd0; apply (m_lambda P s ds HP Hs Hd0); assumption.
   + destruct Se as [Sf Sa]. rewrite Q.eval_apply in H. gate_case H.
     destruct (ask j "kl:buri.eval" [D; enc_term f; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ Sf Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite Q.function_verdict in H.
     destruct w1 as [fv|m| |]; try (ret H; split; [exact I|];
       intros P s HP Hs Hd0; apply (m_app_fail1 P s ds HP Hs Hd0); [exact I|apply G1; assumption]).
     destruct (ask j "kl:buri.eval" [D; enc_term a; enc_env env; _]) as [v2|] eqn:E2; [|discriminate].
     destruct (IE j ltac:(lia) _ _ _ _ Sa Oe E2) as (w2 & -> & O2 & G2).
     destruct j as [|j]; [discriminate|]. rewrite Q.argument_verdict in H.
     destruct w2 as [av|m| |]; try (ret H; split; [exact I|];
       intros P s HP Hs Hd0; eapply (m_app_fail2 P s ds HP Hs Hd0); [exact I|apply G1; assumption|apply G2; assumption]).
     destruct (IA j ltac:(lia) _ _ _ _ O1 O2 H) as (w & -> & O & GA).
     eexists; split; [reflexivity|split; [exact O|]].
     intros P s HP Hs Hd0. eapply (m_app_ret P s ds HP Hs Hd0); [apply G1|apply G2|apply GA]; assumption.
   + destruct Se as [Sa Sb]. rewrite Q.eval_let in H. gate_case H.
     destruct (ask j "kl:buri.eval" [D; enc_term a; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ Sa Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite Q.let_verdict in H.
     destruct w1 as [v|m| |]; try (ret H; split; [exact I|];
       intros P s HP Hs Hd0; apply (m_let_fail P s ds HP Hs Hd0); [exact I|apply G1; assumption]).
     assert (O' : okenv2 ds ((x, v) :: env)) by (constructor; assumption).
     destruct (IE j ltac:(lia) _ _ _ _ Sb O' H) as (w & -> & O & G2).
     eexists; split; [reflexivity|split; [exact O|]].
     intros P s HP Hs Hd0. eapply (m_let_ret P s ds HP Hs Hd0); [apply G1|apply G2]; assumption.
   + destruct Se as (Sc & Sa & Sb). rewrite Q.eval_if in H. gate_case H.
     destruct (ask j "kl:buri.eval" [D; enc_term c; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ Sc Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. apply Q.if_verdict in H.
     destruct w1 as [v|m| |]; try (subst r; eexists; split; [reflexivity|]; split; [exact I|];
       intros P s HP Hs Hd0; apply (m_if_fail P s ds HP Hs Hd0); [exact I|apply G1; assumption]).
     destruct v as [z0| [|] |st|sy| |a1 a2|x0 e0 env0|f0 g0|e0 env0];
       try (subst r; eexists; split; [reflexivity|]; split; [exact I|];
         intros P s HP Hs Hd0; eapply (m_if_nonbool P s ds HP Hs Hd0); [|apply G1; assumption]; intros bv E; discriminate E).
     * destruct (IE j ltac:(lia) _ _ _ _ Sa Oe H) as (w & -> & O & G2).
       eexists; split; [reflexivity|split; [exact O|]].
       intros P s HP Hs Hd0. eapply (m_if_bool P s ds HP Hs Hd0 c a b env true); [apply G1|apply G2]; assumption.
     * destruct (IE j ltac:(lia) _ _ _ _ Sb Oe H) as (w & -> & O & G2).
       eexists; split; [reflexivity|split; [exact O|]].
       intros P s HP Hs Hd0. eapply (m_if_bool P s ds HP Hs Hd0 c a b env false); [apply G1|apply G2]; assumption.
   + destruct Se as [Ar Sargs0]. apply sub2_fold in Sargs0.
     unfold R.prim_ok in Ar. destruct (R.prim_of op) as [p|] eqn:Op; [|contradiction].
     rewrite Q.eval_prim in H. gate_case H.
     destruct (ask j "kl:buri.eval-args" _) as [v1|] eqn:E1; [|discriminate].
     destruct (IG j (le_n j) _ _ _ _ Sargs0 Oe E1) as (a1 & -> & O1 & L1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite Q.primitive_args in H.
     assert (NE : args <> []) by (intro Z; subst args; destruct p; discriminate Ar).
     destruct a1 as [vs|w1].
     * cbn in L1. pose proof (R.prim_table_in op p Op) as In0.
       destruct (R.prim_cases op p Op) as [[I2 A2]|[[I1 A1]|[-> ->]]].
       -- destruct vs as [|v1 [|v2 [|]]]; cbn in L1; try (rewrite <- Ar, A2 in L1; discriminate L1).
          cbn [map] in H. apply Pr.ask_prim2 in H; [|exact I2]. subst r.
          eexists; split; [reflexivity|split; [apply prim_spec_ok2; [exact O1|cbn in I2 |- *; tauto]|]].
          intros P s HP Hs Hd0. eapply (m_prim_vals P s ds HP Hs Hd0); [exact NE|apply G1; assumption|].
          intro k. apply (kl_prim2 P s ds HP Hs Hd0 op p [v1; v2] k); [cbn in I2 |- *; tauto|exact Op|rewrite A2; reflexivity].
       -- destruct vs as [|v1 [|]]; cbn in L1; try (rewrite <- Ar, A1 in L1; discriminate L1).
          cbn [map] in H. apply Pr.ask_prim1 in H; [|exact I1]. subst r.
          eexists; split; [reflexivity|split; [apply prim_spec_ok2; [exact O1|cbn in I1 |- *; tauto]|]].
          intros P s HP Hs Hd0. eapply (m_prim_vals P s ds HP Hs Hd0); [exact NE|apply G1; assumption|].
          intro k. apply (kl_prim2 P s ds HP Hs Hd0 op p [v1] k); [cbn in I1 |- *; tauto|exact Op|rewrite A1; reflexivity].
       -- destruct vs as [|v1 [|v2 [|]]]; cbn in L1; try (rewrite <- Ar in L1; discriminate L1).
          cbn [map] in H. apply Pr.ask_prim_equal in H. subst r.
          eexists; split; [reflexivity|split; [unfold Pr.eq_spec; destruct (Pr.eqv v1 v2); exact I|]].
          intros P s HP Hs Hd0. eapply (m_prim_vals P s ds HP Hs Hd0); [exact NE|apply G1; assumption|].
          intro k. apply (kl_prim_equal2 P s ds HP Hs Hd0 v1 v2 k).
     * ret H. split; [destruct w1; cbn in O1 |- *; tauto|].
       intros P s HP Hs Hd0. apply (m_prim_fail P s ds HP Hs Hd0); [exact NE|apply G1; assumption].
   + rewrite Q.eval_raise in H. gate_case H.
     destruct (ask j "kl:buri.eval" [D; enc_term e; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ Se Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite Q.raise_verdict in H.
     destruct w1 as [v|m| |]; try (ret H; split; [exact I|];
       intros P s HP Hs Hd0; apply (m_raise_fail P s ds HP Hs Hd0); [exact I|apply G1; assumption]).
     destruct v as [z0|b0|t|sy| |a1 a2|x0 e0 env0|f0 g0|e0 env0]; ret H; split; try exact I; intros P s HP Hs Hd0;
       first [eapply (m_raise_str P s ds HP Hs Hd0); apply G1; assumption
             |eapply (m_raise_nonstr P s ds HP Hs Hd0); [|apply G1; assumption]; intros t' E; discriminate E].
   + destruct Se as [Se Sh]. rewrite Q.eval_trap in H. gate_case H.
     destruct (ask j "kl:buri.eval" [D; enc_term e; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ Se Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite Q.trap_verdict in H.
     destruct w1 as [v|m| |].
     * ret H. split; [exact O1|]. intros P s HP Hs Hd0. apply (m_trap_ret P s ds HP Hs Hd0); apply G1; assumption.
     * destruct (ask j "kl:buri.eval" [D; enc_term h; enc_env env; _]) as [v2|] eqn:E2; [|discriminate].
       destruct (IE j ltac:(lia) _ _ _ _ Sh Oe E2) as (w2 & -> & O2 & G2).
       destruct j as [|j]; [discriminate|]. rewrite Q.handler_verdict in H.
       destruct w2 as [hv|m2| |]; try (ret H; split; [exact I|];
         intros P s HP Hs Hd0; eapply (m_trap_raise_fail P s ds HP Hs Hd0); [exact I|apply G1; assumption|apply G2; assumption]).
       destruct (IA j ltac:(lia) hv (RStr m) _ _ O2 I H) as (w & -> & O & GA).
       eexists; split; [reflexivity|split; [exact O|]].
       intros P s HP Hs Hd0. eapply (m_trap_raise_ret P s ds HP Hs Hd0); [apply G1|apply G2|apply GA]; assumption.
     * ret H. split; [exact I|]. intros P s HP Hs Hd0; apply (m_trap_other P s ds HP Hs Hd0); [auto|apply G1; assumption].
     * ret H. split; [exact I|]. intros P s HP Hs Hd0; apply (m_trap_other P s ds HP Hs Hd0); [auto|apply G1; assumption].
   + (* [freeze E] *)
     rewrite G.eval_freeze in H. gate_case H. ret H. split; [split; [exact Se|apply okenv2_fold; exact Oe]|].
     intros P s HP Hs Hd0; apply (m_freeze P s ds HP Hs Hd0).
   + (* [thaw E] *)
     rewrite G.eval_thaw in H. gate_case H.
     destruct (ask j "kl:buri.eval" [D; enc_term e; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ Se Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite G.thaw_verdict in H.
     destruct w1 as [v|m| |]; try (ret H; split; [exact I|];
       intros P s HP Hs Hd0; apply (m_thaw_fail P s ds HP Hs Hd0); [exact I|apply G1; assumption]).
     destruct v as [z0|b0|t|sy| |a1 a2|x0 e0 env0|f0 prev|e0 env0];
       try (ret H; split; [exact I|]; intros P s HP Hs Hd0;
            eapply (m_thaw_ret P s ds HP Hs Hd0); [apply G1; assumption|apply (th_noncallable P s ds HP Hs Hd0); intros; discriminate]).
     * ret H. split; [exact I|]. intros P s HP Hs Hd0.
       eapply (m_thaw_ret P s ds HP Hs Hd0); [apply G1; assumption|apply (th_closure P s ds HP Hs Hd0)].
     * destruct O1 as [Fd Oargs]. destruct Fd as (ps & b & F & Lt).
       destruct (ask j "kl:buri.definition" _) as [dv|] eqn:Df; [|discriminate].
       apply G.ask_definition in Df. rewrite F in Df. subst dv.
       destruct j as [|j]; [discriminate|].
       apply G.apply_global_found in H. apply Nat.ltb_lt in Lt.
       destruct H as [[_ ->]|[Lf _]]; [|rewrite Lt in Lf; discriminate Lf].
       eexists; split; [reflexivity|split; [split; [exists ps, b; split; [exact F|apply Nat.ltb_lt; exact Lt]|exact Oargs]|]].
       intros P s HP Hs Hd0. eapply (m_thaw_ret P s ds HP Hs Hd0); [apply G1; assumption|].
       apply (th_partial P s ds HP Hs Hd0 f0 prev ps b F). apply Nat.ltb_lt; exact Lt.
     * destruct O1 as [Se0 Oe0]. apply okenv2_fold in Oe0.
       destruct (IE j ltac:(lia) _ _ _ _ Se0 Oe0 H) as (w & -> & O & G2).
       eexists; split; [reflexivity|split; [exact O|]].
       intros P s HP Hs Hd0. eapply (m_thaw_ret P s ds HP Hs Hd0); [apply G1; assumption|apply (th_frozen P s ds HP Hs Hd0)].
       apply G2; assumption.
 - (* buri.apply-value *)
   intros f a z r Of Oa H. destruct f as [z0|b0|st|sy| |a1 a2|x e env|g prev|e env].
   7: { rewrite Q.apply_value_eq in H; [|intros ? ? E; discriminate E|intros ? ? E; discriminate E].
        gate_case H. destruct Of as [Se Oe]. apply okenv2_fold in Oe.
        assert (O' : okenv2 ds ((x, a) :: env)) by (constructor; assumption).
        destruct (IE j (le_n j) _ _ _ _ Se O' H) as (w & -> & O & G0).
        eexists; split; [reflexivity|split; [exact O|]].
        intros P s HP Hs Hd0. apply (ap_closure P s ds HP Hs Hd0). apply G0; assumption. }
   8: { rewrite G.apply_value_thunk in H. gate_case H. ret H. split; [exact I|].
        intros P s HP Hs Hd0. apply (ap_thunk P s ds HP Hs Hd0). }
   7: { rewrite G.apply_value_function in H. gate_case H. destruct Of as [Fd Oargs].
        destruct (ask j "kl:buri.definition" _) as [dv|] eqn:Df; [|discriminate].
        destruct Fd as (ps & b & F & Lt).
        apply G.ask_definition in Df. rewrite F in Df. subst dv.
        destruct (ask j "kl:buri.append" _) as [args|] eqn:Ap; [|discriminate].
        apply (G.ask_append j prev [a]) in Ap. subst args.
        destruct j as [|j]; [discriminate|]. apply G.apply_global_found in H.
        apply oklist_fold in Oargs.
        assert (Oall : Forall (ok2 ds) (prev ++ [a])) by (apply Forall_app; split; [exact Oargs|constructor; [exact Oa|constructor]]).
        destruct H as [[Ltb ->]|[Ltb (zr & Zr & Bd)]].
        - eexists; split; [reflexivity|split].
          + split; [exists ps, b; split; [exact F|apply Nat.ltb_lt; exact Ltb]|apply oklist_fold; exact Oall].
          + intros P s HP Hs Hd0. apply (ap_partial P s ds HP Hs Hd0 g prev a ps b F). apply Nat.ltb_lt; exact Ltb.
        - apply Nat.ltb_ge in Ltb. rewrite app_length in Ltb. cbn in Ltb.
          assert (Eq : List.length (prev ++ [a]) = List.length ps) by (rewrite app_length; cbn; lia).
          apply G.ask_zip in Zr. rewrite (G.zipb_combine ps (prev ++ [a])) in Zr by (rewrite app_length; cbn; lia). subst zr.
          destruct j as [|j]; [discriminate|]. rewrite G.apply_bound_zipped in Bd.
          destruct (find_def_ok ds g ps b Hds F) as [_ Sb].
          destruct (IE j ltac:(lia) _ _ _ _ Sb (combine_ok2 ds ps _ Oall) Bd) as (w & -> & O & G0).
          eexists; split; [reflexivity|split; [exact O|]].
          intros P s HP Hs Hd0. apply (ap_call P s ds HP Hs Hd0 g prev a ps b w F Eq). apply G0; assumption. }
   all: rewrite Q.apply_value_eq in H; [|intros ? ? E; discriminate E|intros ? ? E; discriminate E];
     gate_case H; ret H; split; try exact I; intros P s HP Hs Hd0; apply (ap_noncallable P s ds HP Hs Hd0); intros; discriminate.
 - (* buri.eval-args *)
   intros es env z r Ss Oe H. destruct es as [|e es].
   + rewrite Q.args_nil in H. injection H as <-. exists (AVals []); repeat split; [constructor|].
     intros P s HP Hs Hd0 k f done e1 es' E; discriminate E.
   + inversion Ss as [|e0 es0 Se Ss']; subst. rewrite Q.args_cons in H.
     destruct (ask j "kl:buri.eval" [D; enc_term e; enc_env env; _]) as [v1|] eqn:E1; [|discriminate].
     destruct (IE j (le_n j) _ _ _ _ Se Oe E1) as (w1 & -> & O1 & G1).
     destruct j as [|j]; [discriminate|]. rewrite Q.args_first in H.
     destruct w1 as [v|m| |];
       try (match type of H with Some (enc_verdict ?W) = Some ?r => assert (EQ : r = enc_verdict W) by congruence;
         clear H; subst r; exists (AFail W) end; split; [reflexivity|]; split; [exact I|];
         split; [discriminate|]; intros P s HP Hs Hd0; apply (args_fail1 P s ds HP Hs Hd0); [exact I|apply G1; assumption]).
     destruct (ask j "kl:buri.eval-args" _) as [v2|] eqn:E2; [|discriminate].
     destruct (IG j ltac:(lia) _ _ _ _ Ss' Oe E2) as (a2 & -> & O2 & L2 & G2).
     destruct j as [|j]; [discriminate|]. rewrite Q.args_rest in H. injection H as <-.
     destruct a2 as [vs|w2].
     * exists (AVals (v :: vs)); split; [reflexivity|]; split; [constructor; assumption|].
       split; [cbn in L2 |- *; rewrite L2; reflexivity|].
       intros P s HP Hs Hd0. apply (args_ret P s ds HP Hs Hd0); [apply G1; assumption|].
       destruct es as [|e2 es2]; [destruct vs; [reflexivity|discriminate L2]|apply G2; assumption].
     * exists (AFail w2); split; [reflexivity|]; split; [exact O2|]; split; [discriminate|].
       intros P s HP Hs Hd0. destruct es as [|e2 es2]; [contradiction|].
       eapply (args_fail2 P s ds HP Hs Hd0); [apply G1; assumption|apply G2; assumption].
Qed.

Lemma all_fuel : forall n i, i <= n -> Seval i /\ Sapply i /\ Sargs i.
Proof.
 induction n as [|n IH]; intros i L.
 - inversion L; subst. repeat split; intros; discriminate.
 - inversion L as [|n' L']; subst; [apply step_all; exact IH|apply IH; exact L'].
Qed.
End Induction.

(* ---------- the extended E2E-07 refinement theorems ---------- *)
Lemma taus_run_wrong : forall P c c' w, R.taus P c c' -> next P c' = MWrong w ->
 exists m, R.krun P m c tt = VWrong [].
Proof.
 intros P c c' w T W. induction T as [c|c c1 c2 N T IH].
 - exists 0. unfold R.krun. cbn [KLMetatheory.KLMetatheory.run]. rewrite W. reflexivity.
 - destruct (IH W) as [m Rm]. exists (S m). unfold R.krun in *. cbn [KLMetatheory.KLMetatheory.run].
   rewrite N. unfold KLMetatheory.KLMetatheory.cnext. rewrite N. cbn -[KLMetatheory.KLMetatheory.run]. change (R.still tt) with tt. rewrite Rm. reflexivity.
Qed.

(* E2E-07, extended KL-PURE-1 subset. For every well-formed definition table
   ds (positive arities, bodies in the subset), every term e of the subset,
   every budget z and every fuel n of the actual Native evaluator running the
   captured klambda.shen program: if buri.eval returns r, r is the encoding of
   a verdict w and, under every pinned profile and every store that binds the
   primitive names and the translated definitions, the KLambda run of tr e
   agrees: [returned v] is Normal (tr_rv v), [raised m] an exception of the
   stated class, [unsupported closure-equality] is the machine going wrong
   (equality of two function values is undefined), each found by
   KLMetatheory.run with enough fuel; [unknown evaluation-budget] makes no
   behavior claim. *)
Theorem klambda_refines_ext : forall ds n e z r, ds_ok ds -> sub2 e ->
 Native.Native.run n program "kl:buri.eval" [G.enc_defs ds; enc_term e; enc_env []; Native.Native.Integer z] =
   Native.Native.Returned r ->
 exists w, r = enc_verdict w /\ okv ds w /\
 forall P s, pure2 P -> R.prims s -> defs s ds -> match w with
 | WRet v => exists m, R.krun P m (Cfg (Eval [] (R.tr e)) [] s) tt = VDone [] (Normal (R.tr_rv v))
 | WRaise msg => exists x m, exn2 msg x /\ R.krun P m (Cfg (Eval [] (R.tr e)) [] s) tt = VDone [] (Error x)
 | WUnsupported => exists m, R.krun P m (Cfg (Eval [] (R.tr e)) [] s) tt = VWrong []
 | WBudget => True end.
Proof.
 intros ds n e z r Hds Se H. apply native_run_ask in H.
 destruct (all_fuel ds Hds (S n) (S n) (le_n _)) as [SE _].
 destruct (SE e [] z r Se (Forall_nil _) H) as (w & -> & O & Gw).
 exists w; split; [reflexivity|split; [exact O|]]. intros P s HP Hs Hd.
 pose proof (Gw P s HP Hs Hd []) as Rw. destruct w as [v|m| |]; cbn in Rw; try exact I.
 - eapply R.taus_run; [exact Rw|reflexivity].
 - destruct Rw as (x & Cl & T). destruct (R.taus_run P _ _ (Error x) T eq_refl) as [k K]. eauto.
 - destruct Rw as (k' & s' & T). eapply taus_run_wrong; [exact T|reflexivity].
Qed.

(* The compositional form: any oracle fuel, any environment of related values,
   any continuation. *)
Theorem klambda_refines_ext_open : forall ds k e env z r, ds_ok ds -> sub2 e -> okenv2 ds env ->
 ask k "kl:buri.eval" [G.enc_defs ds; enc_term e; enc_env env; Native.Native.Integer z] = Some r ->
 exists w, r = enc_verdict w /\ okv ds w /\
 forall P s kont, pure2 P -> R.prims s -> defs s ds -> reaches2 P s (Cfg (Eval (R.tr_env env) (R.tr e)) kont s) w kont.
Proof.
 intros ds k e env z r Hds Se Oe H. destruct (all_fuel ds Hds k k (le_n _)) as [SE _].
 destruct (SE e env z r Se Oe H) as (w & -> & O & Gw).
 exists w; split; [reflexivity|split; [exact O|]]. intros P s kont HP Hs Hd. apply (Gw P s HP Hs Hd kont).
Qed.
End KLambdaEvaluatorExtended.
