(* E2E-07: the captured KL-PURE-1 reference evaluator (shen/klambda.shen, as
   compiled and installed by the pinned Shen-Scheme image; capture profile
   e2e07_klambda) executed by the Native model. This module fixes the program
   (capture plus the captured base.shen and kernel.shen helpers it calls plus
   the pinned runtime helper templates), the representation of the evaluator's
   own term and value data, the bridge from Native.run to the fuel-free oracle
   semantics of EqualityInductionOracle, and the runtime-helper and buri.get
   specifications. KLambdaEvaluatorEquations states one equation per captured
   body; nothing here is a hand-written interpreter. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native NativeHelpers EqualityInductionOracle
 EqualityInductionBaseInput EqualityInductionKernelInput KLambdaEvaluatorInput.
Import ListNotations Native.Native.
Module KLambdaEvaluatorCapture.
Module O := EqualityInductionOracle.EqualityInductionOracle.
Open Scope string_scope.

(* ---------- the executed program ---------- *)
(* Runtime functions that are not Shen definitions are the pinned helper
   templates (kl:= is equal?, kl:_scm.assert-boolean, kl:symbol?, kl:str) and
   the contract kl:not = (if x #f #t), exactly as for EQ-1. kl:length and
   kl:shen.f-error are not modelled: a call to them has no Native value, so
   every theorem below is silent about runs that reach them. *)
Definition runtime_names := ["kl:=";"kl:_scm.assert-boolean";"kl:symbol?";"kl:str"].
Definition runtime := (filter (fun d => existsb (String.eqb (fst d)) runtime_names) NativeHelpers.helpers ++
 [("kl:not",Def ["x"] (If (Var "x") (Lit (Boolean false)) (Lit (Boolean true))))])%list.
Definition program := (e2e07_klambda_program ++ eq1_base_program ++ eq1_kernel_program ++ runtime)%list.
Definition names := Eval vm_compute in map fst program.
Definition defined s := existsb (String.eqb s) names.
Lemma defined_lookup : forall s, defined s = match lookup program s with Some _ => true | None => false end.
Proof. intro s. unfold defined. rewrite <- O.defined_names. reflexivity. Qed.
(* Every name is defined once, so lookup order cannot select a shadowed body. *)
Fixpoint uniqueb (xs : list string) : bool := match xs with
 | [] => true | x :: xs => negb (existsb (String.eqb x) xs) && uniqueb xs end.
Theorem program_names_unique : uniqueb names = true.
Proof. vm_compute. reflexivity. Qed.
Definition ask := O.oracle program defined.
Definition def_of name := match lookup program name with Some d => d | None => Def [] (Lit Nil) end.
Lemma ask_unfold : forall k s vs d, lookup program s = Some d ->
 ask (S k) s vs = if Nat.eqb (List.length (params d)) (List.length vs)
   then O.step defined (ask k) (arguments (params d) vs) (body d) else None.
Proof. intros. unfold ask. apply O.oracle_unfold. assumption. Qed.
Lemma ask_zero : forall s vs, ask 0 s vs = None.
Proof. reflexivity. Qed.

(* The actual Native evaluator on the captured program reaches the oracle. *)
Theorem native_run_ask : forall n name args r,
 run n program name args = Returned r -> ask (S n) name args = Some r.
Proof.
 intros n name args r H. unfold run in H. destruct (lookup program name) as [d|] eqn:L; [|discriminate].
 rewrite (ask_unfold n name args d L). destruct (Nat.eqb _ _); [|discriminate].
 apply O.eval_oracle; [exact defined_lookup|exact H].
Qed.

(* ---------- the evaluator's own term and value representation ---------- *)
(* rv: the runtime values of shen/klambda.shen; term: its inert input syntax.
   enc/enc_term/enc_env are the exact Shen list shapes the evaluator matches. *)
Inductive rv :=
 | RInt (z : Z) | RBool (b : bool) | RStr (s : string) | RSym (s : string) | RNil
 | RPair (a d : rv)
 | RClosure (x : string) (e : term) (env : list (string * rv))
 | RFunction (f : string) (args : list rv)
 | RThunk (e : term) (env : list (string * rv))
with term :=
 | TLit (d : rv) | TVar (x : string) | TGlobal (x : string) | TLambda (x : string) (e : term)
 | TApply (f a : term) | TLet (x : string) (a b : term) | TIf (c a b : term)
 | TPrim (op : string) (args : list term) | TRaise (e : term) | TTrap (e h : term)
 | TFreeze (e : term) | TThaw (e : term).

Fixpoint enc (v : rv) : value := match v with
 | RInt z => L [Symbol "int"; Integer z]
 | RBool b => L [Symbol "bool"; Boolean b]
 | RStr s => L [Symbol "str"; Text s]
 | RSym s => L [Symbol "sym"; Symbol s]
 | RNil => Symbol "nil"
 | RPair a d => L [Symbol "pair"; enc a; enc d]
 | RClosure x e env => L [Symbol "closure"; Symbol x; enc_term e;
     L (map (fun p => L [Symbol (fst p); enc (snd p)]) env)]
 | RFunction f args => L [Symbol "function"; Symbol f; L (map enc args)]
 | RThunk e env => L [Symbol "thunk"; enc_term e; L (map (fun p => L [Symbol (fst p); enc (snd p)]) env)]
 end
with enc_term (e : term) : value := match e with
 | TLit d => L [Symbol "literal"; enc d]
 | TVar x => L [Symbol "var"; Symbol x]
 | TGlobal x => L [Symbol "global"; Symbol x]
 | TLambda x b => L [Symbol "lambda"; Symbol x; enc_term b]
 | TApply f a => L [Symbol "apply"; enc_term f; enc_term a]
 | TLet x a b => L [Symbol "let"; Symbol x; enc_term a; enc_term b]
 | TIf c a b => L [Symbol "if"; enc_term c; enc_term a; enc_term b]
 | TPrim op args => L [Symbol "primitive"; Symbol op; L (map enc_term args)]
 | TRaise e => L [Symbol "raise"; enc_term e]
 | TTrap e h => L [Symbol "trap"; enc_term e; enc_term h]
 | TFreeze e => L [Symbol "freeze"; enc_term e]
 | TThaw e => L [Symbol "thaw"; enc_term e]
 end.
Definition enc_env (env : list (string * rv)) := L (map (fun p => L [Symbol (fst p); enc (snd p)]) env).

(* Evaluator verdicts produced inside buri.eval. [rejected ...] and
   [unknown host-error] are produced only by buri.evaluate (admission and the
   host guard) and are not in this type. *)
Inductive verdict := WRet (v : rv) | WRaise (m : string) | WBudget | WUnsupported.
Definition enc_verdict (w : verdict) : value := match w with
 | WRet v => L [Symbol "returned"; enc v]
 | WRaise m => L [Symbol "raised"; Text m]
 | WBudget => L [Symbol "unknown"; Symbol "evaluation-budget"]
 | WUnsupported => L [Symbol "unsupported"; Symbol "closure-equality"] end.
Inductive args_verdict := AVals (vs : list rv) | AFail (w : verdict).
Definition enc_args (a : args_verdict) : value := match a with
 | AVals vs => L [Symbol "arguments"; L (map enc vs)]
 | AFail w => enc_verdict w end.
Definition gate (z : Z) (r : option value) : option value :=
 if Z.eqb z 0 then Some (enc_verdict WBudget) else r.

Fixpoint assoc (x : string) (env : list (string * rv)) : option rv := match env with
 | [] => None | (y, v) :: env => if String.eqb x y then Some v else assoc x env end.

(* ---------- captured bodies ---------- *)
Definition d_eval := Eval vm_compute in def_of "kl:buri.eval".
Lemma d_eval_lk : lookup program "kl:buri.eval" = Some d_eval. Proof. vm_compute; reflexivity. Qed.
Definition d_lookup_value := Eval vm_compute in def_of "kl:buri.lookup-value".
Lemma d_lookup_value_lk : lookup program "kl:buri.lookup-value" = Some d_lookup_value. Proof. vm_compute; reflexivity. Qed.
Definition d_eval_let := Eval vm_compute in def_of "kl:buri.eval-let".
Lemma d_eval_let_lk : lookup program "kl:buri.eval-let" = Some d_eval_let. Proof. vm_compute; reflexivity. Qed.
Definition d_eval_if := Eval vm_compute in def_of "kl:buri.eval-if".
Lemma d_eval_if_lk : lookup program "kl:buri.eval-if" = Some d_eval_if. Proof. vm_compute; reflexivity. Qed.
Definition d_eval_function := Eval vm_compute in def_of "kl:buri.eval-function".
Lemma d_eval_function_lk : lookup program "kl:buri.eval-function" = Some d_eval_function. Proof. vm_compute; reflexivity. Qed.
Definition d_eval_argument := Eval vm_compute in def_of "kl:buri.eval-argument".
Lemma d_eval_argument_lk : lookup program "kl:buri.eval-argument" = Some d_eval_argument. Proof. vm_compute; reflexivity. Qed.
Definition d_apply_value := Eval vm_compute in def_of "kl:buri.apply-value".
Lemma d_apply_value_lk : lookup program "kl:buri.apply-value" = Some d_apply_value. Proof. vm_compute; reflexivity. Qed.
Definition d_eval_args := Eval vm_compute in def_of "kl:buri.eval-args".
Lemma d_eval_args_lk : lookup program "kl:buri.eval-args" = Some d_eval_args. Proof. vm_compute; reflexivity. Qed.
Definition d_eval_args_first := Eval vm_compute in def_of "kl:buri.eval-args-first".
Lemma d_eval_args_first_lk : lookup program "kl:buri.eval-args-first" = Some d_eval_args_first. Proof. vm_compute; reflexivity. Qed.
Definition d_eval_args_rest := Eval vm_compute in def_of "kl:buri.eval-args-rest".
Lemma d_eval_args_rest_lk : lookup program "kl:buri.eval-args-rest" = Some d_eval_args_rest. Proof. vm_compute; reflexivity. Qed.
Definition d_eval_primitive := Eval vm_compute in def_of "kl:buri.eval-primitive".
Lemma d_eval_primitive_lk : lookup program "kl:buri.eval-primitive" = Some d_eval_primitive. Proof. vm_compute; reflexivity. Qed.
Definition d_primitive := Eval vm_compute in def_of "kl:buri.primitive".
Lemma d_primitive_lk : lookup program "kl:buri.primitive" = Some d_primitive. Proof. vm_compute; reflexivity. Qed.
Definition d_eval_raise := Eval vm_compute in def_of "kl:buri.eval-raise".
Lemma d_eval_raise_lk : lookup program "kl:buri.eval-raise" = Some d_eval_raise. Proof. vm_compute; reflexivity. Qed.
Definition d_eval_trap := Eval vm_compute in def_of "kl:buri.eval-trap".
Lemma d_eval_trap_lk : lookup program "kl:buri.eval-trap" = Some d_eval_trap. Proof. vm_compute; reflexivity. Qed.
Definition d_eval_handler := Eval vm_compute in def_of "kl:buri.eval-handler".
Lemma d_eval_handler_lk : lookup program "kl:buri.eval-handler" = Some d_eval_handler. Proof. vm_compute; reflexivity. Qed.
Definition d_literal := Eval vm_compute in def_of "kl:buri.literal?".
Lemma d_literal_lk : lookup program "kl:buri.literal?" = Some d_literal. Proof. vm_compute; reflexivity. Qed.
Definition d_get := Eval vm_compute in def_of "kl:buri.get".
Lemma d_get_lk : lookup program "kl:buri.get" = Some d_get. Proof. vm_compute; reflexivity. Qed.
Definition d_equal := Eval vm_compute in def_of "kl:=".
Lemma d_equal_lk : lookup program "kl:=" = Some d_equal. Proof. vm_compute; reflexivity. Qed.
Definition d_assert := Eval vm_compute in def_of "kl:_scm.assert-boolean".
Lemma d_assert_lk : lookup program "kl:_scm.assert-boolean" = Some d_assert. Proof. vm_compute; reflexivity. Qed.
Definition d_evaluate := Eval vm_compute in def_of "kl:buri.evaluate".
Lemma d_evaluate_lk : lookup program "kl:buri.evaluate" = Some d_evaluate. Proof. vm_compute; reflexivity. Qed.

Definition d_fnv := Eval vm_compute in def_of "kl:buri.function-value?".
Lemma d_fnv_lk : lookup program "kl:buri.function-value?" = Some d_fnv. Proof. vm_compute; reflexivity. Qed.
Definition d_equal_fn := Eval vm_compute in def_of "kl:buri.equal".
Lemma d_equal_fn_lk : lookup program "kl:buri.equal" = Some d_equal_fn. Proof. vm_compute; reflexivity. Qed.
Definition d_equal_pair := Eval vm_compute in def_of "kl:buri.equal-pair".
Lemma d_equal_pair_lk : lookup program "kl:buri.equal-pair" = Some d_equal_pair. Proof. vm_compute; reflexivity. Qed.
Definition d_equal_leaf := Eval vm_compute in def_of "kl:buri.equal-leaf".
Lemma d_equal_leaf_lk : lookup program "kl:buri.equal-leaf" = Some d_equal_leaf. Proof. vm_compute; reflexivity. Qed.
Definition d_eq_verdict := Eval vm_compute in def_of "kl:buri.equality-verdict".
Lemma d_eq_verdict_lk : lookup program "kl:buri.equality-verdict" = Some d_eq_verdict. Proof. vm_compute; reflexivity. Qed.
Definition d_fewer := Eval vm_compute in def_of "kl:buri.fewer?".
Lemma d_fewer_lk : lookup program "kl:buri.fewer?" = Some d_fewer. Proof. vm_compute; reflexivity. Qed.
Definition d_apply_global := Eval vm_compute in def_of "kl:buri.apply-global".
Lemma d_apply_global_lk : lookup program "kl:buri.apply-global" = Some d_apply_global. Proof. vm_compute; reflexivity. Qed.
Definition d_apply_bound := Eval vm_compute in def_of "kl:buri.apply-bound".
Lemma d_apply_bound_lk : lookup program "kl:buri.apply-bound" = Some d_apply_bound. Proof. vm_compute; reflexivity. Qed.
Definition d_eval_thaw := Eval vm_compute in def_of "kl:buri.eval-thaw".
Lemma d_eval_thaw_lk : lookup program "kl:buri.eval-thaw" = Some d_eval_thaw. Proof. vm_compute; reflexivity. Qed.
Definition d_definition := Eval vm_compute in def_of "kl:buri.definition".
Lemma d_definition_lk : lookup program "kl:buri.definition" = Some d_definition. Proof. vm_compute; reflexivity. Qed.
Definition d_zip := Eval vm_compute in def_of "kl:buri.zip".
Lemma d_zip_lk : lookup program "kl:buri.zip" = Some d_zip. Proof. vm_compute; reflexivity. Qed.
Definition d_zip_h := Eval vm_compute in def_of "kl:buri.zip-h".
Lemma d_zip_h_lk : lookup program "kl:buri.zip-h" = Some d_zip_h. Proof. vm_compute; reflexivity. Qed.
Definition d_append := Eval vm_compute in def_of "kl:buri.append".
Lemma d_append_lk : lookup program "kl:buri.append" = Some d_append. Proof. vm_compute; reflexivity. Qed.

(* ---------- runtime helpers and base.shen ---------- *)
Lemma ask_equal : forall k a b r, ask k "kl:=" [a; b] = Some r -> r = Boolean (same a b).
Proof. intros [|k] a b r H; [discriminate|]. rewrite (ask_unfold _ _ _ _ d_equal_lk) in H. cbn in H. congruence. Qed.
Lemma ask_assert : forall k w u, ask k "kl:_scm.assert-boolean" [w] = Some u -> exists b, w = Boolean b /\ u = Boolean b.
Proof.
 intros [|k] w u H; [discriminate|]. rewrite (ask_unfold _ _ _ _ d_assert_lk) in H. cbn in H.
 destruct w; try discriminate. injection H as <-. eauto.
Qed.
Lemma ask_get : forall k x env r, ask k "kl:buri.get" [Symbol x; enc_env env] = Some r ->
 r = match assoc x env with Some v => L [Symbol "found"; enc v] | None => Symbol "missing" end.
Proof.
 induction k as [|k IH]; intros x env r H; [discriminate|].
 rewrite (ask_unfold _ _ _ _ d_get_lk) in H. destruct env as [|[y v] env]; cbn in H |- *.
 - congruence.
 - destruct (ask k "kl:=" [Symbol x; Symbol y]) as [u|] eqn:E; [|discriminate].
   apply ask_equal in E; subst u. cbn in H. destruct (String.eqb x y); [congruence|].
   apply IH in H. exact H.
Qed.

End KLambdaEvaluatorCapture.
