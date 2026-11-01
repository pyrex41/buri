(* E2E-07: one equation per captured evaluator body and input shape, about the
   fuel-free oracle semantics of the captured program (KLambdaEvaluatorCapture).
   Each is proved by reducing the decoded captured body; none mentions TLambda. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native KLambdaEvaluatorCapture.
Import ListNotations Native.Native.
Module KLambdaEvaluatorEquations.
Import KLambdaEvaluatorCapture.KLambdaEvaluatorCapture.
Open Scope string_scope.
(* Unfold one captured body and abstract the callee oracle: the reduction is
   then by the VM (the Native primitive table is a large string match). *)
Ltac unf lk := rewrite (ask_unfold _ _ _ _ lk);
 match goal with |- context [O.step _ (ask ?j) _ _] => generalize (ask j) as rec; intro rec end.
(* Close an unfolding equation: compute, split remaining callee results, compute. *)
Ltac calls := vm_compute; repeat match goal with |- context [match ?r ?f ?a with _ => _ end] =>
 is_var r; destruct (r f a) end; vm_compute; reflexivity.

(* ---------- buri.eval, one equation per construct ---------- *)
Section Eval.
Variables (k : nat) (D : value) (env : list (string * rv)) (z : Z).
Lemma eval_lit : forall d, ask (S k) "kl:buri.eval" [D; enc_term (TLit d); enc_env env; Integer z] =
 gate z (Some (enc_verdict (WRet d))).
Proof. intros; unf d_eval_lk; destruct z; calls. Qed.
Lemma eval_var : forall x, ask (S k) "kl:buri.eval" [D; enc_term (TVar x); enc_env env; Integer z] =
 gate z (match ask k "kl:buri.get" [Symbol x; enc_env env] with
   | Some v => ask k "kl:buri.lookup-value" [v] | None => None end).
Proof. intros; unf d_eval_lk; destruct z; calls. Qed.
Lemma eval_lambda : forall x b, ask (S k) "kl:buri.eval" [D; enc_term (TLambda x b); enc_env env; Integer z] =
 gate z (Some (enc_verdict (WRet (RClosure x b env)))).
Proof. intros; unf d_eval_lk; destruct z; calls. Qed.
Lemma eval_apply : forall f a, ask (S k) "kl:buri.eval" [D; enc_term (TApply f a); enc_env env; Integer z] =
 gate z (match ask k "kl:buri.eval" [D; enc_term f; enc_env env; Integer (z - 1)] with
   | Some v => ask k "kl:buri.eval-function" [v; D; enc_term a; enc_env env; Integer (z - 1)] | None => None end).
Proof. intros; unf d_eval_lk; destruct z; calls. Qed.
Lemma eval_let : forall x a b, ask (S k) "kl:buri.eval" [D; enc_term (TLet x a b); enc_env env; Integer z] =
 gate z (match ask k "kl:buri.eval" [D; enc_term a; enc_env env; Integer (z - 1)] with
   | Some v => ask k "kl:buri.eval-let" [v; D; Symbol x; enc_term b; enc_env env; Integer (z - 1)] | None => None end).
Proof. intros; unf d_eval_lk; destruct z; calls. Qed.
Lemma eval_if : forall c a b, ask (S k) "kl:buri.eval" [D; enc_term (TIf c a b); enc_env env; Integer z] =
 gate z (match ask k "kl:buri.eval" [D; enc_term c; enc_env env; Integer (z - 1)] with
   | Some v => ask k "kl:buri.eval-if" [v; D; enc_term a; enc_term b; enc_env env; Integer (z - 1)] | None => None end).
Proof. intros; unf d_eval_lk; destruct z; calls. Qed.
Lemma eval_prim : forall op args, ask (S k) "kl:buri.eval" [D; enc_term (TPrim op args); enc_env env; Integer z] =
 gate z (match ask k "kl:buri.eval-args" [D; L (map enc_term args); enc_env env; Integer (z - 1)] with
   | Some v => ask k "kl:buri.eval-primitive" [v; Symbol op] | None => None end).
Proof. intros; unf d_eval_lk; destruct z; calls. Qed.
Lemma eval_raise : forall e, ask (S k) "kl:buri.eval" [D; enc_term (TRaise e); enc_env env; Integer z] =
 gate z (match ask k "kl:buri.eval" [D; enc_term e; enc_env env; Integer (z - 1)] with
   | Some v => ask k "kl:buri.eval-raise" [v] | None => None end).
Proof. intros; unf d_eval_lk; destruct z; calls. Qed.
Lemma eval_trap : forall e h, ask (S k) "kl:buri.eval" [D; enc_term (TTrap e h); enc_env env; Integer z] =
 gate z (match ask k "kl:buri.eval" [D; enc_term e; enc_env env; Integer (z - 1)] with
   | Some v => ask k "kl:buri.eval-trap" [v; D; enc_term h; enc_env env; Integer (z - 1)] | None => None end).
Proof. intros; unf d_eval_lk; destruct z; calls. Qed.
End Eval.

(* ---------- continuation helpers, one equation per verdict shape ---------- *)
Section Helpers.
Variables (k : nat) (D : value).
Lemma lookup_found : forall v, ask (S k) "kl:buri.lookup-value" [L [Symbol "found"; enc v]] =
 Some (enc_verdict (WRet v)).
Proof. intros; unf d_lookup_value_lk; calls. Qed.
Lemma lookup_missing : ask (S k) "kl:buri.lookup-value" [Symbol "missing"] =
 Some (enc_verdict (WRaise "unbound-variable")).
Proof. unf d_lookup_value_lk; calls. Qed.
Lemma let_verdict : forall w x b env N,
 ask (S k) "kl:buri.eval-let" [enc_verdict w; D; Symbol x; b; enc_env env; N] =
 match w with WRet v => ask k "kl:buri.eval" [D; b; enc_env ((x, v) :: env); N]
 | _ => Some (enc_verdict w) end.
Proof. intros; unf d_eval_let_lk; destruct w; calls. Qed.
(* The Boolean test calls kl:= (equal?), so this one is stated as an inversion. *)
Lemma if_verdict : forall w a b Env N r,
 ask (S k) "kl:buri.eval-if" [enc_verdict w; D; a; b; Env; N] = Some r ->
 match w with
 | WRet (RBool true) => ask k "kl:buri.eval" [D; a; Env; N] = Some r
 | WRet (RBool false) => ask k "kl:buri.eval" [D; b; Env; N] = Some r
 | WRet _ => r = enc_verdict (WRaise "nonboolean-condition")
 | _ => r = enc_verdict w end.
Proof.
 intros w a b Env N r H; rewrite (ask_unfold _ _ _ _ d_eval_if_lk) in H.
 remember (ask k) as rec eqn:R.
 destruct w as [[| [|] | | | | | | |]| | |]; vm_compute in H;
 repeat match type of H with context [rec "kl:=" ?xs] =>
   let E := fresh "E" in destruct (rec "kl:=" xs) as [?u|] eqn:E;
   [rewrite R in E; apply ask_equal in E; subst u; vm_compute in H|vm_compute in H; try discriminate] end;
 subst rec; first [exact H | injection H as <-; vm_compute; reflexivity].
Qed.
Lemma function_verdict : forall w a Env N,
 ask (S k) "kl:buri.eval-function" [enc_verdict w; D; a; Env; N] =
 match w with
 | WRet f => match ask k "kl:buri.eval" [D; a; Env; N] with
   | Some v => ask k "kl:buri.eval-argument" [v; D; enc f; N] | None => None end
 | _ => Some (enc_verdict w) end.
Proof. intros; unf d_eval_function_lk; destruct w; calls. Qed.
Lemma argument_verdict : forall w F N,
 ask (S k) "kl:buri.eval-argument" [enc_verdict w; D; F; N] =
 match w with WRet a => ask k "kl:buri.apply-value" [D; F; enc a; N] | _ => Some (enc_verdict w) end.
Proof. intros; unf d_eval_argument_lk; destruct w; calls. Qed.
(* Application of a closure or of a non-callable value. [function ...]
   values (from [global X]) go through buri.apply-global and kl:length,
   which this profile does not cover (obligation E2E07-GLOBAL). *)
Lemma apply_value_eq : forall f a z, (forall g args, f <> RFunction g args) ->
 ask (S k) "kl:buri.apply-value" [D; enc f; enc a; Integer z] =
 gate z (match f with
   | RClosure x e env => ask k "kl:buri.eval" [D; enc_term e; enc_env ((x, a) :: env); Integer (z - 1)]
   | _ => Some (enc_verdict (WRaise "not-callable")) end).
Proof.
 intros f a z NF; unf d_apply_value_lk; destruct z; [calls| |];
 (destruct f; [calls|calls|calls|calls|calls|calls|calls|exfalso; eapply NF; reflexivity|calls]).
Qed.
Lemma args_nil : forall Env N,
 ask (S k) "kl:buri.eval-args" [D; L (map enc_term []); Env; N] = Some (enc_args (AVals [])).
Proof. intros; unf d_eval_args_lk; calls. Qed.
Lemma args_cons : forall e es Env N,
 ask (S k) "kl:buri.eval-args" [D; L (map enc_term (e :: es)); Env; N] =
 match ask k "kl:buri.eval" [D; enc_term e; Env; N] with
 | Some v => ask k "kl:buri.eval-args-first" [v; D; L (map enc_term es); Env; N] | None => None end.
Proof. intros; unf d_eval_args_lk; calls. Qed.
Lemma args_first : forall w Es Env N,
 ask (S k) "kl:buri.eval-args-first" [enc_verdict w; D; Es; Env; N] =
 match w with
 | WRet v => match ask k "kl:buri.eval-args" [D; Es; Env; N] with
   | Some r => ask k "kl:buri.eval-args-rest" [enc v; r] | None => None end
 | _ => Some (enc_verdict w) end.
Proof. intros; unf d_eval_args_first_lk; destruct w; calls. Qed.
Lemma args_rest : forall v a,
 ask (S k) "kl:buri.eval-args-rest" [enc v; enc_args a] =
 Some (enc_args (match a with AVals vs => AVals (v :: vs) | AFail w => AFail w end)).
Proof. intros; unf d_eval_args_rest_lk; destruct a as [vs|[]]; calls. Qed.
Lemma primitive_args : forall a op,
 ask (S k) "kl:buri.eval-primitive" [enc_args a; Symbol op] =
 match a with AVals vs => ask k "kl:buri.primitive" [Symbol op; L (map enc vs)]
 | AFail w => Some (enc_verdict w) end.
Proof. intros; unf d_eval_primitive_lk; destruct a as [vs|[]]; calls. Qed.
Lemma raise_verdict : forall w,
 ask (S k) "kl:buri.eval-raise" [enc_verdict w] =
 match w with
 | WRet (RStr s) => Some (enc_verdict (WRaise s))
 | WRet _ => Some (enc_verdict (WRaise "error-message-not-string"))
 | _ => Some (enc_verdict w) end.
Proof. intros; unf d_eval_raise_lk; destruct w as [[]| | |]; calls. Qed.
Lemma trap_verdict : forall w H Env N,
 ask (S k) "kl:buri.eval-trap" [enc_verdict w; D; H; Env; N] =
 match w with
 | WRaise m => match ask k "kl:buri.eval" [D; H; Env; N] with
   | Some v => ask k "kl:buri.eval-handler" [v; D; Text m; N] | None => None end
 | _ => Some (enc_verdict w) end.
Proof. intros; unf d_eval_trap_lk; destruct w; calls. Qed.
Lemma handler_verdict : forall w m N,
 ask (S k) "kl:buri.eval-handler" [enc_verdict w; D; Text m; N] =
 match w with WRet h => ask k "kl:buri.apply-value" [D; enc h; enc (RStr m); N]
 | _ => Some (enc_verdict w) end.
Proof. intros; unf d_eval_handler_lk; destruct w; calls. Qed.
End Helpers.
End KLambdaEvaluatorEquations.
