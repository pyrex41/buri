(* E2E-07 (globals, function values, freeze/thaw): one equation per captured
   shen/klambda.shen body and input shape that KLambdaEvaluatorEquations does
   not cover, about the fuel-free oracle semantics of the captured program
   (KLambdaEvaluatorCapture). The definition table is the evaluator's own
   [[Name Params Body] ...] list (enc_defs). Each lemma unfolds one captured
   body once with the callee oracle abstracted, and reduces it with the VM. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native KLambdaEvaluatorCapture.
Import ListNotations Native.Native.
Module KLambdaEvaluatorGlobal.
Import KLambdaEvaluatorCapture.KLambdaEvaluatorCapture.
Open Scope string_scope.

Ltac unf lk := rewrite (ask_unfold _ _ _ _ lk);
 match goal with |- context [O.step _ (ask ?j) _ _] => generalize (ask j) as rec; intro rec end.
Ltac calls := vm_compute; repeat match goal with |- context [match ?r ?f ?a with _ => _ end] =>
 is_var r; destruct (r f a) end; vm_compute; reflexivity.
(* Destruct the result of one abstract callee in hypothesis H (R : rec = ask k). *)
Ltac site R H f := match type of H with context [?rec f ?xs] => is_var rec;
 let E := fresh "E" in let u := fresh "u" in destruct (rec f xs) as [u|] eqn:E;
 [rewrite R in E|vm_compute in H; discriminate] end.
Ltac eqsite R H := site R H constr:("kl:=");
 match goal with E : ask _ "kl:=" _ = Some ?u |- _ => apply ask_equal in E; subst u; vm_compute in H end.

(* ---------- the evaluator's definition table ---------- *)
Definition defn := (string * list string * term)%type.
Definition enc_def (d : defn) : value := match d with (n, ps, b) => L [Symbol n; L (map Symbol ps); enc_term b] end.
Definition enc_defs (ds : list defn) : value := L (map enc_def ds).
Fixpoint find_def (x : string) (ds : list defn) : option (list string * term) := match ds with
 | [] => None
 | (n, ps, b) :: ds => if String.eqb x n then Some (ps, b) else find_def x ds end.
Definition enc_found (o : option (list string * term)) : value := match o with
 | Some (ps, b) => L [Symbol "definition"; L (map Symbol ps); enc_term b]
 | None => Symbol "missing" end.

Lemma ask_definition : forall k x ds r, ask k "kl:buri.definition" [Symbol x; enc_defs ds] = Some r ->
 r = enc_found (find_def x ds).
Proof.
 induction k as [|k IH]; intros x ds r H; [discriminate|].
 rewrite (ask_unfold _ _ _ _ d_definition_lk) in H. remember (ask k) as rec eqn:R.
 destruct ds as [|[[n ps] b] ds].
 - vm_compute in H. injection H as <-. reflexivity.
 - change (enc_defs ((n, ps, b) :: ds)) with (L (L [Symbol n; L (map Symbol ps); enc_term b] :: map enc_def ds)) in H.
   remember (L (map Symbol ps)) as PS eqn:EPS; remember (enc_term b) as B eqn:EB.
   remember (map enc_def ds) as DS eqn:EDS. vm_compute in H. site R H constr:("kl:=").
   apply ask_equal in E. subst u. change (same (Symbol x) (Symbol n)) with (String.eqb x n) in H.
   cbn [find_def]. destruct (String.eqb x n); vm_compute in H.
   + injection H as <-. subst PS B. reflexivity.
   + destruct (rec "kl:buri.definition" _) as [u|] eqn:E; [|discriminate]. injection H as <-.
     subst DS. apply (IH x ds u). exact E.
Qed.

(* ---------- runtime list helpers (base.shen, kernel.shen, klambda.shen) ---------- *)
Lemma ask_append : forall k xs ys r, ask k "kl:buri.append" [L (map enc xs); L (map enc ys)] = Some r ->
 r = L (map enc (xs ++ ys)).
Proof.
 induction k as [|k IH]; intros xs ys r H; [discriminate|].
 rewrite (ask_unfold _ _ _ _ d_append_lk) in H. remember (ask k) as rec eqn:R in H.
 destruct xs as [|x xs].
 - remember (L (map enc ys)) as YS eqn:EY. vm_compute in H. injection H as <-. exact EY.
 - change (L (map enc (x :: xs))) with (Pair (enc x) (L (map enc xs))) in H.
   remember (enc x) as X eqn:EX; remember (L (map enc xs)) as XS eqn:EXS; remember (L (map enc ys)) as YS eqn:EY.
   vm_compute in H. destruct (rec "kl:buri.append" [XS; YS]) as [u|] eqn:E; [|discriminate].
   injection H as <-. rewrite R in E. subst XS YS. apply IH in E. subst u X. reflexivity.
Qed.
Lemma ask_fewer : forall k (xs : list value) (ys : list value) u, ask k "kl:buri.fewer?" [L xs; L ys] = Some u ->
 u = Boolean (Nat.ltb (List.length xs) (List.length ys)).
Proof.
 induction k as [|k IH]; intros xs ys u H; [discriminate|].
 rewrite (ask_unfold _ _ _ _ d_fewer_lk) in H. remember (ask k) as rec eqn:R in H.
 destruct xs as [|x xs]; destruct ys as [|y ys].
 - vm_compute in H. injection H as <-. reflexivity.
 - change (L (y :: ys)) with (Pair y (L ys)) in H. remember (L ys) as YS. vm_compute in H.
   injection H as <-. reflexivity.
 - change (L (x :: xs)) with (Pair x (L xs)) in H. remember (L xs) as XS. vm_compute in H.
   injection H as <-. reflexivity.
 - change (L (x :: xs)) with (Pair x (L xs)) in H. change (L (y :: ys)) with (Pair y (L ys)) in H.
   remember (L xs) as XS eqn:EX; remember (L ys) as YS eqn:EY. vm_compute in H.
   rewrite R, EX, EY in H. apply IH in H. exact H.
Qed.
Fixpoint zipb (ps : list string) (args : list rv) : option (list (string * rv)) := match ps, args with
 | [], [] => Some []
 | p :: ps, a :: args => option_map (cons (p, a)) (zipb ps args)
 | _, _ => None end.
Definition enc_zip (o : option (list (string * rv))) : value := match o with
 | Some env => L [Symbol "zipped"; enc_env env] | None => Symbol "mismatch" end.
Lemma zipb_combine : forall ps args, List.length ps = List.length args -> zipb ps args = Some (combine ps args).
Proof.
 induction ps as [|p ps IH]; intros [|a args] L; cbn in L |- *; try discriminate; [reflexivity|].
 rewrite IH by lia. reflexivity.
Qed.
Lemma ask_zip_h : forall k X Y o r, ask k "kl:buri.zip-h" [X; Y; enc_zip o] = Some r ->
 r = match o with Some env => L [Symbol "zipped"; Pair (L [X; Y]) (enc_env env)] | None => Symbol "mismatch" end.
Proof.
 intros [|k] X Y o r H; [discriminate|]. rewrite (ask_unfold _ _ _ _ d_zip_h_lk) in H.
 generalize dependent H; generalize (ask k) as rec; intros rec H.
 destruct o as [env|].
 - change (enc_zip (Some env)) with (L [Symbol "zipped"; enc_env env]) in H.
   remember (enc_env env) as EV. vm_compute in H. injection H as <-. reflexivity.
 - vm_compute in H. injection H as <-. reflexivity.
Qed.
Lemma ask_zip : forall k ps args r, ask k "kl:buri.zip" [L (map Symbol ps); L (map enc args)] = Some r ->
 r = enc_zip (zipb ps args).
Proof.
 induction k as [|k IH]; intros ps args r H; [discriminate|].
 rewrite (ask_unfold _ _ _ _ d_zip_lk) in H. remember (ask k) as rec eqn:R in H.
 destruct ps as [|p ps]; destruct args as [|a args].
 - vm_compute in H. injection H as <-. reflexivity.
 - change (L (map enc (a :: args))) with (Pair (enc a) (L (map enc args))) in H.
   remember (enc a) as A; remember (L (map enc args)) as AS. vm_compute in H. injection H as <-. reflexivity.
 - change (L (map Symbol (p :: ps))) with (Pair (Symbol p) (L (map Symbol ps))) in H.
   remember (L (map Symbol ps)) as PS. vm_compute in H. injection H as <-. reflexivity.
 - change (L (map Symbol (p :: ps))) with (Pair (Symbol p) (L (map Symbol ps))) in H.
   change (L (map enc (a :: args))) with (Pair (enc a) (L (map enc args))) in H.
   remember (enc a) as A eqn:EA; remember (L (map enc args)) as AS eqn:EAS;
   remember (L (map Symbol ps)) as PS eqn:EPS. vm_compute in H.
   destruct (rec "kl:buri.zip" [PS; AS]) as [u|] eqn:E; [|discriminate].
   rewrite R, EPS, EAS in E. apply IH in E. subst u. rewrite R in H. apply ask_zip_h in H. subst r A.
   cbn [zipb]. destruct (zipb ps args); reflexivity.
Qed.

(* ---------- buri.eval: [global X], [freeze E], [thaw E] ---------- *)
Definition gate_value (z : Z) (v : value) : value := if Z.eqb z 0 then enc_verdict WBudget else v.
Section Eval.
Variables (k : nat) (D : value) (env : list (string * rv)) (z : Z).
(* (= (buri.definition X D) missing) compiles to eq? against the symbol; the
   lookup result is the evaluator's own [definition Ps B] or missing. *)
Lemma eval_global : forall x r,
 ask (S k) "kl:buri.eval" [D; enc_term (TGlobal x); enc_env env; Integer z] = Some r ->
 (z = 0%Z /\ r = enc_verdict WBudget) \/ (exists v, ask k "kl:buri.definition" [Symbol x; D] = Some v /\
 forall o, v = enc_found o -> r = gate_value z (match o with None => enc_verdict (WRaise "unbound-function")
   | Some _ => enc_verdict (WRet (RFunction x [])) end)).
Proof.
 intros x r H. rewrite (ask_unfold _ _ _ _ d_eval_lk) in H. remember (ask k) as rec eqn:R in H.
 remember (enc_env env) as EV. destruct z as [|p|p];
 [left; split; [reflexivity|]; vm_compute in H; injection H as <-; reflexivity|..];
 (right; vm_compute in H; site R H constr:("kl:buri.definition");
  exists u; split; [exact E|]; intros o ->; destruct o as [[ps b]|];
  vm_compute in H; injection H as <-; reflexivity).
Qed.
Lemma eval_freeze : forall e, ask (S k) "kl:buri.eval" [D; enc_term (TFreeze e); enc_env env; Integer z] =
 gate z (Some (enc_verdict (WRet (RThunk e env)))).
Proof. intros; unf d_eval_lk; destruct z; calls. Qed.
Lemma eval_thaw : forall e, ask (S k) "kl:buri.eval" [D; enc_term (TThaw e); enc_env env; Integer z] =
 gate z (match ask k "kl:buri.eval" [D; enc_term e; enc_env env; Integer (z - 1)] with
   | Some v => ask k "kl:buri.eval-thaw" [v; D; Integer (z - 1)] | None => None end).
Proof. intros; unf d_eval_lk; destruct z; calls. Qed.
End Eval.

Section Helpers.
Variables (k : nat) (D : value).
(* buri.eval-thaw, one case per verdict and value shape. *)
Lemma thaw_verdict : forall w N, ask (S k) "kl:buri.eval-thaw" [enc_verdict w; D; N] =
 match w with
 | WRet (RThunk e env) => ask k "kl:buri.eval" [D; enc_term e; enc_env env; N]
 | WRet (RClosure _ _ _) => Some (enc_verdict (WRaise "arity"))
 | WRet (RFunction f prev) => match ask k "kl:buri.definition" [Symbol f; D] with
   | Some dv => ask k "kl:buri.apply-global" [D; dv; Symbol f; L (map enc prev); N] | None => None end
 | WRet _ => Some (enc_verdict (WRaise "not-callable"))
 | _ => Some (enc_verdict w) end.
Proof. intros; unf d_eval_thaw_lk; destruct w as [[]| | |]; calls. Qed.
(* buri.apply-value on a [function ...] value and on a thunk. *)
Lemma apply_value_function : forall f prev a z,
 ask (S k) "kl:buri.apply-value" [D; enc (RFunction f prev); enc a; Integer z] =
 gate z (match ask k "kl:buri.definition" [Symbol f; D] with
   | Some dv => match ask k "kl:buri.append" [L (map enc prev); L [enc a]] with
     | Some args => ask k "kl:buri.apply-global" [D; dv; Symbol f; args; Integer z] | None => None end
   | None => None end).
Proof. intros; unf d_apply_value_lk; destruct z; calls. Qed.
Lemma apply_value_thunk : forall e env a z,
 ask (S k) "kl:buri.apply-value" [D; enc (RThunk e env); enc a; Integer z] =
 gate z (Some (enc_verdict (WRaise "arity"))).
Proof. intros; unf d_apply_value_lk; destruct z; calls. Qed.
(* buri.apply-global: a found definition curries while too few arguments are
   supplied, otherwise binds the parameters (buri.zip) and evaluates the body. *)
Lemma apply_global_found : forall ps b f args N r,
 ask (S k) "kl:buri.apply-global" [D; enc_found (Some (ps, b)); Symbol f; L (map enc args); N] = Some r ->
 (Nat.ltb (List.length args) (List.length ps) = true /\ r = enc_verdict (WRet (RFunction f args))) \/
 (Nat.ltb (List.length args) (List.length ps) = false /\ exists zr,
   ask k "kl:buri.zip" [L (map Symbol ps); L (map enc args)] = Some zr /\
   ask k "kl:buri.apply-bound" [D; enc_term b; zr; N] = Some r).
Proof.
 intros ps b f args N r H. rewrite (ask_unfold _ _ _ _ d_apply_global_lk) in H. remember (ask k) as rec eqn:R in H.
 change (enc_found (Some (ps, b))) with (L [Symbol "definition"; L (map Symbol ps); enc_term b]) in H.
 remember (L (map Symbol ps)) as PS eqn:EPS; remember (enc_term b) as B eqn:EB;
 remember (L (map enc args)) as AS eqn:EAS. vm_compute in H.
 site R H constr:("kl:buri.fewer?"). rewrite EAS, EPS in E. apply ask_fewer in E. subst u.
 rewrite !map_length in *. destruct (Nat.ltb (List.length args) (List.length ps)) eqn:LT; vm_compute in H;
 site R H constr:("kl:_scm.assert-boolean"); apply ask_assert in E; destruct E as (bb & EB0 & ->);
 injection EB0 as <-; vm_compute in H.
 - left; split; [reflexivity|]. injection H as <-. subst AS. reflexivity.
 - right; split; [reflexivity|].
   destruct (rec "kl:buri.zip" [PS; AS]) as [zr|] eqn:Z; [|discriminate].
   exists zr; split; [rewrite R in Z; subst PS AS; exact Z|]. rewrite R in H. subst B. exact H.
Qed.
Lemma apply_global_missing : forall f args N,
 ask (S k) "kl:buri.apply-global" [D; enc_found None; Symbol f; args; N] =
 Some (enc_verdict (WRaise "unbound-function")).
Proof. intros; unf d_apply_global_lk; calls. Qed.
Lemma apply_bound_zipped : forall b env z,
 ask (S k) "kl:buri.apply-bound" [D; enc_term b; enc_zip (Some env); Integer z] =
 ask k "kl:buri.eval" [D; enc_term b; enc_env env; Integer (z - 1)].
Proof. intros; unf d_apply_bound_lk; calls. Qed.
End Helpers.
End KLambdaEvaluatorGlobal.
