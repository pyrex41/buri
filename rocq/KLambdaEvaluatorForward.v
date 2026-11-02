(* E2E-07 completeness support: forward (termination) equations for the
   captured shen/klambda.shen helpers under the fuel-free oracle semantics.
   Each states that, with enough oracle fuel, a captured body returns a named
   value; together with KLambdaEvaluatorEquations/Global (whose equations are
   already forward) they let KLambdaEvaluatorComplete construct the
   evaluator's answer. Every lemma unfolds one captured body once and reduces
   it with the VM; callee results are supplied by rewriting single sites. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native EqualityInductionOracle KLambdaEvaluatorCapture KLambdaEvaluatorPrimitives
 KLambdaEvaluatorGlobal.
Import ListNotations Native.Native.
Module KLambdaEvaluatorForward.
Import KLambdaEvaluatorCapture.KLambdaEvaluatorCapture.
Module Pr := KLambdaEvaluatorPrimitives.KLambdaEvaluatorPrimitives.
Module G := KLambdaEvaluatorGlobal.KLambdaEvaluatorGlobal.
Open Scope string_scope.

(* More oracle fuel never changes an answer. *)
Lemma ask_mono : forall j k s vs v, j <= k -> ask j s vs = Some v -> ask k s vs = Some v.
Proof. intros j k s vs v L H. exact (O.oracle_mono program defined j k L s vs v H). Qed.

Ltac unf lk := rewrite (ask_unfold _ _ _ _ lk);
 match goal with |- context [O.step _ (ask ?j) _ _] => remember (ask j) as rec eqn:R end.
Ltac calls := vm_compute; repeat match goal with |- context [match ?r ?f ?a with _ => _ end] =>
 is_var r; destruct (r f a) end; vm_compute; reflexivity.

Lemma fwd_equal : forall k a b, ask (S k) "kl:=" [a; b] = Some (Boolean (same a b)).
Proof. intros. rewrite (ask_unfold _ _ _ _ d_equal_lk). generalize (ask k); intro rec. reflexivity. Qed.
Lemma fwd_assert : forall k b, ask (S k) "kl:_scm.assert-boolean" [Boolean b] = Some (Boolean b).
Proof. intros. rewrite (ask_unfold _ _ _ _ d_assert_lk). generalize (ask k); intro rec. destruct b; reflexivity. Qed.
(* Replace one abstract kl:= site (rec = ask (S _)) by its value. *)
Ltac fweq R := match goal with |- context [?rec "kl:=" [?a; ?b]] => is_var rec;
 replace (rec "kl:=" [a; b]) with (Some (Boolean (same a b))) by (rewrite R; symmetry; apply fwd_equal) end.

Lemma fwd_get : forall rho x k, S (List.length rho) <= k ->
 ask (S k) "kl:buri.get" [Symbol x; enc_env rho] =
 Some (match assoc x rho with Some v => L [Symbol "found"; enc v] | None => Symbol "missing" end).
Proof.
 induction rho as [|[y v] rho IH]; intros x k HL.
 - unf d_get_lk. vm_compute. reflexivity.
 - destruct k as [|k]; [cbn in HL; lia|]. unf d_get_lk. cbn [assoc].
   change (enc_env ((y, v) :: rho)) with (Pair (L [Symbol y; enc v]) (enc_env rho)).
   destruct (String.eqb x y) eqn:Exy; cbn beta iota;
   remember (enc v) as V eqn:EV; remember (enc_env rho) as EE eqn:EEE.
   + vm_compute. fweq R. change (same (Symbol x) (Symbol y)) with (String.eqb x y). rewrite Exy.
     vm_compute. reflexivity.
   + remember (match assoc x rho with Some v => L [Symbol "found"; enc v] | None => Symbol "missing" end) as M eqn:EM.
     vm_compute. fweq R. change (same (Symbol x) (Symbol y)) with (String.eqb x y). rewrite Exy.
     vm_compute. rewrite R. subst EE M. apply IH. cbn in HL. lia.
Qed.
Lemma fwd_definition : forall ds x k, S (List.length ds) <= k ->
 ask (S k) "kl:buri.definition" [Symbol x; G.enc_defs ds] = Some (G.enc_found (G.find_def x ds)).
Proof.
 induction ds as [|[[n ps] b] ds IH]; intros x k HL.
 - unf d_definition_lk. vm_compute. reflexivity.
 - destruct k as [|k]; [cbn in HL; lia|]. unf d_definition_lk. cbn [G.find_def].
   change (G.enc_defs ((n, ps, b) :: ds)) with (L (L [Symbol n; L (map Symbol ps); enc_term b] :: map G.enc_def ds)).
   remember (L (map Symbol ps)) as PS eqn:EPS; remember (enc_term b) as B eqn:EB;
   remember (map G.enc_def ds) as DS eqn:EDS.
   destruct (String.eqb x n) eqn:Exn.
   + cbn [G.enc_found]. rewrite <- EPS, <- EB.
     vm_compute. fweq R. change (same (Symbol x) (Symbol n)) with (String.eqb x n). rewrite Exn.
     vm_compute. reflexivity.
   + remember (G.enc_found (G.find_def x ds)) as M eqn:EM.
     vm_compute. fweq R. change (same (Symbol x) (Symbol n)) with (String.eqb x n). rewrite Exn.
     vm_compute. rewrite R. subst DS M. apply (IH x k). cbn in HL. lia.
Qed.
Lemma fwd_append : forall xs ys k, S (List.length xs) <= k ->
 ask (S k) "kl:buri.append" [L (map enc xs); L (map enc ys)] = Some (L (map enc (xs ++ ys))).
Proof.
 induction xs as [|x xs IH]; intros ys k HL.
 - unf d_append_lk. remember (L (map enc ys)) as YS eqn:EY. vm_compute. subst YS. reflexivity.
 - destruct k as [|k]; [cbn in HL; lia|]. unf d_append_lk.
   change (L (map enc (x :: xs))) with (Pair (enc x) (L (map enc xs))).
   remember (enc x) as X; remember (L (map enc xs)) as XS eqn:EXS; remember (L (map enc ys)) as YS eqn:EYS.
   vm_compute. rewrite R. subst XS YS X. rewrite (IH ys k) by (cbn in HL; lia). reflexivity.
Qed.
Lemma fwd_fewer : forall (xs ys : list value) k, S (List.length xs) <= k ->
 ask (S k) "kl:buri.fewer?" [L xs; L ys] = Some (Boolean (Nat.ltb (List.length xs) (List.length ys))).
Proof.
 induction xs as [|x xs IH]; intros ys k HL; destruct ys as [|y ys].
 - unf d_fewer_lk. vm_compute. reflexivity.
 - unf d_fewer_lk. change (L (y :: ys)) with (Pair y (L ys)). remember (L ys) as YS. vm_compute. reflexivity.
 - unf d_fewer_lk. change (L (x :: xs)) with (Pair x (L xs)). remember (L xs) as XS. vm_compute. reflexivity.
 - destruct k as [|k]; [cbn in HL; lia|]. unf d_fewer_lk.
   change (L (x :: xs)) with (Pair x (L xs)). change (L (y :: ys)) with (Pair y (L ys)).
   remember (L xs) as XS eqn:EX; remember (L ys) as YS eqn:EY. vm_compute.
   rewrite R. subst XS YS. apply IH. cbn in HL. lia.
Qed.
Lemma fwd_zip_h : forall k X Y o, ask (S k) "kl:buri.zip-h" [X; Y; G.enc_zip o] =
 Some (match o with Some env => L [Symbol "zipped"; Pair (L [X; Y]) (enc_env env)] | None => Symbol "mismatch" end).
Proof.
 intros k X Y o. rewrite (ask_unfold _ _ _ _ d_zip_h_lk). generalize (ask k); intro rec.
 destruct o as [env|].
 - change (G.enc_zip (Some env)) with (L [Symbol "zipped"; enc_env env]).
   remember (enc_env env) as EV. vm_compute. reflexivity.
 - vm_compute. reflexivity.
Qed.
Lemma fwd_zip : forall ps args k, S (List.length ps) <= k ->
 ask (S k) "kl:buri.zip" [L (map Symbol ps); L (map enc args)] = Some (G.enc_zip (G.zipb ps args)).
Proof.
 induction ps as [|p ps IH]; intros args k HL; destruct args as [|a args].
 - unf d_zip_lk. vm_compute. reflexivity.
 - unf d_zip_lk. change (L (map enc (a :: args))) with (Pair (enc a) (L (map enc args))).
   remember (enc a) as A; remember (L (map enc args)) as AS. vm_compute. reflexivity.
 - unf d_zip_lk. change (L (map Symbol (p :: ps))) with (Pair (Symbol p) (L (map Symbol ps))).
   remember (L (map Symbol ps)) as PS. vm_compute. reflexivity.
 - destruct k as [|k]; [cbn in HL; lia|]. unf d_zip_lk.
   assert (Z : rec "kl:buri.zip" [L (map Symbol ps); L (map enc args)] = Some (G.enc_zip (G.zipb ps args)))
     by (rewrite R; apply IH; cbn in HL; lia).
   assert (ZH : forall X Y o, rec "kl:buri.zip-h" [X; Y; G.enc_zip o] =
     Some (match o with Some env => L [Symbol "zipped"; Pair (L [X; Y]) (enc_env env)] | None => Symbol "mismatch" end))
     by (intros; rewrite R; destruct k as [|k]; [cbn in HL; lia|]; apply fwd_zip_h).
   clear R IH. cbn [G.zipb].
   remember (G.enc_zip (option_map (cons (p, a)) (G.zipb ps args))) as RHS eqn:ER.
   change (L (map Symbol (p :: ps))) with (Pair (Symbol p) (L (map Symbol ps))).
   change (L (map enc (a :: args))) with (Pair (enc a) (L (map enc args))).
   remember (enc a) as A eqn:EA; remember (L (map enc args)) as AS eqn:EAS;
   remember (L (map Symbol ps)) as PS eqn:EPS. vm_compute. subst PS AS. rewrite Z.
   remember (G.enc_zip (G.zipb ps args)) as ZR eqn:EZR. vm_compute. subst ZR. rewrite ZH.
   subst RHS A. destruct (G.zipb ps args) as [l|]; cbn [G.enc_zip option_map];
   [change (enc_env ((p, a) :: l)) with (Pair (L [Symbol p; enc a]) (enc_env l))|]; reflexivity.
Qed.

(* ---------- equality ---------- *)
Lemma fwd_fnv : forall k a, ask (S k) "kl:buri.function-value?" [enc a] = Some (Boolean (Pr.fnv a)).
Proof. intros k a. rewrite (ask_unfold _ _ _ _ d_fnv_lk). generalize (ask k); intro rec. destruct a; vm_compute; reflexivity. Qed.
Lemma fwd_equal_leaf : forall k x y A B, ask (S (S k)) "kl:buri.equal-leaf" [Boolean x; Boolean y; A; B] =
 Some (if x then (if y then Symbol "unsupported" else Boolean false)
       else if y then Boolean false else Boolean (same A B)).
Proof.
 intros k x y A B. unf d_equal_leaf_lk. destruct x, y; vm_compute; repeat fweq R; vm_compute; reflexivity.
Qed.
Lemma fwd_equal_pair : forall k u A B, ask (S (S k)) "kl:buri.equal-pair" [u; A; B] =
 match u with Boolean true => ask (S k) "kl:buri.equal" [A; B] | _ => Some u end.
Proof.
 intros k u A B. rewrite (ask_unfold _ _ _ _ d_equal_pair_lk).
 pose proof (fwd_equal k) as EQ. revert EQ. generalize (ask (S k)) as rec. intros rec EQ.
 destruct u as [| | | | | | [|] | | |]; vm_compute; rewrite ?EQ; vm_compute; reflexivity.
Qed.
Fixpoint eq_bound (a : rv) : nat := match a with RPair a1 a2 => 3 + eq_bound a1 + eq_bound a2 | _ => 3 end.
(* The leaf clause of buri.equal: both function-value? sites, then equal-leaf.
   The callee oracle is a generalized variable rec with the needed facts FN
   and LF, so no proof term mentions an unfolded oracle. *)
Ltac leaf FN LF A0 B0 :=
 match goal with |- context [?rec "kl:buri.function-value?" [?v]] => is_var rec;
   replace (rec "kl:buri.function-value?" [v]) with (Some (Native.Boolean (Pr.fnv A0)))
     by (subst; symmetry; exact (FN A0)) end;
 vm_compute;
 match goal with |- context [?rec "kl:buri.function-value?" [?v]] => is_var rec;
   replace (rec "kl:buri.function-value?" [v]) with (Some (Native.Boolean (Pr.fnv B0)))
     by (subst; symmetry; exact (FN B0)) end;
 match goal with |- context [?rec "kl:buri.equal-leaf" [Native.Boolean ?x; Native.Boolean ?y; ?V1; ?V2]] => is_var rec;
   rewrite (LF x y V1 V2) end.
Lemma fwd_equal_rv : forall a b k, eq_bound a <= k ->
 ask k "kl:buri.equal" [enc a; enc b] = Some (Pr.eqr (Pr.eqv a b)).
Proof.
 induction a as [z|bb|st|sy| |a1 IH1 a2 IH2|x e env|f args|e env]; intros b0 k HL;
 (destruct k as [|k]; [cbn in HL; lia|]); (destruct k as [|k]; [cbn in HL; lia|]);
 (destruct k as [|k]; [cbn in HL; lia|]);
 rewrite (ask_unfold _ _ _ _ d_equal_fn_lk);
 pose proof (fwd_fnv (S k)) as FN; pose proof (fwd_equal_leaf k) as LF; pose proof (fwd_equal_pair k) as PR.
 6: { change (enc (RPair a1 a2)) with (L [Symbol "pair"; enc a1; enc a2]).
      destruct b0 as [z0|bb0|st0|sy0| |b1 b2|x0 e0 env0|f0 args0|e0 env0].
      6: { change (enc (RPair b1 b2)) with (L [Symbol "pair"; enc b1; enc b2]).
           assert (I1 : ask (S (S k)) "kl:buri.equal" [enc a1; enc b1] = Some (Pr.eqr (Pr.eqv a1 b1)))
             by (apply IH1; cbn in HL; lia).
           assert (I2 : ask (S k) "kl:buri.equal" [enc a2; enc b2] = Some (Pr.eqr (Pr.eqv a2 b2)))
             by (apply IH2; cbn in HL; lia).
           remember (Pr.eqr (Pr.eqv (RPair a1 a2) (RPair b1 b2))) as RHS eqn:ERHS.
           remember (enc a1) as A1 eqn:EA1; remember (enc a2) as A2 eqn:EA2.
           remember (enc b1) as B1 eqn:EB1; remember (enc b2) as B2 eqn:EB2.
           clear FN LF. revert I1 PR. generalize (ask (S (S k))) as rec. intros rec I1 PR.
           vm_compute. rewrite I1, PR. subst RHS.
           cbn [Pr.eqv]. destruct (Pr.eqv a1 b1) as [[|]|]; cbn [Pr.eqr]; try reflexivity.
           exact I2. }
      all: clear PR; revert FN LF; generalize (ask (S (S k))) as rec; intros rec FN LF.
      all: match goal with |- _ = Some (Pr.eqr (Pr.eqv ?A0 ?B0)) =>
        remember (Pr.eqr (Pr.eqv A0 B0)) as RHS eqn:ERHS;
        remember (enc a1) as A1 eqn:EA1; remember (enc a2) as A2 eqn:EA2;
        vm_compute; leaf FN LF A0 B0; subst; try destruct b0; reflexivity end. }
 all: clear PR; revert FN LF; generalize (ask (S (S k))) as rec; intros rec FN LF.
 all: match goal with |- _ = Some (Pr.eqr (Pr.eqv ?A0 ?B0)) =>
   remember (Pr.eqr (Pr.eqv A0 B0)) as RHS eqn:ERHS; remember (enc B0) as B eqn:EB;
   vm_compute; leaf FN LF A0 B0; subst; try destruct b0; reflexivity end.
Qed.
Lemma fwd_eq_verdict : forall k o, ask (S k) "kl:buri.equality-verdict" [Pr.eqr o] =
 Some (enc_verdict (match o with Some x => WRet (RBool x) | None => WUnsupported end)).
Proof. intros k o. rewrite (ask_unfold _ _ _ _ d_eq_verdict_lk). generalize (ask k); intro rec. destruct o as [[|]|]; reflexivity. Qed.
Lemma fwd_prim_equal : forall a b k, S (eq_bound a) <= k ->
 ask (S k) "kl:buri.primitive" [Symbol "="; L [enc a; enc b]] = Some (enc_verdict (Pr.eq_spec a b)).
Proof.
 intros a b k HL. unf d_primitive_lk. remember (enc a) as A eqn:EA; remember (enc b) as B eqn:EB.
 vm_compute. replace (rec "kl:buri.equal" [A; B]) with (Some (Pr.eqr (Pr.eqv a b)))
   by (rewrite R, EA, EB; symmetry; apply fwd_equal_rv; lia).
 destruct k as [|k]; [lia|]. rewrite R, fwd_eq_verdict. reflexivity.
Qed.
Lemma fwd_prim2 : forall k op a b, In op ["+"; "-"; "*"; "<"; "cons"] ->
 ask (S k) "kl:buri.primitive" [Symbol op; L [enc a; enc b]] = Some (enc_verdict (Pr.prim_spec op [a; b])).
Proof.
 intros k op a b I. rewrite (ask_unfold _ _ _ _ d_primitive_lk). generalize (ask k); intro rec.
 cbn [In] in I. destruct I as [<-|[<-|[<-|[<-|[<-|[]]]]]]; destruct a, b; vm_compute; reflexivity.
Qed.
Lemma fwd_prim1 : forall k op a, In op ["hd"; "tl"; "cons?"; "number?"; "string?"] ->
 ask (S k) "kl:buri.primitive" [Symbol op; L [enc a]] = Some (enc_verdict (Pr.prim_spec op [a])).
Proof.
 intros k op a I. rewrite (ask_unfold _ _ _ _ d_primitive_lk). generalize (ask k); intro rec.
 cbn [In] in I. destruct I as [<-|[<-|[<-|[<-|[<-|[]]]]]]; destruct a; vm_compute; reflexivity.
Qed.

(* ---------- buri.eval-if, [global X], buri.apply-global ---------- *)
Lemma fwd_if : forall k w D a b Env N, ask (S (S k)) "kl:buri.eval-if" [enc_verdict w; D; a; b; Env; N] =
 match w with
 | WRet (RBool true) => ask (S k) "kl:buri.eval" [D; a; Env; N]
 | WRet (RBool false) => ask (S k) "kl:buri.eval" [D; b; Env; N]
 | WRet _ => Some (enc_verdict (WRaise "nonboolean-condition"))
 | _ => Some (enc_verdict w) end.
Proof.
 intros k w D a b Env N. rewrite (ask_unfold _ _ _ _ d_eval_if_lk).
 pose proof (fwd_equal k) as EQ. revert EQ. generalize (ask (S k)) as rec. intros rec EQ.
 destruct w as [[| [|] | | | | | | |]| | |]; vm_compute; repeat (rewrite EQ; vm_compute); reflexivity.
Qed.
Lemma fwd_eval_global : forall k D env z x o, ask k "kl:buri.definition" [Symbol x; D] = Some (G.enc_found o) ->
 ask (S k) "kl:buri.eval" [D; enc_term (TGlobal x); enc_env env; Integer z] =
 Some (G.gate_value z (match o with None => enc_verdict (WRaise "unbound-function")
   | Some _ => enc_verdict (WRet (RFunction x [])) end)).
Proof.
 intros k D env z x o DF. rewrite (ask_unfold _ _ _ _ d_eval_lk). remember (ask k) as rec eqn:R.
 remember (enc_env env) as EV. destruct z as [|p|p]; vm_compute; [reflexivity|..];
 rewrite DF; destruct o as [[ps b]|]; vm_compute; reflexivity.
Qed.
Lemma fwd_apply_global : forall k D ps b f args N, S (S (List.length args)) <= k ->
 ask (S k) "kl:buri.apply-global" [D; G.enc_found (Some (ps, b)); Symbol f; L (map enc args); N] =
 if Nat.ltb (List.length args) (List.length ps) then Some (enc_verdict (WRet (RFunction f args)))
 else match ask k "kl:buri.zip" [L (map Symbol ps); L (map enc args)] with
   | Some zr => ask k "kl:buri.apply-bound" [D; enc_term b; zr; N] | None => None end.
Proof.
 intros k D ps b f args N HL. destruct k as [|k]; [lia|]. rewrite (ask_unfold _ _ _ _ d_apply_global_lk).
 pose proof (fwd_fewer (map enc args) (map Symbol ps) k ltac:(rewrite map_length; lia)) as FW.
 pose proof (fwd_assert k) as AB. rewrite !map_length in FW.
 revert FW AB. generalize (ask (S k)) as rec. intros rec FW AB.
 destruct (Nat.ltb (List.length args) (List.length ps));
 (match goal with |- _ = ?r => remember r as RHS eqn:ERHS end;
  change (G.enc_found (Some (ps, b))) with (L [Symbol "definition"; L (map Symbol ps); enc_term b]);
  remember (L (map Symbol ps)) as PS eqn:EPS; remember (enc_term b) as B eqn:EB;
  remember (L (map enc args)) as AS eqn:EAS; vm_compute; rewrite FW; vm_compute; rewrite AB; vm_compute;
  subst; try reflexivity; destruct (rec "kl:buri.zip" _); reflexivity).
Qed.
End KLambdaEvaluatorForward.
