(* BURI/EQ-1, obligation EQ1-DRIVERS: the captured KLambda drivers of
   shen/kernel.shen (decoded from ports/eq1-kernel.bits) compute the
   reference kernel of EqualityInductionKernel, for all inputs (partial
   correctness under the Native evaluator), and so the code that runs
   inherits check_bundle_sound. The trap-error guard of check-bundle is
   modelled by an explicit stated contract ([guard_model], EQ1-GUARD); the
   Chez-to-Native gap is not addressed here. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native NativeSimulation EqualityInductionOracle EqualityInductionModel
 EqualityInductionSpecs EqualityInductionHelpers EqualityInductionKernel EqualityInductionDrivers.
Import ListNotations Native.Native.
Module EqualityInductionRefinement.
Module O := EqualityInductionOracle.EqualityInductionOracle.
Import EqualityInductionModel.EqualityInductionModel EqualityInductionSpecs.EqualityInductionSpecs
 EqualityInductionHelpers.EqualityInductionHelpers EqualityInductionKernel.EqualityInductionKernel
 EqualityInductionDrivers.EqualityInductionDrivers.
Open Scope string_scope.

Lemma enter : forall k s vs w ps b, lookup program s = Some (Def ps b) -> agree defined kl b = true ->
 ask (S k) s vs = Some w -> O.step kl (ask k) (arguments ps vs) b = Some w.
Proof.
 intros k s vs w ps b L A H. rewrite (ask_unfold k s vs _ L) in H. cbn [params body] in H.
 destruct (Nat.eqb _ _); [|discriminate]. rewrite <- (step_agree defined kl (ask k) b _ A). exact H.
Qed.
Lemma ask_assert_id : forall k w u, ask k "kl:_scm.assert-boolean" [w] = Some u -> u = w.
Proof. intros k w u H. destruct (ask_assert _ _ _ H) as (b & -> & ->). reflexivity. Qed.

(* Every driver and numeric helper, at every oracle fuel. *)
Record drivers_ok k : Prop := {
 d_bundle : forall b ls n u, ask k "kl:buri.bundle-h" [b;ls;Integer n] = Some u -> u = r_bundle b ls n;
 d_next : forall res name C l r rest ls n u, ask k "kl:buri.bundle-next" [res;name;C;l;r;rest;ls;Integer n] = Some u ->
   u = next1 res name C l r rest ls n;
 d_goal : forall C l r u, ask k "kl:buri.goal?" [C;l;r] = Some u -> u = Boolean (r_goal C l r);
 d_theorem : forall C l r p ls n u, ask k "kl:buri.check-theorem" [C;l;r;p;ls;Integer n] = Some u -> u = r_theorem C l r p ls n;
 d_cases : forall ctors cases X C l r ls n u, ask k "kl:buri.check-cases" [ctors;cases;X;C;l;r;ls;Integer n] = Some u ->
   u = r_cases ctors cases X C l r ls n;
 d_bound : forall z ctor ctors cases names steps X C l r ls n u,
   ask k "kl:buri.check-case-bound" [z;ctor;ctors;cases;names;steps;X;C;l;r;ls;Integer n] = Some u ->
   u = bound1 z ctor ctors cases names steps X C l r ls n;
 d_steps : forall l r steps C hs ls n u, ask k "kl:buri.check-steps" [l;r;steps;C;hs;ls;Integer n] = Some u ->
   u = r_steps l r steps C hs ls n;
 d_csr : forall e path dir l r steps C hs ls n u,
   ask k "kl:buri.check-step-result" [e;path;dir;l;r;steps;C;hs;ls;Integer n] = Some u -> u = csr1 e path dir l r steps C hs ls n;
 d_after : forall x r steps C hs ls n u, ask k "kl:buri.after-rewrite" [x;r;steps;C;hs;ls;Integer n] = Some u ->
   u = after1 x r steps C hs ls n;
 d_inst : forall rl sub C u, ask k "kl:buri.instantiate" [rl;sub;C] = Some u -> u = r_inst rl sub C;
 d_substn : forall vars sub C u, ask k "kl:buri.substitution?" [vars;sub;C] = Some u -> u = Boolean (r_substitution vars sub C);
 d_replace : forall t p a b u, ask k "kl:buri.replace" [t;p;a;b] = Some u -> u = r_replace t p a b;
 d_rarg : forall args z is a b u, ask k "kl:buri.replace-arg" [args;Integer z;is;a;b] = Some u -> u = r_rarg args z is a b;
 d_str : forall z u, ask k "kl:str" [Integer z] = Some u -> u = Text (spelling z);
 d_digits : forall s u, ask k "kl:buri.digits?" [Text s] = Some u -> u = Boolean (alldig s);
 d_unsigned : forall s u, ask k "kl:buri.unsigned-spelling?" [Text s] = Some u -> u = Boolean (unsigned s);
 d_ispell : forall s u, ask k "kl:buri.integer-spelling?" [Text s] = Some u -> u = Boolean (ispell s);
 d_exact : forall z u, ask k "kl:buri.exact-integer?" [Integer z] = Some u -> u = Boolean (ispell (spelling z));
 d_nat : forall i u, ask k "kl:buri.nat?" [i] = Some u -> u = Boolean (match i with Integer z => Z.leb 0 z | _ => false end) }.

Lemma nat_exact : forall i, (match i with Integer z => Z.geb z 0 && ispell (spelling z) | _ => false end) =
 (match i with Integer z => Z.leb 0 z | _ => false end).
Proof.
 intros []; try reflexivity. rewrite Z.geb_leb. destruct (Z.leb 0 z) eqn:L; [|reflexivity].
 apply Z.leb_le in L. rewrite (spelling_ok _ L). reflexivity.
Qed.

Ltac facts k := pose proof (ask_eq k); pose proof (ask_assert_id k); pose proof (ask_not k); pose proof (ask_symbol k);
 pose proof (ask_theory k); pose proof (ask_rev k); pose proof (ask_rule k); pose proof (ask_ctx k); pose proof (ask_sort k);
 pose proof (ask_get k); pose proof (ask_allsym k); pose proof (ask_unique k); pose proof (ask_fresh k); pose proof (ask_keys k);
 pose proof (ask_zip k); pose proof (ask_remove k); pose proof (ask_append k); pose proof (ask_vars k); pose proof (ask_ihyps k);
 pose proof (ask_subst k); pose proof (ask_resolve k); pose proof (ask_rapp k); pose proof (ask_head k); pose proof (ask_tail k);
 pose proof (ask_member k).
Ltac drv lemma pX bX k H := let S := fresh "S" in
 pose proof (fun L A => enter k _ _ _ pX bX L A H) as S;
 specialize (S ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
 eapply (lemma (ask k)) in S; [exact S|assumption ..].

Theorem drivers : forall k, drivers_ok k.
Proof.
 induction k as [|k IH].
 { constructor; intros; discriminate. }
 destruct IH. facts k. constructor; intros until u; intro Hrun.
 - drv body_bundle p_bundle b_bundle k Hrun.
 - drv body_next p_next b_next k Hrun.
 - drv body_goal p_goal b_goal k Hrun.
 - drv body_theorem p_theorem b_theorem k Hrun.
 - drv body_cases p_cases b_cases k Hrun.
 - drv body_bound p_bound b_bound k Hrun.
 - drv body_steps p_steps b_steps k Hrun.
 - drv body_csr p_csr b_csr k Hrun.
 - drv body_after p_after b_after k Hrun.
 - drv body_inst p_inst b_inst k Hrun.
 - drv body_substn p_substn b_substn k Hrun.
 - drv body_replace p_replace b_replace k Hrun.
 - drv body_rarg p_rarg b_rarg k Hrun.
 - drv body_str p_str b_str k Hrun.
 - drv body_digits p_digits b_digits k Hrun.
 - drv body_unsigned p_unsigned b_unsigned k Hrun.
 - drv body_ispell p_ispell b_ispell k Hrun.
 - drv body_exact p_exact b_exact k Hrun.
 - rewrite <- (nat_exact i). drv body_nat p_nat b_nat k Hrun.
Qed.

(* The actual Native evaluator on the captured program. *)
Theorem native_bundle : forall n b ls z v, run n program "kl:buri.bundle-h" [b;ls;Integer z] = Returned v ->
 v = r_bundle b ls z.
Proof. intros. eapply (d_bundle _ (drivers (S n))). apply run_ask. eassumption. Qed.
Theorem native_steps : forall n l r steps C hs ls z v,
 run n program "kl:buri.check-steps" [l;r;steps;C;hs;ls;Integer z] = Returned v -> v = r_steps l r steps C hs ls z.
Proof. intros. eapply (d_steps _ (drivers (S n))). apply run_ask. eassumption. Qed.
Theorem native_theorem : forall n C l r p ls z v,
 run n program "kl:buri.check-theorem" [C;l;r;p;ls;Integer z] = Returned v -> v = r_theorem C l r p ls z.
Proof. intros. eapply (d_theorem _ (drivers (S n))). apply run_ask. eassumption. Qed.
Theorem native_cases : forall n ctors cases X C l r ls z v,
 run n program "kl:buri.check-cases" [ctors;cases;X;C;l;r;ls;Integer z] = Returned v -> v = r_cases ctors cases X C l r ls z.
Proof. intros. eapply (d_cases _ (drivers (S n))). apply run_ask. eassumption. Qed.
Theorem native_instantiate : forall n rl sub C v,
 run n program "kl:buri.instantiate" [rl;sub;C] = Returned v -> v = r_inst rl sub C.
Proof. intros. eapply (d_inst _ (drivers (S n))). apply run_ask. eassumption. Qed.
Theorem native_substitution : forall n vars sub C v,
 run n program "kl:buri.substitution?" [vars;sub;C] = Returned v -> v = Boolean (r_substitution vars sub C).
Proof. intros. eapply (d_substn _ (drivers (S n))). apply run_ask. eassumption. Qed.
Theorem native_replace : forall n t p a b v,
 run n program "kl:buri.replace" [t;p;a;b] = Returned v -> v = r_replace t p a b.
Proof. intros. eapply (d_replace _ (drivers (S n))). apply run_ask. eassumption. Qed.
Theorem native_goal : forall n C l r v, run n program "kl:buri.goal?" [C;l;r] = Returned v -> v = Boolean (r_goal C l r).
Proof. intros. eapply (d_goal _ (drivers (S n))). apply run_ask. eassumption. Qed.
Theorem native_nat : forall n i v, run n program "kl:buri.nat?" [i] = Returned v ->
 v = Boolean (match i with Integer z => Z.leb 0 z | _ => false end).
Proof. intros. eapply (d_nat _ (drivers (S n))). apply run_ask. eassumption. Qed.

(* Soundness of the code that runs: whatever the captured bundle-h accepts
   under the Native evaluator is valid in the standard model. *)
Theorem captured_bundle_sound : forall n B z out,
 run n program "kl:buri.bundle-h" [B;Nil;Integer z] = Returned (accepted out) -> all_ok out.
Proof.
 intros n B z out H. apply native_bundle in H.
 exact (bundle_sound _ _ _ _ (fun e (I : entry_in e Nil) => match I with end) (eq_sym H)).
Qed.

(* check-bundle. Its captured body is a guard (trap-error) whose handler is
   the literal [rejected malformed-evidence]; Native has no guard, so its
   meaning is the stated contract [guard_model] (EQ1-GUARD): a raised error
   becomes the handler's value, anything else passes through. *)
Theorem check_bundle_captured : lookup program "kl:buri.check-bundle" = Some (Def p_cb (Call "guard" [h_cb;g_cb])) /\
 p_cb = ["V5960";"V5961";"V5962"] /\
 h_cb = Call "Z5963" [Call "else" [Call "list" [Lit (Symbol "rejected");Lit (Symbol "malformed-evidence")]]].
Proof. split; [vm_compute; reflexivity|split; reflexivity]. Qed.
Definition guard_model (handler : value) (r : result) := match r with
 | Raised _ _ => Returned handler | other => other end.
Definition captured_check_bundle n T B N :=
 guard_model (rejected "malformed-evidence") (eval n (lookup program) (arguments p_cb [T;B;N]) g_cb).
Theorem native_guarded_body : forall n T B N v,
 eval n (lookup program) (arguments p_cb [T;B;N]) g_cb = Returned v -> v = r_check_bundle T B N.
Proof.
 intros n T B N v H. apply (O.eval_oracle program defined defined_lookup) in H.
 assert (A : agree defined kl g_cb = true) by (vm_compute; reflexivity). rewrite (step_agree defined kl _ _ _ A) in H.
 pose proof (drivers n) as D. destruct D. facts n. eapply (body_cb (ask n)) in H; [exact H|assumption ..].
Qed.
Theorem captured_check_bundle_refines : forall n T B N v, captured_check_bundle n T B N = Returned v ->
 v = r_check_bundle T B N \/ v = rejected "malformed-evidence".
Proof.
 intros n T B N v H. unfold captured_check_bundle, guard_model in H.
 destruct (eval n (lookup program) (arguments p_cb [T;B;N]) g_cb) eqn:E; try discriminate.
 - injection H as <-. left. exact (native_guarded_body _ _ _ _ _ E).
 - injection H as <-. right. reflexivity.
Qed.
(* EQ1-DRIVERS, composed: if the captured check-bundle accepts, the theory
   is the loaded one and every output theorem is valid in the standard model. *)
Theorem captured_check_bundle_sound : forall n T B N out, captured_check_bundle n T B N = Returned (accepted out) ->
 same T theory_value = true /\ all_ok out.
Proof.
 intros n T B N out H. destruct (captured_check_bundle_refines _ _ _ _ _ H) as [E|E].
 - apply (check_bundle_sound T B N). symmetry. exact E.
 - discriminate E.
Qed.
Theorem captured_false_lemma_never_accepted : forall n T B N out name,
 captured_check_bundle n T B N = Returned (accepted out) ->
 ~ entry_in (L [name;L [L [sym "x";sym "nat"]];v "x";ap "succ" [v "x"]]) out.
Proof.
 intros n T B N out name H. destruct (captured_check_bundle_refines _ _ _ _ _ H) as [E|E]; [|discriminate E].
 apply (false_lemma_never_accepted T B N). symmetry. exact E.
Qed.
End EqualityInductionRefinement.
