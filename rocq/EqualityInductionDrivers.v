(* BURI/EQ-1, obligation EQ1-DRIVERS, part 1: every captured KLambda body of
   the acceptance drivers (decoded from ports/eq1-kernel.bits and
   ports/eq1-base.bits) computes its reference function, for every input,
   under any call oracle that satisfies the callees' contracts. The bodies
   are read from the decoded program, not restated. Composition by fuel
   induction and the Native corollaries are in EqualityInductionRefinement.

   Proof technique (small proof terms): one directed symbolic evaluation per
   body. Branches are hidden behind the identity marker [hide] so strong
   reduction only expands the evaluation frontier; tests split on their
   outcome; callee results are replaced by their contracts; name
   comparisons stay folded and a successful comparison with a literal
   substitutes it. No proof search is involved in any acceptance path. *)
From Coq Require Import List String Ascii ZArith Bool Lia DecimalString.
From Buri Require Import Native EqualityInductionOracle EqualityInductionModel EqualityInductionSpecs
 EqualityInductionHelpers EqualityInductionKernel.
Import ListNotations Native.Native.
Module EqualityInductionDrivers.
Module O := EqualityInductionOracle.EqualityInductionOracle.
Import EqualityInductionModel.EqualityInductionModel EqualityInductionSpecs.EqualityInductionSpecs
 EqualityInductionKernel.EqualityInductionKernel.
Open Scope string_scope.

(* A three-character test for program names, equal to [defined] on every
   name a checked body calls. *)
Definition kl (s : string) := match s with String "k"%char (String "l"%char (String ":"%char _)) => true | _ => false end.
Fixpoint calls e : list string := match e with
 | Lit _ | Var _ => []
 | If c a b => (calls c ++ calls a ++ calls b)%list
 | Let _ a b | And a b | Or a b => (calls a ++ calls b)%list
 | Call s es => s :: (fix many es := match es with [] => [] | e::es => (calls e ++ many es)%list end) es end.
Definition agree (d1 d2 : string -> bool) e := forallb (fun s => Bool.eqb (d1 s) (d2 s)) (calls e).
Lemma step_agree : forall d1 d2 r e rho, agree d1 d2 e = true -> O.step d1 r rho e = O.step d2 r rho e.
Proof.
 intros d1 d2 r e; induction e using O.expr_rect'; intros rho A; unfold agree in A; cbn [calls] in A;
 rewrite ?forallb_app in A;
 repeat match type of A with (_ && _)%bool = true => apply andb_true_iff in A; destruct A as [? A] end;
 cbn [O.step]; fold (O.step d1 r) (O.step d2 r).
 - reflexivity.
 - reflexivity.
 - rewrite IHe1, IHe2, IHe3 by assumption. reflexivity.
 - rewrite IHe1 by assumption. destruct (O.step d2 r rho e1); [apply IHe2; assumption|reflexivity].
 - rewrite IHe1, IHe2 by assumption. reflexivity.
 - rewrite IHe1, IHe2 by assumption. reflexivity.
 - cbn [forallb] in *.
   apply andb_true_iff in A as [Hd A]. apply Bool.eqb_prop in Hd. rewrite Hd.
   assert (M : forall xs, (forall e, In e xs -> In e es) ->
     forallb (fun s => Bool.eqb (d1 s) (d2 s)) ((fix many es := match es with [] => [] | e::es => (calls e ++ many es)%list end) xs) = true ->
     (fix many es := match es with
     | [] => Some []
     | e::es => match O.step d1 r rho e,many es with Some v,Some vs => Some (v::vs) | _,_ => None end end) xs =
     (fix many es := match es with
     | [] => Some []
     | e::es => match O.step d2 r rho e,many es with Some v,Some vs => Some (v::vs) | _,_ => None end end) xs).
   { induction xs as [|x xs IHx]; intros S F; [reflexivity|].
     rewrite forallb_app in F. apply andb_true_iff in F as [F1 F2].
     rewrite (H x (S x (or_introl eq_refl)) rho F1), (IHx (fun e I => S e (or_intror I)) F2). reflexivity. }
   rewrite (M es (fun e I => I) A). reflexivity.
Qed.


(* Captured bodies, read from the decoded program (vm-computed literals). *)
Definition def_body s := body (def_of s).
Definition def_params s := params (def_of s).
Definition p_cb := Eval vm_compute in def_params "kl:buri.check-bundle".
Definition b_cb := Eval vm_compute in def_body "kl:buri.check-bundle".
Definition p_bundle := Eval vm_compute in def_params "kl:buri.bundle-h".
Definition b_bundle := Eval vm_compute in def_body "kl:buri.bundle-h".
Definition p_next := Eval vm_compute in def_params "kl:buri.bundle-next".
Definition b_next := Eval vm_compute in def_body "kl:buri.bundle-next".
Definition p_goal := Eval vm_compute in def_params "kl:buri.goal?".
Definition b_goal := Eval vm_compute in def_body "kl:buri.goal?".
Definition p_theorem := Eval vm_compute in def_params "kl:buri.check-theorem".
Definition b_theorem := Eval vm_compute in def_body "kl:buri.check-theorem".
Definition p_cases := Eval vm_compute in def_params "kl:buri.check-cases".
Definition b_cases := Eval vm_compute in def_body "kl:buri.check-cases".
Definition p_bound := Eval vm_compute in def_params "kl:buri.check-case-bound".
Definition b_bound := Eval vm_compute in def_body "kl:buri.check-case-bound".
Definition p_steps := Eval vm_compute in def_params "kl:buri.check-steps".
Definition b_steps := Eval vm_compute in def_body "kl:buri.check-steps".
Definition p_csr := Eval vm_compute in def_params "kl:buri.check-step-result".
Definition b_csr := Eval vm_compute in def_body "kl:buri.check-step-result".
Definition p_after := Eval vm_compute in def_params "kl:buri.after-rewrite".
Definition b_after := Eval vm_compute in def_body "kl:buri.after-rewrite".
Definition p_inst := Eval vm_compute in def_params "kl:buri.instantiate".
Definition b_inst := Eval vm_compute in def_body "kl:buri.instantiate".
Definition p_substn := Eval vm_compute in def_params "kl:buri.substitution?".
Definition b_substn := Eval vm_compute in def_body "kl:buri.substitution?".
Definition p_replace := Eval vm_compute in def_params "kl:buri.replace".
Definition b_replace := Eval vm_compute in def_body "kl:buri.replace".
Definition p_rarg := Eval vm_compute in def_params "kl:buri.replace-arg".
Definition b_rarg := Eval vm_compute in def_body "kl:buri.replace-arg".
Definition p_str := Eval vm_compute in def_params "kl:str".
Definition b_str := Eval vm_compute in def_body "kl:str".
Definition p_digits := Eval vm_compute in def_params "kl:buri.digits?".
Definition b_digits := Eval vm_compute in def_body "kl:buri.digits?".
Definition p_unsigned := Eval vm_compute in def_params "kl:buri.unsigned-spelling?".
Definition b_unsigned := Eval vm_compute in def_body "kl:buri.unsigned-spelling?".
Definition p_ispell := Eval vm_compute in def_params "kl:buri.integer-spelling?".
Definition b_ispell := Eval vm_compute in def_body "kl:buri.integer-spelling?".
Definition p_exact := Eval vm_compute in def_params "kl:buri.exact-integer?".
Definition b_exact := Eval vm_compute in def_body "kl:buri.exact-integer?".
Definition p_nat := Eval vm_compute in def_params "kl:buri.nat?".
Definition b_nat := Eval vm_compute in def_body "kl:buri.nat?".
(* check-bundle is [trap-error], compiled to a Chez guard whose handler is
   the literal rejection; [g_cb] is the guarded body. *)
Definition h_cb := Eval vm_compute in match b_cb with Call _ [h;_] => h | _ => Lit Nil end.
Definition g_cb := Eval vm_compute in match b_cb with Call _ [_;g] => g | _ => Lit Nil end.
Lemma b_cb_guard : b_cb = Call "guard" [h_cb;g_cb].
Proof. reflexivity. Qed.
Lemma h_cb_handler : h_cb = Call "Z5963" [Call "else" [Call "list" [Lit (Symbol "rejected");Lit (Symbol "malformed-evidence")]]].
Proof. reflexivity. Qed.

(* One-step reference specifications of the drivers that are fragments of a
   reference-kernel function. *)
Definition rep1 t p a b := match p with
 | Nil => if same t a then L [sym "replaced";b] else mismatch
 | Pair i is => match var_of t with
   | Some _ => mismatch
   | None => match t,i with
     | Pair f args,Integer z => if Z.leb 0 z then r_rapp f (r_rarg args z is a b) else mismatch
     | _,_ => mismatch end end
 | _ => mismatch end.
Lemma rep1_replace : forall t p a b, rep1 t p a b = r_replace t p a b.
Proof. intros t p a b; destruct p; try reflexivity. rewrite r_replace_step. reflexivity. Qed.
Definition rarg1 args z is a b := match args with
 | Pair x xs => if Z.eqb 0 z then r_head (r_replace x is a b) xs else r_tail x (r_rarg xs (z-1)%Z is a b)
 | _ => mismatch end.
Lemma rarg1_rarg : forall args z is a b, rarg1 args z is a b = r_rarg args z is a b.
Proof. intros args z is a b; destruct args; reflexivity. Qed.
Definition after1 x r steps C hs ls n := match tagged "replaced" x with
 | Some l' => r_steps l' r steps C hs ls (n-1) | None => rejected "rewrite-does-not-match" end.
Definition csr1 e path dir l r steps C hs ls n := match equation_parts e,direction dir with
 | Some (a,b),Some fwd => after1 (if fwd then r_replace l path a b else r_replace l path b a) r steps C hs ls n
 | _,_ => rejected "invalid-rule-instance" end.
Definition next1 res name C l r rest ls n := if is_checked res then r_bundle rest (Pair (L [name;C;l;r]) ls) n else res.
Definition bound1 z ctor ctors cases names steps X C l r ls n := match tagged "zipped" z with
 | Some bs =>
   let G := r_remove X C in
   let inst := one X (Pair ctor (r_vars names)) in
   let res := r_steps (r_subst l inst) (r_subst r inst) steps (r_app bs G) (r_ihyps bs X G l r) ls n in
   if is_checked res then r_cases ctors cases X C l r ls n else res
 | None => rejected "constructor-arity" end.

(* buri.nat? decides decimal spelling (EQ1-NUMERIC): for an integer it is
   exactly [0 <= z], since every non-negative spelling is a digit string. *)
Definition digit_texts := L (map Text ["0";"1";"2";"3";"4";"5";"6";"7";"8";"9"]).
Fixpoint alldig s := match s with "" => true | String c s' => r_mem (Text (String c "")) digit_texts && alldig s' end.
Definition unsigned s := match s with "" => false | _ => alldig s end.
Definition ispell s := match s with
 | "" => false
 | String c s' => if String.eqb (String c "") "-" then unsigned s' else unsigned s end.
Lemma alldig_uint : forall d, alldig (NilEmpty.string_of_uint d) = true.
Proof. induction d; cbn [NilEmpty.string_of_uint alldig]; try rewrite IHd; reflexivity. Qed.
Theorem spelling_ok : forall z, (0 <= z)%Z -> ispell (spelling z) = true.
Proof.
 intros z Z. unfold spelling. destruct z as [|p|p]; [reflexivity| |lia].
 cbn [Z.to_int NilZero.string_of_int]. unfold NilZero.string_of_uint.
 destruct (Pos.to_uint p) eqn:U; try reflexivity;
 cbn [NilEmpty.string_of_uint ispell]; unfold unsigned; cbn [alldig]; rewrite alldig_uint; reflexivity.
Qed.
Lemma substring_all : forall s, substring 0 (Z.to_nat (Z.pos (Pos.of_succ_nat (String.length s)) - 1)) s = s.
Proof.
 intro s. rewrite Zpos_P_of_succ_nat, Z.sub_1_r, Z.pred_succ, Nat2Z.id.
 induction s as [|c s IH]; [reflexivity|]. cbn [String.length substring]. rewrite IH. reflexivity.
Qed.

(* Lazy evaluation marker: branch positions are hidden from strong
   reduction until evaluation reaches them. [hide] is the identity. *)
Definition hide (e : expr) := e.
Fixpoint lazify e := match e with
 | Lit _ | Var _ => e
 | If c a b => If (lazify c) (hide (lazify a)) (hide (lazify b))
 | Let s a b => Let s (lazify a) (hide (lazify b))
 | And a b => And (lazify a) (hide (lazify b))
 | Or a b => Or (lazify a) (hide (lazify b))
 | Call s es => Call s (map lazify es) end.
#[local] Arguments hide : simpl never.
#[local] Arguments String.eqb : simpl nomatch.
#[local] Arguments same : simpl nomatch.
#[local] Arguments Z.eqb : simpl nomatch.
#[local] Arguments Z.leb : simpl nomatch.
#[local] Arguments Z.geb : simpl nomatch.
#[local] Arguments Z.sub : simpl nomatch.
Lemma some_inj : forall (a b : value), Some a = Some b -> a = b.
Proof. intros a b H; congruence. Qed.

Section Bodies.
Variable o : string -> list value -> option value.
(* Partial-correctness contracts of every callee (helpers proved in
   EqualityInductionSpecs/Helpers; drivers by fuel induction below). *)
Hypothesis h_eq : forall a b u, o "kl:=" [a;b] = Some u -> u = Boolean (same a b).
Hypothesis h_assert : forall w u, o "kl:_scm.assert-boolean" [w] = Some u -> u = w.
Hypothesis h_not : forall w u, o "kl:not" [w] = Some u -> u = Boolean (match w with Boolean false => true | _ => false end).
Hypothesis h_sym : forall w u, o "kl:symbol?" [w] = Some u -> u = Boolean (is_sym w).
Hypothesis h_nat : forall i u, o "kl:buri.nat?" [i] = Some u -> u = Boolean (match i with Integer z => Z.leb 0 z | _ => false end).
Hypothesis h_theory : forall u, o "kl:buri.theory" [] = Some u -> u = theory_value.
Hypothesis h_rev : forall xs u, o "kl:buri.rev" [xs] = Some u -> u = r_revh xs Nil.
Hypothesis h_rule : forall n rs u, o "kl:buri.rule" [n;rs] = Some u -> u = r_rule n rs.
Hypothesis h_ctx : forall C u, o "kl:buri.context?" [C] = Some u -> u = Boolean (r_ctx C).
Hypothesis h_sort : forall t C u, o "kl:buri.sort" [t;C] = Some u -> u = r_sort t C.
Hypothesis h_get : forall k xs u, o "kl:buri.get" [k;xs] = Some u -> u = r_get k xs.
Hypothesis h_allsym : forall xs u, o "kl:buri.all-symbols?" [xs] = Some u -> u = Boolean (r_allsym xs).
Hypothesis h_unique : forall xs u, o "kl:buri.unique?" [xs] = Some u -> u = Boolean (r_uniq xs).
Hypothesis h_fresh : forall xs ys u, o "kl:buri.fresh?" [xs;ys] = Some u -> u = Boolean (r_fresh xs ys).
Hypothesis h_keys : forall xs u, o "kl:buri.keys" [xs] = Some u -> u = r_keys xs.
Hypothesis h_zip : forall xs ys u, o "kl:buri.zip" [xs;ys] = Some u -> u = r_zip xs ys.
Hypothesis h_remove : forall k xs u, o "kl:buri.remove" [k;xs] = Some u -> u = r_remove k xs.
Hypothesis h_append : forall xs ys u, o "kl:buri.append" [xs;ys] = Some u -> u = r_app xs ys.
Hypothesis h_vars : forall ns u, o "kl:buri.variables" [ns] = Some u -> u = r_vars ns.
Hypothesis h_ihyps : forall bs x g l r u, o "kl:buri.induction-hyps" [bs;x;g;l;r] = Some u -> u = r_ihyps bs x g l r.
Hypothesis h_subst : forall t sub u, o "kl:buri.subst" [t;sub] = Some u -> u = r_subst t sub.
Hypothesis h_resolve : forall ref hs ls u, o "kl:buri.resolve" [ref;hs;ls] = Some u -> u = r_resolve ref hs ls.
Hypothesis h_rapp : forall f x u, o "kl:buri.replace-app" [f;x] = Some u -> u = r_rapp f x.
Hypothesis h_head : forall x ts u, o "kl:buri.replace-head" [x;ts] = Some u -> u = r_head x ts.
Hypothesis h_tail : forall t x u, o "kl:buri.replace-tail" [t;x] = Some u -> u = r_tail t x.
Hypothesis h_bundle : forall b ls n u, o "kl:buri.bundle-h" [b;ls;Integer n] = Some u -> u = r_bundle b ls n.
Hypothesis h_next : forall res name C l r rest ls n u, o "kl:buri.bundle-next" [res;name;C;l;r;rest;ls;Integer n] = Some u ->
 u = next1 res name C l r rest ls n.
Hypothesis h_goal : forall C l r u, o "kl:buri.goal?" [C;l;r] = Some u -> u = Boolean (r_goal C l r).
Hypothesis h_theorem : forall C l r p ls n u, o "kl:buri.check-theorem" [C;l;r;p;ls;Integer n] = Some u -> u = r_theorem C l r p ls n.
Hypothesis h_cases : forall ctors cases X C l r ls n u, o "kl:buri.check-cases" [ctors;cases;X;C;l;r;ls;Integer n] = Some u ->
 u = r_cases ctors cases X C l r ls n.
Hypothesis h_bound : forall z ctor ctors cases names steps X C l r ls n u,
 o "kl:buri.check-case-bound" [z;ctor;ctors;cases;names;steps;X;C;l;r;ls;Integer n] = Some u ->
 u = bound1 z ctor ctors cases names steps X C l r ls n.
Hypothesis h_steps : forall l r steps C hs ls n u, o "kl:buri.check-steps" [l;r;steps;C;hs;ls;Integer n] = Some u ->
 u = r_steps l r steps C hs ls n.
Hypothesis h_csr : forall e path dir l r steps C hs ls n u,
 o "kl:buri.check-step-result" [e;path;dir;l;r;steps;C;hs;ls;Integer n] = Some u -> u = csr1 e path dir l r steps C hs ls n.
Hypothesis h_after : forall x r steps C hs ls n u, o "kl:buri.after-rewrite" [x;r;steps;C;hs;ls;Integer n] = Some u ->
 u = after1 x r steps C hs ls n.
Hypothesis h_inst : forall rl sub C u, o "kl:buri.instantiate" [rl;sub;C] = Some u -> u = r_inst rl sub C.
Hypothesis h_substn : forall vars sub C u, o "kl:buri.substitution?" [vars;sub;C] = Some u -> u = Boolean (r_substitution vars sub C).
Hypothesis h_replace : forall t p a b u, o "kl:buri.replace" [t;p;a;b] = Some u -> u = r_replace t p a b.
Hypothesis h_rarg : forall args z is a b u, o "kl:buri.replace-arg" [args;Integer z;is;a;b] = Some u -> u = r_rarg args z is a b.

Hypothesis h_member : forall x ys u, o "kl:buri.member?" [x;ys] = Some u -> u = Boolean (r_mem x ys).
Hypothesis h_str : forall z u, o "kl:str" [Integer z] = Some u -> u = Text (spelling z).
Hypothesis h_digits : forall s u, o "kl:buri.digits?" [Text s] = Some u -> u = Boolean (alldig s).
Hypothesis h_unsigned : forall s u, o "kl:buri.unsigned-spelling?" [Text s] = Some u -> u = Boolean (unsigned s).
Hypothesis h_ispell : forall s u, o "kl:buri.integer-spelling?" [Text s] = Some u -> u = Boolean (ispell s).
Hypothesis h_exact : forall z u, o "kl:buri.exact-integer?" [Integer z] = Some u -> u = Boolean (ispell (spelling z)).

(* Directed evaluation of one captured body under the contracts. *)
Ltac hyp_call n E := lazymatch n with
 | "kl:=" => apply h_eq in E
 | "kl:_scm.assert-boolean" => apply h_assert in E
 | "kl:not" => apply h_not in E
 | "kl:symbol?" => apply h_sym in E
 | "kl:buri.nat?" => apply h_nat in E
 | "kl:buri.theory" => apply h_theory in E
 | "kl:buri.rev" => apply h_rev in E
 | "kl:buri.rule" => apply h_rule in E
 | "kl:buri.context?" => apply h_ctx in E
 | "kl:buri.sort" => apply h_sort in E
 | "kl:buri.get" => apply h_get in E
 | "kl:buri.all-symbols?" => apply h_allsym in E
 | "kl:buri.unique?" => apply h_unique in E
 | "kl:buri.fresh?" => apply h_fresh in E
 | "kl:buri.keys" => apply h_keys in E
 | "kl:buri.zip" => apply h_zip in E
 | "kl:buri.remove" => apply h_remove in E
 | "kl:buri.append" => apply h_append in E
 | "kl:buri.variables" => apply h_vars in E
 | "kl:buri.induction-hyps" => apply h_ihyps in E
 | "kl:buri.subst" => apply h_subst in E
 | "kl:buri.resolve" => apply h_resolve in E
 | "kl:buri.replace-app" => apply h_rapp in E
 | "kl:buri.replace-head" => apply h_head in E
 | "kl:buri.replace-tail" => apply h_tail in E
 | "kl:buri.bundle-h" => apply h_bundle in E
 | "kl:buri.bundle-next" => apply h_next in E
 | "kl:buri.goal?" => apply h_goal in E
 | "kl:buri.check-theorem" => apply h_theorem in E
 | "kl:buri.check-cases" => apply h_cases in E
 | "kl:buri.check-steps" => apply h_steps in E
 | "kl:buri.after-rewrite" => apply h_after in E
 | "kl:buri.instantiate" => apply h_inst in E
 | "kl:buri.substitution?" => apply h_substn in E
 | "kl:buri.replace" => apply h_replace in E
 | "kl:buri.replace-arg" => apply h_rarg in E
 | "kl:buri.member?" => apply h_member in E
 | "kl:str" => apply h_str in E
 | "kl:buri.digits?" => apply h_digits in E
 | "kl:buri.unsigned-spelling?" => apply h_unsigned in E
 | "kl:buri.integer-spelling?" => apply h_ispell in E
 | "kl:buri.exact-integer?" => apply h_exact in E
 | "kl:buri.check-case-bound" => apply h_bound in E
 | "kl:buri.check-step-result" => apply h_csr in E
 end.
Ltac eqb_norm_h H := repeat match type of H with context [String.eqb ?s ?t] =>
 is_var s; tryif is_var t then fail else rewrite (String.eqb_sym s t) in H end.
Ltac eqb_norm := repeat match goal with |- context [String.eqb ?s ?t] =>
 is_var s; tryif is_var t then fail else rewrite (String.eqb_sym s t) end.
Ltac red_h H := cbn -[r_replace r_rarg r_rapp r_head r_tail r_steps r_subst r_substs r_rule
 r_sort r_get r_substitution r_revh r_theorem r_bundle r_goal r_cases r_ctx r_allsym r_uniq r_fresh r_keys r_zip
 r_remove r_app r_vars r_ihyps r_resolve r_inst next1 bound1 csr1 after1
 theory_value rules_value signature_value constructors_value] in H; try unfold sym in H; eqb_norm_h H.
Ltac red_goal := cbn -[theory_value rules_value signature_value constructors_value]; try unfold sym; eqb_norm.
(* Split on the innermost stuck scrutinee of the evaluation hypothesis [H].
   A boolean test of a variable splits on its outcome; the variable's shape
   is learnt only when the test succeeds. *)
Ltac gen_split H t := first [match goal with E : t = _ |- _ => rewrite E in H end
   | is_var t; destruct t
   | lazymatch type of t with bool => idtac end; lazymatch t with match ?y with _ => _ end => is_var y end;
     let E := fresh "T" in destruct t eqn:E; [lazymatch t with match ?y with _ => _ end => destruct y end; try discriminate E; clear E|]
   | let E := fresh "E" in destruct t eqn:E].
Ltac split_on H t := lazymatch t with
 | match ?u with _ => _ end => split_on H u
 | String.get _ ?x => first [is_var x; destruct x | gen_split H t]
 | O.step ?d ?r ?rho (hide ?x) => change (O.step d r rho (hide x)) with (O.step d r rho x) in H
 | o ?n ?a => let u := fresh "u" in let E := fresh "E" in
   destruct (o n a) as [u|] eqn:E in H; [hyp_call n E; subst u|]
 | String.eqb ?a ?x => first [is_var x; first [match goal with E : t = _ |- _ => rewrite E in H end | let E := fresh "S" in
   destruct (String.eqb a x) eqn:E; [apply String.eqb_eq in E; subst x|]] | gen_split H t]
 | _ => gen_split H t
 end.
Ltac test_split H t := lazymatch t with
 | match ?y with _ => _ end => first [is_var y; lazymatch type of t with bool => idtac end;
     let E := fresh "T" in destruct t eqn:E; [destruct y; try discriminate E; clear E|]
   | split_on H t]
 | _ => split_on H t end.
Ltac drive := let H := fresh "H" in intro H; repeat (red_h H; lazymatch type of H with
 | Some _ = Some _ => apply some_inj in H; subst
 | None = Some _ => discriminate H
 | ?t = Some _ => test_split H t
 end).
Ltac split_r t := lazymatch t with
 | match ?u with _ => _ end => split_r u
 | String.eqb ?a ?x => is_var x; let E := fresh "S" in
   destruct (String.eqb a x) eqn:E; [apply String.eqb_eq in E; subst x|]
 | _ => first [is_var t; destruct t
   | match goal with E : t = _ |- _ => rewrite E end
   | let E := fresh "E" in destruct t eqn:E]
 end.
Ltac rewrite_known := repeat match goal with
 | E : ?t = ?c |- context [?t] => tryif is_var t then fail else rewrite E
 end.
Ltac contra := repeat match goal with F : _ = _ |- _ =>
   progress (cbn -[theory_value rules_value] in F; eqb_norm_h F) end;
 repeat match goal with
 | E : ?t = _, F : context [?t] |- _ => tryif is_var t then fail else (rewrite E in F; cbn in F)
 end; match goal with F : _ = _ |- _ => discriminate F end.
(* Leaf case splits are restricted to variables and literal name
   comparisons (plus rewriting with recorded test outcomes), so a false leaf
   fails quickly instead of exploring compound terms. *)
Ltac split_r_b t := lazymatch t with
 | match ?u with _ => _ end => split_r_b u
 | String.eqb _ ?x => is_var x; split_r t
 | _ => first [is_var t; destruct t | match goal with E : t = _ |- _ => rewrite E end]
 end.
Ltac split_budget := match goal with
 | |- context [match ?t with _ => _ end] => split_r_b t end.
Ltac leaf_with refl := repeat first [refl | progress (red_goal; rewrite_known) | contra |
 split_budget |
 progress unfold r_check_bundle, r_theorem, r_goal, next1, bound1, csr1, after1, rep1, rarg1, r_inst, r_resolve,
   is_checked, theorem_parts, case_parts, ctor_parts, rewrite_parts, equation_parts, direction, tagged, var_of, is_missing,
   unsigned, ispell | reflexivity].
(* Conversion first for the drivers; for the numeral helpers a syntactic
   check first, since conversion would unfold decimal spelling. *)
Ltac leaf := leaf_with ltac:(reflexivity).
Ltac leaf_n := leaf_with ltac:(idtac; match goal with |- ?a = ?a => reflexivity end).
Ltac start b := let e := eval cbv [lazify map] in (lazify b) in change b with e.
Ltac body b := start b; drive; leaf.
Ltac body_n b := start b; drive; leaf_n.

Lemma body_cb : forall T B N w, O.step kl o (arguments p_cb [T;B;N]) g_cb = Some w -> w = r_check_bundle T B N.
Proof. intros until w. body g_cb. Qed.
Lemma body_bundle : forall b ls n w, O.step kl o (arguments p_bundle [b;ls;Integer n]) b_bundle = Some w -> w = r_bundle b ls n.
Proof. intros until w. body b_bundle. Qed.
Lemma body_next : forall res name C l r rest ls n w,
 O.step kl o (arguments p_next [res;name;C;l;r;rest;ls;Integer n]) b_next = Some w -> w = next1 res name C l r rest ls n.
Proof. intros until w. body b_next. Qed.
Lemma body_goal : forall C l r w, O.step kl o (arguments p_goal [C;l;r]) b_goal = Some w -> w = Boolean (r_goal C l r).
Proof. intros until w. body b_goal. Qed.
Local Opaque r_cases r_steps.
Lemma body_theorem : forall C l r p ls n w,
 O.step kl o (arguments p_theorem [C;l;r;p;ls;Integer n]) b_theorem = Some w -> w = r_theorem C l r p ls n.
Proof. intros until w. body b_theorem. Qed.
Local Transparent r_cases r_steps.
Lemma body_cases : forall ctors cases X C l r ls n w,
 O.step kl o (arguments p_cases [ctors;cases;X;C;l;r;ls;Integer n]) b_cases = Some w -> w = r_cases ctors cases X C l r ls n.
Proof. intros until w. body b_cases. Qed.
Lemma body_bound : forall z ctor ctors cases names steps X C l r ls n w,
 O.step kl o (arguments p_bound [z;ctor;ctors;cases;names;steps;X;C;l;r;ls;Integer n]) b_bound = Some w ->
 w = bound1 z ctor ctors cases names steps X C l r ls n.
Proof. intros until w. body b_bound. Qed.
Lemma body_steps : forall l r steps C hs ls n w,
 O.step kl o (arguments p_steps [l;r;steps;C;hs;ls;Integer n]) b_steps = Some w -> w = r_steps l r steps C hs ls n.
Proof. intros until w. body b_steps. Qed.
Lemma body_csr : forall e path dir l r steps C hs ls n w,
 O.step kl o (arguments p_csr [e;path;dir;l;r;steps;C;hs;ls;Integer n]) b_csr = Some w -> w = csr1 e path dir l r steps C hs ls n.
Proof. intros until w. body b_csr. Qed.
Lemma body_after : forall x r steps C hs ls n w,
 O.step kl o (arguments p_after [x;r;steps;C;hs;ls;Integer n]) b_after = Some w -> w = after1 x r steps C hs ls n.
Proof. intros until w. body b_after. Qed.
Lemma body_inst : forall rl sub C w, O.step kl o (arguments p_inst [rl;sub;C]) b_inst = Some w -> w = r_inst rl sub C.
Proof. intros until w. body b_inst. Qed.
Lemma body_substn : forall vars sub C w,
 O.step kl o (arguments p_substn [vars;sub;C]) b_substn = Some w -> w = Boolean (r_substitution vars sub C).
Proof. intros until w. body b_substn. Qed.
Lemma body_replace : forall t p a b w, O.step kl o (arguments p_replace [t;p;a;b]) b_replace = Some w -> w = r_replace t p a b.
Proof. intros until w. rewrite <- rep1_replace. body b_replace. Qed.
Lemma body_rarg : forall args z is a b w,
 O.step kl o (arguments p_rarg [args;Integer z;is;a;b]) b_rarg = Some w -> w = r_rarg args z is a b.
Proof. intros until w. rewrite <- rarg1_rarg. body b_rarg. Qed.
Lemma body_str : forall z w, O.step kl o (arguments p_str [Integer z]) b_str = Some w -> w = Text (spelling z).
Proof. intros until w. body_n b_str. Qed.
Lemma body_digits : forall s w, O.step kl o (arguments p_digits [Text s]) b_digits = Some w -> w = Boolean (alldig s).
Proof. intros until w. start b_digits. drive. all: rewrite ?Pos2Nat.inj_1; cbn [substring]; rewrite ?substring_all. all: leaf_n. Qed.
Lemma body_unsigned : forall s w, O.step kl o (arguments p_unsigned [Text s]) b_unsigned = Some w -> w = Boolean (unsigned s).
Proof. intros until w. body_n b_unsigned. Qed.
Lemma body_ispell : forall s w, O.step kl o (arguments p_ispell [Text s]) b_ispell = Some w -> w = Boolean (ispell s).
Proof. intros until w. start b_ispell. drive. all: rewrite ?Pos2Nat.inj_1; cbn [substring]; rewrite ?substring_all. all: leaf_n. Qed.
Lemma body_exact : forall z w, O.step kl o (arguments p_exact [Integer z]) b_exact = Some w -> w = Boolean (ispell (spelling z)).
Proof. intros until w. body_n b_exact. Qed.
Lemma body_nat : forall i w, O.step kl o (arguments p_nat [i]) b_nat = Some w ->
 w = Boolean (match i with Integer z => Z.geb z 0 && ispell (spelling z) | _ => false end).
Proof. intros until w. body_n b_nat. Qed.
End Bodies.
End EqualityInductionDrivers.
