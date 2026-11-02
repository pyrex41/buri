(* BURI/EQ-1, obligation EQ1-TERM, generic part: a traced evaluation of one
   captured body against a reference call table, and the theorem that a
   traced run whose every recorded program call terminates (under the actual
   Native evaluator, with the recorded value) is itself a terminating Native
   evaluation. No program-specific claim is made here except the reference
   call table [oref] (the reference functions of EqualityInductionModel,
   EqualityInductionKernel and EqualityInductionDrivers) and the domain
   predicates on which the captured code is total. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native NativeSimulation NativeComposition EqualityInductionOracle EqualityInductionModel
 EqualityInductionSpecs EqualityInductionHelpers EqualityInductionKernel EqualityInductionDrivers.
Import ListNotations Native.Native.
Module EqualityInductionTrace.
Module O := EqualityInductionOracle.EqualityInductionOracle.
Import EqualityInductionModel.EqualityInductionModel EqualityInductionSpecs.EqualityInductionSpecs
 EqualityInductionKernel.EqualityInductionKernel EqualityInductionDrivers.EqualityInductionDrivers.
Open Scope string_scope.

(* A recorded program call: name, arguments, returned value. *)
Definition call := (string * list value * value)%type.
Definition okcall (c : call) := match c with (s,vs,w) => exists n, run n program s vs = Returned w end.

(* A literal name test equal to [defined] on every name a checked body calls
   (vm-checked per body by [agree]): program names carry the "kl:" prefix,
   and the pattern-match failure kl:shen.f-error is not a program name. *)
Definition dn (s : string) := (kl s && negb (String.eqb s "kl:shen.f-error"))%bool.

Section Trace.
Variable o : string -> list value -> option value.
Fixpoint stepT (rho : env) (e : expr) {struct e} : option (value * list call) := match e with
 | Lit v => Some (v,[])
 | Var s => match rho s with Some v => Some (v,[]) | None => None end
 | If c a b => match stepT rho c with
   | Some (Boolean false,k) => match stepT rho b with Some (v,k') => Some (v,(k ++ k')%list) | None => None end
   | Some (_,k) => match stepT rho a with Some (v,k') => Some (v,(k ++ k')%list) | None => None end
   | None => None end
 | Let s a b => match stepT rho a with
   | Some (x,k) => match stepT (bind rho s x) b with Some (v,k') => Some (v,(k ++ k')%list) | None => None end
   | None => None end
 | And a b => match stepT rho a with
   | Some (Boolean false,k) => Some (Boolean false,k)
   | Some (_,k) => match stepT rho b with Some (v,k') => Some (v,(k ++ k')%list) | None => None end
   | None => None end
 | Or a b => match stepT rho a with
   | Some (Boolean false,k) => match stepT rho b with Some (v,k') => Some (v,(k ++ k')%list) | None => None end
   | Some (v,k) => Some (v,k)
   | None => None end
 | Call s es =>
   match (fix many es := match es with
     | [] => Some ([],[])
     | e::es => match stepT rho e with
       | Some (v,k) => match many es with Some (vs,k') => Some (v::vs,(k ++ k')%list) | None => None end
       | None => None end end) es with
   | Some (vs,k) => if dn s then match o s vs with Some w => Some (w,(k ++ [(s,vs,w)])%list) | None => None end
     else match external s vs with Returned w => Some (w,k) | _ => None end
   | None => None end
 end.
Definition manyT rho := fix many es := match es with
 | [] => Some ([],[])
 | e::es => match stepT rho e with
   | Some (v,k) => match many es with Some (vs,k') => Some (v::vs,(k ++ k')%list) | None => None end
   | None => None end end.
(* The goal form of one body: the traced run succeeds and every recorded call terminates. *)
Definition Term rho e := match stepT rho e with Some (_,cs) => Forall okcall cs | None => False end.
End Trace.

Lemma mono : forall n m rho e v, n <= m -> eval n (lookup program) rho e = Returned v -> eval m (lookup program) rho e = Returned v.
Proof. intros. eapply NativeComposition.eval_monotone; eauto. Qed.

(* A successful traced run with terminating recorded calls is a terminating
   Native evaluation returning the same value. *)
Lemma stepT_if : forall o rho c a b, stepT o rho (If c a b) = match stepT o rho c with
 | Some (x,k) => match stepT o rho (match x with Boolean false => b | _ => a end) with
   | Some (v,k') => Some (v,(k ++ k')%list) | None => None end
 | None => None end.
Proof. intros. cbn [stepT]. destruct (stepT o rho c) as [[[| | | | | |[|]| | |] k]|]; reflexivity. Qed.
Theorem traced : forall o e rho v cs, agree defined dn e = true -> stepT o rho e = Some (v,cs) -> Forall okcall cs ->
 exists n, eval n (lookup program) rho e = Returned v.
Proof.
 intros o e; induction e using O.expr_rect'; intros rho w cs A Hs F; unfold agree in A; cbn [calls] in A;
 rewrite ?forallb_app in A;
 repeat match type of A with (_ && _)%bool = true => apply andb_true_iff in A; destruct A as [? A] end;
 first [rewrite stepT_if in Hs | cbn [stepT] in Hs; fold (stepT o) in Hs].
 - injection Hs as <- <-. exists 1. reflexivity.
 - destruct (rho s) eqn:R; [|discriminate]. injection Hs as <- <-. exists 1. cbn. rewrite R. reflexivity.
 - destruct (stepT o rho e1) as [[x k]|] eqn:E1; rewrite ?E1 in Hs; cbv beta match in Hs; [|discriminate].
   destruct (stepT o rho (match x with Boolean false => e3 | _ => e2 end)) as [[v' k']|] eqn:B;
    rewrite ?B in Hs; cbv beta match in Hs; [|discriminate].
   injection Hs as <- <-.
   apply Forall_app in F as [F1 F2].
   destruct (IHe1 rho x k ltac:(assumption) E1 F1) as [n1 N1].
   assert (Ab : agree defined dn (match x with Boolean false => e3 | _ => e2 end) = true)
     by (destruct x as [| | | | | |[|]| | |]; assumption).
   destruct x as [| | | | | |[|]| | |];
   (first [destruct (IHe2 rho _ _ Ab B F2) as [n2 N2] | destruct (IHe3 rho _ _ Ab B F2) as [n2 N2]]);
   exists (S (Nat.max n1 n2)); cbn [eval]; rewrite (mono n1 (Nat.max n1 n2) _ _ _ ltac:(lia) N1); apply (mono n2); auto; lia.
 - destruct (stepT o rho e1) as [[x k]|] eqn:E1; rewrite ?E1 in Hs; cbv beta match in Hs; [|discriminate].
   destruct (stepT o (bind rho s x) e2) as [[v' k']|] eqn:E2; rewrite ?E2 in Hs; cbv beta match in Hs; [|discriminate]. injection Hs as <- <-.
   apply Forall_app in F as [F1 F2].
   destruct (IHe1 rho x k ltac:(assumption) E1 F1) as [n1 N1]. destruct (IHe2 _ _ _ ltac:(assumption) E2 F2) as [n2 N2].
   exists (S (Nat.max n1 n2)); cbn [eval]; rewrite (mono n1 (Nat.max n1 n2) _ _ _ ltac:(lia) N1); apply (mono n2); auto; lia.
 - destruct (stepT o rho e1) as [[x k]|] eqn:E1; rewrite ?E1 in Hs; cbv beta match in Hs; [|discriminate].
   destruct x as [| | | | | |[|]| | |];
   try (destruct (stepT o rho e2) as [[v' k']|] eqn:E2; rewrite ?E2 in Hs; cbv beta match in Hs; [|discriminate]; injection Hs as <- <-;
        apply Forall_app in F as [F1 F2];
        destruct (IHe1 rho _ k ltac:(assumption) E1 F1) as [n1 N1]; destruct (IHe2 rho _ _ ltac:(assumption) E2 F2) as [n2 N2];
        exists (S (Nat.max n1 n2)); cbn [eval]; rewrite (mono n1 (Nat.max n1 n2) _ _ _ ltac:(lia) N1); apply (mono n2); auto; lia).
   injection Hs as <- <-. destruct (IHe1 rho _ _ ltac:(assumption) E1 F) as [n1 N1].
   exists (S n1); cbn [eval]; rewrite N1; reflexivity.
 - destruct (stepT o rho e1) as [[x k]|] eqn:E1; rewrite ?E1 in Hs; cbv beta match in Hs; [|discriminate].
   destruct x as [| | | | | |[|]| | |];
   try (injection Hs as <- <-; destruct (IHe1 rho _ _ ltac:(assumption) E1 F) as [n1 N1];
        exists (S n1); cbn [eval]; rewrite N1; reflexivity).
   destruct (stepT o rho e2) as [[v' k']|] eqn:E2; rewrite ?E2 in Hs; cbv beta match in Hs; [|discriminate]. injection Hs as <- <-.
   apply Forall_app in F as [F1 F2].
   destruct (IHe1 rho _ k ltac:(assumption) E1 F1) as [n1 N1]; destruct (IHe2 rho _ _ ltac:(assumption) E2 F2) as [n2 N2].
   exists (S (Nat.max n1 n2)); cbn [eval]; rewrite (mono n1 (Nat.max n1 n2) _ _ _ ltac:(lia) N1); apply (mono n2); auto; lia.
 - cbn [forallb] in A. apply andb_true_iff in A as [Hd A]. apply Bool.eqb_prop in Hd.
   fold (manyT o rho es) in Hs.
   assert (M : forall xs vs k, (forall e, In e xs -> In e es) ->
     forallb (fun s => Bool.eqb (defined s) (dn s)) ((fix many es := match es with [] => [] | e::es => (calls e ++ many es)%list end) xs) = true ->
     manyT o rho xs = Some (vs,k) -> Forall okcall k ->
     exists n, forall m, n <= m -> NativeSimulation.many m (lookup program) rho xs = Values vs).
   { induction xs as [|x xs IHx]; intros vs k S Ag Mx Fk; cbn [manyT] in Mx.
     - injection Mx as <- <-. exists 0. intros m _. destruct m; reflexivity.
     - fold (manyT o rho xs) in Mx. rewrite forallb_app in Ag. apply andb_true_iff in Ag as [Ag1 Ag2].
       destruct (stepT o rho x) as [[v k1]|] eqn:Ex; rewrite ?Ex in Mx; cbv beta match in Mx; [|discriminate].
       destruct (manyT o rho xs) as [[vs' k2]|] eqn:Exs; rewrite ?Exs in Mx; cbv beta match in Mx; [|discriminate]. injection Mx as <- <-.
       apply Forall_app in Fk as [F1 F2].
       destruct (H x (S x (or_introl eq_refl)) rho v k1 Ag1 Ex F1) as [n1 N1].
       destruct (IHx vs' k2 (fun e I => S e (or_intror I)) Ag2 eq_refl F2) as [n2 N2].
       exists (Nat.max n1 n2). intros m L. cbn [NativeSimulation.many].
       rewrite (mono n1 m _ _ _ ltac:(lia) N1), (N2 m ltac:(lia)). reflexivity. }
   destruct (manyT o rho es) as [[vs k]|] eqn:Ms; rewrite ?Ms in Hs; cbv beta match in Hs; [|discriminate].
   destruct (dn s) eqn:K; rewrite ?K in Hs; cbv beta match in Hs.
   + destruct (o s vs) as [w'|] eqn:Os; rewrite ?Os in Hs; cbv beta match in Hs; [|discriminate]. injection Hs as <- <-.
     apply Forall_app in F as [F1 F2]. inversion F2 as [|? ? Fc _]; subst.
     destruct Fc as [n2 R]. destruct (M es vs k (fun e I => I) A Ms F1) as [n1 N1].
     unfold run in R. destruct (lookup program s) as [d|] eqn:D; [|discriminate].
     destruct (Nat.eqb _ _) eqn:Ar; [|discriminate].
     exists (S (Nat.max n1 n2)). cbn [eval]. fold (NativeSimulation.many (Nat.max n1 n2) (lookup program) rho es).
     rewrite (N1 (Nat.max n1 n2) ltac:(lia)), D, Ar. apply (mono n2); [lia|exact R].
   + destruct (external s vs) eqn:X; rewrite ?X in Hs; cbv beta match in Hs; try discriminate. injection Hs as <- <-.
     destruct (M es vs _ (fun e I => I) A Ms F) as [n1 N1].
     assert (D : lookup program s = None).
     { pose proof (defined_lookup s) as Dl. rewrite Hd in Dl; rewrite ?K in Dl. destruct (lookup program s); [discriminate|reflexivity]. }
     exists (S n1). cbn [eval]. fold (NativeSimulation.many n1 (lookup program) rho es).
     rewrite (N1 n1 ltac:(lia)), D. exact X.
Qed.

(* One body: a terminating traced run of a program definition's body is a
   terminating Native run of that definition. *)
Theorem total_def : forall o s ps b vs, lookup program s = Some (Def ps b) -> agree defined dn b = true ->
 Nat.eqb (List.length ps) (List.length vs) = true -> Term o (arguments ps vs) b -> exists n w, run n program s vs = Returned w.
Proof.
 intros o s ps b vs L A Ar T. unfold Term in T.
 destruct (stepT o (arguments ps vs) b) as [[w cs]|] eqn:E; [|contradiction].
 destruct (traced o b _ w cs A E T) as [n N]. exists n, w. unfold run. rewrite L. cbn [params body]. rewrite Ar. exact N.
Qed.

(* The reference call table: each program name the EQ-1 acceptance code
   calls, with the reference value of EqualityInductionModel/Kernel/Drivers.
   Partial correctness of the captured code (EqualityInductionSpecs, Helpers,
   Refinement) says the program returns exactly these values when it returns. *)
Definition oref (s : string) (vs : list value) : option value :=
 if String.eqb s "kl:=" then match vs with [a;b] => Some (Boolean (same a b)) | _ => None end
 else if String.eqb s "kl:_scm.assert-boolean" then match vs with [w] => Some w | _ => None end
 else if String.eqb s "kl:not" then match vs with [w] => Some (Boolean (match w with Boolean false => true | _ => false end)) | _ => None end
 else if String.eqb s "kl:symbol?" then match vs with [w] => Some (Boolean (is_sym w)) | _ => None end
 else if String.eqb s "kl:buri.nat?" then match vs with [i] => Some (Boolean (match i with Integer z => Z.leb 0 z | _ => false end)) | _ => None end
 else if String.eqb s "kl:buri.theory" then match vs with [] => Some theory_value | _ => None end
 else if String.eqb s "kl:buri.signature" then match vs with [] => Some signature_value | _ => None end
 else if String.eqb s "kl:buri.constructors" then match vs with [] => Some constructors_value | _ => None end
 else if String.eqb s "kl:buri.rules" then match vs with [] => Some rules_value | _ => None end
 else if String.eqb s "kl:buri.member?" then match vs with [x;ys] => Some (Boolean (r_mem x ys)) | _ => None end
 else if String.eqb s "kl:buri.unique?" then match vs with [xs] => Some (Boolean (r_uniq xs)) | _ => None end
 else if String.eqb s "kl:buri.append" then match vs with [xs;ys] => Some (r_app xs ys) | _ => None end
 else if String.eqb s "kl:buri.rev" then match vs with [xs] => Some (r_revh xs Nil) | _ => None end
 else if String.eqb s "kl:buri.rev-h" then match vs with [xs;a] => Some (r_revh xs a) | _ => None end
 else if String.eqb s "kl:buri.get" then match vs with [k;xs] => Some (r_get k xs) | _ => None end
 else if String.eqb s "kl:buri.keys" then match vs with [xs] => Some (r_keys xs) | _ => None end
 else if String.eqb s "kl:buri.remove" then match vs with [k;xs] => Some (r_remove k xs) | _ => None end
 else if String.eqb s "kl:buri.all-symbols?" then match vs with [xs] => Some (Boolean (r_allsym xs)) | _ => None end
 else if String.eqb s "kl:buri.sig" then match vs with [f;ss] => Some (r_sig f ss) | _ => None end
 else if String.eqb s "kl:buri.sort" then match vs with [t;C] => Some (r_sort t C) | _ => None end
 else if String.eqb s "kl:buri.sort-app" then match vs with [g;xs;C] => Some (match sig_parts g with
   | Some (sorts,r) => if r_args xs sorts C then found r else missing | None => missing end) | _ => None end
 else if String.eqb s "kl:buri.args?" then match vs with [xs;ss;C] => Some (Boolean (r_args xs ss C)) | _ => None end
 else if String.eqb s "kl:buri.context?" then match vs with [C] => Some (Boolean (r_ctx C)) | _ => None end
 else if String.eqb s "kl:buri.context-h?" then match vs with [C] => Some (Boolean (r_ctxh C)) | _ => None end
 else if String.eqb s "kl:buri.subst" then match vs with [t;sub] => Some (r_subst t sub) | _ => None end
 else if String.eqb s "kl:buri.substs" then match vs with [a;sub] => Some (r_substs a sub) | _ => None end
 else if String.eqb s "kl:buri.subst-var" then match vs with [x;b] => Some (subst_var x b) | _ => None end
 else if String.eqb s "kl:buri.rule" then match vs with [n;rs] => Some (r_rule n rs) | _ => None end
 else if String.eqb s "kl:buri.fresh?" then match vs with [xs;ys] => Some (Boolean (r_fresh xs ys)) | _ => None end
 else if String.eqb s "kl:buri.zip" then match vs with [xs;ys] => Some (r_zip xs ys) | _ => None end
 else if String.eqb s "kl:buri.zip-h" then match vs with [x;y;z] => Some (match tagged "zipped" z with
   | Some zs => L [sym "zipped";Pair (L [x;y]) zs] | None => mismatch end) | _ => None end
 else if String.eqb s "kl:buri.variables" then match vs with [ns] => Some (r_vars ns) | _ => None end
 else if String.eqb s "kl:buri.induction-hyps" then match vs with [bs;x;g;l;r] => Some (r_ihyps bs x g l r) | _ => None end
 else if String.eqb s "kl:buri.resolve" then match vs with [ref;hs;ls] => Some (r_resolve ref hs ls) | _ => None end
 else if String.eqb s "kl:buri.replace-head" then match vs with [x;ts] => Some (r_head x ts) | _ => None end
 else if String.eqb s "kl:buri.replace-tail" then match vs with [t;x] => Some (r_tail t x) | _ => None end
 else if String.eqb s "kl:buri.replace-app" then match vs with [f;x] => Some (r_rapp f x) | _ => None end
 else if String.eqb s "kl:buri.instantiate" then match vs with [rl;sub;C] => Some (r_inst rl sub C) | _ => None end
 else if String.eqb s "kl:buri.substitution?" then match vs with [vars;sub;C] => Some (Boolean (r_substitution vars sub C)) | _ => None end
 else if String.eqb s "kl:buri.replace" then match vs with [t;p;a;b] => Some (r_replace t p a b) | _ => None end
 else if String.eqb s "kl:buri.replace-arg" then match vs with [args;Integer z;is;a;b] => Some (r_rarg args z is a b) | _ => None end
 else if String.eqb s "kl:buri.goal?" then match vs with [C;l;r] => Some (Boolean (r_goal C l r)) | _ => None end
 else if String.eqb s "kl:buri.check-steps" then match vs with [l;r;steps;C;hs;ls;Integer n] => Some (r_steps l r steps C hs ls n) | _ => None end
 else if String.eqb s "kl:buri.check-step-result" then match vs with [e;path;dir;l;r;steps;C;hs;ls;Integer n] =>
   Some (csr1 e path dir l r steps C hs ls n) | _ => None end
 else if String.eqb s "kl:buri.after-rewrite" then match vs with [x;r;steps;C;hs;ls;Integer n] => Some (after1 x r steps C hs ls n) | _ => None end
 else if String.eqb s "kl:buri.check-cases" then match vs with [ctors;cases;X;C;l;r;ls;Integer n] =>
   Some (r_cases ctors cases X C l r ls n) | _ => None end
 else if String.eqb s "kl:buri.check-case-bound" then match vs with [z;ctor;ctors;cases;names;steps;X;C;l;r;ls;Integer n] =>
   Some (bound1 z ctor ctors cases names steps X C l r ls n) | _ => None end
 else if String.eqb s "kl:buri.check-theorem" then match vs with [C;l;r;p;ls;Integer n] => Some (r_theorem C l r p ls n) | _ => None end
 else if String.eqb s "kl:buri.bundle-h" then match vs with [b;ls;Integer n] => Some (r_bundle b ls n) | _ => None end
 else if String.eqb s "kl:buri.bundle-next" then match vs with [res;name;C;l;r;rest;ls;Integer n] =>
   Some (next1 res name C l r rest ls n) | _ => None end
 else if String.eqb s "kl:str" then match vs with [Integer z] => Some (Text (spelling z)) | _ => None end
 else if String.eqb s "kl:buri.digits?" then match vs with [Text t] => Some (Boolean (alldig t)) | _ => None end
 else if String.eqb s "kl:buri.unsigned-spelling?" then match vs with [Text t] => Some (Boolean (unsigned t)) | _ => None end
 else if String.eqb s "kl:buri.integer-spelling?" then match vs with [Text t] => Some (Boolean (ispell t)) | _ => None end
 else if String.eqb s "kl:buri.exact-integer?" then match vs with [Integer z] => Some (Boolean (ispell (spelling z))) | _ => None end
 else None.

(* Domain predicates on which the captured code is total. [idata]: no
   non-integer numbers (the Native number primitives used by nat? support
   integers only). The others describe the validated internal data the
   kernel hands to its partial helpers (Shen functions without a fallback
   clause raise a pattern-match error outside them). *)
Fixpoint idata v := match v with Fraction _ _ | Inexact _ => false | Pair a b => idata a && idata b | _ => true end.
Definition numok v := match v with Fraction _ _ | Inexact _ => false | _ => true end.
Fixpoint lst v := match v with Nil => true | Pair _ r => lst r | _ => false end.
Fixpoint kv v := match v with Nil => true | Pair (Pair _ (Pair _ Nil)) r => kv r | _ => false end.
(* [tm]: a first-order term as buri.subst traverses it: a variable [v X], or
   an application whose argument list is a proper list of terms. *)
Definition symeq s x := match x with Symbol t => String.eqb s t | _ => false end.
#[global] Arguments symeq : simpl nomatch.
Definition symv f := symeq "v" f.
Definition single a := match a with Pair _ Nil => true | _ => false end.
Fixpoint tm t := match t with Pair f args => (symv f && single args) || tms args | _ => false end
with tms a := match a with Nil => true | Pair u r => tm u && tms r | _ => false end.
Lemma tm_pair : forall a b, tm (Pair a b) = match var_of (Pair a b) with Some _ => true | None => tms b end.
Proof.
 intros a b. cbn [tm]. destruct a; try reflexivity. cbn [symv symeq var_of].
 destruct (String.eqb "v" s); destruct b as [| | | | | | |x [| | | | | | | | |]| |]; reflexivity.
Qed.
Fixpoint wfr rs := match rs with
 | Nil => true
 | Pair (Pair _ (Pair _ (Pair l (Pair r Nil)))) rest => tm l && tm r && wfr rest
 | _ => false end.
Definition rl_ok rl := match rl with Pair (Symbol _) (Pair _ (Pair l (Pair r Nil))) => tm l && tm r | _ => true end.
Definition zok z := match tagged "zipped" z with Some bs => kv bs | None => true end.
Fixpoint sigok ss := match ss with Nil => true | Pair (Pair _ (Pair _ (Pair _ Nil))) rest => sigok rest | _ => false end.

Fixpoint tmv xs := match xs with Pair (Pair _ (Pair v Nil)) r => tm v && tmv r | _ => true end.
(* Propagation of the domain predicates through the reference functions. *)
Lemma lst_keys : forall C, lst (r_keys C) = true.
Proof. induction C as [| | | | | | |a _ b IH| |]; try reflexivity. destruct a as [| | | | | | |k [| | | | | | |x [| | | | | | | | |]| |]| |]; cbn; auto. Qed.
Lemma allsym_lst : forall xs, r_allsym xs = true -> lst xs = true.
Proof. induction xs; cbn; try discriminate; auto. intro H; apply andb_true_iff in H as [_ H]; auto. Qed.
Lemma kv_lst : forall xs, kv xs = true -> lst xs = true.
Proof. induction xs as [| | | | | | |a _ b IH| |]; cbn; try discriminate; auto. destruct a as [| | | | | | |k [| | | | | | |x [| | | | | | | | |]| |]| |]; try discriminate; auto. Qed.
Lemma wfr_lst : forall xs, wfr xs = true -> lst xs = true.
Proof.
 induction xs as [| | | | | | |a _ b IH| |]; cbn; try discriminate; auto.
 destruct a as [| | | | | | |k [| | | | | | |x [| | | | | | |l [| | | | | | |r [| | | | | | | | |]| |]| |]| |]| |]; try discriminate.
 intro H; apply andb_true_iff in H as [_ H]; auto.
Qed.
Lemma ctxh_kv : forall C, r_ctxh C = true -> kv C = true.
Proof.
 induction C as [| | | | | | |a _ b IH| |]; cbn; try discriminate; auto.
 destruct a as [| | | | | | |k [| | | | | | |x [| | | | | | | | |]| |]| |]; try discriminate.
 intro H; apply andb_true_iff in H as [_ H]; auto.
Qed.
Lemma ctx_kv : forall C, r_ctx C = true -> kv C = true.
Proof. intros C H. unfold r_ctx in H. apply andb_true_iff in H as [H _]. apply ctxh_kv; exact H. Qed.
Lemma kv_app : forall a b, kv a = true -> kv b = true -> kv (r_app a b) = true.
Proof.
 induction a as [| | | | | | |x _ r IH| |]; cbn; try discriminate; auto.
 destruct x as [| | | | | | |k [| | | | | | |y [| | | | | | | | |]| |]| |]; try discriminate. cbn. auto.
Qed.
Lemma kv_remove : forall k xs, kv xs = true -> kv (r_remove k xs) = true.
Proof.
 intro k; induction xs as [| | | | | | |x _ r IH| |]; cbn; try discriminate; auto.
 destruct x as [| | | | | | |j [| | | | | | |y [| | | | | | | | |]| |]| |]; try discriminate.
 intro H. destruct (same k j); cbn; auto.
Qed.
Lemma zok_zip : forall xs ys, zok (r_zip xs ys) = true.
Proof.
 assert (G : forall xs ys bs, tagged "zipped" (r_zip xs ys) = Some bs -> kv bs = true).
 { induction xs as [| | | | | | |x _ r IH| |]; intros [| | | | | | |y ys| |] bs H; cbn in H; try discriminate.
   - injection H as <-; reflexivity.
   - destruct (tagged "zipped" (r_zip r ys)) as [zs|] eqn:T; cbn in H; [|discriminate].
     injection H as <-. cbn. exact (IH ys zs T). }
 intros xs ys. unfold zok. destruct (tagged "zipped" (r_zip xs ys)) eqn:T; [exact (G _ _ _ T)|reflexivity].
Qed.
Lemma tmv_get : forall x sub, tmv sub = true -> tm (subst_var x (r_get x sub)) = true.
Proof.
 intros x sub; induction sub as [| | | | | | |a _ b IH| |]; cbn; try reflexivity.
 destruct a as [| | | | | | |j [| | | | | | |v [| | | | | | | | |]| |]| |]; try reflexivity.
 intro H; apply andb_true_iff in H as [Hv H]. destruct (same x j); [exact Hv|exact (IH H)].
Qed.
Lemma tm_subst : forall t sub, tmv sub = true -> (tm t = true -> tm (r_subst t sub) = true) /\ (tms t = true -> tms (r_substs t sub) = true).
Proof.
 intros t sub S; induction t as [| | | | | | |a [IHa IHa'] b [IHb IHb']| |]; split; intro H; try discriminate; try exact H.
 - rewrite tm_pair in H. cbn [r_subst]. destruct (var_of (Pair a b)) eqn:V; [apply tmv_get; exact S|].
   rewrite tm_pair. destruct (var_of (Pair a (r_substs b sub))); [reflexivity|exact (IHb' H)].
 - cbn [tms r_substs] in H |- *. apply andb_true_iff in H as [H1 H2]. rewrite (IHa H1), (IHb' H2). reflexivity.
Qed.
Lemma wfr_ihyps : forall bs x g l r, tm l = true -> tm r = true -> wfr (r_ihyps bs x g l r) = true.
Proof.
 intros bs x g l r Hl Hr. induction bs as [| | | | | | |a _ b IH| |]; try reflexivity.
 cbn [r_ihyps]. destruct a as [| | | | | | |k [| | | | | | |e [| | | | | | | | |]| |]| |]; try exact IH; try (destruct e; exact IH).
 destruct e; try exact IH. destruct (String.eqb "expr" s); [|exact IH].
 cbn [wfr L fold_right]. rewrite IH, andb_true_r. apply andb_true_iff; split; [refine (proj1 (tm_subst _ _ _) Hl)|refine (proj1 (tm_subst _ _ _) Hr)]; reflexivity.
Qed.
Lemma rl_rule : forall n rs, wfr rs = true -> rl_ok (r_rule n rs) = true.
Proof.
 intro n; induction rs as [| | | | | | |a _ b IH| |]; cbn; try reflexivity.
 destruct a as [| | | | | | |m [| | | | | | |vs [| | | | | | |l [| | | | | | |r [| | | | | | | | |]| |]| |]| |]| |]; try discriminate.
 intro H. apply andb_true_iff in H as [H W]. destruct (same n m); [exact H|exact (IH W)].
Qed.
Lemma wfr_rules : wfr rules_value = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sigok_signature : sigok signature_value = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rl_resolve : forall ref hs ls, wfr hs = true -> wfr ls = true -> rl_ok (r_resolve ref hs ls) = true.
Proof.
 intros ref hs ls H L. unfold r_resolve.
 destruct ref as [| | | | | | |[| t | | | | | | | |] [| | | | | | |n [| | | | | | | | |]| |]| |]; try reflexivity.
 destruct (String.eqb "definition" t); [apply rl_rule, wfr_rules|].
 destruct (String.eqb "hypothesis" t); [apply rl_rule; exact H|].
 destruct (String.eqb "lemma" t); [apply rl_rule; exact L|reflexivity].
Qed.
Lemma substitution_kv : forall vars sub C, r_substitution vars sub C = true -> kv sub = true.
Proof.
 induction vars as [| | | | | | |a _ b IH| |]; intros sub C H; cbn in H; try discriminate.
 - destruct sub; try discriminate; reflexivity.
 - destruct a as [| | | | | | |x [| | | | | | |s0 [| | | | | | | | |]| |]| |]; try (cbn in H; discriminate H);
   destruct sub as [| | | | | | |c9 d9| |]; try (cbn in H; discriminate H);
   destruct c9 as [| | | | | | |x' [| | | | | | |t [| | | | | | | | |]| |]| |]; try (cbn in H; discriminate H).
   cbn in H. destruct (same x x'); [|discriminate]. apply andb_true_iff in H as [_ H]. cbn. exact (IH _ _ H).
Qed.
Lemma same_missing : forall a b, same a b = true -> is_missing a = false -> is_missing b = false.
Proof.
 intros a [| t | | | | | | | |] S M; try reflexivity. destruct a; try discriminate. cbn in S, M |- *.
 apply String.eqb_eq in S; subst. exact M.
Qed.
Lemma same_found : forall x s, same x (found s) = true -> is_missing x = false.
Proof. intros x s H; destruct x; try reflexivity. cbn in H. discriminate H. Qed.
Lemma sort_tm : forall t C, (is_missing (r_sort t C) = false -> tm t = true) /\ (forall ss, r_args t ss C = true -> tms t = true).
Proof.
 intros t C; induction t as [| | | | | | |a [IHa IHa'] b [IHb IHb']| |]; split; intros; try discriminate; try reflexivity.
 - rewrite tm_pair. destruct (var_of (Pair a b)) eqn:V; [reflexivity|].
   rewrite (r_sort_app a b C V) in H.
   destruct (sig_parts (r_sig a signature_value)) as [[sorts r]|]; [|discriminate].
   destruct (r_args b sorts C) eqn:A; [exact (IHb' _ A)|discriminate].
 - cbn [r_args] in H. destruct ss as [| | | | | | |s ss| |]; try discriminate. apply andb_true_iff in H as [H1 H2].
   cbn [tms]. rewrite (IHa (same_found _ _ H1)), (IHb' _ H2). reflexivity.
Qed.
Lemma goal_ok : forall C l r, r_goal C l r = true -> kv C = true /\ tm l = true /\ tm r = true.
Proof.
 intros C l r H. unfold r_goal in H. apply andb_true_iff in H as [H S]. apply andb_true_iff in H as [Cx M].
 apply negb_true_iff in M. split; [exact (ctx_kv _ Cx)|].
 split; [exact (proj1 (sort_tm l C) M)|exact (proj1 (sort_tm r C) (same_missing _ _ S M))].
Qed.
End EqualityInductionTrace.
