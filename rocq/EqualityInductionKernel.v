(* BURI/EQ-1 reference acceptance kernel. A total Rocq function over raw
   values that mirrors shen/kernel.shen clause by clause (the budget is an
   integer; the Shen code additionally requires its decimal spelling), and
   its soundness for the standard model of BURI/ARITH-1: every accepted
   bundle lists only theorems that are well-sorted in a well-formed context and
   valid for every well-typed assignment, including those proved by
   structural induction over expr. That the captured Shen-Scheme drivers
   compute this function is the open obligation EQ1-DRIVERS (docs/EQ1.md);
   their leaf helpers are proved in EqualityInductionSpecs/Helpers. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Arithmetic Native EqualityInductionModel.
Import ListNotations Native.Native.
Module EqualityInductionKernel.
Import EqualityInductionModel.EqualityInductionModel.
Open Scope string_scope.

Definition checked := Symbol "checked".
Definition verdict v := v = checked \/ (exists s, v = rejected s) \/ v = L [sym "unknown";sym "proof-budget"].
Definition is_checked v := match v with Symbol s => String.eqb "checked" s | _ => false end.
Definition rewrite_parts st := match st with
 | Pair (Symbol t) (Pair path (Pair dir (Pair ref (Pair sub Nil)))) =>
   if String.eqb "rewrite" t then Some (path,dir,ref,sub) else None
 | _ => None end.
Definition equation_parts e := match e with
 | Pair (Symbol t) (Pair a (Pair b Nil)) => if String.eqb "equation" t then Some (a,b) else None
 | _ => None end.
Definition direction d := match d with
 | Symbol s => if String.eqb "forward" s then Some true else if String.eqb "reverse" s then Some false else None
 | _ => None end.
(* check-steps / check-step-result / after-rewrite *)
Fixpoint r_steps (l r steps C hs ls : value) (n : Z) {struct steps} : value := match steps with
 | Nil => if same l r then checked else rejected "conclusion-mismatch"
 | Pair st rest =>
   if Z.eqb 0 n then L [sym "unknown";sym "proof-budget"] else
   match rewrite_parts st with
   | Some (path,dir,ref,sub) =>
     match equation_parts (r_inst (r_resolve ref hs ls) sub C),direction dir with
     | Some (a,b),Some fwd =>
       match tagged "replaced" (if fwd then r_replace l path a b else r_replace l path b a) with
       | Some l' => r_steps l' r rest C hs ls (n-1)
       | None => rejected "rewrite-does-not-match" end
     | _,_ => rejected "invalid-rule-instance" end
   | None => rejected "malformed-rewrite" end
 | _ => rejected "malformed-rewrite" end.
Definition case_parts c := match c with
 | Pair ctor (Pair names (Pair steps Nil)) => Some (ctor,names,steps) | _ => None end.
Definition ctor_parts c := match c with Pair ctor (Pair sorts Nil) => Some (ctor,sorts) | _ => None end.
(* check-cases / check-case-bound *)
Fixpoint r_cases (ctors cases X C l r ls : value) (n : Z) {struct ctors} : value := match ctors,cases with
 | Nil,Nil => checked
 | Pair c ctors',Pair d cases' => match ctor_parts c,case_parts d with
   | Some (ctor,sorts),Some (ctor',names,steps) =>
     if same ctor ctor' then
       if r_allsym names && r_uniq names && r_fresh names (r_keys C) then
         match tagged "zipped" (r_zip names sorts) with
         | Some bs =>
           let G := r_remove X C in
           let inst := one X (Pair ctor' (r_vars names)) in
           let res := r_steps (r_subst l inst) (r_subst r inst) steps (r_app bs G) (r_ihyps bs X G l r) ls n in
           if is_checked res then r_cases ctors' cases' X C l r ls n else res
         | None => rejected "constructor-arity" end
       else rejected "induction-variable-capture"
     else rejected "missing-or-wrong-induction-case"
   | _,_ => rejected "missing-or-wrong-induction-case" end
 | _,_ => rejected "missing-or-wrong-induction-case" end.
Definition expr_ctors := L [L [sym "lit";L [sym "nat"]];L [sym "add";L [sym "expr";sym "expr"]];
 L [sym "mul";L [sym "expr";sym "expr"]]].
Definition r_theorem C l r proof ls n := match proof with
 | Pair (Symbol t) (Pair steps Nil) =>
   if String.eqb "direct" t then r_steps l r steps C Nil ls n else rejected "malformed-proof"
 | Pair (Symbol t) (Pair X (Pair cases Nil)) =>
   if String.eqb "induct" t then
     if same (r_get X C) (found (sym "expr")) then r_cases expr_ctors cases X C l r ls n
     else rejected "unsupported-induction-sort"
   else rejected "malformed-proof"
 | _ => rejected "malformed-proof" end.
Definition theorem_parts t := match t with
 | Pair (Symbol s) (Pair name (Pair C (Pair l (Pair r (Pair proof Nil))))) =>
   if String.eqb "theorem" s then Some (name,C,l,r,proof) else None
 | _ => None end.
Definition accepted out := L [sym "accepted";sym "generic-equations";out].
(* bundle-h / bundle-next *)
Fixpoint r_bundle (b ls : value) (n : Z) {struct b} : value := match b with
 | Nil => accepted (r_revh ls Nil)
 | Pair t rest => match theorem_parts t with
   | Some (name,C,l,r,proof) =>
     if is_sym name && is_missing (r_rule name ls) then
       if r_goal C l r then
         let v := r_theorem C l r proof ls n in
         if is_checked v then r_bundle rest (Pair (L [name;C;l;r]) ls) n else v
       else rejected "ill-sorted-theorem"
     else rejected "duplicate-or-invalid-name"
   | None => rejected "malformed-bundle" end
 | _ => rejected "malformed-bundle" end.
(* check-bundle; the trap-error handler only ever yields a rejection. *)
Definition r_check_bundle T B N := if same T theory_value then
 match N with Integer z => if Z.leb 0 z then r_bundle B Nil z else rejected "invalid-budget"
 | _ => rejected "invalid-budget" end
 else rejected "theory-mismatch".

(* Verdicts: the drivers never fabricate an acceptance. *)
Lemma checked_is : forall v, is_checked v = true -> v = checked.
Proof. intros [] H; try discriminate. apply String.eqb_eq in H; subst; reflexivity. Qed.
Lemma steps_verdict : forall steps l r C hs ls n, verdict (r_steps l r steps C hs ls n).
Proof.
 induction steps; intros; cbn [r_steps]; unfold verdict;
 try (right; left; eexists; reflexivity).
 - destruct (same l r); [left; reflexivity|right; left; eexists; reflexivity].
 - destruct (Z.eqb 0 n); [right; right; reflexivity|].
   destruct (rewrite_parts steps1) as [[[[path dir] ref] sub]|]; [|right; left; eexists; reflexivity].
   destruct (equation_parts _) as [[a b]|]; [|right; left; eexists; reflexivity].
   destruct (direction dir) as [fwd|]; [|right; left; eexists; reflexivity].
   destruct (tagged _ _); [apply IHsteps2|right; left; eexists; reflexivity].
Qed.
Lemma cases_verdict : forall ctors cases X C l r ls n, verdict (r_cases ctors cases X C l r ls n).
Proof.
 induction ctors; intros; destruct cases; cbn [r_cases]; unfold verdict;
 try (right; left; eexists; reflexivity); try (left; reflexivity).
 destruct (ctor_parts ctors1) as [[ctor sorts]|]; [|right; left; eexists; reflexivity].
 destruct (case_parts cases1) as [[[ctor' names] steps]|]; [|right; left; eexists; reflexivity].
 destruct (same ctor ctor'); [|right; left; eexists; reflexivity].
 destruct (_ && _); [|right; left; eexists; reflexivity].
 destruct (tagged _ _) as [bs|]; [|right; left; eexists; reflexivity]. cbv zeta.
 destruct (is_checked _) eqn:K; [apply IHctors2|apply steps_verdict].
Qed.
Lemma theorem_verdict : forall C l r proof ls n, verdict (r_theorem C l r proof ls n).
Proof.
 intros. unfold r_theorem. unfold verdict.
 destruct proof as [|s9|s8|z9|n9 d9|t9|b9|t p|c9|h9]; try (right; left; eexists; reflexivity).
 destruct t; try (right; left; eexists; reflexivity).
 destruct p as [|s9|s8|z9|n9 d9|t9|b9|a p|c9|h9]; try (right; left; eexists; reflexivity).
 destruct p as [|s9|s8|z9|n9 d9|t9|b9|b p|c9|h9]; try (right; left; eexists; reflexivity).
 - destruct (String.eqb "direct" s); [apply steps_verdict|right; left; eexists; reflexivity].
 - destruct p; try (right; left; eexists; reflexivity).
   destruct (String.eqb "induct" s); [|right; left; eexists; reflexivity].
   destruct (same _ _); [apply cases_verdict|right; left; eexists; reflexivity].
Qed.

(* Soundness of the reference kernel. *)
Definition entry_ok e := exists name C l r, e = L [name;C;l;r] /\ is_sym name = true /\
 r_goal C l r = true /\ valid C l r.
Definition all_ok ls := forall e, entry_in e ls -> entry_ok e.
Definition lemmas_true ls := forall rho, rules_true rho ls.
Lemma lemmas_true_of : forall ls, all_ok ls -> lemmas_true ls.
Proof.
 intros ls A rho n vars l r H. apply rule_member in H as [m I].
 destruct (A _ I) as (name & C & l' & r' & E & _ & G & V). injection E as -> -> -> ->.
 unfold r_goal in G. apply andb_true_iff in G as [G _]. apply andb_true_iff in G as [Cx _].
 split; [apply ctx_keys; apply andb_true_iff in Cx; tauto|].
 intros rho' OK _. apply V. exact OK.
Qed.
Lemma equation_shape : forall e a b, equation_parts e = Some (a,b) -> e = L [sym "equation";a;b].
Proof.
 intros e a b H. destruct e as [|s9|s8|z9|n9 d9|t9|b9|t e|c9|h9]; try discriminate. destruct t; try discriminate.
 destruct e as [|s9|s8|z9|n9 d9|t9|b9|x e|c9|h9]; try discriminate. destruct e as [|s9|s8|z9|n9 d9|t9|b9|y e|c9|h9]; try discriminate.
 destruct e; try discriminate. cbn -[String.eqb] in H. destruct (String.eqb "equation" s) eqn:Q; [|discriminate].
 apply String.eqb_eq in Q; subst. injection H as -> ->. reflexivity.
Qed.
Lemma steps_sound : forall steps l r C hs ls n, r_steps l r steps C hs ls n = checked ->
 forall rho, env_ok rho C -> table_true rho hs ls -> denote rho l = denote rho r.
Proof.
 induction steps as [|s9|s8|z9|n9 d9|t9|b9|st _ rest IH|c9|h9]; intros l r C hs ls n H rho OK T; cbn [r_steps] in H;
 try discriminate.
 - destruct (same l r) eqn:S; [|discriminate]. exact (proj1 (same_denote _ _ rho S)).
 - destruct (Z.eqb 0 n); [discriminate|].
   destruct (rewrite_parts st) as [[[[path dir] ref] sub]|]; [|discriminate].
   destruct (equation_parts _) as [[a b]|] eqn:Eq; [|discriminate].
   destruct (direction dir) as [fwd|]; [|discriminate].
   destruct (tagged _ _) as [l'|] eqn:T'; [|discriminate].
   apply equation_shape in Eq. pose proof (instance_sound _ _ _ _ _ _ _ _ T OK Eq) as AB.
   apply tagged_shape in T'. rewrite <- (IH _ _ _ _ _ _ H rho OK T).
   destruct fwd.
   + exact (replace_sound _ _ _ _ AB _ _ T').
   + exact (replace_sound _ _ _ _ (eq_sym AB) _ _ T').
Qed.
Lemma cases_sound : forall ctors cases X C l r ls n, r_cases ctors cases X C l r ls n = checked ->
 lemmas_true ls -> forall c ctor sorts, entry_in c ctors -> ctor_parts c = Some (ctor,sorts) ->
 is_sym ctor = true -> case_ok C X l r ctor sorts.
Proof.
 induction ctors as [|s9|s8|z9|n9 d9|t9|b9|c0 _ ctors' IH|c9|h9]; intros cases X C l r ls n H Ls c ctor sorts I P Sy;
 try contradiction. destruct cases as [|s9|s8|z9|n9 d9|t9|b9|d cases'|c9|h9]; cbn [r_cases] in H; try discriminate.
 destruct (ctor_parts c0) as [[ctor0 sorts0]|] eqn:P0; [|discriminate].
 destruct (case_parts d) as [[[ctor' names] steps]|]; [|discriminate].
 destruct (same ctor0 ctor') eqn:Sc; [|discriminate].
 destruct (r_allsym names && r_uniq names && r_fresh names (r_keys C)) eqn:N; [|discriminate].
 destruct (tagged "zipped" (r_zip names sorts0)) as [bs|] eqn:Z; [|discriminate]. cbv zeta in H.
 destruct (is_checked _) eqn:K.
 - destruct I as [<-|I]; [|exact (IH _ _ _ _ _ _ _ H Ls _ _ _ I P Sy)].
   rewrite P0 in P. injection P as <- <-. destruct ctor0; try discriminate Sy.
   apply same_symbol_l in Sc. subst ctor'.
   apply andb_true_iff in N as [N F]. apply andb_true_iff in N as [A U].
   exists names, bs. split; [exact A|]. split; [exact U|]. split; [exact F|].
   split; [exact (tagged_shape _ _ _ Z)|].
   intros rhob OK Hy. apply checked_is in K.
   apply (steps_sound _ _ _ _ _ _ _ K rhob OK). split; [apply rules_value_true|]. split; [exact Hy|apply Ls].
 - rewrite H in K. discriminate K.
Qed.
Lemma sort_cases : forall t C, r_sort t C = missing \/ exists s, r_sort t C = found s.
Proof.
 intros t C. destruct t as [|s9|s8|z9|n9 d9|t9|b9|f args|c9|h9]; try (left; reflexivity).
 destruct (var_of (Pair f args)) eqn:V.
 - cbn [r_sort]. rewrite V. apply r_get_cases.
 - rewrite r_sort_app by exact V. destruct (sig_parts _) as [[sorts r]|]; [|left; reflexivity].
   destruct (r_args _ _ _); [right; eexists; reflexivity|left; reflexivity].
Qed.
Lemma same_nil_l : forall a, same Nil a = true -> a = Nil.
Proof. intros a H; destruct a; cbn in H; try discriminate; reflexivity. Qed.
Lemma goal_parts : forall C l r, r_goal C l r = true ->
 r_ctx C = true /\ (exists s, r_sort l C = found s) /\ (exists s, r_sort r C = found s).
Proof.
 intros C l r G. unfold r_goal in G. apply andb_true_iff in G as [G S]. apply andb_true_iff in G as [Cx M].
 split; [exact Cx|]. destruct (sort_cases l C) as [E|[s E]]; rewrite E in M, S; [discriminate|].
 split; [eauto|]. apply same_pair_l in S as (x & y & Ey & _ & Y).
 apply same_pair_l in Y as (u & w & -> & _ & W). apply same_nil_l in W. subst.
 destruct (sort_cases r C) as [E'|[s' E']]; rewrite E' in Ey; [discriminate|]. eauto.
Qed.
Lemma theorem_sound : forall C l r proof ls n, r_theorem C l r proof ls n = checked ->
 r_goal C l r = true -> lemmas_true ls -> valid C l r.
Proof.
 intros C l r proof ls n H G Ls. destruct (goal_parts _ _ _ G) as (Cx & [sl Sl] & [sr Sr]).
 intros rho OK. split.
 { destruct (sort_denotes _ _ _ _ OK Sl) as (d & D & _). rewrite D. discriminate. }
 unfold r_theorem in H.
 destruct proof as [|s9|s8|z9|n9 d9|t9|b9|t p|c9|h9]; try discriminate. destruct t; try discriminate.
 destruct p as [|s9|s8|z9|n9 d9|t9|b9|a p|c9|h9]; try discriminate. destruct p as [|s9|s8|z9|n9 d9|t9|b9|b p|c9|h9]; try discriminate.
 - destruct (String.eqb "direct" s); [|discriminate].
   apply (steps_sound _ _ _ _ _ _ _ H rho OK). split; [apply rules_value_true|]. split; [|apply Ls].
   intros m vars l' r' R. discriminate R.
 - destruct p; try discriminate. destruct (String.eqb "induct" s); [|discriminate].
   destruct (same (r_get a C) (found (sym "expr"))) eqn:Gx; [|discriminate].
   assert (Gx' : r_get a C = found (sym "expr")).
   { apply same_pair in Gx as (x & y & -> & X & Y). apply same_symbol in X; subst.
     apply same_pair in Y as (u & w & -> & U & W). apply same_symbol in U. apply same_nil in W. subst. reflexivity. }
   assert (Cs := cases_sound _ _ _ _ _ _ _ _ H Ls).
   apply (induction_sound C a l r Cx Gx' (ex_intro _ sl Sl) (ex_intro _ sr Sr)); try assumption.
   + apply (Cs _ _ _ (or_introl eq_refl) eq_refl eq_refl).
   + apply (Cs _ _ _ (or_intror (or_introl eq_refl)) eq_refl eq_refl).
   + apply (Cs _ _ _ (or_intror (or_intror (or_introl eq_refl))) eq_refl eq_refl).
Qed.
Lemma revh_member : forall ls acc e, entry_in e (r_revh ls acc) -> entry_in e ls \/ entry_in e acc.
Proof.
 induction ls as [|s9|s8|z9|n9 d9|t9|b9|x _ rest IH|c9|h9]; intros acc e I; cbn [r_revh] in I; try (right; exact I).
 destruct (IH _ _ I) as [J|[J|J]]; [left; right; exact J|left; left; exact J|right; exact J].
Qed.
Theorem bundle_sound : forall b ls n out, all_ok ls -> r_bundle b ls n = accepted out -> all_ok out.
Proof.
 induction b as [|s9|s8|z9|n9 d9|t9|b9|t _ rest IH|c9|h9]; intros ls n out A H; cbn [r_bundle] in H; try discriminate.
 - injection H as <-. intros e I. destruct (revh_member _ _ _ I) as [J|[]]. exact (A _ J).
 - destruct (theorem_parts t) as [[[[[name C] l] r] proof]|] eqn:Tp; [|discriminate].
   destruct (is_sym name && is_missing (r_rule name ls)) eqn:Nm; [|discriminate].
   destruct (r_goal C l r) eqn:G; [|discriminate]. cbv zeta in H.
   destruct (is_checked (r_theorem C l r proof ls n)) eqn:K.
   + refine (IH _ _ _ _ H). intros e [<-|I]; [|exact (A _ I)].
     exists name, C, l, r. split; [reflexivity|]. split; [apply andb_true_iff in Nm; tauto|].
     split; [exact G|]. apply checked_is in K. exact (theorem_sound _ _ _ _ _ _ K G (lemmas_true_of _ A)).
   + destruct (theorem_verdict C l r proof ls n) as [E|[[s E]|E]]; rewrite E in H; discriminate H.
Qed.
Theorem check_bundle_sound : forall T B N out, r_check_bundle T B N = accepted out ->
 same T theory_value = true /\ all_ok out.
Proof.
 intros T B N out H. unfold r_check_bundle in H. destruct (same T theory_value) eqn:S; [|discriminate].
 split; [reflexivity|]. destruct N; try discriminate. destruct (Z.leb 0 z); [|discriminate].
 apply (bundle_sound _ _ _ _ (fun e (I : entry_in e Nil) => match I with end) H).
Qed.
(* Stale or substituted theories are rejected before any proof is read. *)
Theorem stale_theory_rejected : forall T B N, same T theory_value = false ->
 r_check_bundle T B N = rejected "theory-mismatch".
Proof. intros T B N S. unfold r_check_bundle. rewrite S. reflexivity. Qed.
(* No accepted bundle, however its certificates or labels are forged,
   contains a false equation; e.g. x = succ x over nat. *)
Theorem false_lemma_never_accepted : forall T B N out name,
 r_check_bundle T B N = accepted out ->
 ~ entry_in (L [name;L [L [sym "x";sym "nat"]];v "x";ap "succ" [v "x"]]) out.
Proof.
 intros T B N out name H I. destruct (check_bundle_sound _ _ _ _ H) as [_ A].
 destruct (A _ I) as (n' & C & l & r & E & _ & _ & V). injection E as E1 E2 E3 E4; subst C l r.
 set (rho := fun s : string => if String.eqb s "x" then Some (DNat O) else None).
 assert (OK : env_ok rho (L [L [sym "x";sym "nat"]])).
 { intros k s G. cbn [L fold_right r_get] in G. destruct (same k (sym "x")) eqn:Q; [|discriminate].
   apply same_symbol in Q. subst. injection G as <-. exists "x", (DNat O). split; [reflexivity|]. split; reflexivity. }
 destruct (V rho OK) as [_ D]. unfold rho in D. vm_compute in D. congruence.
Qed.
End EqualityInductionKernel.
