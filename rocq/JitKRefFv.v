(* Shen/JIT Phase 2: free variables against scoping, and the fv lemmas fund_gen's induction needs
   (r1-fv-mutants). fv, scoped and fund_below are JitKRef.v's; this file adds no Definition that
   changes them, and proves:

   - expr_ind': induction on expr with the clauses of ECond and the arguments of EApp and ECall
     under Forall (Rocq's generated expr_ind gives no hypothesis for list elements).
   - fv_cond, fv_app, fv_call, scoped_cond: fv and scoped on the list forms, as flat_map and
     forallb.
   - scoped_fv: scoped g e = true -> forall x, In x (fv e) -> In x g. The one direction KRef_refl
     needs: an expression scoped in g has no free variable outside g.
   - The binder lemmas: fv_lam_iff, fv_let_iff (a name is free under a binder iff it is free in
     the body and is not the binder), fv_defun (a defun has no free variable: its body is scoped
     by its parameters, scoped_defun_fv), and the list lemmas fv_cond_iff, fv_app_iff,
     fv_call_iff.
   - fund_below's scope condition (fv_scope, the unfolded hypothesis of fund_below) carried to
     subterms (fv_scope_sub and its instances for each form) and under a binder
     (fv_scope_bind: the body of a lambda or let, its binder bound on both sides), and obtained
     from scoped (fv_scope_of_scoped).
   - fund_below at 0 (vacuous), fund_below_S (the induction step: below k and at k gives below
     S k), and fund_below_all (from the step at every index, fund_below at every index): the
     induction fund_gen_statement will be proved by.

   NOT proved here: fund_gen_statement itself (the step needs the compatibility lemmas at every
   form; JitKRefFund owns it), and nothing closes KRef_refl_statement or fundamental_statement. *)
From Coq Require Import List Bool Lia.
From Buri Require Import KLSyntax KLValue KLSemantics JitKRef.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitKRefFv.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics JitKRef.JitKRef.

(* ======================= nested induction on expr ======================= *)
Section ExprInd.
Variable Q : expr -> Prop.
Hypotheses (Hnum : forall n, Q (ENum n)) (Hstr : forall t, Q (EStr t)) (Hsym : forall s, Q (ESym s))
 (Hbool : forall b, Q (EBool b)) (Hnil : Q ENil) (Hvar : forall x, Q (EVar x))
 (Hlam : forall x b, Q b -> Q (ELam x b))
 (Hlet : forall x a b, Q a -> Q b -> Q (ELet x a b))
 (Hif : forall c a b, Q c -> Q a -> Q b -> Q (EIf c a b))
 (Hand : forall a b, Q a -> Q b -> Q (EAnd a b))
 (Hor : forall a b, Q a -> Q b -> Q (EOr a b))
 (Hcond : forall cl, Forall (fun p => Q (fst p) /\ Q (snd p)) cl -> Q (ECond cl))
 (Htrap : forall a b, Q a -> Q b -> Q (ETrap a b))
 (Hfrz : forall b, Q b -> Q (EFreeze b))
 (Htype : forall b, Q b -> Q (EType b))
 (Hdefun : forall f ps b, Q b -> Q (EDefun f ps b))
 (Happ : forall h args, Q h -> Forall Q args -> Q (EApp h args))
 (Hcall : forall f args, Forall Q args -> Q (ECall f args)).

Fixpoint expr_ind' (e : expr) : Q e :=
 match e with
 | ENum n => Hnum n | EStr t => Hstr t | ESym s => Hsym s | EBool b => Hbool b | ENil => Hnil
 | EVar x => Hvar x
 | ELam x b => Hlam x b (expr_ind' b)
 | ELet x a b => Hlet x a b (expr_ind' a) (expr_ind' b)
 | EIf c a b => Hif c a b (expr_ind' c) (expr_ind' a) (expr_ind' b)
 | EAnd a b => Hand a b (expr_ind' a) (expr_ind' b)
 | EOr a b => Hor a b (expr_ind' a) (expr_ind' b)
 | ECond cl => Hcond cl ((fix gl (l : list (expr * expr)) : Forall (fun p => Q (fst p) /\ Q (snd p)) l :=
     match l with
     | [] => @Forall_nil _ _
     | (c, b) :: l' => @Forall_cons _ (fun p => Q (fst p) /\ Q (snd p)) (c, b) l'
                    (conj (expr_ind' c) (expr_ind' b)) (gl l') end) cl)
 | ETrap a b => Htrap a b (expr_ind' a) (expr_ind' b)
 | EFreeze b => Hfrz b (expr_ind' b)
 | EType b => Htype b (expr_ind' b)
 | EDefun f ps b => Hdefun f ps b (expr_ind' b)
 | EApp h args => Happ h args (expr_ind' h) ((fix ga (l : list expr) : Forall Q l :=
     match l with [] => @Forall_nil _ _ | a :: l' => @Forall_cons _ Q a l' (expr_ind' a) (ga l') end) args)
 | ECall f args => Hcall f args ((fix ga (l : list expr) : Forall Q l :=
     match l with [] => @Forall_nil _ _ | a :: l' => @Forall_cons _ Q a l' (expr_ind' a) (ga l') end) args)
 end.
End ExprInd.

(* ======================= fv and scoped on the list forms ======================= *)
Lemma fv_cond : forall cl, fv (ECond cl) = flat_map (fun p => fv (fst p) ++ fv (snd p)) cl.
Proof.
 induction cl as [|[c b] cl IH]; [reflexivity|].
 change (fv (ECond ((c, b) :: cl))) with (fv c ++ fv b ++ fv (ECond cl)).
 rewrite IH. cbn [flat_map fst snd]. rewrite app_assoc. reflexivity.
Qed.

Lemma fv_call : forall f args, fv (ECall f args) = flat_map fv args.
Proof.
 intros f. induction args as [|a args IH]; [reflexivity|].
 change (fv (ECall f (a :: args))) with (fv a ++ fv (ECall f args)).
 rewrite IH. reflexivity.
Qed.

Lemma fv_app : forall h args, fv (EApp h args) = fv h ++ flat_map fv args.
Proof.
 intros h args. rewrite <- (fv_call [] args). reflexivity.
Qed.

Lemma scoped_cond : forall g cl,
 scoped g (ECond cl) = forallb (fun p => scoped g (fst p) && scoped g (snd p)) cl.
Proof.
 intros g. induction cl as [|[c b] cl IH]; [reflexivity|].
 change (scoped g (ECond ((c, b) :: cl))) with (scoped g c && scoped g b && scoped g (ECond cl)).
 rewrite IH. reflexivity.
Qed.

(* ======================= scoped against fv ======================= *)
Lemma bound_In : forall g x, bound g x = true -> In x g.
Proof.
 intros g x H. unfold bound in H. apply existsb_exists in H. destruct H as (y & I & E).
 apply text_eqb_eq in E. subst. exact I.
Qed.

Lemma In_filter_neq : forall x y l, In y (filter (fun z => negb (text_eqb z x)) l) <-> In y l /\ y <> x.
Proof.
 intros x y l. rewrite filter_In. split.
 - intros [I E]. split; [exact I|]. intro Q. subst. rewrite text_eqb_refl in E. discriminate.
 - intros [I N]. split; [exact I|]. apply text_eqb_neq in N. rewrite N. reflexivity.
Qed.

Theorem scoped_fv : forall g e, scoped g e = true -> forall x, In x (fv e) -> In x g.
Proof.
 intros g e. revert g.
 induction e as [n|t|s|b|  |y|y b IH|y a b IHa IHb|c a b IHc IHa IHb|a b IHa IHb|a b IHa IHb|cl F
   |a b IHa IHb|b IH|b IH|f ps b IH|h args IH F|f args F] using expr_ind';
   intros g Hs x I; cbn [fv] in I; try (destruct I; fail).
 - destruct I as [<-|[]]. apply bound_In. exact Hs.
 - cbn [scoped] in Hs. apply In_filter_neq in I. destruct I as [I N].
   destruct (IH (y :: g) Hs x I) as [E|I']; [subst; contradiction|exact I'].
 - cbn [scoped] in Hs. apply andb_prop in Hs. destruct Hs as [Sa Sb]. apply in_app_or in I. destruct I as [I|I].
   + exact (IHa g Sa x I).
   + apply In_filter_neq in I. destruct I as [I N].
     destruct (IHb (y :: g) Sb x I) as [E|I']; [subst; contradiction|exact I'].
 - cbn [scoped] in Hs. apply andb_prop in Hs. destruct Hs as [Hs Sb]. apply andb_prop in Hs. destruct Hs as [Sc Sa].
   apply in_app_or in I. destruct I as [I|I]; [exact (IHc g Sc x I)|].
   apply in_app_or in I. destruct I as [I|I]; [exact (IHa g Sa x I)|exact (IHb g Sb x I)].
 - cbn [scoped] in Hs. apply andb_prop in Hs. destruct Hs as [Sa Sb].
   apply in_app_or in I. destruct I as [I|I]; [exact (IHa g Sa x I)|exact (IHb g Sb x I)].
 - cbn [scoped] in Hs. apply andb_prop in Hs. destruct Hs as [Sa Sb].
   apply in_app_or in I. destruct I as [I|I]; [exact (IHa g Sa x I)|exact (IHb g Sb x I)].
 - change (In x (fv (ECond cl))) in I. rewrite fv_cond in I. rewrite scoped_cond in Hs.
   apply in_flat_map in I. destruct I as (p & Ip & I). rewrite forallb_forall in Hs.
   pose proof (Hs p Ip) as Sp. apply andb_prop in Sp. destruct Sp as [Sc Sb].
   rewrite Forall_forall in F. destruct (F p Ip) as [Fc Fb].
   apply in_app_or in I. destruct I as [I|I]; [exact (Fc g Sc x I)|exact (Fb g Sb x I)].
 - cbn [scoped] in Hs. apply andb_prop in Hs. destruct Hs as [Sa Sb].
   apply in_app_or in I. destruct I as [I|I]; [exact (IHa g Sa x I)|exact (IHb g Sb x I)].
 - cbn [scoped] in Hs. exact (IH g Hs x I).
 - cbn [scoped] in Hs. exact (IH g Hs x I).
 - change (In x (fv (EApp h args))) in I. rewrite fv_app in I. cbn [scoped] in Hs.
   apply andb_prop in Hs. destruct Hs as [Sh Sa]. apply in_app_or in I. destruct I as [I|I]; [exact (IH g Sh x I)|].
   apply in_flat_map in I. destruct I as (a & Ia & I). rewrite forallb_forall in Sa. rewrite Forall_forall in F.
   exact (F a Ia g (Sa a Ia) x I).
 - change (In x (fv (ECall f args))) in I. rewrite fv_call in I. cbn [scoped] in Hs.
   apply in_flat_map in I. destruct I as (a & Ia & I). rewrite forallb_forall in Hs. rewrite Forall_forall in F.
   exact (F a Ia g (Hs a Ia) x I).
Qed.

(* ======================= binders and lists ======================= *)
Lemma fv_lam_iff : forall x b y, In y (fv (ELam x b)) <-> In y (fv b) /\ y <> x.
Proof. intros x b y. cbn [fv]. apply In_filter_neq. Qed.

Lemma fv_let_iff : forall x a b y, In y (fv (ELet x a b)) <-> In y (fv a) \/ (In y (fv b) /\ y <> x).
Proof.
 intros x a b y. cbn [fv]. rewrite in_app_iff. rewrite In_filter_neq. reflexivity.
Qed.

Lemma fv_defun : forall f ps b, fv (EDefun f ps b) = [].
Proof. reflexivity. Qed.

(* A defun's body is scoped by its parameters alone, whatever the scope around it. *)
Lemma scoped_defun_fv : forall g f ps b, scoped g (EDefun f ps b) = true -> forall y, In y (fv b) -> In y ps.
Proof. intros g f ps b S. cbn [scoped] in S. apply scoped_fv. exact S. Qed.

Lemma fv_cond_iff : forall cl y,
 In y (fv (ECond cl)) <-> exists c b, In (c, b) cl /\ (In y (fv c) \/ In y (fv b)).
Proof.
 intros cl y. rewrite fv_cond, in_flat_map. split.
 - intros ([c b] & I & J). exists c, b. split; [exact I|]. apply in_app_or. exact J.
 - intros (c & b & I & J). exists (c, b). split; [exact I|]. apply in_or_app. exact J.
Qed.

Lemma fv_call_iff : forall f args y, In y (fv (ECall f args)) <-> exists a, In a args /\ In y (fv a).
Proof. intros f args y. rewrite fv_call, in_flat_map. reflexivity. Qed.

Lemma fv_app_iff : forall h args y,
 In y (fv (EApp h args)) <-> In y (fv h) \/ exists a, In a args /\ In y (fv a).
Proof. intros h args y. rewrite fv_app, in_app_iff, in_flat_map. reflexivity. Qed.

(* ======================= fund_below's scope condition ======================= *)
(* The hypothesis fund_below puts on an expression's free variables, unfolded: each is in g or
   bound on neither side. *)
Definition fv_scope {A B : Type} (g : list name) (rho0 : list (name * A)) (rho : list (name * B)) (e : expr) : Prop :=
 forall y, In y (fv e) -> In y g \/ (lookup y rho0 = None /\ lookup y rho = None).

Lemma fv_scope_of_scoped : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) e,
 scoped g e = true -> fv_scope g rho0 rho e.
Proof. intros A B g rho0 rho e S y I. left. exact (scoped_fv g e S y I). Qed.

Lemma fv_scope_sub : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) e e',
 (forall y, In y (fv e') -> In y (fv e)) -> fv_scope g rho0 rho e -> fv_scope g rho0 rho e'.
Proof. intros A B g rho0 rho e e' H F y I. apply F, H, I. Qed.

(* Under a binder x: the body, with x bound on both sides, at scope x :: g. For a lambda's body
   and a let's body; the binder's own value is whatever the two sides bind. *)
Lemma fv_scope_bind : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) x b v0 v,
 (forall y, In y (fv b) -> y <> x -> fv_scope g rho0 rho (EVar y)) ->
 fv_scope (x :: g) ((x, v0) :: rho0) ((x, v) :: rho) b.
Proof.
 intros A B g rho0 rho x b v0 v H y I. cbn [lookup]. destruct (text_eqb y x) eqn:E.
 - apply text_eqb_eq in E. subst. left. left. reflexivity.
 - apply text_eqb_neq in E. destruct (H y I E y (or_introl eq_refl)) as [J|N]; [left; right; exact J|right; exact N].
Qed.

Lemma fv_scope_lam_body : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) x b v0 v,
 fv_scope g rho0 rho (ELam x b) -> fv_scope (x :: g) ((x, v0) :: rho0) ((x, v) :: rho) b.
Proof.
 intros A B g rho0 rho x b v0 v F. apply fv_scope_bind. intros y I N z [<-|[]].
 apply F. apply fv_lam_iff. split; assumption.
Qed.

Lemma fv_scope_let_bound : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) x a b,
 fv_scope g rho0 rho (ELet x a b) -> fv_scope g rho0 rho a.
Proof. intros A B g rho0 rho x a b. apply fv_scope_sub. intros y I. apply fv_let_iff. left. exact I. Qed.

Lemma fv_scope_let_body : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) x a b v0 v,
 fv_scope g rho0 rho (ELet x a b) -> fv_scope (x :: g) ((x, v0) :: rho0) ((x, v) :: rho) b.
Proof.
 intros A B g rho0 rho x a b v0 v F. apply fv_scope_bind. intros y I N z [<-|[]].
 apply F. apply fv_let_iff. right. split; assumption.
Qed.

Lemma fv_scope_if : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) c a b,
 fv_scope g rho0 rho (EIf c a b) ->
 fv_scope g rho0 rho c /\ fv_scope g rho0 rho a /\ fv_scope g rho0 rho b.
Proof.
 intros A B g rho0 rho c a b F. cbn [fv] in F.
 split; [|split]; (eapply fv_scope_sub; [|exact F]); intros y I; cbn [fv]; rewrite !in_app_iff; tauto.
Qed.

Lemma fv_scope_pair : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) a b e,
 (forall y, In y (fv e) <-> In y (fv a) \/ In y (fv b)) ->
 fv_scope g rho0 rho e -> fv_scope g rho0 rho a /\ fv_scope g rho0 rho b.
Proof.
 intros A B g rho0 rho a b e H F.
 split; (eapply fv_scope_sub; [|exact F]); intros y I; apply H; tauto.
Qed.

Lemma fv_scope_and : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) a b,
 fv_scope g rho0 rho (EAnd a b) -> fv_scope g rho0 rho a /\ fv_scope g rho0 rho b.
Proof. intros A B g rho0 rho a b. apply fv_scope_pair. intros y. cbn [fv]. apply in_app_iff. Qed.

Lemma fv_scope_or : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) a b,
 fv_scope g rho0 rho (EOr a b) -> fv_scope g rho0 rho a /\ fv_scope g rho0 rho b.
Proof. intros A B g rho0 rho a b. apply fv_scope_pair. intros y. cbn [fv]. apply in_app_iff. Qed.

Lemma fv_scope_trap : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) a b,
 fv_scope g rho0 rho (ETrap a b) -> fv_scope g rho0 rho a /\ fv_scope g rho0 rho b.
Proof. intros A B g rho0 rho a b. apply fv_scope_pair. intros y. cbn [fv]. apply in_app_iff. Qed.

Lemma fv_scope_freeze : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) b,
 fv_scope g rho0 rho (EFreeze b) -> fv_scope g rho0 rho b.
Proof. intros A B g rho0 rho b F. exact F. Qed.

Lemma fv_scope_type : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) b,
 fv_scope g rho0 rho (EType b) -> fv_scope g rho0 rho b.
Proof. intros A B g rho0 rho b F. exact F. Qed.

Lemma fv_scope_cond : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) cl,
 fv_scope g rho0 rho (ECond cl) ->
 Forall (fun p => fv_scope g rho0 rho (fst p) /\ fv_scope g rho0 rho (snd p)) cl.
Proof.
 intros A B g rho0 rho cl F. apply Forall_forall. intros [c b] Ip. cbn [fst snd].
 split; (eapply fv_scope_sub; [|exact F]); intros y I; apply fv_cond_iff; exists c, b; tauto.
Qed.

Lemma fv_scope_app : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) h args,
 fv_scope g rho0 rho (EApp h args) -> fv_scope g rho0 rho h /\ Forall (fv_scope g rho0 rho) args.
Proof.
 intros A B g rho0 rho h args F. split.
 - eapply fv_scope_sub; [|exact F]. intros y I. apply fv_app_iff. left. exact I.
 - apply Forall_forall. intros a Ia. eapply fv_scope_sub; [|exact F]. intros y I.
   apply fv_app_iff. right. exists a. split; assumption.
Qed.

Lemma fv_scope_call : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) f args,
 fv_scope g rho0 rho (ECall f args) -> Forall (fv_scope g rho0 rho) args.
Proof.
 intros A B g rho0 rho f args F. apply Forall_forall. intros a Ia. eapply fv_scope_sub; [|exact F].
 intros y I. apply fv_call_iff. exists a. split; assumption.
Qed.

Lemma fv_scope_defun : forall {A B : Type} g (rho0 : list (name * A)) (rho : list (name * B)) f ps b,
 fv_scope g rho0 rho (EDefun f ps b).
Proof. intros A B g rho0 rho f ps b y []. Qed.

(* ======================= fund_below by induction on the index ======================= *)
Section Fund.
Variables (sealed : list name) (D : list (name * fundef)).
Notation VRel := (JitKRef.JitKRef.VRel sealed D).
Notation ERel := (JitKRef.JitKRef.ERel sealed D).
Notation fund_below := (JitKRef.JitKRef.fund_below sealed D).
Notation fund_gen_statement := (JitKRef.JitKRef.fund_gen_statement sealed D).
Notation D_wf := (JitKRef.JitKRef.D_wf sealed D).

(* The fundamental property at index k exactly, in fund_below's scope form. *)
Definition fund_at (k : nat) : Prop :=
 forall w g rho0 rho e, wf_world w -> EnvRel_with (VRel k) w g rho0 rho ->
  fv_scope g rho0 rho e -> ERel k w rho0 e rho e.

Lemma fund_below_0 : fund_below 0.
Proof. intros j L. lia. Qed.

Lemma fund_below_S : forall k, fund_below k -> fund_at k -> fund_below (S k).
Proof.
 intros k F H j L. assert (D' : (j < k)%nat \/ j = k) by lia.
 destruct D' as [Lt| ->]; [apply F; exact Lt|exact H].
Qed.

Lemma fund_below_at : forall k, fund_below (S k) -> fund_at k.
Proof. intros k F w g rho0 rho e. apply F. lia. Qed.

(* The induction fund_gen_statement is proved by: the step at every index gives fund_below at
   every index. *)
Theorem fund_below_all : (forall k, fund_below k -> fund_at k) -> forall k, fund_below k.
Proof.
 intros H k. induction k as [|k IH]; [exact fund_below_0|].
 apply fund_below_S; [exact IH|apply H; exact IH].
Qed.

Theorem fund_gen_of_step : (D_wf -> forall k, fund_below k -> fund_at k) -> fund_gen_statement.
Proof. intros H Dw k. apply fund_below_all. apply H. exact Dw. Qed.
End Fund.
End JitKRefFv.
