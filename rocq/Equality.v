(* A separate, proved certificate checker for the equational core.
   This is not yet a proof that shen/kernel.shen implements this checker. *)
From Coq Require Import List Arith.
Import ListNotations.

Inductive term := Var : nat -> term | Const : nat -> term | App : term -> term -> term.
Fixpoint term_eq_dec (a b : term) : {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Fixpoint substitute (sigma : list term) (t : term) : term :=
 match t with
 | Var n => match nth_error sigma n with Some x => x | None => Var n end
 | Const n => Const n
 | App f x => App (substitute sigma f) (substitute sigma x)
 end.
Inductive certificate :=
| Refl : term -> certificate
| Sym : certificate -> certificate
| Trans : certificate -> certificate -> certificate
| Cong : certificate -> certificate -> certificate
| Instance : nat -> list term -> certificate.
Fixpoint check (rules : list (term * term)) (p : certificate) : option (term * term) :=
 match p with
 | Refl a => Some (a,a)
 | Sym q => match check rules q with Some (a,b) => Some (b,a) | None => None end
 | Trans q r =>
    match check rules q, check rules r with
    | Some (a,b), Some (c,d) => if term_eq_dec b c then Some (a,d) else None
    | _,_ => None
    end
 | Cong q r =>
    match check rules q, check rules r with
    | Some (a,b), Some (c,d) => Some (App a c, App b d)
    | _,_ => None
    end
 | Instance n sigma =>
    match nth_error rules n with
    | Some (a,b) => Some (substitute sigma a, substitute sigma b)
    | None => None
    end
 end.

Section Soundness.
Variable D : Type.
Variable constants : nat -> D.
Variable application : D -> D -> D.
Fixpoint denote (rho : nat -> D) (t : term) : D :=
 match t with
 | Var n => rho n | Const n => constants n
 | App f x => application (denote rho f) (denote rho x)
 end.
Definition valid (eqn : term * term) := forall rho, denote rho (fst eqn) = denote rho (snd eqn).
Definition substituted_env (rho : nat -> D) (sigma : list term) n :=
 match nth_error sigma n with Some t => denote rho t | None => rho n end.
Lemma substitution_correct : forall t sigma rho,
 denote rho (substitute sigma t) = denote (substituted_env rho sigma) t.
Proof.
 induction t; intros; simpl.
 - unfold substituted_env; destruct (nth_error sigma n); reflexivity.
 - reflexivity.
 - rewrite IHt1, IHt2; reflexivity.
Qed.
Theorem check_sound_under_rules : forall rules,
 (forall a b, In (a,b) rules -> valid (a,b)) ->
 forall p a b, check rules p = Some (a,b) -> valid (a,b).
Proof.
 intros rules Hr p; induction p; intros a b H.
 - inversion H; subst; intro rho; reflexivity.
 - simpl in H. destruct (check rules p) as [[x y]|] eqn:E; try discriminate.
   inversion H; subst. specialize (IHp _ _ eq_refl). intro rho; simpl; symmetry; apply IHp.
 - simpl in H. destruct (check rules p1) as [[x y]|] eqn:E1; try discriminate.
   destruct (check rules p2) as [[z w]|] eqn:E2; try discriminate.
   destruct (term_eq_dec y z); try discriminate. subst z.
   inversion H; subst. specialize (IHp1 _ _ eq_refl); specialize (IHp2 _ _ eq_refl).
   intro rho; simpl. transitivity (denote rho y); [apply IHp1 | apply IHp2].
 - simpl in H. destruct (check rules p1) as [[x y]|] eqn:E1; try discriminate.
   destruct (check rules p2) as [[z w]|] eqn:E2; try discriminate.
   inversion H; subst. specialize (IHp1 _ _ eq_refl); specialize (IHp2 _ _ eq_refl).
   intro rho; simpl. specialize (IHp1 rho); specialize (IHp2 rho).
   simpl in IHp1, IHp2. rewrite IHp1, IHp2; reflexivity.
 - simpl in H. destruct (nth_error rules n) as [[x y]|] eqn:E; try discriminate.
   inversion H; subst. intro rho; simpl. rewrite !substitution_correct.
   apply (Hr x y). eapply nth_error_In; eauto.
Qed.
End Soundness.
Print Assumptions check_sound_under_rules.
