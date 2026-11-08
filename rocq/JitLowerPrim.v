(* Shen/JIT Phase 2: the admitted primitives give related results on related arguments, or both
   raise. Messages are not related, except that simple-error's text is the message
   (docs/semantics.md section 8; OB-JIT-ERROR-TEXT). *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitProfile JitLowerRel.
Import ListNotations.
Module JitLowerPrim.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort JitLowerRel.JitLowerRel JitProfile.JitProfile.

Definition exn_ok (x : exn) (msg : B.text) : Prop := match x with
 | XUser t => t = msg | _ => True end.

Inductive PR (sealed : list name) (E : B.env) (pt : B.tree (B.prim * nat)) (m : B.machine) (d : N)
    (p : prim) (q : B.prim) (args : list value) (args' : list B.val) (s : store) : Prop :=
 | PR_ret v v' : prim_rule_r (jit_rules sealed) jit_profile p args s = PDone (ORet v s) ->
     B.prim_step E pt m d q args' = B.ret_to m d v' -> VR v v' -> PR sealed E pt m d p q args args' s
 | PR_raise x msg tv : prim_rule_r (jit_rules sealed) jit_profile p args s = PDone (OThrow x) ->
     B.prim_step E pt m d q args' = B.raise m msg tv -> exn_ok x msg -> PR sealed E pt m d p q args args' s.

Lemma VR_bool_eq : forall x y, x = y -> VR (VBool x) (B.VBool y).
Proof. intros; subst; constructor. Qed.

Ltac pr_ret := eapply PR_ret; [reflexivity|reflexivity|repeat constructor; try assumption].
Ltac pr_raise := eapply PR_raise; [reflexivity|reflexivity|exact I].
Ltac pr_any := first [pr_ret | pr_raise].

Section P.
Variables (sealed : list name) (E : B.env) (pt : B.tree (B.prim * nat)) (m : B.machine) (d : N) (s : store).

Lemma arith_int : forall p q (iop : Z -> Z -> Z) x y,
 (forall args, prim_rule_r (jit_rules sealed) jit_profile p args s = rule_arith_r (jit_rules sealed) jit_profile p iop args s) ->
 B.prim_step E pt m d q [B.VFix x; B.VFix y] =
   (if B.fix_fits (iop x y) then B.ret_to m d (B.VFix (iop x y)) else B.raise_s m "integer overflow") ->
 PR sealed E pt m d p q [VNum (NInt x); VNum (NInt y)] [B.VFix x; B.VFix y] s.
Proof.
 intros p q iop x y Hs Ht. destruct (B.fix_fits (iop x y)) eqn:Q.
 - eapply PR_ret with (v := VNum (NInt (iop x y))) (v' := B.VFix (iop x y)); [|exact Ht|constructor].
   rewrite Hs. unfold rule_arith_r. change (in_range (jit_rules sealed) (iop x y)) with (B.fix_fits (iop x y)). rewrite Q. reflexivity.
 - eapply PR_raise with (x := XPrim p); [|exact Ht|exact I].
   rewrite Hs. unfold rule_arith_r. change (in_range (jit_rules sealed) (iop x y)) with (B.fix_fits (iop x y)). rewrite Q. reflexivity.
Qed.

Ltac arith_tac := intros a b a' b' Ha Hb; inversion Ha; subst;
 first
 [ inversion Hb; subst;
   first [ eapply arith_int with (iop := _); [intros; reflexivity|reflexivity] | pr_any ]
 | pr_raise ].

Lemma p_add : forall a b a' b', VR a a' -> VR b b' -> PR sealed E pt m d PAdd B.PAdd [a; b] [a'; b'] s.
Proof.
 intros a b a' b' Ha Hb. inversion Ha; subst; try pr_raise; inversion Hb; subst; try pr_raise; try pr_ret.
 all: eapply arith_int with (iop := Z.add); [intros; reflexivity|reflexivity].
Qed.
Lemma p_sub : forall a b a' b', VR a a' -> VR b b' -> PR sealed E pt m d PSub B.PSub [a; b] [a'; b'] s.
Proof.
 intros a b a' b' Ha Hb. inversion Ha; subst; try pr_raise; inversion Hb; subst; try pr_raise; try pr_ret.
 all: eapply arith_int with (iop := Z.sub); [intros; reflexivity|reflexivity].
Qed.
Lemma p_mul : forall a b a' b', VR a a' -> VR b b' -> PR sealed E pt m d PMul B.PMul [a; b] [a'; b'] s.
Proof.
 intros a b a' b' Ha Hb. inversion Ha; subst; try pr_raise; inversion Hb; subst; try pr_raise; try pr_ret.
 all: eapply arith_int with (iop := Z.mul); [intros; reflexivity|reflexivity].
Qed.


Lemma p_pgt : forall a b a' b', VR a a' -> VR b b' -> PR sealed E pt m d PGt B.PGt [a; b] [a'; b'] s.
Proof.
 intros a b a' b' Ha Hb. inversion Ha; subst; try pr_raise; inversion Hb; subst; try pr_raise.
 - pr_ret.
 - assert (S0 : prim_rule_r (jit_rules sealed) jit_profile PGt [VNum (NInt z); VNum (NFloat b0)] s =
      PDone (ORet (VBool (jit_order PGt (B.compare_fix_real z b0))) s)) by reflexivity.
   assert (T0 : forall c0, B.compare_fix_real z b0 = c0 -> B.prim_step E pt m d B.PGt [B.VFix z; B.VReal b0] =
      B.boolean m d (match c0, B.PGt with
       | Some Lt, (B.PLt | B.PLe) | Some Gt, (B.PGt | B.PGe) | Some Eq, (B.PLe | B.PGe) => true | _, _ => false end))
     by (intros c0 Ec; rewrite <- Ec; reflexivity).
   destruct (B.compare_fix_real z b0) as [[]|] eqn:Cc; eapply PR_ret; [exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor].
 - assert (S0 : prim_rule_r (jit_rules sealed) jit_profile PGt [VNum (NFloat b0); VNum (NInt z)] s =
      PDone (ORet (VBool (jit_order PGt (flip (B.compare_fix_real z b0)))) s)) by reflexivity.
   assert (T0 : forall c0, B.compare_fix_real z b0 = c0 -> B.prim_step E pt m d B.PGt [B.VReal b0; B.VFix z] =
      B.boolean m d (match c0, B.PGt with
       | Some Gt, (B.PLt | B.PLe) | Some Lt, (B.PGt | B.PGe) | Some Eq, (B.PLe | B.PGe) => true | _, _ => false end))
     by (intros c0 Ec; rewrite <- Ec; reflexivity).
   destruct (B.compare_fix_real z b0) as [[]|] eqn:Cc; eapply PR_ret; [exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor].
 - eapply PR_ret; [reflexivity|reflexivity|]. apply VR_bool_eq. reflexivity.
Qed.

Lemma p_plt : forall a b a' b', VR a a' -> VR b b' -> PR sealed E pt m d PLt B.PLt [a; b] [a'; b'] s.
Proof.
 intros a b a' b' Ha Hb. inversion Ha; subst; try pr_raise; inversion Hb; subst; try pr_raise.
 - pr_ret.
 - assert (S0 : prim_rule_r (jit_rules sealed) jit_profile PLt [VNum (NInt z); VNum (NFloat b0)] s =
      PDone (ORet (VBool (jit_order PLt (B.compare_fix_real z b0))) s)) by reflexivity.
   assert (T0 : forall c0, B.compare_fix_real z b0 = c0 -> B.prim_step E pt m d B.PLt [B.VFix z; B.VReal b0] =
      B.boolean m d (match c0, B.PLt with
       | Some Lt, (B.PLt | B.PLe) | Some Gt, (B.PGt | B.PGe) | Some Eq, (B.PLe | B.PGe) => true | _, _ => false end))
     by (intros c0 Ec; rewrite <- Ec; reflexivity).
   destruct (B.compare_fix_real z b0) as [[]|] eqn:Cc; eapply PR_ret; [exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor].
 - assert (S0 : prim_rule_r (jit_rules sealed) jit_profile PLt [VNum (NFloat b0); VNum (NInt z)] s =
      PDone (ORet (VBool (jit_order PLt (flip (B.compare_fix_real z b0)))) s)) by reflexivity.
   assert (T0 : forall c0, B.compare_fix_real z b0 = c0 -> B.prim_step E pt m d B.PLt [B.VReal b0; B.VFix z] =
      B.boolean m d (match c0, B.PLt with
       | Some Gt, (B.PLt | B.PLe) | Some Lt, (B.PGt | B.PGe) | Some Eq, (B.PLe | B.PGe) => true | _, _ => false end))
     by (intros c0 Ec; rewrite <- Ec; reflexivity).
   destruct (B.compare_fix_real z b0) as [[]|] eqn:Cc; eapply PR_ret; [exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor].
 - eapply PR_ret; [reflexivity|reflexivity|]. apply VR_bool_eq. reflexivity.
Qed.

Lemma p_pge : forall a b a' b', VR a a' -> VR b b' -> PR sealed E pt m d PGe B.PGe [a; b] [a'; b'] s.
Proof.
 intros a b a' b' Ha Hb. inversion Ha; subst; try pr_raise; inversion Hb; subst; try pr_raise.
 - pr_ret.
 - assert (S0 : prim_rule_r (jit_rules sealed) jit_profile PGe [VNum (NInt z); VNum (NFloat b0)] s =
      PDone (ORet (VBool (jit_order PGe (B.compare_fix_real z b0))) s)) by reflexivity.
   assert (T0 : forall c0, B.compare_fix_real z b0 = c0 -> B.prim_step E pt m d B.PGe [B.VFix z; B.VReal b0] =
      B.boolean m d (match c0, B.PGe with
       | Some Lt, (B.PLt | B.PLe) | Some Gt, (B.PGt | B.PGe) | Some Eq, (B.PLe | B.PGe) => true | _, _ => false end))
     by (intros c0 Ec; rewrite <- Ec; reflexivity).
   destruct (B.compare_fix_real z b0) as [[]|] eqn:Cc; eapply PR_ret; [exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor].
 - assert (S0 : prim_rule_r (jit_rules sealed) jit_profile PGe [VNum (NFloat b0); VNum (NInt z)] s =
      PDone (ORet (VBool (jit_order PGe (flip (B.compare_fix_real z b0)))) s)) by reflexivity.
   assert (T0 : forall c0, B.compare_fix_real z b0 = c0 -> B.prim_step E pt m d B.PGe [B.VReal b0; B.VFix z] =
      B.boolean m d (match c0, B.PGe with
       | Some Gt, (B.PLt | B.PLe) | Some Lt, (B.PGt | B.PGe) | Some Eq, (B.PLe | B.PGe) => true | _, _ => false end))
     by (intros c0 Ec; rewrite <- Ec; reflexivity).
   destruct (B.compare_fix_real z b0) as [[]|] eqn:Cc; eapply PR_ret; [exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor].
 - eapply PR_ret; [reflexivity|reflexivity|]. apply VR_bool_eq. reflexivity.
Qed.

Lemma p_ple : forall a b a' b', VR a a' -> VR b b' -> PR sealed E pt m d PLe B.PLe [a; b] [a'; b'] s.
Proof.
 intros a b a' b' Ha Hb. inversion Ha; subst; try pr_raise; inversion Hb; subst; try pr_raise.
 - pr_ret.
 - assert (S0 : prim_rule_r (jit_rules sealed) jit_profile PLe [VNum (NInt z); VNum (NFloat b0)] s =
      PDone (ORet (VBool (jit_order PLe (B.compare_fix_real z b0))) s)) by reflexivity.
   assert (T0 : forall c0, B.compare_fix_real z b0 = c0 -> B.prim_step E pt m d B.PLe [B.VFix z; B.VReal b0] =
      B.boolean m d (match c0, B.PLe with
       | Some Lt, (B.PLt | B.PLe) | Some Gt, (B.PGt | B.PGe) | Some Eq, (B.PLe | B.PGe) => true | _, _ => false end))
     by (intros c0 Ec; rewrite <- Ec; reflexivity).
   destruct (B.compare_fix_real z b0) as [[]|] eqn:Cc; eapply PR_ret; [exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor].
 - assert (S0 : prim_rule_r (jit_rules sealed) jit_profile PLe [VNum (NFloat b0); VNum (NInt z)] s =
      PDone (ORet (VBool (jit_order PLe (flip (B.compare_fix_real z b0)))) s)) by reflexivity.
   assert (T0 : forall c0, B.compare_fix_real z b0 = c0 -> B.prim_step E pt m d B.PLe [B.VReal b0; B.VFix z] =
      B.boolean m d (match c0, B.PLe with
       | Some Gt, (B.PLt | B.PLe) | Some Lt, (B.PGt | B.PGe) | Some Eq, (B.PLe | B.PGe) => true | _, _ => false end))
     by (intros c0 Ec; rewrite <- Ec; reflexivity).
   destruct (B.compare_fix_real z b0) as [[]|] eqn:Cc; eapply PR_ret; [exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor|exact S0|exact (T0 _ eq_refl)|constructor].
 - eapply PR_ret; [reflexivity|reflexivity|]. apply VR_bool_eq. reflexivity.
Qed.

Lemma p_cons : forall a b a' b', VR a a' -> VR b b' -> PR sealed E pt m d PCons B.PCons [a; b] [a'; b'] s.
Proof. intros. eapply PR_ret; [reflexivity|reflexivity|constructor; auto]. Qed.
Lemma p_hd : forall a a', VR a a' -> PR sealed E pt m d PHd B.PHd [a] [a'] s.
Proof. intros a a' Ha. inversion Ha; subst; try pr_raise. eapply PR_ret; [reflexivity|reflexivity|auto]. Qed.
Lemma p_tl : forall a a', VR a a' -> PR sealed E pt m d PTl B.PTl [a] [a'] s.
Proof. intros a a' Ha. inversion Ha; subst; try pr_raise. eapply PR_ret; [reflexivity|reflexivity|auto]. Qed.
Lemma p_consp : forall a a', VR a a' -> PR sealed E pt m d PConsP B.PConsp [a] [a'] s.
Proof. intros a a' Ha. inversion Ha; subst; (eapply PR_ret; [reflexivity|reflexivity|constructor]). Qed.
Lemma p_numberp : forall a a', VR a a' -> PR sealed E pt m d PNumberP B.PNumberp [a] [a'] s.
Proof. intros a a' Ha. inversion Ha; subst; (eapply PR_ret; [reflexivity|reflexivity|constructor]). Qed.
Lemma p_stringp : forall a a', VR a a' -> PR sealed E pt m d PStringP B.PStringp [a] [a'] s.
Proof. intros a a' Ha. inversion Ha; subst; (eapply PR_ret; [reflexivity|reflexivity|constructor]). Qed.

(* = against a constant pguard admits. The model spends fuel only at absvectors, which VR never
   relates, and both semantics answer every other pair, so no resource case arises. *)
Lemma text_eqb_same : forall t u, B.text_eqb t u = text_eqb t u.
Proof. induction t as [|x t IH]; destruct u as [|y u]; cbn; auto; rewrite IH; reflexivity. Qed.
Definition eqr_of (r : bool) : B.eqr := if r then B.EqT else B.EqF.
Lemma eq_core : forall R h n a b a' b' hb f, VR a a' -> VR b b' -> existsb eq_safe_val [a'; b'] = true ->
 exists r, eq_depth_r R jit_profile h (S n) a b = Some r /\ B.eq_val hb (S f) a' b' = eqr_of r.
Proof.
 intros R h n a b a' b' hb f Ha Hb G.
 inversion Ha; subst; inversion Hb; subst; cbn in G |- *; try discriminate G.
 all: rewrite ?orb_false_r in G.
 all: first
  [ eexists; split; [reflexivity|]; unfold eqr_of;
    first
    [ reflexivity
    | destruct (Z.eqb _ _); reflexivity
    | destruct (B.compare_fix_real _ _) as [[]|]; reflexivity
    | rewrite text_eqb_same; destruct (text_eqb _ _); reflexivity
    | destruct (Bool.eqb _ _); reflexivity
    | match goal with |- context [JitFloat.JitFloat.is_nan ?x && JitFloat.JitFloat.is_nan ?y] =>
        replace (JitFloat.JitFloat.is_nan x && JitFloat.JitFloat.is_nan y)%bool with false
          by (destruct (JitFloat.JitFloat.is_nan x), (JitFloat.JitFloat.is_nan y); cbn in G |- *; congruence);
        unfold JitFloat.JitFloat.eqv; destruct (JitFloat.JitFloat.compare x y) as [[]|]; reflexivity end ]
  | idtac ].
Qed.

Lemma p_eq : forall a b a' b', VR a a' -> VR b b' -> existsb eq_safe_val [a'; b'] = true ->
 PR sealed E pt m d PEqual B.PEq [a; b] [a'; b'] s.
Proof.
 intros a b a' b' Ha Hb G.
 destruct (eq_core (jit_rules sealed) (heap s) (List.length (heap s)) a b a' b' (B.m_heap m) 4095 Ha Hb G) as [r [K T]].
 assert (S0 : prim_rule_r (jit_rules sealed) jit_profile PEqual [a; b] s =
   match eq_depth_r (jit_rules sealed) jit_profile (heap s) (S (List.length (heap s))) a b with
   | Some r => ret (VBool r) s | None => PDone (OWrong (kw "equality-undefined")) end) by reflexivity.
 assert (T0 : B.prim_step E pt m d B.PEq [a'; b'] = match B.eq_val (B.m_heap m) (S 4095) a' b' with
   | B.EqT => B.boolean m d true | B.EqF => B.boolean m d false
   | B.EqIdentity => B.MStuck B.RIdentity | B.EqCycle => B.MStuck B.RCyclic end) by reflexivity.
 rewrite K in S0. rewrite T in T0.
 eapply PR_ret with (v := VBool r) (v' := B.VBool r); [exact S0| |constructor].
 rewrite T0. destruct r; reflexivity.
Qed.
End P.

(* Why pguard leaves symbols out (OB-JIT-SYM-TEXT): B.sym_of_text is not injective on texts of
   code points, so two names the source tells apart can be one symbol in the model. C interns
   by name and agrees with the source. And -0.0 = 0.0 in both semantics. *)
Example eq_sym_text_collision : forall R h n hb f,
 B.sym_of_text [1; 1]%N = B.sym_of_text [65537]%N /\
 eq_depth_r R jit_profile h (S n) (VSym [1; 1]%N) (VSym [65537]%N) = Some false /\
 B.eq_val hb (S f) (B.VSym (B.sym_of_text [1; 1]%N)) (B.VSym (B.sym_of_text [65537]%N)) = B.EqT.
Proof. intros. split; [vm_compute; reflexivity|split; reflexivity]. Qed.
Example eq_signed_zero : JitFloat.JitFloat.eqv 0 9223372036854775808 = true /\
 jit_order PEqual (JitFloat.JitFloat.compare 0 9223372036854775808) = true.
Proof. vm_compute. split; reflexivity. Qed.

Definition vguard (q : B.prim) (args' : list B.val) : bool := match q with
 | B.PEq => existsb eq_safe_val args' | _ => true end.

Lemma prim_agree : forall sealed E pt m d p q args args' s,
 pmap p = Some q -> Forall2 VR args args' -> List.length args = prim_arity p -> vguard q args' = true ->
 PR sealed E pt m d p q args args' s.
Proof.
 intros sealed E pt m d p q args args' s Hp H L G.
 destruct p; cbn in Hp; try discriminate; injection Hp as <-; cbn [prim_arity] in L.
 all: destruct H as [|a a' args args' Ha H]; [discriminate|]; destruct H as [|b b' args args' Hb H].
 all: try (destruct H; [|discriminate L]).
 all: try discriminate L.
 all: first [ apply p_add | apply p_sub | apply p_mul | apply p_pgt | apply p_plt | apply p_pge | apply p_ple
            | apply p_cons | apply p_hd | apply p_tl | apply p_consp | apply p_numberp | apply p_stringp
            | apply p_eq ]; assumption.
Qed.
End JitLowerPrim.
