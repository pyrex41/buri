(* E2E-08: call contracts of KLambda primitives, proved from the primitive
   rule table (so they are discharged, not assumed, wherever they appear in a
   context), the visibility of failed and partial writes in IO-trace
   postconditions, and two refutations showing that dropping a premise of the
   calculus is unsound: the non-Boolean premise of r_if, and the measure of
   rec_total. A contract for any name that is not a KLambda primitive (a host
   operation) has no such theorem: it stays a premise of the soundness
   theorems (ctx_at). *)
From Coq Require Import List ZArith NArith String Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLMetatheory ContractLogic.
Import ListNotations.
Module ContractPrims.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics ContractLogic.ContractLogic.

Section Prims.
Variable P : profile.
Variable RP : resource -> Prop.

(* The exact contract of a non-IO primitive bound under f: its result is what
   the rule table computes; resource failure only within the policy; eval-kl
   (which evaluates new code) and undefined operations are excluded by the
   precondition. *)
Definition prim_spec (f : name) (p : prim) : cspec := CSpec f
 (fun vs s => lookup f (gfuns s) = Some (FPrim p) /\ List.length vs = prim_arity p /\
    match prim_rule P p vs s with
    | PDone (ORet _ _) | PDone (OThrow _) => True
    | PDone (OFail r) => RP r
    | _ => False end)
 (fun vs s0 v s t => t = [] /\ prim_rule P p vs s0 = PDone (ORet v s))
 (fun vs s0 x s t => t = [] /\ s = s0 /\ prim_rule P p vs s0 = PDone (OThrow x)).

Lemma prim_call_next : forall f p vs k s, lookup f (gfuns s) = Some (FPrim p) -> List.length vs = prim_arity p ->
 next P (Cfg (Ret (VPartial f [])) (KApply vs :: k) s) = prim_move P p vs [] k s.
Proof.
 intros f p vs k s Lk Ln. cbn [next ctl kont mem ret_move apply_value app]. unfold call_named. rewrite Lk.
 rewrite Ln, Nat.ltb_irrefl. rewrite <- Ln, skipn_all, firstn_all. reflexivity.
Qed.

Theorem prim_spec_valid : forall m n f p, call_at P RP m n (prim_spec f p).
Proof.
 intros m n f p vs s0 j L Phi h k s O [<- (Lk & Ln & Hr)] [HQ HE].
 pose proof (prim_call_next f p vs k s Lk Ln) as Nx. unfold prim_move in Nx.
 destruct (prim_rule P p vs s) as [o|q kont] eqn:R; [|contradiction].
 destruct o as [v s'|x|e|r|w]; try contradiction; eapply G_tau_same; try exact Nx; cbn [pout_config continue_with].
 - rewrite <- (app_nil_r h). apply HQ. cbn; auto.
 - rewrite <- (app_nil_r h). apply HE. cbn; auto.
 - apply (G_fail P RP); [exact O|exact Hr].
Qed.

(* The contract of an IO primitive: the local trace is exactly the one IO
   event with whatever response the environment gave; the result is what the
   rule computes from that response. Under Always I the event must satisfy I
   for every possible response. *)
Definition io_spec (m : mode) (f : name) (p : prim) : cspec := CSpec f
 (fun vs s => lookup f (gfuns s) = Some (FPrim p) /\ List.length vs = prim_arity p /\
    exists q kont, prim_rule P p vs s = PIO q kont /\
    forall r, inv_of m (EvIO q r) /\ match kont r with ORet _ _ | OThrow _ => True | _ => False end)
 (fun vs s0 v s t => exists q kont r, prim_rule P p vs s0 = PIO q kont /\ t = [EvIO q r] /\ kont r = ORet v s)
 (fun vs s0 x s t => exists q kont r, prim_rule P p vs s0 = PIO q kont /\ t = [EvIO q r] /\ s = s0 /\ kont r = OThrow x).

Theorem io_spec_valid : forall m n f p, call_at P RP m n (io_spec m f p).
Proof.
 intros m n f p vs s0 j L Phi h k s O [<- (Lk & Ln & q & kont & R & Hk)] [HQ HE].
 pose proof (prim_call_next f p vs k s Lk Ln) as Nx. unfold prim_move in Nx. rewrite R in Nx.
 apply (G_le P m Phi j (S j)); [lia|]. eapply G_io; [exact Nx|].
 intro r. destruct (Hk r) as [Hi Hr]. split; [exact Hi|].
 destruct (kont r) as [v s'|x|e|rr|w] eqn:Kr; try contradiction; cbn [pout_config continue_with].
 - apply HQ. exists q, kont, r; auto.
 - apply HE. exists q, kont, r; auto.
Qed.
End Prims.

(* Failed and partial writes are visible: write-byte returns normally only
   after the environment reports the full one-byte write; a failed or partial
   write (Observation.write_failed) always raises an XIO exception, and the
   event is in the local trace of the io_spec postconditions either way. *)
Theorem write_byte_visible : forall b h s, (0 <= b < 256)%Z ->
 exists kont, rule_write_byte [VNum (NInt b); VStream h] s = PIO (QWrite h [Z.to_N b]) kont /\
 forall r,
  (forall v s', kont r = ORet v s' -> r = RWrote 1 /\ v = VNum (NInt b) /\ s' = s /\
     ~ write_failed (EvIO (QWrite h [Z.to_N b]) r)) /\
  (write_failed (EvIO (QWrite h [Z.to_N b]) r) -> exists e, kont r = OThrow (XIO e)) /\
  match kont r with ORet _ _ | OThrow _ => True | _ => False end.
Proof.
 intros b h s [B0 B1]. unfold rule_write_byte.
 replace (Z.leb 0 b && Z.ltb b 256)%bool with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
 eexists; split; [reflexivity|]. intro r. split; [|split].
 - intros v s' K. destruct r; cbn in K; try discriminate.
   destruct (N.eqb count 1) eqn:C; [|destruct (N.eqb count 0); discriminate].
   apply N.eqb_eq in C; subst. injection K as <- <-. repeat split. cbn. lia.
 - intros W. destruct r; cbn in W |- *; try contradiction; eauto.
   destruct (N.eqb count 1) eqn:C; [apply N.eqb_eq in C; subst; lia|]. destruct (N.eqb count 0); eauto.
 - destruct r; cbn; try exact I. destruct (N.eqb count 1); [exact I|destruct (N.eqb count 0); exact I].
Qed.

(* ---------- dropped premises are unsound ---------- *)
Section Refutations.
Variable P : profile.
Variable RP : resource -> Prop.
Hypothesis NoStack : stack_limit P = None.

Lemma term_tau_inv : forall Phi h c c', term P Phi h c -> next P c = MTau c' -> term P Phi h c'.
Proof. intros Phi h c c' T N; inversion T; congruence. Qed.
Lemma term_final_inv : forall Phi h c o, term P Phi h c -> next P c = MFinal o -> Phi h o.
Proof. intros Phi h c o T N; inversion T; subst; [|congruence|congruence]. rewrite N in H; injection H as <-; exact H0. Qed.

Definition if0 := EIf (ENum (NInt 0)) (ENum (NInt 1)) (ENum (NInt 1)).
(* Without the non-Boolean premise, r_if would derive this total triple: its
   condition is derivable with R v := v = 0, and both branch premises are
   vacuous. The triple is false: the program raises XNotBoolean. *)
Theorem if_nonbool_premise_needed :
 deriv P RP Total [] (fun _ => True) [] (ENum (NInt 0)) (fun v _ t => v = VNum (NInt 0) /\ t = []) (fun _ _ _ => False) /\
 (forall (s1 : store) (t1 : trace), ~ (VBool true = VNum (NInt 0) /\ t1 = [])) /\
 (forall (s1 : store) (t1 : trace), ~ (VBool false = VNum (NInt 0) /\ t1 = [])) /\
 ~ triple P RP Total (fun _ => True) [] if0 (fun v _ _ => v = VNum (NInt 1)) (fun _ _ _ => False).
Proof.
 split; [|split; [intros s1 t1 [E _]; discriminate|split; [intros s1 t1 [E _]; discriminate|]]].
 - eapply r_conseq; [apply (r_val P RP Total [] [] (ENum (NInt 0)) (VNum (NInt 0)) (fun v _ t => v = VNum (NInt 0) /\ t = []) (fun _ _ _ => False) eq_refl)|..];
   cbn; auto.
 - intro T. pose (s := Store [] [] []).
   pose proof (triple_top P RP Total _ [] if0 _ _ s 0 T I) as Tm. cbn [G] in Tm.
   assert (N1 : next P (Cfg (Eval [] if0) [] s) = MTau (Cfg (Eval [] (ENum (NInt 0))) [KIf (ENum (NInt 1)) (ENum (NInt 1)) []] s))
     by (cbn; unfold push; rewrite NoStack; reflexivity).
   pose proof (term_tau_inv _ _ _ _ Tm N1) as T2.
   pose proof (term_tau_inv _ _ _ _ T2 eq_refl) as T3.
   pose proof (term_tau_inv _ _ _ _ T3 eq_refl) as T4.
   pose proof (term_final_inv _ _ _ _ T4 eq_refl) as F. cbn in F. destruct F as [_ []].
Qed.

(* Without the measure, a rec_partial-style rule for total correctness would
   validate the self-call loop f x = (f x): its body is derivable from its own
   unrestricted contract, but no call terminates. *)
Definition fx := of_string "f". Definition xx := of_string "x".
Definition loop_body := ECall fx [EVar xx].
Definition loop_spec : cspec := CSpec fx
 (fun vs s => lookup fx (gfuns s) = Some (FUser [xx] loop_body) /\ List.length vs = 1)
 (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False).
Definition loop_def := FDef loop_spec [xx] loop_body.

Theorem unmeasured_recursion_unsound :
 binds loop_def /\ body_ok P RP Total [loop_spec] loop_def /\
 ~ call_at P RP Total 0 loop_spec.
Proof.
 split; [intros vs s [Lk Ln]; split; [exact Lk|exact Ln]|split].
 - intros vs s0 [Lk Ln]. destruct vs as [|v [|v' vs]]; try discriminate. cbn [combine fd_params fd_body loop_def].
   eapply r_call with (Qs := fun vs s t => vs = [v] /\ s = s0 /\ t = []).
   + apply da_one. eapply r_conseq; [apply (r_val P RP Total _ [(xx, v)] (EVar xx) v (fun w s t => [w] = [v] /\ s = s0 /\ t = []) (fun _ _ _ => False) eq_refl)|..];
     cbn; intros; subst; auto; contradiction.
   + intros vs s1 t1 (-> & -> & ->). change (VPartial fx []) with (VPartial (c_name loop_spec) []).
     apply aj_ctx; [left; reflexivity|]. intros s ->. cbn. repeat split; auto; contradiction.
 - intro C. pose (s := Store [] [] [(fx, FUser [xx] loop_body)]).
   assert (Pre : c_pre loop_spec [VNil] s) by (split; reflexivity).
   pose proof (C [VNil] s 0 (le_n _) (top RP (fun _ _ _ => False) (fun _ _ _ => False)) [] [] s
     (top_ok RP _ _) (conj eq_refl Pre) (top_conts P RP Total 0 _ _)) as Tm. cbn [G] in Tm.
   pose (rho := [(xx, VNil)]).
   pose (c1 := Cfg (Eval rho loop_body) [] s).
   pose (c2 := Cfg (Eval rho (EVar xx)) [KCallArgs fx [] [] rho] s).
   pose (c3 := Cfg (Ret VNil) [KCallArgs fx [] [] rho] s).
   assert (Cyc : forall h c, term P (top RP (fun _ _ _ => False) (fun _ _ _ => False)) h c -> c = c1 \/ c = c2 \/ c = c3 -> False).
   { intros h c T; induction T as [h c o F _|h c c' N T IH|h c q kk N T IH]; intros [ -> | [ -> | -> ] ].
     - discriminate F. - discriminate F. - discriminate F.
     - apply IH; right; left. assert (E : next P c1 = MTau c2) by (cbn; unfold push; rewrite NoStack; reflexivity).
       rewrite E in N; injection N as <-; reflexivity.
     - apply IH; right; right. assert (E : next P c2 = MTau c3) by reflexivity. rewrite E in N; injection N as <-; reflexivity.
     - apply IH; left. assert (E : next P c3 = MTau c1) by reflexivity. rewrite E in N; injection N as <-; reflexivity.
     - discriminate N. - discriminate N. - discriminate N. }
   apply (Cyc [] c1); [|left; reflexivity].
   eapply term_tau_inv; [exact Tm|]. reflexivity.
Qed.
End Refutations.
End ContractPrims.
